from hdbcli import dbapi
from lib.backupRecoveryCommon import BackupRecoveryManager, BackupType, DestinationType
from lib.ExpectedSimpleResultSet import ExpectedSimpleResultSet
from lib.ExpectedSortedSimpleResultSet import ExpectedSortedSimpleResultSet
from hierarchies.libHierarchiesGlobals import HierarchyGlobalSymbols
from lib.NewDbTestCase import NewDbTestCase, logger
from lib.performanceUtils import Stopwatch, triggerRSVersionGC, waitForRSVersionGC, preloadTables
from lib.RemoteDataManager import RemoteDataManager
from lib.sqlTestUtilityMethods import isOemBuild, isAddressSanitizerBuild, isAddressSanitizerDSOBuild, _isBuildType, executeSetIniParametersWithRetrys, enableSQLDBCTrace
from lib.SQLHelper import SQLHelper
from lib.ChangeConfigChecker import ChangeConfigChecker
from lib.getIndexServerList import getIndexServerList
from connectionManager import DecoratedDbApiConnection
from multidb.multidbUtil import MultiDBUtil


import codecs
import datetime
import os
import re
import servicecontrol
import subprocess
import sys
import threading
import time
import types

class TestError(Exception):
    pass

class SqlTestCase(NewDbTestCase):
    """Base class for SQL tests of NewDB. A SQL test should inherit this class.

    Sets up a connection before every test (done in setUp()) and closes it
    afterwards (done in tearDown()). The connection is usable in between via the
    self.conn variable."""

    _CONFIG_DIR = "config"
    _TEST_CONFIG_FILENAME = "testConfig.ini"
    _REMOTE_TABLE_CONFIG_FILENAME = "remoteData.ini"
    _REMOTE_DELIVERY_UNIT_CONFIG_FILENAME = "remoteDataDeliveryUnit.ini"
    _REMOTE_RECOVERY_CONFIG_FILENAME = "remoteDataRecovery.ini"

    _tableImportCache = {}

    _itabLeakCheck = { 'disabled': True }
    _ignoreItabLeaks = []
    _memoryLeakCheck = []
    _configChangeChecker = True
    _isESSActive = True
    _isDebugBuild = False
    _isReleaseBuild = False
    _isSyncGuardBuild = False
    _hasDebugAllocatorEnabled = False
    _hasEPMInstalled = False
    _tableImportTearDownStmts = []
    _supportCheckIndexserverConnection = True
    _preventRecheckIndexserverConnection = False
    _observers = []
    _max_resultrows = 20

    def __init__(self, methodName='runTest'):
        super(SqlTestCase, self).__init__(methodName)
        self.backupRecoveryManager = BackupRecoveryManager(self)
        self.configChangeChecker = None

    def setUp(self):
        """Creates a connection that can be used with dbapi. The connection
        handle is stored in self.conn."""
        self.conman = self.createConnectionManager()
        doAutocommit = True if self._malFunctionMode else False
        if self.globalCfg.has_key("autocommit"):
            doAutocommit = int(self.globalCfg["autocommit"])
        doDistributed = 'ALL'
        if self.globalCfg.has_key("clientDistributed") and self.globalCfg["clientDistributed"] == 'OFF':
            doDistributed = 'OFF'
        self.conn = self.conman.createConnection(autocommit=doAutocommit, DISTRIBUTION=doDistributed)

        # check table consistency
        if len(self._checkTableConsistency) is not 0:
            checkActions = list(set(self._checkTableConsistency))
            cursor = self.conn.cursor()
            for action in checkActions:
                if not action:
                    continue
                print '[setUp test]',
                self.checkTableConsistency(cursor, action)
            cursor.close()

        # check file permissions in MDC high-isolation mode
        if self.isMultiDBDatabaseIsolationActive():
            self.checkFilePermissions()

        if DecoratedDbApiConnection.readOnlyModeActive():
            DecoratedDbApiConnection._readOnlyExecution = True
        self.notifyObservers({'type': 'SETUP',
                              'subtype': 'end',
                              'testName': self._testMethodName,
                              'moduleTestName': self.name(),
                              'testCase': type(self).__name__,
                              'testCaseObj': self})
        if self._leakCheckTestCase:
            self.runHdbConsChecked('mm flag Pool -rs astrace; mm resetusage -r Pool')
            print "Activated alloc traces"

    def hasDebugAllocatorEnabled(self):
        """Check whether debug allocators are active for hdbindexserver."""
        return self._hasDebugAllocatorEnabled

    def isDebugBuild(self):
        """Check whether test is running on a debug build."""
        return self._isDebugBuild

    def isReleaseBuild(self):
        """Check whether test is running on a release build."""
        return self._isReleaseBuild

    def isSyncGuardBuild(self):
        """Check whether test is running on a sync-guard build."""
        return self._isSyncGuardBuild

    def isEPMInstalled(self):
        return self._hasEPMInstalled

    def isCoverageRun(self):
        """Check if it's a coverage run."""
        return os.environ.get('USE_HDBCOV', False)

    @classmethod
    def notifyObservers(cls, action):
        for observer in cls._observers:
            observer.notify(action)

    @classmethod
    def registerObserver(cls, observer):
        cls._observers.append(observer)

    def tearDown(self):
        """Closes the connection which was set up in setUp()."""

        if self._leakCheckTestCase:
            self.runHdbConsChecked('mm flag Pool -rd astrace')
            print "Deactivated alloc trace"
            cursor = self.conn.cursor()
            cursor.execute('ALTER SYSTEM RECLAIM VERSION SPACE')
            cursor.execute('ALTER SYSTEM CLEAR COLUMN RESULT CACHE')
            cursor.execute('ALTER SYSTEM CLEAR SQL PLAN CACHE')
            cursor.execute('ALTER SYSTEM CLEAR RESULT CACHE')
            cursor.execute("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('joins', 'plan_cache_size') = '0' WITH RECONFIGURE")
            cursor.execute("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') UNSET ('joins', 'plan_cache_size') WITH RECONFIGURE")
            self.conn.commit()
            logFile = os.path.join(os.path.realpath(self._leakCheckLogPath), 'leaks_%d_%s_%s.log' % (os.getpid(), self.name().replace('.', '_'), self.getCurCfg()))
            self.runHdbConsChecked('mm top -r -l 0 -m %d -o "%s" Pool' % (self._leakCheckBytesThreshold, logFile))
            print "Remaining allocations dumped to", logFile

        if DecoratedDbApiConnection.readOnlyModeActive():
            DecoratedDbApiConnection._readOnlyExecution = False

        # check file permissions in MDC high-isolation mode
        if self.isMultiDBDatabaseIsolationActive():
            self.checkFilePermissions()

        self.conman.closeAllConnections()

        # check table consistency
        if len(self._checkTableConsistency) is not 0:
            checkActions = list(set(self._checkTableConsistency))
            doDistributed = 'ALL'
            if self.globalCfg.has_key("clientDistributed") and self.globalCfg["clientDistributed"] == 'OFF':
                doDistributed = 'OFF'
            conn = self.conman.createConnection(autocommit=True, DISTRIBUTION=doDistributed)
            cursor = conn.cursor()
            for action in checkActions:
                if not action:
                    continue
                print '[tearDown test]',
                self.checkTableConsistency(cursor, action)
            cursor.close()
            conn.close()

        #self.conn_loc = self.conman.createConnection(autocommit=True, DISTRIBUTION='ON')
        #cursor = self.conn_loc.cursor()
        #removeVolumeIds=[]
        #host = ""
        #port = 0
        #self.checkPendingRemoteOperations(cursor, removeVolumeIds, 0, host, port, False)
        self.notifyObservers({'type': 'TEARDOWN',
                              'subtype': 'end',
                              'testWasSkipped': self._testWasSkipped,
                              'testName': self._testMethodName,
                              'moduleTestName': self.name(),
                              'testCase': type(self).__name__,
                              'testCaseObj': self})
        self._testWasSkipped = False


    def _checkIndexserverConnection(self, conman, host=None, port=None):
        try:
            if host:
                conn = conman.createConnection(address=host, port=port, DISTRIBUTION='OFF')
            else:
                conn = conman.createConnection()
            try:
                with conn.cursor() as cursor:
                    cursor.execute("select c.host, s.sql_port from (select host, port from m_connections where connection_id=current_connection) as c left join m_services as s on c.host=s.host and c.port=s.port")
                    ret = cursor.fetchall()
                    if len(ret) != 1:
                        print "%s: --- checkIndexserverConnection: wrong result" % datetime.datetime.now() # as it is a left outer join, result should always be 1 row
                        return False
                    host2, port2 = ret[0]
                    if host and (host != host2 or port2 != port):
                        print "%s: --- checkIndexserverConnection: wrong connection - (requested: %s:%s, connected: %s:%s)" % (datetime.datetime.now(), host, port, host2, port2)
                        return False
                    return True
            finally:
                conn.close()
        except dbapi.Error, e:
            print "%s: --- checkIndexserverConnection: failure: %s" % (datetime.datetime.now(), e)
            return False

    def getRunningServers(self):
        return [(None, None, None)]

    def checkIndexserverConnection(self, testFrameworkCall=False, numReps=None, getDumpsOnReconnectFailure=True):
        if testFrameworkCall:
            from infraenv import InfraEnv
            print "%s: --- checkIndexserverConnection as previous test failed" % datetime.datetime.now()
            # if not supported (some tests do not need/have an indexserver, so checking for a connection makes no sense)
            if not self._supportCheckIndexserverConnection:
                print "%s: --- checkIndexserverConnection skipped as not supported" % datetime.datetime.now()
                return True
            # if not active
            if not InfraEnv().getValueAsBool("tfwCheckForIndexserverConnection", 'ENABLED', False): # disabled on local machines
                print "%s: --- checkIndexserverConnection skipped as it is disabled in InfraEnv" % datetime.datetime.now()
                return True
            if self._preventRecheckIndexserverConnection:
                print "%s: --- checkIndexserverConnection skipped due to prevent rechecking" % datetime.datetime.now()
                return False
        #else:
        #    print "%s: --- checkIndexserverConnection due to explicit call" % datetime.datetime.now()
        # cannot use global available conman as some tests overwrite setUp and therefore no conman will be created
        userdbConman = self.createConnectionManager()
        from multidb.multidbUtil import MultiDBUtil
        if MultiDBUtil.isMultiDBInstance():
            systemdbConman = self.createSystemDBConnectionManager()

        numReps = numReps or (60 if self.isDebugBuild() else 30)
        waitTimeInBetween = 10 # seconds
        try:
            error = False
            lastError = False
            numTries = 0
            # add connection manager to use
            serverToCheck = map(lambda l: (userdbConman, l[0], l[2]), self.getRunningServers())
            if MultiDBUtil.isMultiDBInstance():
                serverToCheck.append((systemdbConman, None, None))
            for server in serverToCheck:
                #print "*** check server %s:%s, conman is systemDB=%s" % (server[1], server[2], server[0] != userdbConman) # temporary
                while True:
                    numTries += 1
                    if not self._checkIndexserverConnection(server[0], server[1], server[2]):
                        error = True
                        lastError = True
                        if numTries >= numReps:
                            print "%s: --- checkIndexserverConnection: connection to %s:%s not responding, try %d of %d" % (datetime.datetime.now(), server[1], server[2], numTries, numReps)
                            break
                        else:
                            print "%s: --- checkIndexserverConnection: connection to %s:%s not responding, try %d of %d, wait %d seconds ..." % (datetime.datetime.now(), server[1], server[2], numTries, numReps, waitTimeInBetween)
                            time.sleep(waitTimeInBetween)
                    else:
                        lastError = False
                        break
                if lastError:
                    break # no need to check the other servers if the current one is not available
            if error: # we had (at least) one error
                if lastError: # and (at least) one server didn't come back
                    if testFrameworkCall:
                        print "%s: --- checkIndexserverConnection: connection could not be re-established, no further tries will be made" % datetime.datetime.now()
                        self._preventRecheckIndexserverConnection = True
                    else:
                        print "%s: --- checkIndexserverConnection: connection could not be re-established" % datetime.datetime.now()
                    # limit to a useful subset as for example STATISTICS may acquire locks
                    if getDumpsOnReconnectFailure:
                        multiDBName = MultiDBUtil.getDatabaseName()
                        if multiDBName:
                            traceSuffix = "/DB_%s" % multiDBName
                        else:
                            traceSuffix = ""
                        cmd = "hdbcons -t 120 'runtimedump dump'"
                        print "%s: --- get RTE dumps for analysis: %s" % (datetime.datetime.now(), cmd)
                        os.system(cmd)
                        print "%s: --- finished" % datetime.datetime.now()
                        print
                        cmd = "PYTHONPATH=$(echo $DIR_EXECUTABLE)/Python/lib/python2.7 gstack $(pgrep -u $(whoami) hdbindexserver) > $(echo $SAP_RETRIEVAL_PATH)/trace%s/indexserver_%s.gstack" % (traceSuffix, datetime.datetime.now().strftime("%Y%m%d_%H%M%S%f"))
                        print "%s: --- get gstack callstacks of hdbindexserver for analysis: %s" % (datetime.datetime.now(), cmd)
                        os.system(cmd)
                        print "%s: --- finished" % datetime.datetime.now()
                        print
                        cmd = "PYTHONPATH=$(echo $DIR_EXECUTABLE)/Python/lib/python2.7 gstack $(pgrep -u $(whoami) hdbesserver) > $(echo $SAP_RETRIEVAL_PATH)/trace%s/esserver_%s.gstack" % (traceSuffix, datetime.datetime.now().strftime("%Y%m%d_%H%M%S%f"))
                        print "%s: --- get gstack callstacks of hdbesserver for analysis: %s" % (datetime.datetime.now(), cmd)
                        os.system(cmd)
                        print "%s: --- finished" % datetime.datetime.now()
                else:
                    print "%s: --- checkIndexserverConnection: connection was re-established. Following indexserver were checked: %s" % (datetime.datetime.now(), zip(*zip(*serverToCheck)[1:]) if serverToCheck else []) # pylint: disable=W0142
            #else:
            #    print "%s: --- checkIndexserverConnection: no connection issue" % datetime.datetime.now()
            return error, lastError
        except Exception, e:
            print " %s: -- checkIndexserverConnection: exception: %s" % (datetime.datetime.now(), e)
            raise
        finally:
            userdbConman.closeAllConnections()
            if MultiDBUtil.isMultiDBInstance():
                systemdbConman.closeAllConnections()

    def restartDaemonServices(self, runlevel=1, timeout=600):
        """ Restart all services started by the daemon with run level greater than the one provided. """
        scontrolverbosity = 1 # Print error messages
        scontrol = servicecontrol.ServiceController(scontrolverbosity)
        if self.isCoverageRun():
            timeout *= 6
        scontrol.restartAllDaemonServices(runlevel, timeout)
        del scontrol

    def restartIndexServer(self, timeout=600.0, server=None, dbName=None, ignoreItabLeaks=()):
        """Restart indexserver. When used on linux, start watchdog thread, fetch
        debug information when timeout is exceeded and send it via email."""

        # double restart timeout for debug builds
        if self.isDebugBuild():
            if self._verbosity > 0:
                print("#### double timeout, original timeout was " + str(timeout))
            timeout *= 2

        if self.isAddressSanitizerBuild():
            timeout *= 3

        if self.isCoverageRun():
            timeout *= 6

        if self._verbosity > 0:
            serverInfo = ""
            if not server: serverInfo = "All"
            else: serverInfo = str(server)
            onDatabaseStr = ""
            if dbName: onDatabaseStr = " on database %s "%(dbName)
            print "#### restart indexserver: " + serverInfo + onDatabaseStr + " with timeout " + str(timeout) + " (" + str(datetime.datetime.now()) + ")"
        if sys.platform.startswith("linux") and timeout > 0:

            restartThread = threading.Thread(
                target=self.__restartIndexServer,
                kwargs={'server':server, 'timeout':timeout, 'dbName':dbName, 'ignoreItabLeaks': ignoreItabLeaks})
            restartThread.start()
            restartThread.join(timeout + (0 if (not SqlTestCase._itabLeakCheck.has_key('disabled') or SqlTestCase._itabLeakCheck['disabled'] == True) else 60)) # give itabLeakCheckVerify 60s to finish

            if restartThread.isAlive():
                # timeout occurred

                print "restartIndexServer() seems to hang, fetching debug information...", ("(" + str(datetime.datetime.now()) + ")")

                def run(*cmds):
                    """Run the given commands *cmds. Pipe stdout of a command to
                    the following one.
                    Return (rc, stdout, stderr) of the last command."""
                    process = []
                    last = 0
                    # First process just runs the command with no special stdin
                    try:
                        process.append(subprocess.Popen(cmds[0],
                                                    stdout=subprocess.PIPE,
                                                    stderr=subprocess.PIPE,
                                                    shell=True))
                    except Exception as e:
                        print "%s at executing '%s'" % (e, cmds[0])
                        raise

                    for i in range(1, len(cmds)):
                        # 2nd to last process get stdout -> stdin
                        try:
                            process.append(subprocess.Popen(cmds[i],
                                                stdin=process[i - 1].stdout,
                                                stdout=subprocess.PIPE,
                                                stderr=subprocess.PIPE,
                                                shell=True))
                        except Exception as e:
                            print "%s at executing '%s'" % (e, cmds[i])
                            raise
                        last = i

                    _stdout, _stderr = process[last].communicate()
                    return process[last].returncode, _stdout, _stderr

                def getRTEDumps():
                    for server in self.getRunningServers():
                        try:
                            if server[0]:
                                command = "distribute execute %s:%s runtimedump dump" % (server[0], server[1])
                            else:
                                command = "runtimedump dump"
                            print "%s: get 1. RTE dump for %s:%s" % (datetime.datetime.now(), server[0], server[1])
                            rc, stdout, stderr = run("hdbcons -t 120  '%s'" % command)
                            print "rc", rc
                            print "stdout", stdout
                            print "stderr", stderr
                        except Exception, e:
                            print "caught unknown exception during RTE dump"
                            print e
                            # ignore this exception here, the test fails nevertheless
                    time.sleep(15)
                    for server in self.getRunningServers():
                        try:
                            if server[0]:
                                command = "distribute execute %s:%s runtimedump dump" % (server[0], server[1])
                            else:
                                command = "runtimedump dump"
                            print "%s: get 2. RTE dump for %s:%s" % (datetime.datetime.now(), server[0], server[1])
                            rc, stdout, stderr = run("hdbcons -t 120  '%s'" % command)
                            print "rc", rc
                            print "stdout", stdout
                            print "stderr", stderr
                        except Exception, e:
                            print "caught unknown exception during RTE dump"
                            print e
                            # ignore this exception here, the test fails nevertheless

                getRTEDumps()
                msg = "restartIndexServer() didn't come back after %.1f secs\n" % timeout
                self.fail(msg)
        # ----------------------------------------------------------------------

        else:
            self.__restartIndexServer(server=server, timeout=timeout, dbName=dbName, ignoreItabLeaks=ignoreItabLeaks)


    def __restartIndexServer(self, server=None, timeout=600.0, dbName=None, ignoreItabLeaks=()):
        """ Restart index server. In case server is None ALL services
            of type indexserver are restarted in parallel. This may lead to
            problems in a environment with multiple indexservers and
            indexserver like services! restartDaemonServices() should
            therefore be prefered in case multiple servers should be
            restarted. """

        try:
            # statistics server will be stopped again below in itabLeakCheckInit()
            self.itabLeakCheckVerify(ignoreItabLeaks=ignoreItabLeaks, reenableStatisticsServer=False)
            self.memoryLeakCheckVerify()
        except dbapi.Error as e:
            if e[0] <> -10709: # Connection refused error
                raise
            print ('!!!! WARNING: Itab leak check failed with error: %s'%(str(e)))

        scontrolverbosity = 1 # Print error messages
        scontrol = servicecontrol.ServiceController(scontrolverbosity)
        if server:
            serviceString = str(server)
            serviceTokens = serviceString.split(":")
            if len(serviceTokens) == 1 and len(serviceTokens[0]) > 0:
                host = "localhost"
                port = serviceTokens[0]
            elif len(serviceTokens) == 2:
                host = serviceTokens[0]
                port = serviceTokens[1]
            else:
                raise Exception("Invalid server string '%s'" % str(server))

            service = scontrol.get(port, host)
            if (service and
                    service['type'] == servicecontrol.ServiceType.IndexServer):
                scontrol.restart(port, host, timeout)
            else:
                raise Exception(
                    "Service '%s' is not a valid indexserver" % str(server))
        else:
            scontrol.restartAll(servicecontrol.ServiceType.IndexServer, None, timeout, dbName)
        doAutocommit = False
        if self.globalCfg.has_key("autocommit"):
            doAutocommit = int(self.globalCfg["autocommit"])
        doDistributed = 'ALL'
        if self.globalCfg.has_key("clientDistributed") and self.globalCfg["clientDistributed"] == 'OFF':
            doDistributed = 'OFF'
        self.itabLeakCheckInit()
        self.memoryLeakCheckInit()
        # restore connection
        self.conn = self.conman.createConnection(autocommit=doAutocommit, DISTRIBUTION=doDistributed)
        del scontrol

    def __createConnectionIfNotpassed(self, cursor):
        closeCursor = False
        if cursor is None:
            cursor = self.conn.cursor()
            closeCursor = True
        return cursor, closeCursor

    def executeSQLReturnSingleResult(self, stmt, cursor = None, raiseException = True):
        cursor, closeCursor = self.__createConnectionIfNotpassed(cursor)
        return SQLHelper.executeSQLReturnSingleResult(stmt, cursor, closeCursor, raiseException)

    def executeSQLReturnSingleResults(self, stmt, cursor = None, raiseException = True):
        """returns an array of singleResult values (instead of the usual tuple) to easier insert into sets"""
        cursor, closeCursor = self.__createConnectionIfNotpassed(cursor)
        return SQLHelper.executeSQLReturnSingleResults(stmt, cursor, closeCursor, raiseException)

    def executeSQLReturnResult(self, stmt, cursor = None, raiseException = True):
        cursor, closeCursor = self.__createConnectionIfNotpassed(cursor)
        return SQLHelper.executeSQLReturnResult(stmt, cursor, closeCursor, raiseException)

    def checkTopology(self):
        conn = self.conman.createConnection()
        cursor = conn.cursor()
        try:
            cursor.execute("CALL CHECK_CATALOG('CHECK_TOPOLOGY','','','')")
            result = cursor.fetchall()
            if len(result) is not 0:
                print "check topology failed"
                for row in result:
                    print row
                self.fail("CHECK_CATALOG showed inconsistent metadata")
        except dbapi.Error, err:
            print "check topology failed", err
            # more detail information of error
            cursor.execute("select * from m_services sv, m_volumes vol where sv.host = vol.host and sv.port = vol.port and sv.active_status <> 'YES'")
            ret = cursor.fetchall()
            print "invalid server lists:", ret
            raise
        finally:
            cursor.close()
            if conn :
                self.conman.closeConnection(conn)

    def checkCatalogIntegrity(self):
        conn = self.conman.createConnection()
        cursor = conn.cursor()
        try:
            cursor.execute("CALL CHECK_CATALOG('CHECK_OBJECT_REFERENTIAL_INTEGRITY','','','')")
            result = cursor.fetchall()
            if len(result) is not 0:
                print "catalog check failed"
                for row in result:
                    print row
                self.fail("CHECK_CATALOG showed inconsistent metadata")
        except dbapi.Error, err:
            print "catalog check Failed", err
            raise
        finally:
            cursor.close()
            if conn :
                self.conman.closeConnection(conn)

    def createUser(self, user, password, setparameters=None, restricted=None):
        if setparameters:
            if restricted:
                self.execute('CREATE RESTRICTED USER %s PASSWORD %s NO FORCE_FIRST_PASSWORD_CHANGE %s' % (user, password, setparameters))
                self.execute('ALTER USER %s ENABLE CLIENT CONNECT' %user)

            else:
                self.execute('CREATE USER %s PASSWORD %s NO FORCE_FIRST_PASSWORD_CHANGE %s' % (user, password, setparameters))
        else:
            if restricted:
                self.execute('CREATE RESTRICTED USER %s PASSWORD %s NO FORCE_FIRST_PASSWORD_CHANGE' % (user, password))
                self.execute('ALTER USER %s ENABLE CLIENT CONNECT' %user)
            else:
                self.execute('CREATE USER %s PASSWORD %s NO FORCE_FIRST_PASSWORD_CHANGE' % (user, password))
        self.conn.commit()

    def createRole(self, roleName):
        with self.conn.cursor() as cursor:
            cursor.execute("CREATE ROLE " + roleName)
            self.conn.commit()

    def creatCollection(self, collectionName, conn=None):
        if conn is None:
            conn = self.conn

        with conn.cursor() as cursor:
            try:
                cursor.execute("create collection %s" % collectionName)
            finally:
                conn.commit()

    def createTable(self, createSql, partitioning=False, params=[], conn=None, replicate=False, commit=True):
        """
        Create table. Parameter partitioning controls, if the table should be partitioned or not.
        The WITH PARAMETERS in the SQL statement is not allowed! Parameters should be passed with the list params

        See also: :ref:`db-object-creation`
        """

        if conn is None:
            conn = self.conn

        with conn.cursor() as cursor:
            try:
                statements = self.createTableStatements(createSql, partitioning, params, replicate)
                for statement in statements:
                    cursor.execute(statement)
            finally:
                if commit:
                    conn.commit()

    def createTableStatements(self, createSql, partitioning=False, params=[], replicate=False):
        """Generate Create table Statements. Parameter partitioning controls, if the table should be partitioned or not.
        The WITH PARAMETERS in the SQL statement is not allowed! Parameters should be passed with the list params"""

        statements = []
        workParams = params[:]

        splitCount = 2

        if partitioning:
            keys = []
            # extract primary keys from sql statement
            matches = re.findall("(\"?)([a-z0-9%_\-/]+?)(\"?) +?[a-z0-9_\-/]+?(?: *?\([0-9]*\))? +?primary +?key *?[a-z\s]*?", createSql, re.I)
            if len(matches) > 0:
                for match in matches:
                    key = match[1]
                    if match[0] != "\"" or match[2] != "\"": # convert to uppercase if without quotes
                        key = key.upper()
                    key = key.strip()
                    keys.append(key)
            else:
                matches = re.findall("primary +?key *?[a-z\s]*? *?\(([a-z0-9_\-/ ,\"]+?)\)", createSql, re.I)
                if len(matches) > 0:
                    for match in matches[0].split(','):
                        key = match.replace("\"", "")
                        if key == match: # convert to uppercase if without quotes
                            key = key.upper()
                        key = key.strip()
                        keys.append(key)

            if len(keys) > 0:
                workParams.append("'PARTITION_SPEC' = 'HASH %(splitCount)i %(primaryKeys)s'" % {"splitCount": splitCount, "primaryKeys": ", ".join(keys)})
            else:
                workParams.append("'PARTITION_SPEC' = 'ROUNDROBIN %i'" % splitCount)

        if replicate:
            if partitioning != True:  # only set one at a time
                workParams.append("'PARTITION_SPEC' = 'REPLICATE 3'")

        if len(workParams) > 0:
            sql = createSql + " WITH PARAMETERS(%s)" % ",\n".join(workParams)
        else:
            sql = createSql

        statements.append(sql)

        #if distribution:
        #    for i in range(splitCount):
        #        if len(params) > 0:
        #            sql = createSql + " WITH PARAMETERS(%s)" % ",\n".join(params)
        #        else:
        #            sql = createSql
        #
        #        matches = re.findall(" +?TABLE +?(?:(?:\"([^\(\)]+?)\")|([^ \(\)]+)) *?", sql, re.I)
        #        tablename = matches[0][0] if matches[0][0] != "" else matches[0][1]
        #        sql = sql.replace(tablename, tablename + "_" + str(i + 1))
        #        statements.append(sql)
        #
        return statements

    def createCollection(self, collectionName, caseSensitive=False, conn=None):
        if conn is None:
            conn = self.conn
        if caseSensitive:
            stmt = 'create collection "%s"' % collectionName
        else:
            stmt = 'create collection %s' % collectionName
        try:
            with conn.cursor() as cursor:
                cursor.execute(stmt)
                conn.commit()
        except:
            raise

    def dropAndCreateSchema(self, schemaName, cascade = False):
        with self.conn.cursor() as cursor:
            try:
                sqlCmd = 'DROP SCHEMA \"' + schemaName + '\"'
                if cascade:
                    sqlCmd += " CASCADE"
                cursor.execute(sqlCmd)
                self.conn.commit()
            except dbapi.Error, err:
                if err[0] != 362:
                    raise
            cursor.execute('CREATE SCHEMA \"' + schemaName + '\"')
            self.conn.commit()

    def createStatistics(self, tableName, histType="HISTOGRAM", caseSensitive=False, persistMode=None, qerror=None, qtheta=None, memory=None):
        """create statistics """
        if caseSensitive:
            sql = 'CREATE STATISTICS ON "' + tableName + '" TYPE ' + histType
        else:
            sql = "CREATE STATISTICS ON " + tableName + " TYPE " + histType

        if persistMode != None:
            sql = sql + " PERSISTENT " + persistMode

        if qerror != None or qtheta != None:
            sql = sql + " CONSTRAINT 'QOPTIMAL'"

        if qerror != None:
            sql = sql + " QERROR " + str(qerror)

        if qtheta != None:
            sql = sql + " QTHETA " + str(qtheta)

        if memory != None:
            sql = sql + " MEMORY " + str(memory)

        try:
            with self.conn.cursor() as cursor:
                cursor.execute(sql)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 2:
                raise

    def dropStatisticsONTable(self, tableName, caseSensitive=False, IgnoreErr = False):
        """drop statistics """
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP STATISTICS ON "' + tableName + '"')
                else:
                    cursor.execute("DROP STATISTICS ON " + tableName)
                self.conn.commit()
        except dbapi.Error, err:
            # Ignore Error: (1089, 'no matching data statistics ..')
            if not IgnoreErr and err[0] != 1089:
                raise

    def dropProcedure(self, procedureName, withCascade=False, caseSensitive=False, conn=None):
        """remove procedure if it already exists"""
        try:
            if conn is None:
                conn = self.conn
            with conn.cursor() as cursor:
                if caseSensitive:
                    procedureName = '"%s"' % procedureName
                cursor.execute("DROP PROCEDURE " + procedureName + (" CASCADE" if withCascade else ""))
                conn.commit()
        except dbapi.Error, err:
            if err[0] != 328:
                raise

    def dropLibrary(self, libraryName, withCascade=False, caseSensitive=False, conn=None):
        """remove library if it already exists"""
        try:
            if conn is None:
                conn = self.conn
            with conn.cursor() as cursor:
                if caseSensitive:
                    libraryName = '"%s"' % libraryName
                cursor.execute("DROP LIBRARY " + libraryName + (" CASCADE" if withCascade else ""))
                conn.commit()
        except dbapi.Error, err:
            if err[0] != 724:
                raise

    def dropView(self, viewName, option=""):
        """remove view if it already exists.
        Parameter option can be None, 'RESTRICT' or 'CASCADE'."""
        assert option in ["", "CASCADE", "RESTRICT"]

        dropStmt = " ".join(["DROP VIEW", viewName, option])
        try:
            with self.conn.cursor() as cursor:
                cursor.execute(dropStmt)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 321:
                # view not found
                raise

    def dropTable(self, tableName, caseSensitive=False, withCascade = False, commit=True, conn = None):
        """remove table if it already exists"""
        withCascadeStr = ""
        if withCascade:
            withCascadeStr = " CASCADE"
        if conn is None:
            conn = self.conn
        try:
            with conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP TABLE "' + tableName + '"' + withCascadeStr)
                else:
                    cursor.execute("DROP TABLE " + tableName + withCascadeStr)
                if commit:
                    conn.commit()
                if self._malFunctionMode:
                    deleted = False
                    try:
                        cursor.execute("DROP TABLE " + tableName + withCascadeStr)
                    except:
                        deleted = True
                    if not deleted:
                        print "table " + tableName + " not deleted, sleeping for 1s"
                        time.sleep(1)
        except dbapi.Error, err:
            if err[0] != 259:
                raise

    def truncateTable(self, tableName, caseSensitive=False):
        """truncate table if it exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('TRUNCATE TABLE "' + tableName + '"')
                else:
                    cursor.execute("TRUNCATE TABLE " + tableName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 259:
                raise

    def dropFunction(self, tableName):
        """remove function if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                cursor.execute("DROP PROCEDURE " + tableName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] == 7:
                try:
                    with self.conn.cursor() as cursor:
                        cursor.execute("DROP FUNCTION " + tableName)
                        self.conn.commit()
                except dbapi.Error, err:
                    if err[0] != 2823 and err[0] != 328:
                        raise
            elif err[0] != 2823 and err[0] != 328:
                raise

    def dropTableType(self, tableTypeName):
        """remove table type if it already exists"""
        self.dropType(tableTypeName)

    def dropType(self, typeName):
        """remove type if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                cursor.execute("DROP TYPE " + typeName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 395:
                raise

    def dropSchema(self, schemaName, caseSensitive=False, conn=None):
        """remove schema if it already exists"""
        if not conn:
            conn = self.conn

        try:
            with conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP SCHEMA "' + schemaName + '" CASCADE')
                else:
                    cursor.execute("DROP SCHEMA " + schemaName + " CASCADE")
                conn.commit()
        except dbapi.Error, err:
            if err[0] != 362:
                raise

    def emptySchema(self, schema='SYSTEM'):
        """ remove all physical tables from the schema, useful for cleaning up SYSTEM which can't be dropped """
        self.setSchema(schema)
        with self.conn.cursor() as cursor:
            cursor.execute("SELECT VIEW_NAME FROM VIEWS WHERE SCHEMA_NAME=? AND VIEW_NAME NOT LIKE '_SYS%'", schema)
            for (view, ) in cursor.fetchall():
                self.dropView('"' + view.replace('"', '""') + '"', "CASCADE")
            cursor.execute("SELECT TABLE_NAME FROM M_TABLES WHERE SCHEMA_NAME=? AND TABLE_NAME NOT LIKE '_SYS%'", schema)
            for (table, ) in cursor.fetchall():
                self.dropTable(table.replace('"', '""'), caseSensitive=True)
            cursor.execute("SELECT PROCEDURE_NAME FROM PROCEDURES WHERE SCHEMA_NAME=? AND PROCEDURE_NAME NOT LIKE '_SYS%'", schema)
            for (procedure, ) in cursor.fetchall():
                self.dropProcedure('"' + procedure.replace('"', '""') + '"')
            cursor.execute("SELECT SEQUENCE_NAME FROM SEQUENCES WHERE SCHEMA_NAME=? AND SEQUENCE_NAME NOT LIKE '_SYS%'", schema)
            for (sequence, ) in cursor.fetchall():
                self.dropSequence('"' + sequence.replace('"', '""') + '"')

    def dropSequence(self, sequenceName):
        """remove sequence if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                cursor.execute("DROP SEQUENCE " + sequenceName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 313:
                raise

    def dropSynonym(self, synonymName, caseSensitive=False):
        """remove synonym if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP SYNONYM "' + synonymName + '"')
                else:
                    cursor.execute("DROP SYNONYM " + synonymName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 315:
                raise

    def dropPublicSynonym(self, synonymName, caseSensitive=False):
        """remove synonym if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP PUBLIC SYNONYM "' + synonymName + '"')
                else:
                    cursor.execute("DROP PUBLIC SYNONYM " + synonymName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 315:
                raise

    def dropTrigger(self, triggerName, caseSensitive=False):
        """remove trigger if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP TRIGGER "' + triggerName + '"')
                else:
                    cursor.execute('DROP TRIGGER ' + triggerName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 445:
                raise

    def dropIndex(self, indexName, caseSensitive=False):
        """remove index if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP INDEX "' + indexName + '"')
                else:
                    cursor.execute('DROP INDEX ' + indexName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 261:
                # index not found
                raise

    def dropFulltextIndex(self, indexName, caseSensitive=False):
        """remove fulltext index if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP FULLTEXT INDEX "' + indexName + '"')
                else:
                    cursor.execute('DROP FULLTEXT INDEX ' + indexName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 261:
                # index not found
                raise

    def dropGeocodeIndex(self, indexName, caseSensitive=False):
        """remove geocode index if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP GEOCODE INDEX "' + indexName + '"')
                else:
                    cursor.execute('DROP GEOCODE INDEX ' + indexName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 261:
                # index not found
                raise

    def dropUser(self, userName, conn=None):
        """remove user if it already exists"""
        if not conn:
            conn = self.conn

        try:
            with conn.cursor() as cursor:
                cursor.execute("DROP USER " + userName + " CASCADE")
                conn.commit()
        except dbapi.Error, err:
            if err[0] != 332:
                raise

    def dropRole(self, userName):
        """remove role if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                cursor.execute("DROP ROLE " + userName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 389:
                raise

    def dropUsergroup(self, groupName):
        """remove usergroup if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                cursor.execute("DROP USERGROUP " + groupName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 702:
                raise

    def dropCredential(self, component, purpose, credentialType, user=None):
        """remove credential if it  exists"""
        try:
            with self.conn.cursor() as cursor:
                cursor.execute("DROP CREDENTIAL FOR %s COMPONENT '%s' PURPOSE '%s' TYPE '%s'" % (((" USER %s " % user) if user else ""), component, purpose, credentialType))
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 466:
                raise

    def dropAllCredentials(self, component=None):
        with self.conn.cursor() as cursor:
            cursor.execute("select COMPONENT, PURPOSE, TYPE from SYS.P_CREDENTIALS_%s" % (" where COMPONENT = '%s'" % component if component is not None else ""))
            res = cursor.fetchall()
            for r in res:
                self.dropCredential(r[0], r[1], r[2])

    def dropCalculationScenario(self, scenarioName, cascade=False):
        """remove calculation scenario if it already exists"""
        sql = "DROP CALCULATION SCENARIO " + scenarioName
        if cascade:
            sql += " CASCADE"
        try:
            with self.conn.cursor() as cursor:
                cursor.execute(sql)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 2048 and err[0] != 443:
                raise

    def dropAuditPolicy(self, policyName):
        """remove audit policy if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                cursor.execute("DROP AUDIT POLICY " + policyName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 3847:
                raise

    def dropAllRemoteSourcesForAdapterName(self, adapterName):
        with self.conn.cursor() as cursor:
            cursor.execute("SELECT remote_source_name FROM sys.remote_sources WHERE adapter_name = ?", (adapterName, ))
            existingAdapters = cursor.fetchall()
            for remoteSourceName in existingAdapters:
                self.dropRemoteSource(remoteSourceName[0], caseSensitive=True)
        return len(existingAdapters)

    def dropRemoteSource(self, remoteSourceName, caseSensitive=False):
        """remove remote source if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    remoteSourceName = '"%s"' % remoteSourceName
                cursor.execute("DROP REMOTE SOURCE " + remoteSourceName + " CASCADE")
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 471:
                raise

    def dropRemoteSubscription(self, RSubName):
        try:
            with self.conn.cursor() as cursor:
                cursor.execute("DROP REMOTE SUBSCRIPTION " + RSubName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 641:
                raise

    def dropStatisticsByName(self, statisticsName, caseSensitive=False):
        """remove statistics if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP STATISTICS "' + statisticsName + '"')
                else:
                    cursor.execute("DROP STATISTICS " + statisticsName)
                self.conn.commit()
        except dbapi.Error, err:
            # Ignore Error: 1089 - data statistics object not found for name
            if err[0] != 1089:
                raise

    def dropStatisticsOnTable(self, tableName, columnNames, caseSensitive=False):
        """remove statistics if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP STATISTICS ON "' + tableName + '" ' + columnNames)
                else:
                    cursor.execute("DROP STATISTICS ON " + tableName + " " + columnNames)
                self.conn.commit()
        except dbapi.Error, err:
            # Ignore Error: 1089 - data statistics object not found for specified parameters
            if err[0] != 1089:
                raise

    def dropConstraint(self, table, constraint, caseSensitive=False):
        if caseSensitive:
            stmt = 'alter table "%s" drop constraint "%s"' % (table, constraint)
        else:
            stmt = 'alter table %s drop constraint %s' % (table, constraint)
        try:
            with self.conn.cursor() as cursor:
                cursor.execute(stmt)
                self.conn.commit()
        except dbapi.Error, err:
            ERR_SQL_INV_OBJ_NAME = 397
            if err[0] != ERR_SQL_INV_OBJ_NAME:
                raise

    def dropWorkloadClass(self, workload_class, caseSensitive=False):
        if caseSensitive:
            stmt = 'drop workload class "%s"' % workload_class
        else:
            stmt = 'drop workload class %s' % workload_class
        try:
            with self.conn.cursor() as cursor:
                cursor.execute(stmt)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 660:
                raise

    def dropWorkloadMapping(self, workload_mapping, caseSensitive=False):
        if caseSensitive:
            stmt = 'drop workload mapping "%s"' % workload_mapping
        else:
            stmt = 'drop workload mapping %s' % workload_mapping
        try:
            with self.conn.cursor() as cursor:
                cursor.execute(stmt)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 662:
                raise

    def dropCollection(self, collectionName, caseSensitive=False, conn=None):
        if conn is None:
            conn = self.conn
        if caseSensitive:
            stmt = 'drop collection "%s"' % collectionName
        else:
            stmt = 'drop collection %s' % collectionName
        try:
            with conn.cursor() as cursor:
                cursor.execute(stmt)
                conn.commit()
        except dbapi.Error, err:
            if err[0] != 259:
                raise

    def checkResultDict(self, info, stmt, expected, exclude=[], conn_ = None):
        cursor = None
        if conn_ is not None:
            cursor = conn_.cursor()
        else:
            cursor = self.conn.cursor()
        cursor.execute(stmt)
        rs = cursor.fetchall()
        rscols = [(d[0]) for d in cursor.description]
        result = []
        if expected != None:
            self.assertTrue(len(expected) == len(rs), "%s:: # of records: expected: %d, result: %d\nexpected:\n%s\nresult:\n%s"
                    % (info, len(expected), len(rs), expected, rs))
        if self._verbosity >= 3 and (expected == None or (expected != None and (len(expected) > 0 or len(rs) > 0))):
            print '--[%s]' % rscols
        for i in range(len(rs)):
            row = {}
            if self._verbosity >= 3:
                print '--[%s]' % rs[i]
            r = rs[i]
            for j in range(len(rscols)):
                key = rscols[j]
                if expected != None and key not in exclude:
                    exp = expected[i]
                    self.assertTrue(exp[key] == r[key], "%s:: expected[%d][%s]: %s, result[%d][%s]: %s"
                            % (info, i, key, exp[key], i, key, r[key]))
                else:
                    row[key] = r[key]
            if expected == None:
                result.append(row)
        cursor.close()
        return result

    def checkResultSet(self, info, stmt, expected, conn_ = None, compareFirstColumnOnly = False):
        cursor = None
        if conn_ is not None:
            cursor = conn_.cursor()
        else:
            cursor = self.conn.cursor()
        cursor.execute(stmt)
        rs = cursor.fetchall()
        result = []
        if expected != None:
            self.assertTrue(len(expected) == len(rs), "%s:: # of records: expected: %d, result: %d\nexpected:\n%s\nresult:\n%s"
                    % (info, len(expected), len(rs), expected, rs))
        for i in range(len(rs)):
            row = []
            if self._verbosity >= 3:
                print '--[%s]' % rs[i]
            for j in range(len(rs[i])):
                if expected != None:
                    self.assertTrue(expected[i][j] == rs[i][j], "%s:: expected[%d][%d]: %s, result[%d][%d]: %s"
                            % (info, i, j, expected[i][j], i, j, rs[i][j]))
                else:
                    row.append(rs[i][j])
                if compareFirstColumnOnly == True:
                    break
            if expected == None:
                result.append(row)
        cursor.close()
        return result

    def verboseInfo(self, info, verbosity = 3):
        if self._verbosity >= verbosity:
            print '--%s' % info

    def expectErr(self, stmts, errorcode, info = '', commit = True, conn_ = None, ignoreErr = False):
        """Execute given statements and except dbapi.Error with errorcode to be raised."""
        conn = conn_
        if conn == None:
            conn = self.conn
        results = []
        for stmt in stmts:
            cursor = conn.cursor()
            errorcode_ = 0
            errormessage_ = ''
            try:
                cursor.execute(stmt)
            except dbapi.Error as e:
                errorcode_ = e[0]
                errormessage_ = e[1]
            finally:
                cursor.close()

            if commit == True:
                conn.commit()

            if ignoreErr == False:
                self.assertEqual(errorcode, errorcode_,
                    "The following statement did not trigger errorcode %d (but %d : %s): %s:\n%s"
                    % (errorcode, errorcode_, errormessage_, info, stmt))

            r = [errorcode, errormessage_]
            results.append(r)

        self.verboseInfo(results)
        return results

    def expectErrs(self, stmts, errorcodes, commit = True, conn_ = None):
        """Execute given statements and except dbapi.Error with errorcode to be
        raised."""
        conn = conn_
        if conn == None:
            conn = self.conn
        results = []
        for stmt in stmts:
            cursor = conn.cursor()
            errorcode_ = 0
            errormessage_ = ''
            try:
                cursor.execute(stmt)
            except dbapi.Error as e:
                errorcode_ = e[0]
                errormessage_ = e[1]
            finally:
                cursor.close()

            if commit == True:
                conn.commit()

            errorcode = errorcodes[0]
            for e in errorcodes:
                if errorcode_ == e:
                    errorcode = e
                    break

            self.assertEqual(errorcode, errorcode_,
                "The following statement did not trigger errorcode %d (but %d : %s):\n%s"
                % (errorcode, errorcode_, errormessage_, stmt))

            r = [errorcode, errormessage_]
            results.append(r)

        self.verboseInfo(results)
        return results

    def createAndSetSchema(self, schema, caseSensitive=False):
        self.dropSchema(schema, caseSensitive)
        self.createSchema(schema, caseSensitive)
        self.setSchema(schema, caseSensitive)

    def dropAndSetSchema(self, schema, caseSensitive=False):
        self.setSchema("SYSTEM")
        self.dropSchema(schema, caseSensitive)

    def createSchema(self, schema, caseSensitive=False, conn=None):
        """create schema"""

        if not conn:
            conn = self.conn

        with conn.cursor() as cursor:
            if caseSensitive:
                cursor.execute('CREATE SCHEMA "' + schema + '"')
            else:
                cursor.execute("CREATE SCHEMA " + schema)
            conn.commit()

    def setSchema(self, schema, caseSensitive=False):
        """set schema"""
        if caseSensitive:
            self.conn.cursor().execute('SET SCHEMA "' + schema + '"')
        else:
            self.conn.cursor().execute("SET SCHEMA " + schema)
        self.conn.commit()

    def dropTask(self, taskName, caseSensitive=False):
        """drop task"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP TASK "' + taskName + '"')
                else:
                    cursor.execute("DROP TASK " + taskName )
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 256:
                raise

    def dropEpmModel(self, modelName, caseSensitive=False):
        """drop epm model"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP EPM MODEL "' + modelName + '"')
                else:
                    cursor.execute("DROP EPM MODEL " + modelName )
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 489:
                raise

    def dropEpmQuerySource(self, querySourceName, caseSensitive=False):
        """drop epm query source"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP EPM QUERY SOURCE "' + querySourceName + '"')
                else:
                    cursor.execute("DROP EPM QUERY SOURCE " + querySourceName )
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 492:
                raise

    def dropAdapter(self, adapterName, caseSensitive=False):
        """remove adapter if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP ADAPTER "' + adapterName + '"' )
                else:
                    cursor.execute('DROP ADAPTER ' + adapterName )
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 474:
                raise

    def dropAgent(self, agentName, caseSensitive=False):
        """remove agent if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    agentName = '"{0}"'.format(agentName)
                cursor.execute('DROP AGENT ' + agentName + ' CASCADE')
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 507:
                raise

    def dropAgentGroup(self, agentGroupName, caseSensitive=False):
        """remove agent group if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP AGENT GROUP "' + agentGroupName + '"' )
                else:
                    cursor.execute('DROP AGENT GROUP ' + agentGroupName )
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 664:
                raise

    def dropPSE(self, pseName, caseSensitive=False):
        """remove pse if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP PSE "' + pseName + '"' )
                else:
                    cursor.execute('DROP PSE ' + pseName )
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 5639:
                raise

    def dropProvider(self, providerType, providerName, caseSensitive=False, cascade=False):
        """remove provider if it exists
        providerType -- JWT, LDAP, SAML (no default)
        caseSensitive -- (default False)
        cascade -- (default false)"""
        cascadeClause = " cascade" if cascade else ""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP '+ providerType + ' PROVIDER "' + providerName + '"' + cascadeClause)
                else:
                    cursor.execute('DROP '+ providerType + ' PROVIDER ' + providerName + cascadeClause)
                self.conn.commit()
        except dbapi.Error, err:
            if providerType is "LDAP":
                if err[0] != 4202:
                    raise
            else:
                if err[0] != 4229:
                    raise

    def dropSpatialUnitOfMeasure(self, unitName, caseSensitive=False):
        """remove spatial unit of measure if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP SPATIAL UNIT OF MEASURE "' + unitName + '"')
                else:
                    cursor.execute('DROP SPATIAL UNIT OF MEASURE ' + unitName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 480:
                raise

    def dropSpatialReferenceSystem(self, srsName, caseSensitive=False):
        """remove spatial reference system if it already exists"""
        try:
            with self.conn.cursor() as cursor:
                if caseSensitive:
                    cursor.execute('DROP SPATIAL REFERENCE SYSTEM "' + srsName + '"')
                else:
                    cursor.execute('DROP SPATIAL REFERENCE SYSTEM ' + srsName)
                self.conn.commit()
        except dbapi.Error, err:
            if err[0] != 482:
                raise

    def checkTable(self, tableName, testUnload=True):
        import uniqueChecker
        errors = []
        uniqueChecker.checkTable(self.conn, tableName, errors)
        if len(errors) > 0:
            errStr = "".join(errors)
            self.fail(("checkTable for %s failed with %d errors:\n" % (tableName, len(errors)))
                       + errStr)
        elif testUnload:
            try:
                self.conn.cursor().execute("UNLOAD %s" % tableName)
            except dbapi.Error, err:
                if err[0] != 259:
                    raise
                else:
                    pass
            uniqueChecker.checkTable(self.conn, tableName, errors)
            if (len(errors) > 0):
                errStr = "".join(errors)
                self.fail(("checkTable after UNLOAD for %s failed with %d errors:\n" % (tableName, len(errors)))
                          + errStr)

    def executeMany(self, stmts, expect=None, respectOrder=False, ignore_rounding_errors=False, theCompareColumnInfos=True, cursor=None, msg=None, module_name=None, theIgnoreColumnNames=[]):
        """Execute the given statements. If expect is not None, make expected
        results."""
        if cursor is None:
            cursor = self.conn.cursor()

        try:
            for stmt in stmts:
                cursor.execute(stmt)
        except dbapi.Error as err:
            raise

        if expect is not None:
            if not respectOrder:
                e = ExpectedSimpleResultSet(cursor, ignore_rounding_errors=ignore_rounding_errors, compare_column_infos=theCompareColumnInfos, ignore_column_names=theIgnoreColumnNames)
            else:
                e = ExpectedSortedSimpleResultSet(cursor)
            self.assertExpected(e, expect, msg, self.getDefaultFilePath(), module_name)

        self.conn.commit()
        cursor.close()

    def executeStatement(self, statement, schema=None):
        with self.conn.cursor() as cursor:
            if schema is not None:
                cursor.execute("SET SCHEMA %s" % schema)
            cursor.execute(statement)
            self.conn.commit()

    def sanitize(self, myStr, statementSep):
        if statementSep is None:
            raise ValueError("statementSep is None")

        if myStr is None:
            return myStr

        myStr = re.sub(statementSep, "", myStr)

        myStr = myStr.strip()
        myStr = myStr.replace("'", "\'")

        if myStr.endswith(";"):
            myStr = myStr[:-1]

        return myStr

    def parseSqlDump(self, sqlFile, statementSep=None):
        if sqlFile is None:
            raise ValueError("sqlFile is None")
        if statementSep is None:
            raise ValueError("statementSep is None")

        statements = []
        lines = []

        context_procedure = False

        with codecs.open(sqlFile, "r", "utf-8") as f:
            print "Parsing file '%s'" % sqlFile
            for line in f:
                line = line.strip()

                if not line:
                    continue

                lineWithoutComment = line.split("--")[0].strip()
                if not lineWithoutComment:
                    continue

                if re.search("create\s+procedure", line, re.I):
                    if context_procedure:
                        raise Exception("context_begin_procedure already true")
                    context_procedure = True

                if re.search("end$", line, re.I):
                    if not context_procedure:
                        raise Exception("context_begin_procedure is false")
                    context_procedure = False

                if context_procedure:
                    lines.append(line)
                    continue

                if not context_procedure and re.search(statementSep, line):
                    lines.append(self.sanitize(line, statementSep))
                    statement = " ".join(lines)
                    statements.append(statement)

                    lines = []
                else:
                    line = self.sanitize(line, statementSep)
                    if len(line):
                        lines.append(line)

        if len(lines):
            statement = " ".join(lines)
            statements.append(statement)
            lines = []

        assert len(lines) == 0
        return statements

    def parseSqlTrace(self, sqlFile, translate_flag=0):
        if sqlFile is None:
            raise ValueError("sqlTraceFile is None")

        from sqltraceproc import SqlTraceProcessor
        return SqlTraceProcessor(sqlFile).process(translate_flag)

    def expectError(self, stmts, errorcode, conn=None):
        """Execute given statements and except dbapi.Error with errorcode to be raised."""
        self.expectErrorWithErrorText(stmts, errorcode, "", conn)

    def expectErrorWithErrorText(self, stmts, errorcode, errortext, conn=None):
        """Execute given statements and except dbapi.Error with errorcode/errortext to be raised."""
        if conn is None:
            conn = self.conn

        if not isinstance(stmts, list):
            stmts = [stmts]

        with conn.cursor() as cursor:
            for stmt in stmts:
                errorcode_ = 0
                errortext_ = ""
                try:
                    cursor.execute(stmt)
                except dbapi.Error as e:
                    errorcode_ = e[0]
                    errortext_ = e[1]

                conn.commit()

                # use %r instead of %s for errortext and stmt to prevent inicond/utf8/ascii conversin issues
                # see for example test: "python testImportExportWithSpecialNames.py -t testTemporaryTables"
                self.assertEqual(errorcode, errorcode_,
                    "The following statement did not trigger errorcode %d (but %d '%r'):\n%r"
                    % (errorcode, errorcode_, errortext_, stmt))
                self.assertTrue(errortext in errortext_,
                    "The following statement did not trigger errorcode %d with error text '%r' (but '%r'):\n%r"
                    % (errorcode, errortext, errortext_, stmt))

    #
    # Use these when it is enough to check if a statement raises an error.
    # For instance, authorization tests are good examples.
    #
    def execute(self, stmts, ignoreErr=False, printError=True, printStmt=False, separator=';', cursor=None):
        "Executes the string of SQL statements, after split by separator"

        stmtlist = stmts.split(separator)
        if not cursor:
            cursor = self.conn.cursor()
        for s in stmtlist:
            try:
                if ((not s.isspace()) and (len(s) != 0)):
                    if printStmt is True:
                        print s
                    cursor.execute(s)
            except dbapi.Error, err:
                if (not ignoreErr):
                    if (printError):
                        print "Error in statement ", '"', s, '"'
                        print err
                    raise err
        cursor.close()

    def executeOnDb(self, stmt, dbName, user=None, password=None):
        connMan = self.createUserDBConnectionManager(dbName)
        if user and password:
            conn = connMan.createConnection(user=user, password=password)
        else:
            conn = connMan.createConnection()
        cursor = conn.cursor()
        cursor.execute(stmt)
        result = cursor.fetchall()
        return result

    def executeErrorSkip(self, conn, stmts, ignoreErr='ALL'):
        "Executes a list of SQL statements upon a specific connection, which are separated by ';', skips the predefined errors"
        stmtlist = stmts.split(';')
        cursor = conn.cursor()
        for s in stmtlist:
            try:
                if ((not s.isspace()) and (len(s) != 0)):
                    cursor.execute(s)
            except dbapi.Error, err:
                if ignoreErr != 'ALL' and err[0] not in ignoreErr:
                    print "Error in statement ", '"', s, '"'
                    print err
                    raise
        cursor.close()

    def executeRetry(self, stmt, ignoreErr='ALL', retries=5, sleep=5):
        """ Executes a single SQL statement and retries when certain errors occur.
            ignoreErr: ALL to ignore all errors, or a list of errors to ignore
        """

        lastExeption = None
        cursor = self.conn.cursor()
        i = 0
        for i in xrange(retries):
            try:
                cursor.execute(stmt)
                lastException = None
                break
            except dbapi.Error, err:
                lastException = err
                print "error during execution of SQL: ", stmt
                print "error:", str(err)
                if ignoreErr != 'ALL' and err[0] not in ignoreErr:
                    print "got errorcode %s, raising" % repr(err[0])
                    print "(ignoreErr was %s)" % str(ignoreErr)
                    raise
                elif i < retries - 1:
                    print "retrying"
                    time.sleep(sleep)

        if lastException is None:
            print "SQL ran, %d tries" % (i+1)
        else:
            print "raising last exception (unsuccessful after %d tries):" % (i+1), str(err)
            raise lastException

    def executeAndAssertSingle(self, stmt, refval):
        "Executes SQL statement and checks if statement raises an error"

        cursor = self.conn.cursor()
        result = ""
        msg = ""
        msg1 = ""
        try:
            if ((not stmt.isspace()) and (len(stmt) != 0)):
                msg += "\n" + "1: "
                cursor.execute(stmt)
                result = 'S'
                msg += "(0)"
        except dbapi.Error, err:
            result = 'F'
            msg += str(err)
        if not result == refval:
            msg1 = '%r != %r\n' % (result, refval)
        self.assertEqual(result, refval, msg1 + msg)
        cursor.close()

    def executeAndAssert(self, stmts, refval):
        "Executes SQL statements and checks if each statement raises an error"

        stmtlist = stmts.split(';')
        cursor = self.conn.cursor()
        result = ""
        msg = ""
        msg1 = ""
        i = 0
        for s in stmtlist:
            i = i + 1
            try:
                if ((not s.isspace()) and (len(s) != 0)):
                    msg += "\n" + str(i) + ": "
                    cursor.execute(s)
                    result += 'S'
                    msg += "(0)"
            except dbapi.Error, err:
                result += 'F'
                msg += str(err)
        if not result == refval:
            msg1 = '%r != %r\n' % (result, refval)
        self.assertEqual(result, refval, msg1 + msg)
        cursor.close()

    def executeAndExpectError(self, statements, expectedError):
        """Execute stmts as the given user, expecting an error"""

        if isinstance(statements, str):
            statements = statements.split(';')

        try:
            self.expectError(statements, expectedError)
        finally:
            # Get new session to have user SYSTEM again
            self.conn.close()
            self.conn = self.conman.createConnection()

    def executeAs(self, user, passwd, stmts, ignoreErr=False):
        """Execute stmts as the given user"""
        cursor = self.conn.cursor()
        cursor.execute('CONNECT %s PASSWORD "%s"' % (user, passwd))
        try:
            self.execute(stmts, ignoreErr)
        finally:  # Get new session to have user SYSTEM again
            self.conn.close()
            self.conn = self.conman.createConnection()

    def executeAsAndAssert(self, user, passwd, stmts, refval):
        """Execute stmts as the given user and check against refval"""
        cursor = self.conn.cursor()
        cursor.execute('CONNECT %s PASSWORD "%s"' % (user, passwd))
        try:
            self.executeAndAssert(stmts, refval)
        finally:  # Get new session to have user SYSTEM again
            self.conn.close()
            self.conn = self.conman.createConnection()

    def executeAsAndExpectError(self, user, password, statements, expectedError):
        """Execute stmts as the given user, expecting an error"""
        cursor = self.conn.cursor()
        cursor.execute('CONNECT %s PASSWORD "%s"' % (user, password))
        if isinstance(statements, str):
            statements = statements.split(';')

        try:
            self.expectError(statements, expectedError)
        finally:
            # Get new session to have user SYSTEM again
            self.conn.close()
            self.conn = self.conman.createConnection()

    def executeQueryAndAssertValue(self, query, refval):
        "Executes a query and checks if statement raises an error"

        cursor = self.conn.cursor()
        msg = ""
        msg1 = ""
        try:
            cursor.execute(query)
            result = cursor.fetchone()
        except dbapi.Error, err:
            msg += str(err)
        if not result[0] == refval:
            msg1 = '%r != %r\n' % (result[0], refval)
        self.assertEqual(result[0], refval, msg1 + msg)
        cursor.close()

    def executeQueryAsAndAssertValue(self, user, passwd, query, refval):
        """Execute a query as the given user and check against refval"""
        cursor = self.conn.cursor()
        cursor.execute('CONNECT %s PASSWORD "%s"' % (user, passwd))
        try:
            self.executeQueryAndAssertValue(query, refval)
        finally: # Get new session to have user SYSTEM again
            self.conn.close()
            self.conn = self.conman.createConnection()

    def getCurrentUser(self):
        """Get the SQL user name of the current default connection"""
        cursor = self.conn.cursor()
        cursor.execute("SELECT CURRENT_USER FROM SYS.DUMMY")
        username = cursor.fetchall()[0][0]
        cursor.close()
        return username

    def getTransactionId(self, conn=None):
        if conn:
            cursor = conn.cursor()
        else:
            cursor = self.conn.cursor()
        try:
            cursor.execute("SELECT t.UPDATE_TRANSACTION_ID from M_CONNECTIONS c inner join M_TRANSACTIONS t on (t.HOST,T.PORT,t.TRANSACTION_ID) = (c.HOST,c.PORT,c.TRANSACTION_ID) where c.OWN = 'TRUE'")
            rs = cursor.fetchall()
            self.assertEqual(len(rs), 1, "no results from connection/transaction table %s"%(rs))
        finally:
            cursor.close()
        return rs[0][0]

    def getTransactionObjectId(self, conn=None):
        if conn:
            cursor = conn.cursor()
        else:
            cursor = self.conn.cursor()
        try:
            cursor.execute("SELECT t.TRANSACTION_ID from M_CONNECTIONS c inner join M_TRANSACTIONS t on (t.HOST,T.PORT,t.TRANSACTION_ID) = (c.HOST,c.PORT,c.TRANSACTION_ID) where c.OWN = 'TRUE'")
            rs = cursor.fetchone()
            self.assertTrue(rs, "no results from connection/transaction table")
        finally:
            cursor.close()
        return rs[0]

    def getTransactionIdForOtherConnectionId(self, conn_id):
        """Get transaction id for conn_id in new connection to avoid monitor view access in default transaction."""
        conn = self.conman.createConnection()
        cursor = conn.cursor()
        try:
            cursor.execute("SELECT UPDATE_TRANSACTION_ID FROM M_TRANSACTIONS WHERE CONNECTION_ID=%d" % conn_id)
            rs = cursor.fetchone()
            self.assertTrue(rs, "no results from transactions table")
        finally:
            cursor.close()
        return rs[0]

    def getLastCommitId(self, conn=None):
        if conn:
            cursor = conn.cursor()
        else:
            cursor = self.conn.cursor()
        try:
            cursor.execute("SELECT LAST_COMMIT_ID FROM M_HISTORY_INDEX_LAST_COMMIT_ID WHERE SESSION_ID = CURRENT_CONNECTION")
            rs = cursor.fetchone()
            self.assertTrue(rs, "no results from connection/transaction table")
        finally:
            cursor.close()

        return rs[0]

    def getConnAndTransId(self, conn=None):
        if conn:
            cursor = conn.cursor()
        else:
            cursor = self.conn.cursor()
        try:
            cursor.execute("SELECT c.CONNECTION_ID, t.UPDATE_TRANSACTION_ID from M_CONNECTIONS c inner join M_TRANSACTIONS t on (t.HOST,T.PORT,t.TRANSACTION_ID) = (c.HOST,c.PORT,c.TRANSACTION_ID) where c.OWN = 'TRUE'")
            rs = cursor.fetchone()
            self.assertTrue(rs, "no results from connection/transaction table")
        finally:
            cursor.close()

        return (rs[0], rs[1])

    def getConnectionId(self, conn=None):
        if conn:
            cursor = conn.cursor()
        else:
            cursor = self.conn.cursor()
        try:
            cursor.execute("SELECT c.CONNECTION_ID from M_CONNECTIONS c where c.OWN = 'TRUE'")
            rs = cursor.fetchone()
            self.assertTrue(rs, "no results from connection table")
        finally:
            cursor.close()

        return rs[0]

    def getIndexServer(self, schemaname, tablename, part=0, conn=None):
        """Get the indexserver that currently owns the named table."""

        if conn:
            cursor = conn.cursor()
        else:
            cursor = self.conn.cursor()

        if part == 0:
            cursor.execute("SELECT LOCATION FROM SYS.M_TABLE_LOCATIONS where SCHEMA_NAME='%s' AND TABLE_NAME='%s'" % (schemaname, tablename))
        else:
            cursor.execute("SELECT LOCATION FROM SYS.M_TABLE_LOCATIONS where SCHEMA_NAME='%s' AND TABLE_NAME='%s' AND PART_ID='%s'" % (schemaname, tablename, part))

        result = cursor.fetchall()
        try:
            location = result[0][0]
        except IndexError, e:
            print result
            raise
        cursor.close()
        return location

    def getDIServers(self, conn=None):
        """Get a list of all active DI servers in the current NewDb
        landscape. Returns None on error."""

        if not conn:
            cursor = self.conn.cursor()
        else:
            cursor = conn.cursor()

        cursor.execute("select HOST,PORT from SYS.M_SERVICES where SERVICE_NAME='diserver' AND ACTIVE_STATUS='YES' ORDER BY HOST, PORT")
        resultset = cursor.fetchall()
        cursor.close()
        return resultset

    def getIndexServersTable(self, schemaname, tablename, conn=None):
        """Get the indexservers that currently owns the named table."""
        if conn:
            thecursor = conn.cursor()
        else:
            thecursor = self.conn.cursor()

        locations = []

        with thecursor as cursor:
            cursor.execute("SELECT LOCATION FROM SYS.M_TABLE_LOCATIONS where SCHEMA_NAME='%s' AND TABLE_NAME='%s'" % (schemaname, tablename))
            locations = [i[0] for i in cursor.fetchall()]

        return locations

    def setLockWaitTimeout(self, timeoutMillis):
        conn = self.conman.createConnection()
        cursor = conn.cursor()
        statement = "ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'system') SET ( 'transaction',  'lock_wait_timeout') = '%d' WITH RECONFIGURE" % int(timeoutMillis)
        SqlTestCase.executeSetIniParametersWithRetrys(statement, cursor)
        conn.commit()

    def unsetLockWaitTimeout(self):
        conn = self.conman.createConnection()
        cursor = conn.cursor()
        statement = "ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'system') UNSET ( 'transaction',  'lock_wait_timeout') WITH RECONFIGURE"
        SqlTestCase.executeSetIniParametersWithRetrys(statement, cursor)
        conn.commit()

    def getConfigParameters(self, filename, layer, section, conn=None):
        if self._multiDBInstance:
            if not ((layer.upper() == 'SYSTEM' or (layer.upper() == 'DATABASE'))
                    and (filename.lower() in self.getTenantSpecificIniFiles())):
                conman = self.createSystemDBConnectionManager()
                conn = conman.createConnection()

        if conn is None:
            conn = self.conn
        with conn.cursor() as cursor:
            pairs = {}
            cursor.execute("SELECT KEY, VALUE, HOST FROM M_INIFILE_CONTENTS WHERE FILE_NAME='%s' AND SECTION='%s' AND LAYER_NAME='%s'" % (filename, section, layer))
            settings = cursor.fetchall()
            for setting in settings:
                pairs[setting[0]] = (setting[1], setting[2]) if layer.upper() == 'HOST' else setting[1]
            return pairs

    def getConfigParameter(self, filename, layer, section, key, conn=None):
        if self._multiDBInstance:
            if not ((layer.upper() == 'SYSTEM' or (layer.upper() == 'DATABASE'))
                    and (filename.lower() in self.getTenantSpecificIniFiles())):
                conman = self.createSystemDBConnectionManager()
                conn = conman.createConnection()

        if conn is None:
            conn = self.conn
        with conn.cursor() as cursor:
            return self.getParam(cursor, filename, layer, "", section, key)

    def getParam(self, cursor, filename, layer, layername, section, key):
        layerQuery = ""
        if layername and layer.upper() == "HOST":
            layerQuery = "AND HOST = '%s'" % layername
        if layername and layer.upper().startswith("DATABASE"):
            layerQuery = "AND DATABASE_NAME = '%s'" % layername
        cursor.execute("""
    SELECT
        VALUE
    FROM
        SYS.M_INIFILE_CONTENTS
    WHERE
        FILE_NAME = ?
        AND LAYER_NAME = ?
        %s
        AND SECTION = ?
        AND KEY = ?
""" % layerQuery, (filename, layer.upper(), section, key))
        row = cursor.fetchone()

        if row is None:
            return None
        else:
            return row[0]

    #structure of sectionKeyValueDict:
    # { section1 : [(key1,value1), (key2,value2), ...] , section2: [(key3, value3], [key4, value4],...] }
    # layer := layer or (layer, layerName)
    def setConfigParameterBulk(self, filename, layer, sectionKeyValueDict, setValues=True, conn = None):

        layerName = None

        if isinstance(layer, tuple):
            layerName = layer[1]
            layer = layer[0]

        sqlAlterSystem = "ALTER SYSTEM ALTER CONFIGURATION ('%s','%s'" % (filename, layer.upper())
        sqlAlterSystem += ") " if layerName is None else (",'%s') " % layerName)
        sqlAlterSystem += "SET " if setValues else "UNSET "

        for section in sectionKeyValueDict.keys():
            if setValues:
                for key, value in sectionKeyValueDict[section]:
                    if value is None:
                        raise Exception("setting None not supported/implemented here")
                    sqlAlterSystem += "('%s','%s')='%s', "%(section, key, value)
            else:
                #inspect 1st element and decide whether it is a (key, value) pair or just a plain "key"
                #such that same object can be used to set and unset the parameters
                sectionEntries = sectionKeyValueDict[section]
                if not ( isinstance(sectionEntries[0], tuple) or isinstance(sectionEntries[0], list) ):
                    for key in sectionEntries:
                        sqlAlterSystem += "('%s'%s), " % (section, ("" if key is None else (",'%s'" % key)))
                else:
                    #ignore value since we are told to unset the ini parameter
                    #used to set and unset the parameters with the same object
                    for key, value in sectionEntries:
                        sqlAlterSystem += "('%s'%s), " % (section, ("" if key is None else (",'%s'" % key)))

        sqlAlterSystem = sqlAlterSystem[:len(sqlAlterSystem)-2] #remove last ", "
        sqlAlterSystem += " WITH RECONFIGURE"

        conman = None

        if self._multiDBInstance:
            if not ((layer.upper() == 'SYSTEM' or (layer.upper() == 'DATABASE' and layerName is None))
                    and (filename.lower() in self.getTenantSpecificIniFiles())):
                conman = self.createSystemDBConnectionManager()
                conn = conman.createConnection()

        if conn is None:
            conn = self.conn

        with conn.cursor() as cursor:
            SqlTestCase.executeSetIniParametersWithRetrys(sqlAlterSystem, cursor)

    def setConfigParameter(self, filename, layer, section, key, value, conn = None):
        if value is None:
            self.setConfigParameterBulk(filename, layer, {section : [key,]}, setValues=False, conn = conn)
        else:
            self.setConfigParameterBulk(filename, layer, {section : [(key,value),]}, setValues=True, conn = conn)
        #conn.close() do not close self.conn, systemDB conn will be closed automatically once local conman is deleted

    def movePartsToCommonLocation(self, table, schema='SYSTEM'):
        sql = """SELECT
                        DISTINCT P.PARTITION, L.LOCATION
                    FROM
                        SYS.M_CS_PARTITIONS P
                    JOIN
                        SYS.M_TABLE_LOCATIONS L
                    ON
                        P.PART_ID = L.PART_ID AND
                        P.SCHEMA_NAME = L.SCHEMA_NAME AND
                        P.TABLE_NAME = L.TABLE_NAME
                    WHERE
                        L.SCHEMA_NAME='%s' AND
                        L.TABLE_NAME='%s' AND
                        (L.host, L.port) in (select S.host, S.port from sys.m_services S where S.service_name = 'indexserver')""" \
        % (schema, table)
        cursor = self.conn.cursor()
        cursor.execute(sql)
        rows = cursor.fetchall()
        if len(rows) == 0:
            self.fail('Table is not partitioned!')
        else:
            commonLocation = rows[0][1]
            for (partId, location) in rows:
                if location != commonLocation:
                    # actually we move part groups
                    sql = """ALTER TABLE "%s"."%s" MOVE PART %d TO LOCATION '%s'""" % (schema, table, partId, commonLocation)
                    cursor.execute(sql)

    def enableItabLeakCheck(self):
        SqlTestCase._itabLeakCheck['disabled'] = False

    def disableItabLeakCheck(self):
        SqlTestCase._itabLeakCheck['disabled'] = True

    def enableMemoryLeakCheck(self, allocatorCheckSpec):
        '''
        allocatorCheckSpec should be a tuple (name, thresholdBytes) or just (name, )
        name: allocator name
        thresholdBytes: amount of allocated bytes which are acceptable (default 0)
        service: name of service to check, '' or * for all services

        example: allocatorCheckSpec = ("Pool/FuzzySearch", 10)
        means:   if the allocator "Pool/FuzzySearch" climbs more than 10 bytes
                 between the readings in setUpTestCase() and tearDownTestCase() it will trigger a test failure

        example: allocatorCheckSpec = ("Pool/FuzzySearch", 10, 'indexserver')
        means:   if the allocator "Pool/FuzzySearch" climbs more than 10 bytes in all indexserver processes/services
                 between the readings in setUpTestCase() and tearDownTestCase() it will trigger a test failure
        '''
        SqlTestCase._memoryLeakCheck.append(allocatorCheckSpec)

    def disableMemoryLeakCheck(self):
        del SqlTestCase._memoryLeakCheck[:]

    def disableConfigChangeChecker(self):
        SqlTestCase._configChangeChecker = False

    def isConfigCangeCheckerActive(self):
        return self._configChangeChecker

    def setUpTestCase(self):
        super(SqlTestCase, self).setUpTestCase()

        envEnableDebugAllocator = os.environ.get("HDB_ENABLE_DEBUG_ALLOCATOR")
        if not envEnableDebugAllocator is None:
            envEnableDebugAllocatorList = [x.strip() for x in envEnableDebugAllocator.split(',')]
            SqlTestCase._hasDebugAllocatorEnabled = ('all' in envEnableDebugAllocatorList) or ('hdbindexserver' in envEnableDebugAllocatorList)
        else:
            SqlTestCase._hasDebugAllocatorEnabled = False

        if self._multiDBInstance:
            conman = self.createSystemDBConnectionManager()
        else:
            conman = self.createConnectionManager()

        if DecoratedDbApiConnection.readOnlyModeActive():
            self.prepareReadOnlyMode(conman.createConnection(autocommit=True))

        SqlTestCase._isDebugBuild = _isBuildType('build_gen', 'dbg%', conman=conman)
        SqlTestCase._isReleaseBuild = _isBuildType('build_gen', 'rel%', conman=conman)
        SqlTestCase._isSyncGuardBuild = _isBuildType('build_gen', '%sync-guards%', conman=conman)
        asanBuild = isAddressSanitizerBuild(conman=conman) # do not remove
        isAddressSanitizerDSOBuild(conman=conman)          # initializes cache

        conn = conman.createConnection(autocommit=True)
        cursor = conn.cursor()

        if asanBuild:
            # Raise limit for resource container
            # This prevents performance degradation due to overeager unloads
            self.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM')" \
                " SET ('persistence', 'resource_container_max_size') = '200000' WITH RECONFIGURE", cursor)

        sql = """SELECT * FROM SYS.M_HEAP_MEMORY WHERE CATEGORY LIKE '%libhdbina%'"""
        cursor.execute(sql)
        rows = cursor.fetchall()
        if len(rows) == 0:
            SqlTestCase._hasEPMInstalled = False
        else:
            SqlTestCase._hasEPMInstalled = True

        conman.closeAllConnections()

        self.itabLeakCheckInit()
        self.memoryLeakCheckInit()
        self.configChangeChecker = ChangeConfigChecker(type(self).__name__, self._malFunctionMode, self.isConfigCangeCheckerActive())
        self.notifyObservers({'type': 'SETUPTESTCASE',
                              'subtype': 'end',
                              'testName': self._testMethodName,
                              'moduleTestName': self.name(),
                              'testCase': type(self).__name__,
                              'testCaseObj': self})

    def tearDownTestCase(self):
        self.notifyObservers({'type': 'TEARDOWNTESTCASE',
                              'subtype': 'begin',
                              'testWasSkipped': self._testWasSkipped,
                              'testName': self._testMethodName,
                              'moduleTestName': self.name(),
                              'testCase': type(self).__name__,
                              'testCaseObj': self})
        super(SqlTestCase, self).tearDownTestCase()

        if self._multiDBInstance:
            conman = self.createSystemDBConnectionManager()
        else:
            conman = self.createConnectionManager()

        conn = conman.createConnection(autocommit=True)
        cursor = conn.cursor()

        if isAddressSanitizerBuild(conman=conman):
            self.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM')" \
                " UNSET ('persistence', 'resource_container_max_size') WITH RECONFIGURE", cursor)

        if DecoratedDbApiConnection.readOnlyModeActive():
            self.finishReadOnlyMode(conman.createConnection(autocommit=True))

        conman.closeAllConnections()

        try:
            if self.isItabLeakCheckActive():
                print "closing connections before itab leak check"
                self.conman.closeAllConnections()
        except:
            pass
        self.itabLeakCheckVerify()
        self.memoryLeakCheckVerify()

        # it has to be enable before SqlTestCase.setUpTestCase()
        self.disableItabLeakCheck()
        self.disableMemoryLeakCheck()
        if self.configChangeChecker is not None:
            self.configChangeChecker.reportConfigChanges()

    def isItabLeakCheckActive(self):
        if self._itabLeakCheckCmdLineDisable:
            return False
        leakCheck = SqlTestCase._itabLeakCheck
        if not leakCheck.has_key('disabled') or leakCheck['disabled'] == True:
            return False
        else:
            return True

    def itabLeakCheckInit(self):
        if not self.isItabLeakCheckActive():
            return

        conman = self.createConnectionManager()
        conn = conman.createConnection(autocommit=True)
        cursor = conn.cursor()

        # Set task framework 'ini' parameters to disable the garbage collection thread, not to execute any cleanup SQL queries during the "itabLeakCheck"
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('task_framework', 'gc_disable') = 'true'", cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('scriptserver.ini', 'SYSTEM') SET ('task_framework', 'gc_disable') = 'true'", cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('xsengine.ini', 'SYSTEM') SET ('task_framework', 'gc_disable') = 'true'", cursor)

        self._isESSActive = self.checkStatisticsServerActive(conn)
        self.setForceStopOfStatisticsServer(conn, True)
        self.disableStatisticsServer(conn)

        # clear caches # purge cached itabs
        self._clearForLeakChecks(cursor)

        # get original ini parameter values
        SqlTestCase._itabLeakCheck['trace_leaks'] = None
        cursor.execute("SELECT VALUE FROM M_INIFILE_CONTENTS WHERE FILE_NAME='indexserver.ini' AND LAYER_NAME='SYSTEM' AND SECTION='itab' AND KEY='trace_leaks'")
        rows = cursor.fetchall()
        if len(rows):
            SqlTestCase._itabLeakCheck['trace_leaks'] = rows[0][0]

        SqlTestCase._itabLeakCheck['trace_callstack'] = None
        cursor.execute("SELECT VALUE FROM M_INIFILE_CONTENTS WHERE FILE_NAME='indexserver.ini' AND LAYER_NAME='SYSTEM' AND SECTION='itab' AND KEY='trace_leakcallstack'")
        rows = cursor.fetchall()
        if len(rows):
            SqlTestCase._itabLeakCheck['trace_callstack'] = rows[0][0]

        SqlTestCase._itabLeakCheck['leaktrace_max_callstacks'] = None
        cursor.execute("SELECT VALUE FROM M_INIFILE_CONTENTS WHERE FILE_NAME='indexserver.ini' AND LAYER_NAME='SYSTEM' AND SECTION='itab' AND KEY='leaktrace_max_callstacks'")
        rows = cursor.fetchall()
        if len(rows):
            SqlTestCase._itabLeakCheck['leaktrace_max_callstacks'] = rows[0][0]

        SqlTestCase._itabLeakCheck['trace_toid_callstack'] = None
        cursor.execute("SELECT VALUE FROM M_INIFILE_CONTENTS WHERE FILE_NAME='indexserver.ini' AND LAYER_NAME='SYSTEM' AND SECTION='itab' AND KEY='trace_toid_leakcallstack'")
        rows = cursor.fetchall()
        if len(rows):
            SqlTestCase._itabLeakCheck['trace_toid_leakcallstack'] = rows[0][0]

        # set ini parameters
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('itab', 'trace_leaks') = 'yes' ", cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('itab', 'leaktrace_max_callstacks') = '10000' ", cursor) # original behavior
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('itab', 'trace_leakcallstack') = 'yes' ", cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('itab', 'trace_toid_leakcallstack') = 'yes' WITH RECONFIGURE", cursor)
        print "set gc_disable, trace_leaks, trace_toid_leakcallstack to true / yes"
        columnNames = ['COLUMN_NR', 'COLUMN_NAME', 'INDEX_ATTRIBUTE_NAME', 'HOST', 'PORT']
        cursor.execute("SELECT %s from SYS.M_DEV_ITAB_LEAK" % ", ".join(columnNames))
        SqlTestCase._itabLeakCheck['start_time'] = datetime.datetime.now()
        columns = 0
        result = cursor.fetchall()
        for row in result:
            if columns < 100: # print only the first 100 columns
                for columnName, value in zip(columnNames, row):
                    print "%21s: %s" % (columnName, value)
            else:
                print "... skip further leaks"
                break
            print
            columns += 1
        print "ItabLeakCheck: %d columns currently allocated" % len(result) + " (" + str(datetime.datetime.now()) + ")"
        conman.closeAllConnections()

    def itabLeakCheckVerify(self, _TESTPARAMETER_maxRuns=None, _TESTPARAMETER_waitTime=None, # those parameters are only for testing, do not set them productively
            ignoreItabLeaks=(), reenableStatisticsServer=True):
        if not self.isItabLeakCheckActive():
            return

        leakCheck = SqlTestCase._itabLeakCheck
        conman = self.createConnectionManager()
        conn = conman.createConnection(autocommit=True)
        cursor = conn.cursor()
        # clear caches # purge cached itabs
        self._clearForLeakChecks(cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('calcengine', 'gc_disable') = 'true'", cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('calcengine', 'gc_thread_timeout') = '10000000'", cursor)
        columnNames = ['COLUMN_NR', 'HOST', 'PORT']
        SqlTestCase._itabLeakCheck['end_time'] = datetime.datetime.now()

        def checkForLeaks(numRun):
            leakedColumns = set() # open columns from first since this interation, possible leaks
            sql = "SELECT %s FROM SYS.M_DEV_ITAB_LEAK where creation_time > ? AND creation_time < ?" % ", ".join(columnNames)
            cursor.execute(sql, (SqlTestCase._itabLeakCheck['start_time'], SqlTestCase._itabLeakCheck['end_time']))
            for row in cursor.fetchall():
                # new possible leak, iteration of checkForLeaks will find temp 'leaks'
                leakedColumns.add(tuple(row))
                print "ItabLeakCheck (%d. run): New possible leak (%s)" % (numRun, str(datetime.datetime.now()))
                if len(leakedColumns) < 100:
                    for columnName, value in zip(columnNames, row):
                        if type(value) == types.UnicodeType:
                            value = value.encode('utf8')
                        print "%21s: %s" % (columnName, value)
                    print
                elif len(leakedColumns) == 100:
                    print "... skip further leaks"
                    print

            return leakedColumns

        def checkForVariableToidLeaks():
            sql = "SELECT * FROM SYS.M_DEV_TOID_MAP where create_time > ? AND create_time < ?"
            cursor.execute(sql, (SqlTestCase._itabLeakCheck['start_time'], SqlTestCase._itabLeakCheck['end_time']))
            return cursor.fetchall()

        # here check for possible leaks, do some repetition do limit impact from parallel quries
        maxRuns = _TESTPARAMETER_maxRuns if _TESTPARAMETER_maxRuns else 2
        waitTime = _TESTPARAMETER_waitTime if _TESTPARAMETER_waitTime else 20
        currentRun = 1
        possibleLeaks = checkForLeaks(currentRun)
        while possibleLeaks and currentRun < maxRuns:
            # do a new check in Xs again to limit sporadic itab leak check failures due to other running querys in the background
            currentRun += 1
            print "... wait %d seconds and try the itab leak check again ... (%d. try)" % (waitTime, currentRun) + " (" + str(datetime.datetime.now()) + ")"
            time.sleep(waitTime)
            possibleLeaks = checkForLeaks(currentRun)

        variableToidLeaks = checkForVariableToidLeaks()
        while variableToidLeaks and currentRun < maxRuns:
            currentRun += 1
            print "... wait %d seconds and try the variable toid itab leak check again ... (%d. try)" % (waitTime, currentRun) + " (" + str(datetime.datetime.now()) + ")"
            time.sleep(waitTime)
            variableToidLeaks = checkForVariableToidLeaks()

        # if we have some candidates, get the callstack and check if they are known
        if possibleLeaks:
            columnNames = ['COLUMN_NR', 'COLUMN_NAME', 'INDEX_ATTRIBUTE_NAME', 'TYPE_STRING', 'CREATION_TIME', 'REF_COUNT', 'STATEMENT_STRING', 'USER_NAME', 'SCHEMA_NAME', 'CONNECTION_ID', 'STATEMENT_ID', 'HOST', 'PORT', 'CALL_STACK']
            ignoreLeaksDefinitions = [
                "(INDEX_ATTRIBUTE_NAME not like '%CE\\_DEBUG\\_%' escape '\\')", # ?
                "(CALL_STACK not like '%AttributeEngine::BTreeAttribute<%>::\\_\\_insertFromReference\\_tiny\\_updates(%' escape '\\')", # those itab columns will be used in the Delta for small updates and are release when the column/delta is unloaded/dropped, but not all test do this at the end
                #"(STATEMENT_STRING not like 'CALL CHECK_TABLE_CONSISTENCY%' or CALL_STACK not like '%ptime::ExternalStatement::ExecutionResponse::deserialize%ptime::ExternalStatement::executeAtRemote%ptime::CallableStatement::execute%')", # bug #41445
                #"(CALL_STACK not like '%ptime::TrexITab::addColumn%ptime::Itab\\_materializer::do\\_open%ptime::TrexPlanOp::executePop%Executor::X2::run%Execution::JobWorker::run%' escape '\\')", # bug #40890/46040
                #"(CALL_STACK not like '%ptime::TrexPlanData::deserialize%Executor::X2::handleX2%TRexAPI::TREXIndexServer::handle%TrexThreads::PoolThread::run%')", # bug #40890/46040
                "(CALL_STACK not like '%JoinEvaluator::deepCopyItab%JoinEvaluator::CachedPlan::cacheEmptyResult%')", # Empty itabs are kept in the plan cache for future use.  Clearing the plan cache will release them.
                "(STATEMENT_STRING not like 'INSERT INTO SYS.LICENSE_MEASUREMENTS_(GLAS_APPLICATION_ID, MEASURE_TIME, VALUE, SUCCESSFUL, HOST, PORT, DATABASE_NAME) VALUES(?, ?, ?, ?, ?, ?, ?)' or CALL_STACK not like '%Licensing::LicenseEAPIUtils::storeMeasurement%Licensing::LicensePluginRegistry::performHanaLicenseMeasurement%Licensing::LicenseRemoteRequestHandler::handle%')", # bug #168808
            ]
            ignoreLeaksDefinitions.extend(ignoreItabLeaks)
            ignoreLeaksDefinitions.extend(self._ignoreItabLeaks)

            sql = "SELECT %s FROM SYS.M_DEV_ITAB_LEAK where creation_time > ? AND creation_time < ?" % ", ".join(columnNames)
            sql += "AND (" + " OR ".join((" (COLUMN_NR=%s AND HOST='%s' and PORT=%s) " % leak) for leak in possibleLeaks) + ")"

            if ignoreLeaksDefinitions:
                sql = "SELECT * FROM (%s) WHERE " % sql
                sql += " AND ".join(ignoreLeaksDefinitions)

            cursor.execute(sql, (SqlTestCase._itabLeakCheck['start_time'], SqlTestCase._itabLeakCheck['end_time']))
            leaks = cursor.fetchall() # here we know that these are real leaks
            leakCallStacks = []
            column = 0
            for row in leaks:
                print "ItabLeakCheck: New leak (%s)" % str(datetime.datetime.now())
                leakCallStacks.append(row[-1])
                if column < 100:
                    column += 1
                    for columnName, value in zip(columnNames, row):
                        if type(value) == types.UnicodeType:
                            value = value.encode('utf8')
                        print "%21s: %s" % (columnName, value)
                    print
                elif column == 100:
                    column += 1
                    print "... skip further leaks"
                    print
        else:
            leaks = []
            leakCallStacks = []

        # reset ini parameters
        if leakCheck['trace_leaks'] is None:
            SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') UNSET ('itab', 'trace_leaks')", cursor)
        else:
            SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('itab', 'trace_leaks') = '%s'" % leakCheck['trace_leaks'], cursor)
        if leakCheck['leaktrace_max_callstacks'] is None:
            SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') UNSET ('itab', 'leaktrace_max_callstacks')", cursor)
        else:
            SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('itab', 'leaktrace_max_callstacks') = '%s'" % leakCheck['leaktrace_max_callstacks'], cursor)
        if leakCheck['trace_callstack'] is None:
            SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') UNSET ('itab', 'trace_leakcallstack') ", cursor)
        else:
            SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('itab', 'trace_leakcallstack') = '%s'" % leakCheck['trace_callstack'], cursor)
        if leakCheck['trace_toid_callstack'] is None:
            SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') UNSET ('itab', 'trace_toid_leakcallstack') ", cursor)
        else:
            SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('itab', 'trace_toid_leakcallstack') = '%s' " % leakCheck['trace_toid_callstack'], cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') UNSET ('calcengine', 'gc_disable')", cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') UNSET ('calcengine', 'gc_thread_timeout')", cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') UNSET ('task_framework', 'gc_disable')", cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('scriptserver.ini', 'SYSTEM') UNSET ('task_framework', 'gc_disable')", cursor)
        SqlTestCase.executeSetIniParametersWithRetrys("ALTER SYSTEM ALTER CONFIGURATION ('xsengine.ini', 'SYSTEM') UNSET ('task_framework', 'gc_disable') WITH RECONFIGURE", cursor)
        print "unset gc_disable and set trace_leaks, trace_toid_leakcallstack to old value"

        if reenableStatisticsServer:
            self.setForceStopOfStatisticsServer(conn, False)
            if self._isESSActive:
                self.enableStatisticsServer(conn)
            else:
                print "ESS not enabled"
        conman.closeAllConnections()

        def addCallstackIntoTree(callStackList, callStackTree):
            if not callStackList:
                return
            if callStackList[0] not in callStackTree:
                callStackTree[callStackList[0]] = {}
            addCallstackIntoTree(callStackList[1:], callStackTree[callStackList[0]])

        def treeToString(callStackTree, treeString="", indent=0):
            if callStackTree:
                for v in callStackTree.items():
                    treeString += (" " * indent) + v[0] + "\n"
                    treeString = treeToString(v[1], treeString, indent+(0 if len(v[1]) == 1 and len(v[1].items()[0][1]) == 1 else 2))
            return treeString

        if leaks:
            # add the callstack line by line into a tree to find common parts of the callstacks

            uniqueCallStacks = set()
            uniqueCallStackTree = {}
            regEx = re.compile(".*: 0x.* in (.*)")
            for callStack in leakCallStacks:
                newCallStackList = []
                for line in callStack.split("\n")[1:]: # ommit the first line: "Dumping saved stack trace 140016370071840, 18 frames: "
                    res = regEx.search(line)
                    if res:
                        newCallStackList.append(res.group(1))
                    else:
                        newCallStackList.append(line)
                uniqueCallStacks.add("\n".join(newCallStackList))

                newCallStackList.reverse()
                addCallstackIntoTree(newCallStackList, uniqueCallStackTree)

            msg = "%d itab leaks; %d unique call stacks:\n\n" % (len(leaks), len(uniqueCallStacks))
            msg += "unique callstacks:\n------------------\n\n%s\n\ncallstack tree:\n---------------\n%s\n\n" % ("\n".join(uniqueCallStacks), treeToString(uniqueCallStackTree))
            msg += "(see http://trexweb.wdf.sap.corp:1080/wiki/index.php/InternalTable#Finding_leaks )"
            self.assertTrue(False, msg)
        print "itab leak check was successful"

        if variableToidLeaks:
            msg = "%s variable toid leak\n" % len(variableToidLeaks)

            uniqueCallStacks = set()
            uniqueCallStackTree = {}
            regEx = re.compile(".*: 0x.* in (.*)")
            for schemaName, tableName, connectionId, statementId, toid, internalTablePtr, createTime, callStack, host, port, _ in variableToidLeaks[:50]:
                newCallStackList = []
                for line in callStack.split("\n")[1:]: # ommit the first line: "Dumping saved stack trace 140016370071840, 18 frames: "
                    res = regEx.search(line)
                    if res:
                        newCallStackList.append(res.group(1))
                    else:
                        newCallStackList.append(line)
                uniqueCallStacks.add("\n".join(newCallStackList))

                newCallStackList.reverse()
                addCallstackIntoTree(newCallStackList, uniqueCallStackTree)

                msg += str({'schemaName':schemaName, 'tableName':tableName, 'connectionId':connectionId, 'statementId':statementId, 'toid':toid, 'internalTablePtr':internalTablePtr, 'createTime':createTime})
                msg += "\n"

            msg += "\n"
            msg += "\n"
            msg += "%s unique callstacks:\n------------------\n\n%s\n\ncallstack tree:\n---------------\n%s\n\n" % (len(uniqueCallStacks), "\n".join(uniqueCallStacks), treeToString(uniqueCallStackTree))

            self.assertTrue(False, msg)

        print "variable toid leak check was successful"

    def memoryLeakCheckInit(self, verbose=True):
        if len(SqlTestCase._memoryLeakCheck) == 0:
            return

        conman = self.createConnectionManager()
        try:
            conn = conman.createConnection(autocommit=True)
            cursor = conn.cursor()
            # clear caches # purge cached itabs
            self._clearForLeakChecks(cursor)

            # to see what was allocated beforehand
            if verbose:
                for allocatorCheckSpec in SqlTestCase._memoryLeakCheck:
                    print "enable memory leak check for %s" % str(allocatorCheckSpec)
                    cursor.execute("""SELECT * FROM sys.m_heap_memory_reset WHERE category like '%s%%'""" % allocatorCheckSpec[0])
                    result = cursor.fetchall()
                    if result:
                        print "previous allocated memory from M_HEAP_MEMORY_RESET"
                        for l in result:
                            print l
            reset = "ALTER SYSTEM RESET MONITORING VIEW SYS.M_HEAP_MEMORY_RESET"
            cursor.execute(reset)
        finally:
            conman.closeAllConnections()

    def memoryLeakCheckVerify(self, returnLeakInfosInsteadOfThrow=False, verbose=True):
        if len(SqlTestCase._memoryLeakCheck) == 0:
            return

        collectedLeaks = []
        conman = self.createConnectionManager()
        try:
            conn = conman.createConnection(autocommit=True)
            cursor = conn.cursor()
            # clear caches # purge cached itabs
            self._clearForLeakChecks(cursor)

            for allocatorCheckSpec in SqlTestCase._memoryLeakCheck:
                thresholdBytes = 0
                service = None
                if len(allocatorCheckSpec) > 1:
                    thresholdBytes = int(allocatorCheckSpec[1])
                if len(allocatorCheckSpec) > 2:
                    service = allocatorCheckSpec[2]
                    if service in ("*", ""):
                        service = None
                sql = """SELECT sum(inclusive_size_in_use) FROM sys.m_heap_memory_reset WHERE category = '%s'""" % allocatorCheckSpec[0]
                if service:
                    sql += """ and (host, port) in (select host, port from sys.m_services where service_name = '%s')""" % service
                cursor.execute(sql)
                ret = cursor.fetchone()[0]
                if ret and ret > thresholdBytes:
                    # to see where the leak is (it might be that here it is already empty as it is some ms later then the above query)
                    cursor.execute("""SELECT * FROM sys.m_heap_memory_reset WHERE category like '%s%%'""" % allocatorCheckSpec[0])
                    leakResult = cursor.fetchall()
                    for l in leakResult:
                        print l
                    leakResult = [tuple(r) for r in leakResult]
                    collectedLeaks.append((allocatorCheckSpec[0], ret, leakResult))
                elif verbose:
                    print "memory leak check for '%s' was successful (threshold %d bytes)" % (allocatorCheckSpec[0], thresholdBytes)
        finally:
            conman.closeAllConnections()
        if returnLeakInfosInsteadOfThrow or not collectedLeaks:
            return collectedLeaks
        collectedLeaks = zip(*collectedLeaks)
        self.fail("allocator(s) '%s' contains %s bytes more than in memoryLeakCheckInit() (see testlog for more information)" % ("; ".join(collectedLeaks[0]), "/".join([str(x) for x in collectedLeaks[1]])))

    def extendIgnoreItabLeaks(self, ignoreItabLeaks):
            self._ignoreItabLeaks.extend(ignoreItabLeaks)

    @staticmethod
    def _setUnsetIniParameter(cursor, section, parameter, value):

        SqlTestCase.executeSetIniParametersWithRetrys(
            "ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') SET ('%s', '%s') = '%s' WITH RECONFIGURE" % (section,parameter,value),
            cursor)
        SqlTestCase.executeSetIniParametersWithRetrys(
            "ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini', 'SYSTEM') UNSET ('%s', '%s') WITH RECONFIGURE" % (section,parameter),
            cursor)

    @staticmethod
    def _clearForLeakChecks(cursor):
        cursor.execute("ALTER SYSTEM RECLAIM VERSION SPACE")
        cursor.execute("ALTER SYSTEM CLEAR COLUMN RESULT CACHE")
        cursor.execute("ALTER SYSTEM CLEAR SQL PLAN CACHE")
        cursor.execute("ALTER SYSTEM CLEAR RESULT CACHE")


        # set and unset cache size limitation to clear caches

        for (section,param) in [ ('joins','plan_cache_size'),
                                 ('hierarchy',HierarchyGlobalSymbols.HIERARCHYVIEW_TRANSACTIONAL_CACHE_SIZE_PARAM_NAME),
                                 ('hierarchy',HierarchyGlobalSymbols.HIERARCHYVIEW_NOINVALIDATE_CACHE_SIZE_PARAM_NAME),
                                 ('hierarchy',HierarchyGlobalSymbols.HIERARCHYSQL_TRANSACTIONAL_CACHE_SIZE_PARAM_NAME) ]:

            SqlTestCase._setUnsetIniParameter(cursor, section, param, 0)



    def printResultSet (self, cursor, query):
        try:
            cursor.execute(query)
            rows = cursor.fetchall()
            for row in rows:
                print str(row)
        finally:
            cursor.close()

    def prettyPrintResultSet(self, cursor, query, printAllRows=False):
        try:
            cursor.execute(query)
            columns = []
            for c in cursor.description:
                columns.append([])
                columns[-1].append(c[0].strip())

            result = cursor.fetchall()
            printRows = self._max_resultrows
            skipped = 0
            if printAllRows:
                printRows = len(result)
            else:
                if len(result) > printRows:
                    skipped = len(result)-printRows
            for x in result[:printRows]:
                pos = 0
                for y in x:
                    columns[pos].append(str(y).strip())
                    pos = pos + 1

            rows = len(columns[0])
            sizes = []
            for c in columns:
                sizes.append(0)
                for v in c:
                    if len(v) > sizes[-1]:
                        sizes[-1] = len(v)
            row = 0
            while row < rows:
                if row == 0:
                    times = len(columns) + 1
                    for s in sizes:
                        times += s + 2
                    print times * "-"
                print "|",
                for c in range(len(columns)):
                    print str(columns[c][row]).ljust(sizes[c]),
                    print "|",
                print
                if row == 0 or row == rows-1:
                    print times * "-"
                row += 1

            if skipped > 0: print "---", skipped, "rows skipped for better readability --- "
            print
        finally:
            cursor.close()

    def runCommand(self, command):
        if self._verbosity > 2:
            print "  Executing: " + str(command)

        process = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE)
        process.communicate()

    def runHdbConsChecked(self, commandString):
        def reportError(returnCode, output):
            print 'Error when calling: hdbcons', commandString
            print 'Returncode:', returnCode
            print 'Output:', output

        if self._verbosity > 2:
            print "  Executing hdbcons command(s):", commandString
        try:
            out = subprocess.check_output(['hdbcons', commandString], stderr=subprocess.STDOUT)
            if '[ERROR]' in out:
                reportError(0, out)
                self.assertTrue(False, "See above")
        except subprocess.CalledProcessError as exc:
            reportError(exc.returncode, exc.output)
            raise

    def startReadOnlyMode(self, mode):
        """ activate the given read only mode """
        self.prepareReadOnlyMode(self.conn)
        self.runCommand('hdbcons "log readOnly -s ' + str(mode) + '"')

    def startDynamicReadOnlyMode(self, mode):
        """ only select-statements are executed within the given mode """
        DecoratedDbApiConnection._readOnlyMode = mode
        DecoratedDbApiConnection._readOnlyExecution = True
        self.prepareReadOnlyMode(self.conn)

    def stopReadOnlyMode(self):
        """ stop the read only mode """
        DecoratedDbApiConnection._readOnlyMode = None
        DecoratedDbApiConnection._readOnlyExecution = None
        self.runCommand('hdbcons "log readOnly -s 0"')
        self.finishReadOnlyMode(self.conn)


    def prepareReadOnlyMode(self, conn):
        """Prepare test system for select queries running in read only mode"""
        readOnlyExecution = DecoratedDbApiConnection._readOnlyExecution
        DecoratedDbApiConnection._readOnlyExecution = False # temporarily deactivate read only mode
        try:
            self.statisticsServerActiveBeforeReadOnly = self.checkStatisticsServerActive(conn)

            if self.statisticsServerActiveBeforeReadOnly:
                if self._verbosity > 2:
                    print "Read Only Mode, deactivate statistics server"
                self.disableStatisticsServer(conn)

            self.stoppedServices = []
            sc = servicecontrol.ServiceController()
            servicesToStop = [] # [servicecontrol.ServiceType.XSEngine, servicecontrol.ServiceType.Preprocessor]

            for s in servicesToStop:
                servs = sc.getAll(s)
                for serv in servs:
                    if self._verbosity > 2:
                        print "Read Only Mode, deactivating service: " + str(( servicecontrol.ServiceType.toString(s), serv['port'], serv['host'] ))
                    self.stoppedServices.append( ( s, serv['port'], serv['host'] ) )
                    sc.removeFromDaemon( serv['port'], serv['host'] )

            with conn.cursor() as cursor:
                # deactivate peridoc savepoints
                cursor.execute(
                    """select value from "PUBLIC"."M_INIFILE_CONTENTS" where file_name = 'indexserver.ini' and layer_name = 'SYSTEM' and section = 'persistence' and key = 'savepoint_interval_s'""")
                result = cursor.fetchone()

                if result is not None:
                    self.savepoint_interval = result[0].lower()
                else:
                    self.savepoint_interval = None

                SqlTestCase.executeSetIniParametersWithRetrys(
                    """ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini','SYSTEM') SET ('persistence','savepoint_interval_s') = '0' WITH RECONFIGURE""",
                    cursor)

            with conn.cursor() as cursor:
                # deactivate peridoc lob garbage collection
                cursor.execute(
                    """select value from "PUBLIC"."M_INIFILE_CONTENTS" where file_name = 'indexserver.ini' and layer_name = 'SYSTEM' and section = 'lobhandling' and key = 'garbage_collect_interval_s'""")
                result = cursor.fetchone()

                if result is not None:
                    self.lob_garbage_collect_interval = result[0].lower()
                else:
                    self.lob_garbage_collect_interval = None

                SqlTestCase.executeSetIniParametersWithRetrys(
                    """ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini','SYSTEM') SET ('lobhandling','garbage_collect_interval_s') = '0' WITH RECONFIGURE""",
                    cursor)

            with conn.cursor() as cursor:
                # deactivate postdrop watchdog
                cursor.execute(
                    """select value from "PUBLIC"."M_INIFILE_CONTENTS" where file_name = 'indexserver.ini' and layer_name = 'SYSTEM' and section = 'row_engine' and key = 'Postdrop_watchdog_enabled'""")
                result = cursor.fetchone()

                if result is not None:
                    self.post_drop_watchdog = result[0].lower()
                else:
                    self.post_drop_watchdog = None

                SqlTestCase.executeSetIniParametersWithRetrys(
                    """ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini','SYSTEM') SET ('row_engine','Postdrop_watchdog_enabled') = 'false' WITH RECONFIGURE""",
                    cursor)

        finally:
            DecoratedDbApiConnection._readOnlyExecution = readOnlyExecution # reactivate read only mode

    def finishReadOnlyMode(self, conn):
        """reset test system"""
        if self.statisticsServerActiveBeforeReadOnly is not None and self.statisticsServerActiveBeforeReadOnly:
            if self._verbosity > 2:
                print "Read Only Mode, activate statisticsserver"
            self.enableStatisticsServer(conn)

        sc = servicecontrol.ServiceController()
        for serv in self.stoppedServices:
            if self._verbosity > 2:
                print "Read Only Mode, activating service: " + str(( servicecontrol.ServiceType.toString(serv[0]), serv[1], serv[2] ))
            sc.addToDaemon( serv[0], serv[1], serv[2] )

        if self.savepoint_interval is not None:
            SqlTestCase.executeSetIniParametersWithRetrys(
                """ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini','SYSTEM') SET ('persistence','savepoint_interval_s') = '%s' WITH RECONFIGURE"""%(str(self.savepoint_interval)),
                conn.cursor())
        else:
            SqlTestCase.executeSetIniParametersWithRetrys(
                """ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini','SYSTEM') UNSET ('persistence','savepoint_interval_s') WITH RECONFIGURE""",
                conn.cursor())

        if self.lob_garbage_collect_interval is not None:
            SqlTestCase.executeSetIniParametersWithRetrys(
                """ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini','SYSTEM') SET ('lobhandling','garbage_collect_interval_s') = '%s' WITH RECONFIGURE"""%(str(self.lob_garbage_collect_interval)),
                conn.cursor())
        else:
            SqlTestCase.executeSetIniParametersWithRetrys(
                """ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini','SYSTEM') UNSET ('lobhandling','garbage_collect_interval_s') WITH RECONFIGURE""",
                conn.cursor())

        if self.post_drop_watchdog is not None:
            SqlTestCase.executeSetIniParametersWithRetrys(
                """ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini','SYSTEM') SET ('row_engine','Postdrop_watchdog_enabled') = '%s' WITH RECONFIGURE"""%(str(self.post_drop_watchdog)),
                conn.cursor())
        else:
            SqlTestCase.executeSetIniParametersWithRetrys(
                """ALTER SYSTEM ALTER CONFIGURATION ('indexserver.ini','SYSTEM') UNSET ('row_engine','Postdrop_watchdog_enabled') WITH RECONFIGURE""",
                conn.cursor())

    def checkStatisticsServerActive(self, conn, forSystemDB = False):
        print "Check embedded stat server is active"
        conn = conn or self.conn

        iniFile = self.getInifileNameForESS(forSystemDB=forSystemDB)

        isActive = False
        with conn.cursor() as cursor:
            cursor.execute("""select value from "PUBLIC"."M_INIFILE_CONTENTS" where file_name = '%s' and layer_name = 'SYSTEM' and section = 'statisticsserver' and key = 'active'"""%iniFile)
            result = cursor.fetchone()
            if result is not None:
                isActive = result[0].lower() == 'true'
            else:
                cursor.execute("""select value from "PUBLIC"."M_INIFILE_CONTENTS" where file_name = '%s' and layer_name = 'DEFAULT' and section = 'statisticsserver' and key = 'active'"""%iniFile)
                result = cursor.fetchone()
                if result is not None:
                    isActive = result[0].lower() == 'true'

        return isActive

    def waitForStatisticsServerWorkerThreadsStopped(self, waitTime=120, conn=None, forSystemDB = False):
        logger.info ("Wait for embedded stat server worker threads stopped ...")
        sleepTime = 15
        if self.isDebugBuild() or os.environ.get('USE_HDBCOV', False) or self.isAddressSanitizerBuild() or self.hasDebugAllocatorEnabled():
            waitTime *= 35
        conn = conn or self.conn

        iniFile = self.getInifileNameForESS(forSystemDB=forSystemDB)

        with conn.cursor() as cursor:
            cursor.execute("select count(*) from sys.m_service_threads where thread_type='WorkerThread (StatisticsServer)' and not to_nvarchar(thread_detail) = 'ready'")
            count = cursor.fetchone()[0]
            if count > 0:            # speed up with more parallel threads
                cursor.execute("alter system alter configuration('%s','SYSTEM') SET ('statisticsserver','threadpool') = '15' with reconfigure"%iniFile)

            for _ in xrange(0, waitTime/sleepTime):
                cursor.execute("select thread_id, thread_detail, thread_state from sys.m_service_threads where thread_type='WorkerThread (StatisticsServer)' and not to_nvarchar(thread_detail) = 'ready'")
                rs = cursor.fetchall()
                workingWorkers = len (rs)
                if workingWorkers > 0:
                    print "waiting for %d statisticsserver workers to stop..." % workingWorkers
                    for row in rs:
                        print row
                    time.sleep(sleepTime)

                    # if still not finished => cancel
                    inlist = list('')
                    for row in rs:
                        inlist.append(row[1])

                    commandString = "select connection_id from m_connections where current_thread_id in (select thread_id from sys.m_service_threads where thread_type like '%%StatisticsServer%%' and to_nvarchar(thread_detail) in (" + "'"+"','".join(inlist)+"'" + "))"

                    cursor.execute(commandString)
                    rs = cursor.fetchall()
                    for row in rs:
                        commandString = "ALTER SYSTEM CANCEL SESSION '%s'" % row[0]
                        logger.info (commandString)
                        cursor.execute(commandString)

                else:
                    logger.info ("all statisticsserver workers idle")
                    cursor.execute("alter system alter configuration('%s','SYSTEM') UNSET ('statisticsserver','threadpool') with reconfigure"%iniFile)
                    break
            else:
                logger.info ("active statistics worker:")
                self.printResultSet (cursor, "select to_nvarchar(thread_detail) from sys.m_service_threads where thread_type = 'WorkerThread (StatisticsServer)' and to_nvarchar(thread_detail) != 'ready'")

                cursor.execute("alter system alter configuration('%s','SYSTEM') UNSET ('statisticsserver','threadpool') with reconfigure"%iniFile)
                # rtedumps to find out, where the threads are stuck
                MultiDBUtil.create_database_runtime_dumps(dbname=self.getConnectionDatabaseName())
                self.fail("Not all statisticsserver worker threads could be stopped after %d seconds." % waitTime)

    def getInifileNameForESS(self, forSystemDB = False):
        return 'indexserver.ini' if (self._multiDBInstance and (not forSystemDB)) else 'nameserver.ini'

    def ensureInstalledEmbeddedStatisticsServer(self, conn, forSystemDB = False):
        initESS = True
        cursor = conn.cursor()
        try:
            cursor.execute("select value from _SYS_STATISTICS.STATISTICS_PROPERTIES where key = 'internal.installation.state'")
            row = cursor.fetchone()

            if row is not None:
                if row[0].startswith("Done (okay)"):
                    initESS = False

        except dbapi.Error:
            pass

        if initESS:
            self.setForceStopOfStatisticsServer(conn, False)

            cursor = conn.cursor()
            SqlTestCase.executeSetIniParametersWithRetrys("""ALTER SYSTEM ALTER CONFIGURATION ('%s','SYSTEM') SET ('statisticsserver','active') = 'true' WITH RECONFIGURE""" % self.getInifileNameForESS(forSystemDB=forSystemDB), cursor)

            try:
                cursor.execute("delete from _SYS_STATISTICS.STATISTICS_PROPERTIES where key = 'internal.installation.state'")
            except dbapi.Error:
                pass

            commandString = "hdbindexserver" if (self._multiDBInstance and (not forSystemDB)) else "hdbnameserver"
            commandString = 'hdbcons -e ' + commandString + ' "statisticsservercontroller init"'
            logger.info (commandString)
            os.system (commandString)
            self.waitForEmbeddedStatisticsServer(conn=conn, forSystemDB=forSystemDB)

    def isStatisticsServerForcedStopped(self, conn):
        iniFile = self.getInifileNameForESS()
        section = 'statisticsserver'

        with conn.cursor() as cursor:
            cursor.execute("select count(*) from m_inifile_contents where file_name = '%s' and section = '%s' and key = 'forcestop' and value = 'true'" %(iniFile, section))
            return False if cursor.fetchone()[0] == 0 else True

    def setForceStopOfStatisticsServer(self, conn, setTrue, forSystemDB = False):
        iniFile = self.getInifileNameForESS(forSystemDB=forSystemDB)
        section = 'statisticsserver'

        with conn.cursor() as cursor:
            if setTrue:
                SqlTestCase.executeSetIniParametersWithRetrys("""ALTER SYSTEM ALTER CONFIGURATION ('%s','SYSTEM') SET ('%s','forcestop') = 'true' WITH RECONFIGURE""" % (iniFile, section), cursor)
                logger.info ("statisticsserver forcestop: %s", "true")
            else:
                SqlTestCase.executeSetIniParametersWithRetrys("""ALTER SYSTEM ALTER CONFIGURATION ('%s','SYSTEM') UNSET ('%s','forcestop') WITH RECONFIGURE""" % (iniFile, section), cursor)
                logger.info ("statisticsserver forcestop: %s", "false")

    def disableStatisticsServer(self, conn, forSystemDB = False):
        iniFile = self.getInifileNameForESS(forSystemDB=forSystemDB)
        section = 'statisticsserver'

        cursor = conn.cursor()

        # make sure, that the installation has finished
        maxTime = 1000
        self.waitForEmbeddedStatisticsServer(waitTime=maxTime, conn=conn, forSystemDB=forSystemDB)

        maxWaitingTimeForStatisticsServerWorkersStopped = 240

        # shutdown statisticsserver
        SqlTestCase.executeSetIniParametersWithRetrys("""ALTER SYSTEM ALTER CONFIGURATION ('%s','SYSTEM') SET ('%s','active') = 'false' WITH RECONFIGURE""" % (iniFile, section), cursor)
        maxRepeatCount = 361
        if self.isDebugBuild() or os.environ.get('USE_HDBCOV', False) or self.isAddressSanitizerBuild() or self.hasDebugAllocatorEnabled():
            maxRepeatCount *= 15
        for i in xrange(0, maxRepeatCount):
            try:
                cursor.execute("select count(*) from _SYS_STATISTICS.STATISTICS_SCHEDULE where status = 'Scheduled'")
            except dbapi.Error, err:
                if err[0] != 259 or i != 0:
                    raise
                else:
                    # statistics table does not exist, so statisticsserver is deactivated
                    print "Deactivated statisticsserver service (statisticstable does not exist)"
                    return
            count = cursor.fetchone()[0]
            if count == 0:
                self.waitForStatisticsServerWorkerThreadsStopped(waitTime=maxWaitingTimeForStatisticsServerWorkersStopped, conn=conn, forSystemDB=forSystemDB)
                break
            print "wait 1s for Embedded Statistics Server to finish active queue: %d/%d" % (i, maxRepeatCount)
            if i % 10 == 0:
                print "scheduled ids:"
                self.printResultSet (cursor, "select id from _SYS_STATISTICS.STATISTICS_SCHEDULE where status = 'Scheduled'")

                print "active statistics worker:"
                self.printResultSet (cursor, "select to_nvarchar(thread_detail), to_nvarchar(thread_state), to_nvarchar(thread_id) from sys.m_service_threads where service_name = 'indexserver' and thread_type = 'WorkerThread (StatisticsServer)' and to_nvarchar(thread_detail) != 'ready'")

                cursor.execute("select count(*) from sys.m_service_threads where service_name = 'indexserver' and thread_type = 'WorkerThread (StatisticsServer)' and to_nvarchar(thread_detail) != 'ready'")
                countWorker = cursor.fetchone()[0]
                # there are scheduled entries, but no worker thread is active: -> set to Idle
                if countWorker == 0:
                    cursor.execute("update _sys_statistics.statistics_schedule set status = 'Idle' where status = 'Scheduled'")
            # in case of hanging worker threads, get rtedumps every minutes after half of waiting time
            if i % 60 == 0  and  i > (maxRepeatCount/2)-1:
                MultiDBUtil.create_database_runtime_dumps(dbname=self.getConnectionDatabaseName())

            time.sleep(1)

        if count != 0:
            self.fail("Embedded Statistics Server did not finish all objects. This may interfere with itab check.") # see bug #82235

        cursor.execute("update _SYS_STATISTICS.STATISTICS_SCHEDULE set status = 'Inactive', statusreason='during tests' where status != 'Inactive'")

        print "Deactivated statisticsserver service"


    def enableStatisticsServer(self, conn, forSystemDB = False):
        """Activate statisticsserver service"""

        iniFile = self.getInifileNameForESS(forSystemDB=forSystemDB)
        section = 'statisticsserver'

        cursor = conn.cursor()
        try:
            cursor.execute("update _SYS_STATISTICS.STATISTICS_SCHEDULE set status = 'Idle', statusreason='' where status = 'Inactive' and statusreason='during tests'")
        except dbapi.Error:
            pass
        SqlTestCase.executeSetIniParametersWithRetrys("""ALTER SYSTEM ALTER CONFIGURATION ('%s','SYSTEM') UNSET ('%s','active') WITH RECONFIGURE""" % (iniFile, section), cursor)
        print "Activated statisticsserver service"

    def waitForEmbeddedStatisticsServer(self, waitTime=1000, conn=None, ignoreErrors=True, forSystemDB = False):
        logger.info("Wait for embedded stat server migration ...")
        # per default the embedded statisticsserver is set, can be overwritten by SYSTEM layer

        iniFileName = self.getInifileNameForESS(forSystemDB=forSystemDB)

        active = True
        if not conn:
            conn = self.conn
        cursor = conn.cursor()
        cursor.execute("select value from m_inifile_contents where file_name = '%s' and layer_name ='SYSTEM' and section='statisticsserver' and key = 'active'" % iniFileName)
        result = cursor.fetchone()
        if result is not None:
            active = result[0].lower() == 'true'
        if  not active:
            logger.info("statisticsserver-existence-check_result = %s", result[0].lower())
            logger.info("Skip (embedded statisticsserver not active)")
            return

        if self.isStatisticsServerForcedStopped (conn):
            logger.info("Skip (embedded statisticsserver: forcestop is set)")
            return

        # adjust waitTime
        if self.isDebugBuild() or os.environ.get('USE_HDBCOV', False) or self.isAddressSanitizerBuild() or self.hasDebugAllocatorEnabled(): # debug build or Coverage or ASan Run or debug allocators
            waitTime *= 30

        installationDone = False
        sumVersion = 0

        try:
            cursor.execute("select seconds_between(a, current_utctimestamp), b from (select substr_before (substr_after (definition,'-- created: '),'0000') a, substr_before (substr_after (definition, '-- created: '), '0000') b from procedures where schema_name = '_SYS_STATISTICS' and procedure_name = 'STATISTICS_SCHEDULABLEWRAPPER')")

            row = cursor.fetchone()
            if row is not None:    # the wrapper procedure was not there => no migration will happen
                ts = row[0]
                if row[1] == '':
                    print "initial wrapper"
                else:
                    print "existing wrapper created days %d (minutes %d) ago" % (ts/3600/24, ts/60)

            cursor.execute("select count(*) from (select seconds_between(substr_before (substr_after (definition,'-- created: '),'0000'), current_utctimestamp) a, substr_before (substr_after (definition, '-- created: '), '0000') b from procedures where schema_name = '_SYS_STATISTICS' and procedure_name = 'STATISTICS_SCHEDULABLEWRAPPER') where a > 4*3600 and b != ''")
            oldWrapper = cursor.fetchone()[0]    # 0: does not exist or is fresh generated (<4h)
            if oldWrapper > 0:
                time.sleep(15)                   # extra sleep time only if a wrapper from a backup exists => ESS will start migration

                # check, if migration already started (current timestamp in installation.state ([Installing|Done]... current_timestamp)
                for i in range (0, 60):
                    cursor.execute("select seconds_between(substr_after(value,'local time:'), current_timestamp) from _SYS_STATISTICS.STATISTICS_PROPERTIES where key = 'internal.installation.state'")
                    value = cursor.fetchone()[0]
                    if value < 3*3600:
                        print "installation.state updated %ds ago, continue ..." % value
                        break
                    time.sleep(1)

        except dbapi.Error:
            pass

        try:
            cursor.execute("select sum(version) from _sys_statistics.statistics_objects")
            sumVersion = cursor.fetchone()[0]
        except dbapi.Error:
            pass

        for i in range (0, int(waitTime / 5)):
            try:
                cursor.execute("select value from _SYS_STATISTICS.STATISTICS_PROPERTIES where key = 'internal.installation.state'")
                row = cursor.fetchone()
                if row is None:
                    logger.info("Could not get result from \"select value from _SYS_STATISTICS.STATISTICS_PROPERTIES where key = 'internal.installation.state'\". Try again...")
                else:
                    value = row[0]
                    if value.startswith("Done (okay)"):
                        installationDone = True
                        logger.info("OK: internal installation done")
                        break
                    elif value.startswith("Done"): # Done (error), Done (installation interrupted)
                        if ignoreErrors:
                            logger.debug("Status: %s", value)
                            installationDone = True
                        break
                    else:
                        logger.info("Wait: internal installation not yet done (%s)", value)
                        if (i+1) % 10 == 0:
                            if i >= waitTime/5/10:    # 50s default, much more in Dbg/Asan
                                sumVersion2 = 0
                                try:
                                    cursor.execute("select sum(version) from _sys_statistics.statistics_objects")
                                    sumVersion2 = cursor.fetchone()[0]
                                except dbapi.Error:
                                    pass
                                if sumVersion == sumVersion2:
                                    logger.info("not even a single object version has changed after %ds: ESS is off", i*5)
                                    cursor.close()
                                    return

                            active = True
                            cursor.execute("select value from m_inifile_contents where file_name = '%s' and layer_name ='SYSTEM' and section='statisticsserver' and key = 'active'" % iniFileName)
                            result = cursor.fetchone()
                            if result is not None:
                                active = result[0].lower() == 'true'
                                if not active:
                                    logger.info("statisticsserver-existence-check_result = %s", result[0].lower())
                                    logger.info("Skip (embedded statisticsserver disabled during installation)")
                                    break
                            cursor.execute("select count(*) from _sys_statistics.statistics_objects")
                            objCount = cursor.fetchone()[0]
                            logger.info("ESS objects installed: %d", objCount)
            except dbapi.Error,  e:
                if e.errorcode == 258: # system user not yet authorized
                    logger.info("Wait: Retry as SYSTEM user not yet authorized on _SYS_STATISTICS")
                elif e.errorcode == 259: # invalid table name
                    logger.info("Wait: Retry as table _SYS_STATISTICS.STATISTICS_PROPERTIES not yet found")
                else:
                    logger.info("Wait: Retry due to error: %d(%s)", e.errorcode, e.errortext)
                time.sleep(15)

            time.sleep(5)

        cursor.close()
        if active and not installationDone:
            self.fail ("statisticsserver did not manage to finish initialization before test starts. Check indexserver traces.")
        logger.info("Done (embedded statistics server ready or deactivated)")

    def getIndexServers(self, conn=None):
        return getIndexServerList(conn or self.conn)

    def getComputeServers(self, conn=None):
        """Get a list of all active computeservers in the current NewDb
        landscape. Returns None on error."""

        mainConn = conn or self.conn
        cursor = mainConn.cursor()

        cursor.execute("select HOST,PORT,SQL_PORT, COORDINATOR_TYPE from SYS.M_SERVICES where SERVICE_NAME='computeserver' AND ACTIVE_STATUS='YES' ORDER BY HOST, PORT")
        resultset = cursor.fetchall()
        cursor.close()
        return resultset

    def createBackupUser(self):
        """Create backup user backupAdmin"""
        self.backupRecoveryManager.createBackupUser(None)

    def dropBackupUser(self):
        """Drop backup user backupAdmin"""
        self.backupRecoveryManager.dropBackupUser(None)

    def createBackup(self, backupName, backupType=BackupType.COMPLETE, destinationType=DestinationType.FILE, isVerbose=False):
        """Create backup"""
        self.backupRecoveryManager.createBackup(backupName, backupType, destinationType, True, None, isVerbose)

    def doRecoverUntilNow(self, clearLog=False, isVerbose=False, usingResume=False, ignoreVolume=None, dataSource=None, logSource=None, catalogSource=None, backupId=None):
        """Recover until most recent state"""
        if self._multiDBInstance:
            self.backupRecoveryManager.doRecoverUntilNowForDatabase(self.getConnectionDatabaseName(), clearLog, verbose=isVerbose, dataSource=dataSource, logSource=logSource, catalogSource=catalogSource, backupId=backupId)
        else:
            self.backupRecoveryManager.doRecoverUntilNow(clearLog, verbose=isVerbose, usingResume=usingResume, ignoreVolume=ignoreVolume, dataSource=dataSource, logSource=logSource, catalogSource=catalogSource, backupId=backupId)

    def doRecoverUntilTimestamp(self, timestamp, clearLog=False, isVerbose=False, usingResume=False):
        """Recover until timestamp is reached"""
        if self._multiDBInstance:
            self.backupRecoveryManager.doRecoverUntilTimestampForDatabase(timestamp, self.getConnectionDatabaseName(), clearLog, verbose=isVerbose)
        else:
            self.backupRecoveryManager.doRecoverUntilTimestamp(timestamp, clearLog, verbose=isVerbose, usingResume=usingResume)

    def doRecoverUntilLogPos(self, volumeId, logPos, clearLog=False, isVerbose=False):
        """Recover until redo log position of a given volume is reached"""
        if self._multiDBInstance:
            self.backupRecoveryManager.doRecoverUntilLogPosForDatabase(self.getConnectionDatabaseName(), volumeId, logPos, clearLog, verbose=isVerbose)
        else:
            self.backupRecoveryManager.doRecoverUntilLogPos(volumeId, logPos, clearLog, verbose=isVerbose)

    def doRecoverData(self, backupName, clearLog=True, isVerbose=False):
        """Recover data backup (if log mode is legacy clearLog == False will replay log)"""
        if self._multiDBInstance:
            self.backupRecoveryManager.doRecoverDataForDatabase(self.getConnectionDatabaseName(), backupName, clearLog, verbose=isVerbose)
        else:
            self.backupRecoveryManager.doRecoverData(backupName, clearLog, verbose=isVerbose)

    def getCurrentLogPositionByVolume(self, volumeId):
        cursor = self.conn.cursor()
        cursor.execute("SELECT POSITION FROM SYS.M_DEV_SERVICE_LOG_POSITIONS WHERE VOLUME_ID = ?", volumeId )
        ret = cursor.fetchone()
        return ret[0]

    def getCurrentLogPositions(self):
        cursor = self.conn.cursor()
        cursor.execute("SELECT VOLUME_ID, POSITION FROM SYS.M_DEV_SERVICE_LOG_POSITIONS")
        rc = {}
        while(True):
            ret = cursor.fetchone()
            if(not ret): break
            if(ret[1] != -1):
                rc[ret[0]] = ret[1]
        return rc

    def getVolumeIdForIndexMaster(self):
        cursor = self.conn.cursor()
        cursor.execute("""SELECT VOLUME_ID FROM M_SERVICES AS S, M_VOLUMES AS V
             WHERE S.HOST = V.HOST AND S.PORT = V.PORT
             AND S.SERVICE_NAME = 'indexserver' AND S.COORDINATOR_TYPE = 'MASTER'""")
        ret = cursor.fetchone()
        return ret[0]

    def updateDatabase(self):#, revision):
        """ currently only updates to latest orange (opt) """
        #function added for bug 75218

        def getHdbupdPath():#revision):
            if os.name == "posix":
                #does not work as root user is required to trigger hdbupd for a release build
                #-> only dev builds work currently
                #path = "/sapmnt/production/newdb/NewDB100/rel/%s"%(revision)
                #path = os.path.join(path,"server","linuxx86_64","SAP_HANA_DATABASE")
                pathToRevision = "/sapmnt/production2/makeresults/HANA/pools/Engine/MT/CO/orange/opt/linuxx86_64/LastBuild/__installer.HDB/"
            else:
                raise TestError('getHdbupdPath() not supported for %s'%(os.name))

            self.assertTrue(os.path.isdir(pathToRevision), " '%s' does not exist or is not a folder"%(pathToRevision))
            self.assertTrue(os.path.isfile(os.path.join(pathToRevision,"hdbupd")), " '%s' does not exist or is not a file"%(os.path.join(pathToRevision,"hdbupd")))
            return pathToRevision

        oldDir = os.getcwd()
        hdbupdDir = getHdbupdPath()#revision)
        os.chdir(os.path.abspath(hdbupdDir)) #use absolute path instead

        try:
            #do not use subprocess.call with PIPEs for stdout/stderr -> might deadlock
            #use communicate or poll to see whether child process is done or not
            parameters = "--batch --password=trextrex --system_user_password=manager"
            command = "hdbupd %s"%(parameters)
            if self._verbosity>0:
                print "calling command: %s path: %s"%(command, hdbupdDir)
            child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, shell=True)

            # pylint: disable=W0612
            # Unused variable 'stdErrData' suppressed
            (stdoutData, stdErrData) = child.communicate() #if communicate returns, child process has finished
            ret = child.returncode

            if ret != 0:
                #something went wrong -> get stdout and throw exception
                raise Exception(stdoutData)
            elif self._verbosity > 0:
                print "*** hdbupd call summary: ***"
                print stdoutData

        finally:
            os.chdir(oldDir)

    # workaround for bug #11870: Reconfigure can fail in many ways, so we are retrying
    @staticmethod
    def executeSetIniParametersWithRetrys(sql, cursor):
        executeSetIniParametersWithRetrys(sql, cursor)

    def dropImportedTables(self):
        """Drop tables which were imported before with importTables"""

        conn_mgr = self.createConnectionManager()
        conn = conn_mgr.createConnection(autocommit=False)
        cursor = conn.cursor()

        stopwatch = Stopwatch()
        stopwatch.start()

        if os.environ.get("HDB_DROP_TABLES") != "NO":
            while len(self._tableImportTearDownStmts) > 0:
                stmt = self._tableImportTearDownStmts.pop()

                try:
                    cursor.execute(stmt)
                except dbapi.Error, err:
                    pass

        stopwatch.stop()
        logger.info("drop of tables took %ss" % stopwatch.getElapsedSeconds())

        conn.commit()

    def importTables(self, tableQualifier, readOnly=False, threads=12, catalogOnly=False, onConnection = None, preload=False, location = None):
        """Import tables"""

        if type(tableQualifier) != types.TupleType:
            tableQualifier = (tableQualifier,)

        if len(tableQualifier) > 0:
            iniData = RemoteDataManager.tableLookup(tableQualifier)

            if os.environ.get("HDB_DROP_TABLES") == "NO":
                readOnly = True

            if not readOnly:
                replace = "replace"
            else:
                replace = ""

            if catalogOnly:
                catalogOnlyOption = "catalog only"
            else:
                catalogOnlyOption = ""

            if onConnection is None:
                conn_mgr = self.createConnectionManager()
                conn = conn_mgr.createConnection(autocommit=False)
            else:
                conn = onConnection
            cursor = conn.cursor()

            locationOption = ""
            if location is not None:
                if type(location) == str:
                    locationOption = "at location '%s'"%location
                elif type(location) == int:
                    locationOption = "at location '%s'"%self.getServerString(location)
                else:
                    raise Exception('Cannot handle location value %s with type %s'%(str(location),str(type(location))))

            logger.info("starting import of tables")
            stopwatch = Stopwatch()
            preload_stopwatch = Stopwatch()
            preload_stopwatch.startPaused()
            stopwatch.start()

            for tableInfo in iniData:
                try:
                    cursor.execute('''select SCHEMA_NAME from SYS.SCHEMAS''')
                    schemas = [schema[0] for schema in cursor.fetchall()]

                    cursor.execute("import %(tables)s as binary from '%(path)s' with %(catalogOnlyOption)s %(replace)s threads %(threads)i %(locationOption)s" % {"tables": tableInfo["table_name"], "path": tableInfo["path"], "catalogOnlyOption": catalogOnlyOption, "replace": replace, "threads": threads, "locationOption":locationOption})
                    cursor.execute('''select * from "#IMPORT_RESULT" where status = 'done' ''')
                    rows = cursor.fetchall()
                    newschemas = list(set([row["SCHEMA_NAME"] for row in rows]) - set(schemas))

                    for row in rows:
                        if row["SCHEMA_NAME"].startswith("_SYS") and row["OBJECT_TYPE"] == "TABLE":
                            self._tableImportTearDownStmts.append("""truncate table "%(schema)s"."%(name)s" """ % {"schema": row["SCHEMA_NAME"], "name": row["OBJECT_NAME"]})
                        else:
                            self._tableImportTearDownStmts.append("""drop %(type)s "%(schema)s"."%(name)s" """ % {"type": row["OBJECT_TYPE"], "schema": row["SCHEMA_NAME"], "name": row["OBJECT_NAME"]})
                    if preload:
                        preload_stopwatch.resume()
                        tabList = []
                        for row in rows:
                            if row["OBJECT_TYPE"] == "TABLE" and not row["OBJECT_NAME"].startswith("_SYS_SPLIT_"):
                                tabList.append("%(schema)s.%(name)s" % {"schema": row["SCHEMA_NAME"], "name": row["OBJECT_NAME"]})
                        if onConnection is None:
                            preloadTables(conn_mgr, tabList, threads) # Note: connman is preferred as is does not serialize on the cursor
                        else:
                            preloadTables(cursor, tabList, threads)
                        preload_stopwatch.pause()
                    self._tableImportTearDownStmts += ["""drop schema %s cascade""" %schema for schema in newschemas]
                except dbapi.Error, e:
                    if not (e.errorcode == 651 and readOnly):
                        # code 651 = can't import due to table already exists
                        # TODO: Check that before importing
                        raise

            stopwatch.stop()
            preload_stopwatch.stop()
            logger.info("import of tables took %ss" , stopwatch.getElapsedSeconds())
            if preload:
                logger.info("and preload of tables took %ss out of %ss" , preload_stopwatch.getElapsedSeconds(), stopwatch.getElapsedSeconds())

    def waitForGarbageCollection(self, maxwait=600, minversioncount=100, conn=None):
        """Wait for garbage collection"""
        if conn is None:
            conn = self.conman.createConnection()
        triggerRSVersionGC(conn)
        waitForRSVersionGC(conn, maxwait, minversioncount)

    def checkPendingRemoteOperations(self, cursor, removeVolumeIds, reorg_id, host, port, fail):
        import PersistenceLayerPy
        PersistenceLayerPy.init()

        if not removeVolumeIds:
            cursor.execute("select VOLUME_ID from SYS.M_VOLUMES")
            rows=cursor.fetchall()
            removestate=rows[0][0]
            for row in rows:
                removeVolumeIds.append(row[0])

        retryCount = 20
        remoteOpsCount = 0
        retry = 0
        while retry < retryCount:
            remoteOpsCount = 0
            for current_volumeid in removeVolumeIds:
                try:
                    tempRemoteOpsCount = PersistenceLayerPy.getRemoteOperationCount(current_volumeid)
                    if tempRemoteOpsCount != 0:
                        remoteOpsCount += tempRemoteOpsCount
                        sqlCmd = "SELECT * FROM \"SYS\".\"M_UNDO_CLEANUP_FILES\" WHERE TYPE <> 'FREE' and VOLUME_ID = %i" % current_volumeid
                        cursor.execute(sqlCmd)
                        undoCleanUp = cursor.fetchall()
                        print  '''Undo Cleanup (SELECT * FROM "SYS"."M_UNDO_CLEANUP_FILES" WHERE TYPE <> 'FREE' and VOLUME_ID = %i):
%s'''%(current_volumeid, undoCleanUp)
                except:
                    pass

            if remoteOpsCount == 0:
                break
            cursor.execute('alter system reclaim version space')
            cursor.execute('ALTER SYSTEM SAVEPOINT')
            time.sleep(2)
            retry += 1

        if remoteOpsCount > 0:
            retryCount += 5
            while retry < retryCount:
                remoteOpsCount = 0
                for current_volumeid in removeVolumeIds:
                    try:
                        remoteOpsCount += PersistenceLayerPy.getRemoteOperationCount(current_volumeid)
                    except:
                        pass

                if remoteOpsCount == 0:
                    break
                print 'remoteops not gone after %i retry, still %i pending'%(retry, remoteOpsCount)
                self.printSmallSystemStat(cursor)
                cursor.execute('alter system reclaim version space')
                cursor.execute('ALTER SYSTEM SAVEPOINT')
                time.sleep(2)
                retry += 1

            if reorg_id > 0:
                self.printRemoveHostFailure(cursor, reorg_id, host, port)
            self.printSystemStat(cursor)
            if fail == True:
                raise self.failureException('''not all remote operation got cleared (even after explicit trigger of savepoint) - %i savepoints, still %i pending''' %(retryCount, remoteOpsCount))
            else:
                print('''not all remote operation got cleared (even after explicit trigger of savepoint) - %i savepoints, still %i pending''' %(retryCount, remoteOpsCount))

    def checkTableConsistency(self, cursor, checkAction, schema = None, table = None):
        result = []
        errorEntries = []
        infoEntries = []
        errorCodeAllocationFailed = 5088

        print 'Executing table consistency check (action: %s)... ' % checkAction,
        stopwatch = Stopwatch()
        stopwatch.start()
        try:
            cursor.callproc("CHECK_TABLE_CONSISTENCY", (checkAction, schema, table))
        except dbapi.Error, err:
            stopwatch.stop()
            print '''failure: %s''' % err
            raise
        else:
            stopwatch.stop()
        elapsedSeconds = stopwatch.getElapsedSeconds()

        result = cursor.fetchall()
        for entry in result:
            severity = str(entry['SEVERITY'])
            errorCode = int(entry['ERROR_CODE'])
            if severity != 'INFO' and errorCode != errorCodeAllocationFailed:
                errorEntries.append(entry)
            else:
                infoEntries.append(entry)

        if not errorEntries:
            print 'success (took %ss)' % elapsedSeconds
        else:
            print 'failure: %d errors (took %ss)' % (len(errorEntries), elapsedSeconds)

        for entry in errorEntries:
            print '  -', entry
        for entry in infoEntries:
            print '  - (information)', entry

        self.assertEqual(len(errorEntries), 0, 'Found inconsistency during table consistency check')

    def enableSQLDBCTrace(self, enable):
        return enableSQLDBCTrace(enable=enable)

    def isOemBuild(self):
        return isOemBuild()

    def isAddressSanitizerBuild(self):
        return isAddressSanitizerBuild()

    def isAddressSanitizerDSOBuild(self):
        return isAddressSanitizerDSOBuild()

    def getServerStartTime(self, host, port):
        import NameServerPy
        ns = NameServerPy.TNSClient()
        (activeState, currentStartTime) = ns.getServerActive(host, int(port), True)
        return currentStartTime

    def waitForServer(self, host, port, oldStartTime, maxwait=600):
        import NameServerPy
        ns = NameServerPy.TNSClient()
        t = 0
        if self.isCoverageRun():
            maxwait *= 6

        for t in range(maxwait + 1):
            try:
                (activeState, currentStartTime) = ns.getServerActive(host, int(port), True)
            except:
                time.sleep(3)
                continue
            if currentStartTime != oldStartTime and activeState == NameServerPy.ActiveYes: break
            time.sleep(3)
        if t == maxwait:
            raise TestError, 'restart timeout'

        doAutocommit = False
        if self.globalCfg.has_key("autocommit"):
            doAutocommit = int(self.globalCfg["autocommit"])
        doDistributed = 'ALL'
        if self.globalCfg.has_key("clientDistributed") and self.globalCfg["clientDistributed"] == 'OFF':
            doDistributed = 'OFF'

        try:
            if self.conn.isconnected() is False:
                self.conn = self.conman.createConnection(autocommit=doAutocommit, DISTRIBUTION=doDistributed)
            cursor = self.conn.cursor()
            cursor.execute('SELECT 1 FROM DUMMY')
            cursor.close()
            del cursor
            self.conn.commit()
        except dbapi.Error as e:
            if e.errorcode == -10108 or e.errorcode == -10807 or e.errorcode == 145 or e.errorcode == 129 or e.errorcode == 149:
                self.conn = self.conman.createConnection(autocommit=doAutocommit, DISTRIBUTION=doDistributed)
            else:
                raise

    def forceStopInstance(self, host, indexServerPort):
        host = host.lower()
        scontrolverbosity = 1 # Print error messages
        scontrol = servicecontrol.ServiceController(scontrolverbosity)
        service = scontrol.get(indexServerPort, host)
        if service:
            scontrol.stop(indexServerPort, host)
        else:
            raise TestError('Can not stop indexserver "%s:%s": Remote '\
                'service is unknown' % (host, str(indexServerPort)))
        return

    def forceKillInstance(self, host, indexServerPort):
        host = host.lower()
        scontrolverbosity = 1 # Print error messages
        scontrol = servicecontrol.ServiceController(scontrolverbosity)
        service = scontrol.get(indexServerPort, host)
        if service:
            scontrol.kill(indexServerPort, host, 0)
        elif host == "localhost" or host == scontrol.getLocalhost():
            pidNum = self.getPid(host, indexServerPort)
            if pidNum == None:
                return
            PLATFORM = sys.platform #win32, sunos5, linux2
            if PLATFORM[:3].lower() == 'win':   killCmd = "taskkill /F /PID "
            else:                               killCmd = "kill -9 "
            killCmd += str(pidNum)
            os.system(killCmd)
            if self._verbosity > 0:
                print("#### Killed hdbindexserver: " + killCmd)
        else:
            raise TestError('Can not kill indexserver "%s:%s": Remote '\
                'service is unknown' % (host, str(indexServerPort)))
        return

    def assertDdlContextEmpty(self, tableName = ""):
        outputPath = os.path.join(os.getenv('DIR_INSTANCE'), os.getenv('HOSTNAME'), 'trace', 'hdbconsDdlContext.out')
        os.system("hdbcons 'ddlcontextstore list -o %s'" %outputPath)
        data_file = open(outputPath)
        isEmpty = True
        searchString = 'DdlContext'
        if not tableName == "":
            searchString = tableName.upper()
        for line in data_file:
            if searchString in line:
                print line
                isEmpty = False
        if not isEmpty:
            self.fail("DdlContext is not empty")
