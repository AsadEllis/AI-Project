import SudokuBoard
import Variable
import Domain
import Trail
import Constraint
import ConstraintNetwork
import time
import random

class BTSolver:

    # ==================================================================
    # Constructors
    # ==================================================================

    def __init__ ( self, gb, trail, val_sh, var_sh, cc ):
        self.network = ConstraintNetwork.ConstraintNetwork(gb)
        self.hassolution = False
        self.gameboard = gb
        self.trail = trail

        self.varHeuristics = var_sh
        self.valHeuristics = val_sh
        self.cChecks = cc

    # ==================================================================
    # Consistency Checks
    # ==================================================================

    # Basic consistency check, no propagation done
    def assignmentsCheck ( self ):
        for c in self.network.getConstraints():
            if not c.isConsistent():
                return False
        return True

    def forwardChecking ( self ):

        modifiedVars = {} # Dictionary maps modified variables to modified domain
        isConsistent = True # Boolean value for if the FC detects inconsistency
        vars = []
        for c in self.network.constraints:
            for v in c.vars:
                vars.append(v) # Finds all variables in network

        for v in vars:
            if v.isAssigned():
                assignedValue = v.getAssignment()
                for neighbor in self.network.getNeighborsOfVariable(v):
                    if neighbor.isChangeable and neighbor.isAssigned() == False and assignedValue in neighbor.getValues():
                        self.trail.push(neighbor) 
                        neighbor.removeValueFromDomain(assignedValue)
                        modifiedVars.update({neighbor: neighbor.getDomain()})
                        if neighbor.domain.size() == 0:
                            isConsistent = False
                        if neighbor.domain.size() == 1:
                            # self.trail.push(neighbor)
                            neighbor.assignValue(neighbor.getValues()[0])
                            modifiedVars.update({neighbor : neighbor.getDomain()})
                            nValue = neighbor.getAssignment()
                            for n in self.network.getNeighborsOfVariable(neighbor):
                               if n.domain.size() == 1 and nValue in n.getValues():
                                   isConsistent = False
                        

        return (modifiedVars, isConsistent)
    
    # =================================================================
	# Arc Consistency
	# =================================================================
    def arcConsistency( self ):
        assignedVars = []
        for c in self.network.constraints:
            for v in c.vars:
                if v.isAssigned():
                    assignedVars.append(v)
        while len(assignedVars) != 0:
            av = assignedVars.pop(0)
            for neighbor in self.network.getNeighborsOfVariable(av):
                if neighbor.isChangeable and not neighbor.isAssigned() and neighbor.getDomain().contains(av.getAssignment()):
                    neighbor.removeValueFromDomain(av.getAssignment())
                    if neighbor.domain.size() == 1:
                        neighbor.assignValue(neighbor.domain.values[0])
                        assignedVars.append(neighbor)

    
    
    def norvigCheck ( self ):

        # (1)
        fcTuple = self.forwardChecking()
        # modifiedVars = fcTuple[0]
        isConsistent = fcTuple[1]
        if isConsistent == False:
            return ({}, False)
        
        # (2)
        assignedNorvigVars = {}
        counter = []
        N = self.gameboard.N 
        
        # print(len(self.network.constraints))

        for unit in self.network.constraints:
            #print()
            #print(unit)
            #print()
            for i in range(0, N+1):
                counter.append(0)
            for i in range(1, N + 1):
                for val in unit.vars[i - 1].getValues():
                    counter[val] += 1
            for i in range(1, N + 1):
                if counter[i] == 1:
                    for v in unit.vars:
                        if i in v.getValues():
                            self.trail.push(v)
                            v.assignValue(i)
                            assignedNorvigVars.update({v : i})
                            #isConsistent = self.forwardChecking()[1]
                            #if isConsistent == False:
                            #    return (assignedNorvigVars, isConsistent)
                        break


       # print("Returning: ", assignedNorvigVars, isConsistent)
        return (assignedNorvigVars, isConsistent)


    def getTournCC ( self ):
        isConsistent = self.norvigCheck()
        return isConsistent

    # ==================================================================
    # Variable Selectors
    # ==================================================================

    # Basic variable selector, returns first unassigned variable
    def getfirstUnassignedVariable ( self ):
        for v in self.network.variables:
            if not v.isAssigned():
                return v

        # Everything is assigned
        return None

    def getMRV ( self ):
        unassignedVars = []
        result = None # The MRV that needs to be returned

        for c in self.network.constraints:
            for v in c.vars:
                if not v.isAssigned():
                    unassignedVars.append(v) # Finds all unassigned variables in network

        for v in unassignedVars:
            if result == None or v.getDomain().size() < result.getDomain().size():
                result = v

        return result

    def MRVwithTieBreaker ( self ):
        unassignedVars = []
        result = [] # The MRV list that needs to be returned
        resultDomain  = None # Used to keep track of the domain that all the result variables have
        minSize = -1 # Used to keep track of variable domain sizes in result list

        for v in self.network.variables:
            if v.isAssigned() == False:
                unassignedVars.append(v) # Finds all unassigned variables in network
        # print(*unassignedVars)

        for v in unassignedVars:
            vDomain = v.getValues()
            vSize = v.getDomain().size()
            if len(result) == 0:
                result.append(v)
                resultDomain = vDomain
                minSize = vSize
            elif vSize < minSize:
                result = []
                result.append(v)
                resultDomain = vDomain
                minSize = vSize
            elif vSize == minSize and vDomain == resultDomain:
                result.append(v)
            
        if len(result) == 0:
            return [None]

        result = self.degreeHeuristic(result)
        # print(*result)

        return result


    # Helper function for MAD heuristic
    def degreeHeuristic(self, varList):
        result = []
        maxNeighbors = -1 # Max count of neighbor variables

        for var in varList:
            varNeighbors = self.getUnassignedNeighbors(var)
            if maxNeighbors < len(varNeighbors):
                result.clear()
                maxNeighbors = len(varNeighbors)
                result.append(var)
            elif maxNeighbors == len(varNeighbors):
                result.append(var)


        return result

    # Helper function for degree heuristic
    def getUnassignedNeighbors(self, v):
        result = []

        for neighbor in self.network.getNeighborsOfVariable(v):
            if neighbor.isAssigned() == False:
                result.append(neighbor)

        return result


    def getTournVar ( self ):
        return self.MRVwithTieBreaker()[0]

    # ==================================================================
    # Value Selectors
    # ==================================================================

    # Default Value Ordering
    def getValuesInOrder ( self, v ):
        values = v.domain.values
        return sorted( values )

    def getValuesLCVOrder ( self, v ):
        result = []
        vValues = v.getValues()
        valueFrequency = {}
        neighbors = self.network.getNeighborsOfVariable(v)
        unassignedNeighbors = []
                
        if len(vValues) == 1:
            return vValues
        
        for value in vValues:
            valueFrequency[value] = 0

        for neighbor in neighbors:
            if not neighbor.isAssigned():
                unassignedNeighbors.append(neighbor)

        for value in valueFrequency.keys():
            for neighbor in unassignedNeighbors:
                for nValue in neighbor.getValues():
                    if value == nValue:
                        valueFrequency[value] += 1

        sortedDict= sorted(valueFrequency.items(), key=lambda element: element[1]) # Returns tuple list of tuples sorted by value [(key, value)]

        for pair in sortedDict:
            result.append(pair[0])
            # print(pair)

        # For (testing) sorted pairs
        '''
        strValues = ""

        for element in sortedDict.keys():
            strValues += str(element) + ": " + str(sortedDict[element]) + " "
        print(strValues)
        '''

        return result

     def getTournVal ( self, v ):
        return self.getValuesLCVOrder(v)

    # ==================================================================
    # Engine Functions
    # ==================================================================

    def solve ( self, time_left=600):
        if time_left <= 60:
            return -1

        start_time = time.time()
        if self.hassolution:
            return 0

        # Variable Selection
        v = self.selectNextVariable()

        # check if the assigment is complete
        if ( v == None ):
            # Success
            self.hassolution = True
            return 0

        # Attempt to assign a value
        for i in self.getNextValues( v ):

            # Store place in trail and push variable's state on trail
            self.trail.placeTrailMarker()
            self.trail.push( v )

            # Assign the value
            v.assignValue( i )

            # Propagate constraints, check consistency, recur
            if self.checkConsistency():
                elapsed_time = time.time() - start_time 
                new_start_time = time_left - elapsed_time
                if self.solve(time_left=new_start_time) == -1:
                    return -1
                
            # If this assignment succeeded, return
            if self.hassolution:
                return 0

            # Otherwise backtrack
            self.trail.undo()
        
        return 0

    def checkConsistency ( self ):
        if self.cChecks == "forwardChecking":
            return self.forwardChecking()[1]

        if self.cChecks == "norvigCheck":
            return self.norvigCheck()[1]

        if self.cChecks == "tournCC":
            return self.getTournCC()

        else:
            return self.assignmentsCheck()

    def selectNextVariable ( self ):
        if self.varHeuristics == "MinimumRemainingValue":
            # print("Select next variable with MRV returns:", self.getMRV())
            return self.getMRV()

        if self.varHeuristics == "MRVwithTieBreaker":
            # print("Select next variable with MAD returns:", self.MRVwithTieBreaker())
            return self.MRVwithTieBreaker()[0]

        if self.varHeuristics == "tournVar":
            return self.getTournVar()

        else:
            return self.getfirstUnassignedVariable()

    def getNextValues ( self, v ):
        if self.valHeuristics == "LeastConstrainingValue":
            return self.getValuesLCVOrder( v )

        if self.valHeuristics == "tournVal":
            return self.getTournVal( v )

        else:
            return self.getValuesInOrder( v )

    def getSolution ( self ):
        return self.network.toSudokuBoard(self.gameboard.p, self.gameboard.q)
