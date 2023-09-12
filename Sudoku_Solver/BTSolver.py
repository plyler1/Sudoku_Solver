import SudokuBoard
import Variable
import Domain
import Trail
import Constraint
import ConstraintNetwork
import time
import random

import string

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

    """
        User-defined Function: Implement the Forward Checking Heuristic

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        Note: remember to trail.push variables before you assign them
        Return: a tuple of a dictionary and a bool. The dictionary contains all MODIFIED variables, mapped to their MODIFIED domain.
                The bool is true if assignment is consistent, false otherwise.
    """
    def forwardChecking ( self ):
        modified = {}
        assignedVars = []
        for c in self.network.constraints:
            for v in c.vars:
                if v.isAssigned():
                    assignedVars.append(v)
        while len(assignedVars) != 0:
            av = assignedVars.pop(0)
            for neighbor in self.network.getNeighborsOfVariable(av):
                if neighbor.isChangeable and not neighbor.isAssigned() and neighbor.getDomain().contains(av.getAssignment()):
                    self.trail.push(neighbor)
                    neighbor.removeValueFromDomain(av.getAssignment())
                    if neighbor.domain.size() == 0:
                        return (modified, False)
                    modified[neighbor] = neighbor.getDomain()

        return (modified, True)

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

    
    """
        User-defined Function: Implement both of Norvig's Heuristics

        This function will do both Constraint Propagation and check
        the consistency of the network

        (1) If a variable is assigned then eliminate that value from
            the square's neighbors.

        (2) If a constraint has only one possible place for a value
            then put the value there.

        Note: remember to trail.push variables before you assign them
        Return: a pair of a dictionary and a bool. The dictionary contains all variables 
		        that were ASSIGNED during the whole NorvigCheck propagation, and mapped to the values that they were assigned.
                The bool is true if assignment is consistent, false otherwise.
    """
    def norvigCheck ( self ):
        assigned = {}
        assignedVars = []  
        numVars = len(self.network.constraints[0].vars)
        for c in self.network.constraints:
            # Make and zero out counter array
            counter = [0]*numVars
            for v in c.vars:
                if v.isAssigned():
                    assignedVars.append(v)
                for val in v.domain.values:
                    counter[val - 1] += 1
            # Norvig's Second Heuristic Pre-check
            # If a constraint has only one possible place for a value then put the value there
            for i in range(len(counter)):
                if counter[i] == 1:
                    for v in c.vars:
                        if v.isChangeable and not v.isAssigned() and v.getDomain().contains(i + 1):
                            self.trail.push(v)
                            v.assignValue(i + 1)
                            assigned[v] = v.getAssignment()
                            assignedVars.append(v)
                elif counter[i] == 0:
                    return (assigned, False)

        # Norvig's First Heuristic
        while len(assignedVars) != 0:
            av = assignedVars.pop(0)
            for neighbor in self.network.getNeighborsOfVariable(av):
                if neighbor.isChangeable and not neighbor.isAssigned() and neighbor.getDomain().contains(av.getAssignment()):
                    self.trail.push(neighbor)
                    neighbor.removeValueFromDomain(av.getAssignment())
                    if neighbor.domain.size() == 1:
                        if not self.forwardChecking()[1]:
                            return (assigned, False)
                        neighbor.assignValue(neighbor.domain.values[0])
                        assigned[neighbor] = neighbor.getAssignment()
                        assignedVars.append(neighbor)
                    elif neighbor.domain.size() == 0:
                        return (assigned, False)

        # Norvig's Second Heuristic
        for c in self.network.getModifiedConstraints():
            counter = [0]*numVars
            for v in c.vars:
                for val in v.domain.values:
                    counter[val - 1] += 1
            for i in range(len(counter)):
                if counter[i] == 1:
                    for v in c.vars:
                        if v.isChangeable and not v.isAssigned() and v.getDomain().contains(i + 1):
                            if not self.norvigCheck()[1]:
                                return (assigned, False)
                            self.trail.push(v)
                            v.assignValue(i + 1)
                            assigned[v] = v.getAssignment()
                elif counter[i] == 0:
                    return (assigned, False)

        return (assigned, True)
    
    def getTournCC ( self ):
        return self.norvigCheck()

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

    """
        User-defined Function: Implement the Minimum Remaining Value Heuristic

        Return: The unassigned variable with the smallest domain
    """
    def getMRV ( self ):
        minVar = None
        minSize = -1
        for v in self.network.variables:
            if not v.isAssigned():
                if minSize == -1 or minSize > v.domain.size():
                    minVar = v
                    minSize = v.domain.size()

        return minVar

    """
        User-defined Function: Implement the Minimum Remaining Value Heuristic
                       with Degree Heuristic as a Tie Breaker

        Return: The unassigned variable with the smallest domain and affecting the  most unassigned neighbors.
                If there are multiple variables that have the same smallest domain with the same number of unassigned neighbors, add them to the list of Variables.
                If there is only one variable, return the list of size 1 containing that variable.
    """
    def MRVwithTieBreaker ( self ):
        minVars = [None]
        minSize = -1
        for v in self.network.variables:
            if not v.isAssigned():
                if minSize == -1 or minSize > v.domain.size():
                    minVars = [v]
                    minSize = v.domain.size()
                    minVarDegree = -1
                elif minSize == v.domain.size():
                    if minVarDegree == -1:
                        minVarDegree = 0
                        for neighbor in self.network.getNeighborsOfVariable(minVars[0]):
                            if not neighbor.isAssigned():
                                minVarDegree += 1
                    degree = 0
                    for neighbor in self.network.getNeighborsOfVariable(v):
                        if not neighbor.isAssigned():
                            degree += 1
                    if minVarDegree < degree:
                        minVars = [v]
                        minVarDegree = degree
                    elif minVarDegree == degree:
                        minVars.append(v)
        return minVars

    def getTournVar ( self ):
        return self.MRVwithTieBreaker()[0]

    # ==================================================================
    # Value Selectors
    # ==================================================================

    # Default Value Ordering
    def getValuesInOrder ( self, v ):
        values = v.domain.values
        return sorted( values )

    """
        User-defined Function: Implement the Least Constraining Value Heuristic

        The Least constraining value is the one that will knock the least
        values out of it's neighbors domain.

        Return: A list of v's domain sorted by the LCV heuristic
                The LCV is first and the MCV is last
    """
    def getValuesLCVOrder ( self, v ):
        values = v.domain.values
        removedNums = [0]*len(values)
        domain = {}

        for neighbor in self.network.getNeighborsOfVariable(v):
            for i in range(len(values)):
                if neighbor.isChangeable and not neighbor.isAssigned() and neighbor.getDomain().contains(values[i]):
                    removedNums[i] += 1

        # make domain dictionary
        for i in range(len(values)):
            domain[values[i]] = removedNums[i]
        # sort domain by it's number of removed values
        sortedDomain = sorted(domain.items(), key=lambda x:x[1])
        vals = [pair[0] for pair in sortedDomain]
        return vals

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
            return self.getMRV()

        if self.varHeuristics == "MRVwithTieBreaker":
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