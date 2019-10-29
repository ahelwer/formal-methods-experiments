class Action:
    def __init__(self, resultState, actionName):
        self.resultState = resultState
        self.actionName = actionName
    
    def __str__(self):
        return "{}: {}".format(self.actionName, self.resultState)

def GetNextStates(current):
    nextStates = []
    small = current[0]
    large = current[1]

    # fill 3
    next = (3, large)
    nextStates.append(Action(next, "fill 3"))

    # fill 5
    next = (small, 5)
    nextStates.append(Action(next, "fill 5"))

    # empty 3
    next = (0, large)
    nextStates.append(Action(next, "empty 3"))

    # empty 5
    next = (small, 0)
    nextStates.append(Action(next, "empty 5"))

    # transfer 3 to 5
    transferred = min(5 - large, small)
    next = (small - transferred, large + transferred)
    nextStates.append(Action(next, "transfer 3 to 5"))

    # transfer 5 to 3
    transferred = min(3 - small, large)
    next = (small + transferred, large - transferred)
    nextStates.append(Action(next, "transfer 5 to 3"))

    return nextStates

def InvariantHolds(current):
    return current[1] != 4

def PathToState(source, predecessor, sink):
    pathHashes = []
    current = hash(sink)
    while current != 0:
        pathHashes.append(current)
        current = predecessor[current]

    pathHashes.reverse()
    pathHashes.pop(0)

    path = ["init: {}".format(source)]
    current = source
    for nextHash in pathHashes:
        actions = GetNextStates(current)
        for action in actions:
            nextState = action.resultState
            if hash(nextState) == nextHash:
                path.append(str(action))
                current = nextState
                break

    return path

def ModelCheck(source):
    queue = [source]
    visited = {hash(source)}
    predecessor = { hash(source) : 0 }
    while len(queue) != 0:
        current = queue.pop(0)

        if not InvariantHolds(current):
            return PathToState(source, predecessor, current)

        actions = GetNextStates(current)
        for action in actions:
            nextState = action.resultState
            if hash(nextState) not in visited:
                visited.add(hash(nextState))
                predecessor[hash(nextState)] = hash(current)
                queue.append(nextState)

    return None

source = (0, 0)
result = ModelCheck(source)
print(result)