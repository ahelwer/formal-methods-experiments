import numpy as np

class Action:
    def __init__(self, resultState, actionName, probability):
        self.resultState = resultState
        self.actionName = actionName
        self.probability = probability
    
    def __str__(self):
        return "{} with P({}): {}".format(self.actionName, self.probability, self.resultState)

def StateTransitions():
    return { \
        0 : (1, 2), \
        1 : (3, 4), \
        2 : (5, 6), \
        3 : (7, 1), \
        4 : (8, 9), \
        5 : (10, 11), \
        6 : (12, 2), \
        7 : (7, 7), \
        8 : (8, 8), \
        9 : (9, 9), \
        10 : (10, 10), \
        11 : (11, 11), \
        12 : (12, 12)}

def TransitionMatrix(subgraph):
    T = StateTransitions()
    P = [[0.5*(sp == T[s][0]) + 0.5*(sp == T[s][1]) for sp in subgraph] for s in subgraph]
    return np.matrix(P)

def GetNextStates(current):
    transitions = StateTransitions()
    next = transitions[current]
    heads = Action(next[0], "H", 0.5)
    tails = Action(next[1], "T", 0.5)
    return [heads, tails]

def InGoalState(current):
    return current in {10}

def BuildGraph(source):
    # Fully explore graph
    queue = [source]
    visited = {source}
    sourcePredecessor = -1
    predecessor = { source : [sourcePredecessor] }
    G = set()
    while len(queue) != 0:
        current = queue.pop(0)

        if InGoalState(current):
            G.add(current)

        actions = GetNextStates(current)
        for action in actions:
            nextState = action.resultState
            if nextState in visited:
                predecessor[nextState].append(current)
            else:
                visited.add(nextState)
                predecessor[nextState] = [current]
                queue.append(nextState)

    # Find subgraph where goal states are reachable
    queue = [s for s in G]
    visited = {s for s in G}
    while len(queue) != 0:
        current = queue.pop(0)
        predecessors = predecessor[current]
        for pred in predecessors:
            if pred not in visited and pred != sourcePredecessor:
                visited.add(pred)
                queue.append(pred)
    T = visited - G

    # Calculate probabilities of transitioning directly to goal state
    predecessors = set().union(*[predecessor[s] for s in G]) - G
    next = StateTransitions()
    b = [0.5*(next[s][0] in G) + 0.5*(next[s][1] in G) for s in T]

    return (G, T, np.matrix(b).T)

source = 0
G, T, b = BuildGraph(source)
P = TransitionMatrix(T)
I = np.identity(len(T))
print('Solving (I-P)x = b')
print(np.linalg.solve(I - P, b))