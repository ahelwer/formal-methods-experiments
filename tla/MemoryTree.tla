----------------------------- MODULE MemoryTree -----------------------------
EXTENDS Naturals

CONSTANTS Address, Value

VARIABLE rootAddr, mem

Null == CHOOSE n : n \notin Address
Node == [
    value   : Value,
    left    : Address \cup {Null},
    right   : Address \cup {Null}
]
Empty == CHOOSE n : n \notin Node
Memory == [Address -> Node \cup {Empty}]

IsSortedBinaryTree ==
    /\ \A addr \in Address :
        /\ mem[addr] /= Empty =>
            LET node == mem[addr] IN
            /\ node.left /= Null =>
                /\ mem[node.left] /= Empty
                /\ mem[node.left].value < node.value
            /\ node.right /= Null =>
                /\ mem[node.right] /= Empty
                /\ mem[node.right].value > node.value

ExactlyOneParent ==
    /\ \A addr \in Address :
        /\ mem[addr] /= Empty =>
            IF rootAddr = addr
            THEN
                /\ \A otherAddr \in Address :
                    LET otherNode == mem[otherAddr] IN
                    /\ otherNode /= Empty =>
                        /\ otherNode.left /= addr
                        /\ otherNode.right /= addr
            ELSE
                /\ \E parentAddr \in Address \ {addr} :
                    LET parentNode == mem[parentAddr] IN
                    /\ parentNode /= Empty
                    /\  \/  /\ parentNode.left = addr
                            /\ parentNode.right /= addr
                        \/  /\ parentNode.right = addr
                            /\ parentNode.left /= addr

DescendentsOf[a \in Address \cup {Null}] ==
    LET Descendents[addr \in Address \cup {Null}, seen \in SUBSET Address] ==
        CASE addr = Null        -> {}
        [] addr \in seen        -> {}
        [] mem[addr] = Empty    -> {}
        [] OTHER                ->
            LET node == mem[addr] IN
            LET nowSeen == seen \cup {addr} IN
            {addr}
                \cup Descendents[node.left, nowSeen]
                \cup Descendents[node.right, nowSeen]
    IN Descendents[a, {}]

AllReachableFromRoot ==
    LET rootDescendents == DescendentsOf[rootAddr] IN
    /\ \A addr \in Address :
        /\ mem[addr] /= Empty =>
            /\ addr \in rootDescendents

TypeInv ==
    /\ mem \in Memory
    /\ rootAddr \in Address \cup {Null}

SafetyInv ==
    /\ IsSortedBinaryTree
    /\ ExactlyOneParent
    /\ AllReachableFromRoot

Init ==
    /\ mem = [a \in Address |-> Empty]
    /\ rootAddr = Null

RECURSIVE GetParentAddrOf(_, _)
GetParentAddrOf(nodeAddr, value) ==
    LET node == mem[nodeAddr] IN
    CASE
        node.value < value ->
            IF node.right = Null
            THEN nodeAddr
            ELSE GetParentAddrOf(node.right, value)
        [] node.value = value -> Null
        [] node.value > value ->
            IF node.left = Null
            THEN nodeAddr
            ELSE GetParentAddrOf(node.left, value)

Allocate == CHOOSE a \in Address : mem[a] = Empty

Add(value) ==
    IF rootAddr = Null
    THEN
        LET addr == Allocate IN
        /\ mem' =
            [mem EXCEPT
                ![addr] = [
                    value   |-> value,
                    left    |-> Null,
                    right   |-> Null
                ]
            ]
        /\ rootAddr' = addr
    ELSE
        LET parentAddr == GetParentAddrOf(rootAddr, value) IN
        IF parentAddr = Null
        THEN FALSE
        ELSE
            LET parent == mem[parentAddr] IN
            LET addr == Allocate IN
            /\ mem' =
                [mem EXCEPT
                    ![addr] = [
                        value   |-> value,
                        left    |-> Null,
                        right   |-> Null
                    ],
                    ![parentAddr] = [
                        @ EXCEPT ![
                            IF parent.value < value
                            THEN "right"
                            ELSE "left"
                        ] = addr
                    ]
                ]
            /\ UNCHANGED rootAddr

Next ==
    \/ \E a \in Address :
        /\ mem[a] = Empty
        /\ \E v \in Value :
            /\ Add(v)
    \/ UNCHANGED <<mem, rootAddr>>

=============================================================================
