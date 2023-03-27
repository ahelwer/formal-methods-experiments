------------------------------ MODULE AddTwo --------------------------------
EXTENDS Naturals, TLAPS

(****************************************************************************
--algorithm Increase {
  variable x = 0; {
    while (TRUE) {
      x := x + 2
    }
  }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "b4b07666" /\ chksum(tla) = "8adfa002")
VARIABLE x

vars == << x >>

Init == (* Global variables *)
        /\ x = 0

Next == x' = x + 2

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

TypeOK == x \in Nat

THEOREM TypeInvariant == Spec => []TypeOK
  <1>a. Init => TypeOK
    BY DEF Init, TypeOK
  <1>b. TypeOK /\ UNCHANGED vars => TypeOK'
    BY DEF TypeOK, vars
  <1>c. TypeOK /\ Next => TypeOK'
    <2> SUFFICES
          ASSUME TypeOK, Next
          PROVE TypeOK'
    <2> USE DEF TypeOK, Next
    <2>1. x \in Nat
    <2>2. x + 2 \in Nat
      <3>1. \A n \in Nat : n + 2 \in Nat
        OBVIOUS
      <3> QED BY <3>1, <2>1
    <2>3. x' \in Nat BY <2>1, <2>2
    <2>4. TypeOK' BY <2>3
    <2> QED BY <2>4
  <1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec

a|b == \E c \in Nat : a*c = b

AlwaysEven == 2|x

THEOREM Spec => []AlwaysEven
  <1>a. Init => AlwaysEven
    BY DEF Init, AlwaysEven, |
  <1>b. AlwaysEven /\ UNCHANGED vars => AlwaysEven'
    BY DEF AlwaysEven, vars
  <1>c. AlwaysEven /\ Next => AlwaysEven'
    <2> SUFFICES
          ASSUME AlwaysEven, Next
          PROVE AlwaysEven'
    <2> USE DEF AlwaysEven, Next
    <2>1. PICK c \in Nat : 2 * c = x BY DEF |
    <2>2. 2*(c + 1) = x + 2 BY <2>1
    <2>3. 2|(x + 2) BY <2>2 DEF |
    <2>4. QED BY <2>3
  <1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec

=============================================================================

