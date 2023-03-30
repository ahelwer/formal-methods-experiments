---------------------------- MODULE FindHighest -----------------------------
EXTENDS Sequences, Naturals, Integers, TLAPS

(****************************************************************************
--algorithm Highest {
  variables
    f \in Seq(Nat);
    h = -1;
    i = 1;
  define {
    max(a, b) == IF a >= b THEN a ELSE b
  } {
lb: while (i <= Len(f)) {
      h := max(h, f[i]);
      i := i + 1;
    }
  }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "31f24270" /\ chksum(tla) = "819802c6")
VARIABLES f, h, i, pc

(* define statement *)
max(a, b) == IF a >= b THEN a ELSE b


vars == << f, h, i, pc >>

Init == (* Global variables *)
        /\ f \in Seq(Nat)
        /\ h = -1
        /\ i = 1
        /\ pc = "lb"

lb == /\ pc = "lb"
      /\ IF i <= Len(f)
            THEN /\ h' = max(h, f[i])
                 /\ i' = i + 1
                 /\ pc' = "lb"
            ELSE /\ pc' = "Done"
                 /\ UNCHANGED << h, i >>
      /\ f' = f

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == lb
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

TypeOK ==
  /\ f \in Seq(Nat)
  /\ i \in 1..(Len(f) + 1)
  /\ i \in Nat
  /\ h \in Nat \cup {-1}

THEOREM TypeInvariantHolds == Spec => []TypeOK
PROOF
  <1>a. Init => TypeOK
    BY DEFS Init, TypeOK
  <1>b. TypeOK /\ UNCHANGED vars => TypeOK'
    BY DEFS TypeOK, vars
  <1>c. TypeOK /\ Next => TypeOK'
    <2>a. TypeOK /\ lb => TypeOK'
      <3> SUFFICES  ASSUME TypeOK, lb
                    PROVE TypeOK'
          OBVIOUS
      <3> USE DEFS TypeOK, lb
      <3>a. CASE i <= Len(f) BY DEF max
      <3>b. CASE ~(i <= Len(f))
        <4>a. UNCHANGED <<f, h, i>> BY <3>b
        <4> QED BY <3>b, <4>a DEF lb
      <3> QED BY <3>a, <3>b
    <2>b. TypeOK /\ Terminating => TypeOK'
      BY DEFS TypeOK, Terminating, vars
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec

InductiveInvariant ==
  \A idx \in 1..(i - 1) : f[idx] <= h

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
PROOF
  <1>a. Init => InductiveInvariant
    BY DEFS Init, InductiveInvariant
  <1>b. InductiveInvariant /\ UNCHANGED vars => InductiveInvariant'
    BY DEFS InductiveInvariant, vars
  <1>c. InductiveInvariant /\ TypeOK /\ TypeOK' /\ Next => InductiveInvariant'
    <2>a. InductiveInvariant /\ Terminating => InductiveInvariant'
      BY DEFS InductiveInvariant, Terminating, vars
    <2>b. InductiveInvariant /\ TypeOK /\ TypeOK' /\ lb => InductiveInvariant'
      <3> SUFFICES  ASSUME InductiveInvariant, TypeOK, TypeOK', lb
                    PROVE InductiveInvariant'
          OBVIOUS
      <3> USE DEF TypeOK
      <3>a. CASE i <= Len(f)
        <4>a. f[i] <= h' BY <3>a DEFS lb, max
        <4>b. h <= h' BY <3>a DEFS lb, max
        <4>c. \A idx \in 1..i : f[idx] <= h'
          BY <4>a, <4>b DEF InductiveInvariant
        <4>d. i = i' - 1 BY <3>a DEF lb
        <4>e. UNCHANGED f
          BY DEF lb
        <4>f. \A idx \in 1..(i' - 1) : f'[idx] <= h'
          BY Zenon, <4>c, <4>d, <4>e
        <4> QED
          BY Zenon, <4>f DEF InductiveInvariant
      <3>b. CASE ~(i <= Len(f))
        <4> UNCHANGED <<f, h, i>> BY <3>b DEF lb
        <4> QED BY DEF InductiveInvariant
      <3> QED BY <3>a, <3>b DEF lb
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED BY PTL, <1>a, <1>b, <1>c, TypeInvariantHolds DEF Spec

DoneIndexValue == pc = "Done" => i = Len(f) + 1

THEOREM DoneIndexValueThm == Spec => []DoneIndexValue
PROOF
  <1>a. Init => DoneIndexValue
    BY DEF Init, DoneIndexValue
  <1>b. DoneIndexValue /\ UNCHANGED vars => DoneIndexValue'
    BY DEFS DoneIndexValue, vars
  <1>c. DoneIndexValue /\ TypeOK /\ Next => DoneIndexValue'
    <2>a. DoneIndexValue /\ Terminating => DoneIndexValue'
      BY DEFS DoneIndexValue, Terminating, vars
    <2>b. DoneIndexValue /\ TypeOK /\ lb => DoneIndexValue'
      <3> SUFFICES  ASSUME DoneIndexValue, TypeOK, lb
                    PROVE DoneIndexValue'
          OBVIOUS
      <3> USE DEFS DoneIndexValue, TypeOK, lb
      <3>a. CASE i <= Len(f)
        <4>a. pc' /= "Done" BY <3>a
        <4> QED BY <3>a, <4>a DEF lb
      <3>b. CASE ~(i <= Len(f))
        <4>b. i \in 1..(Len(f) + 1) BY DEF TypeOK
        <4>c. i = Len(f) + 1 BY <3>b, <4>b
        <4>d. UNCHANGED <<f, i>> BY <3>b
        <4>e. i' = Len(f') + 1 BY <4>c, <4>d
        <4>f. pc' = "Done" BY <3>b
        <4> QED BY <4>e, <4>f DEF DoneIndexValue
      <3> QED BY <3>a, <3>b DEF lb
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED BY PTL, <1>a, <1>b, <1>c, TypeInvariantHolds DEF Spec

Correctness ==
  pc = "Done" =>
    \A idx \in DOMAIN f : f[idx] <= h

THEOREM IndImpliesCorrectness == Spec => []Correctness
PROOF
  <1>a. Init => Correctness
    BY DEF Init, Correctness
  <1>b. Correctness /\ UNCHANGED vars => Correctness'
    BY DEF Correctness, vars
  <1>c. /\ Correctness
        /\ InductiveInvariant'
        /\ DoneIndexValue'
        /\ Next
        => Correctness'
    <2>a. Correctness /\ Terminating => Correctness'
      BY DEF Correctness, Terminating, vars
    <2>b.
        /\ Correctness
        /\ InductiveInvariant'
        /\ DoneIndexValue'
        /\ lb
        => Correctness'
      <3> SUFFICES ASSUME
            Correctness,
            InductiveInvariant',
            DoneIndexValue',
            lb
          PROVE
            Correctness'
          OBVIOUS
      <3>a. CASE i <= Len(f)
        <4>a. pc' /= "Done" BY <3>a DEF lb
        <4> QED BY <3>a, <4>a DEFS Correctness, lb
      <3>b. CASE ~(i <= Len(f))
        <4>a. pc' = "Done" BY <3>b DEF lb
        <4>b. i' = Len(f') + 1 BY <4>a DEF DoneIndexValue
        <4>c. DOMAIN f' = 1..Len(f') BY lb
        <4>d. DOMAIN f' = 1..(i' - 1) BY <4>b, <4>c
        <4>e. \A idx \in 1..(i' - 1) : f'[idx] <= h'
          BY DEF InductiveInvariant
        <4>f. \A idx \in DOMAIN f' : f'[idx] <= h'
          BY <4>d, <4>e
        <4> QED BY <4>f DEF Correctness
      <3> QED BY <3>a, <3>b, lb
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED
    BY
      <1>a, <1>b, <1>c,
      InductiveInvariantHolds, DoneIndexValueThm, PTL
    DEF Spec

=============================================================================

