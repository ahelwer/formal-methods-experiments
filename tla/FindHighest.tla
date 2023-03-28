---------------------------- MODULE FindHighest -----------------------------
EXTENDS Sequences, Naturals, Integers, TLAPS

(****************************************************************************
--algorithm Highest {
  variables
    f \in Seq(Nat);
    h = -1;
    i = 1;
  define {
    max(a, b) == IF a > b THEN a ELSE b
  } {
lb: while (i <= Len(f)) {
      h := max(h, f[i]);
      i := i + 1;
    }
  }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "c908a386" /\ chksum(tla) = "36657a9f")
VARIABLES f, h, i, pc

(* define statement *)
max(a, b) == IF a > b THEN a ELSE b


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
  /\ h \in Nat \cup {-1}

Correctness ==
  pc = "Done" =>
    \A idx \in DOMAIN f : f[idx] <= h

THEOREM Spec => []TypeOK
PROOF
  <1>a. Init => TypeOK
    BY DEFS Init, TypeOK
  <1>b. TypeOK /\ UNCHANGED vars => TypeOK'
    BY DEFS TypeOK, vars
  <1>c. TypeOK /\ Next => TypeOK'
    <2>a. TypeOK /\ lb => TypeOK'
      <3> SUFFICES  ASSUME TypeOK, lb
                    PROVE TypeOK'
      <3>a. CASE i <= Len(f)
        BY DEF TypeOK, lb, max
      <3>b. CASE ~(i <= Len(f))
        <4>a. i = Len(f) + 1
          <5>a. i \in 1..(Len(f) + 1) /\ i > Len(f) => i = Len(f) + 1
            PROOF OBVIOUS
          <5>b. i \in 1..(Len(f) + 1) BY DEF TypeOK
          <5>c. i > Len(f)
            <6>a. ~(i <= Len(f)) <=> i > Len(f)
              <7>a. Len(f) \in Nat
              <7>b. i \in Nat BY DEF TypeOK
              <7> QED BY <7>a, <7>b
            <6>b. ~(i <= Len(f)) BY <3>b
            <6> QED BY <6>a, <6>b
          <5>d i = Len(f) + 1 BY <5>a, <5>b, <5>c
          <5> QED BY <5>d
        <4>b. UNCHANGED i
          <5>a ~(i <= Len(f)) /\ lb => UNCHANGED i
            BY DEF lb
          <5> QED BY <3>b, <5>a DEF lb
        <4> QED BY <4>a, <4>b DEFS TypeOK, lb
      <3> QED BY <3>a, <3>b DEFS TypeOK, lb
    <2>b. TypeOK /\ Terminating => TypeOK'
      BY DEFS TypeOK, Terminating, vars
    <2> QED BY <2>a, <2>b DEF Next
  <1> QED BY PTL, <1>a, <1>b, <1>c DEF Spec
=============================================================================

