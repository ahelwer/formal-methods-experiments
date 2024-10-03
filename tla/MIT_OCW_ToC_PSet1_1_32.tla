---- MODULE MIT_OCW_ToC_PSet1_1_32 ----
EXTENDS Naturals, Sequences, TLC

CONSTANT k

LOCAL ℕ ≜ Nat

VARIABLES w, q, i

vars ≜ ⟨w, q, i⟩

Start ≜ "start"
Accept ≜ "accept"
Carry ≜ "carry"
Fail ≜ "fail"
State ≜ {
  Start,
  Accept,
  Carry,
  Fail
}

Binary ≜ {0, 1}
BinaryVector ≜ Binary × Binary × Binary

Transition[current ∈ State, v ∈ BinaryVector] ≜
  CASE
    current ∈ {Start, Accept} → (
      CASE
        v = ⟨0, 0, 0⟩ → Accept
      □ v = ⟨0, 0, 1⟩ → Fail
      □ v = ⟨0, 1, 0⟩ → Fail
      □ v = ⟨0, 1, 1⟩ → Accept
      □ v = ⟨1, 0, 0⟩ → Fail
      □ v = ⟨1, 0, 1⟩ → Accept
      □ v = ⟨1, 1, 0⟩ → Carry
      □ v = ⟨1, 1, 1⟩ → Fail
    )
  □ current = Carry → (
      CASE
        v = ⟨0, 0, 0⟩ → Fail
      □ v = ⟨0, 0, 1⟩ → Accept
      □ v = ⟨0, 1, 0⟩ → Carry
      □ v = ⟨0, 1, 1⟩ → Fail
      □ v = ⟨1, 0, 0⟩ → Carry
      □ v = ⟨1, 0, 1⟩ → Fail
      □ v = ⟨1, 1, 0⟩ → Fail
      □ v = ⟨1, 1, 1⟩ → Carry
    )
  □ current = Fail → Fail

Input ≜ ⟨
  ⟨1, 1, 0⟩,
  ⟨0, 0, 1⟩,
  ⟨0, 0, 1⟩
⟩

BinaryToNat[input ∈ Seq(BinaryVector), exp ∈ ℕ] ≜
  IF input = ⟨⟩
  THEN ⟨0, 0, 0⟩
  ELSE LET
    v ≜ Head(input)
    t ≜ BinaryToNat[Tail(input), exp + 1]
  IN ⟨v[1] * exp + t[1], v[2] * exp + t[2], v[3] * exp + t[3]⟩

ASSUME BinaryToNat[⟨⟨0,0,0⟩,⟨0,0,0⟩⟩, 0] = ⟨0,0,0⟩

IsValidSum[input ∈ Seq(BinaryVector)] ≜
  LET values ≜ BinaryToNat[input, 0] IN
  values[1] + values[2] = values[3]

ASSUME IsValidSum[⟨⟨0,0,0⟩,⟨0,0,0⟩⟩]

M ≜
  INSTANCE DFA WITH
    Q     ← State,
    Sigma ← BinaryVector,
    q_0   ← Start,
    delta ← Transition,
    F     ← {Accept}

KSeq(S) ≜ [1 ‥ k → S]

ASSUME M!IsValidDFA
Spec ≜
  ∧ ∃ input ∈ KSeq(BinaryVector) : M!Init[input]
  ∧ □[M!Next]_vars
  ∧ WF_vars(M!Next)
TypeInvariant ≜ M!TypeInvariant
Accepts ≜ ∀ input ∈ KSeq(BinaryVector) : IsValidSum[input] ⇒ M!Accepts(Input)
AcceptsOnly ≜ ∀ input ∈ KSeq(BinaryVector) : M!Accepts(Input) ⇒ IsValidSum[input]

(*
THEOREM AcceptsOnlyValidSums ≜
  ∀ w ∈ Seq(BinaryVector) :
    (M(w) ⇒ M!Accepts) ⇔ (IsValidSum[w])

*)
====

