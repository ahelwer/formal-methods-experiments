---- MODULE MIT_OCW_ToC_PSet1_1_7 ----
EXTENDS Naturals, Sequences, TLC

LOCAL ℕ ≜ Nat

VARIABLES w, q, i, acc

vars ≜ ⟨w, q, i, acc⟩

k ≜ 6
len ≜ 18

State ≜ SUBSET (1 ‥ k)
a ≜ "a"
b ≜ "b"
Alphabet ≜ {a, b}
Transition[current ∈ State, v ∈ Alphabet] ≜
  LET incremented ≜ {n + 1 : n ∈ {n ∈ current : n < k}} IN
  IF v = a THEN incremented ∪ {1}
  ELSE incremented

Input ≜ UNION {[1 ‥ strlen → Alphabet] : strlen ∈ 0 ‥ len} 

M ≜
  INSTANCE DFA WITH
    Q     ← State,
    Sigma ← Alphabet,
    q_0   ← {},
    delta ← Transition,
    F     ← {s ∈ State : k ∈ s}

HasAKFromEnd(input) ≜
  ∧ Len(input) ≥ k
  ∧ input[Len(input) - k + 1] = a

ASSUME M!IsValidDFA
Spec ≜
  ∧ ∃ input ∈ Input : M!Init[input]
  ∧ □[M!Next]_vars
  ∧ WF_vars(M!Next)
TypeInvariant ≜ M!TypeInvariant
Accepts ≜
  ∨ HasAKFromEnd(w) ∧ M!Accepts
  ∨ ¬HasAKFromEnd(w) ∧ ¬M!Accepts

InductiveInvariant ≜
  ∀ offset ∈ 1 ‥ k :
    LET idx ≜ i - offset IN
    (idx ∈ DOMAIN w ∧ w[idx] = a)
      ⇒ offset ∈ q

====

