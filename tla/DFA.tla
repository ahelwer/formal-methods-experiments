------------------------------- MODULE DFA ----------------------------------
EXTENDS Naturals, Sequences, FiniteSets

LOCAL ℕ ≜ Nat

CONSTANTS
  Q,      \* The set of all DFA states
  Sigma,  \* The alphabet handled by the DFA
  q_0,    \* The start state
  delta,  \* The transition function
  F       \* The set of accepting states

ASSUME IsValidDFA ≜
  ∧ IsFiniteSet(Q)
  ∧ IsFiniteSet(Sigma)
  ∧ q_0 ∈ Q
  ∧ delta ∈ [Q × Sigma → Q]
  ∧ F ⊆ Q

VARIABLES w, q, i

vars ≜ ⟨w, q, i⟩

Init[input ∈ Seq(Sigma)] ≜
  ∧ w = input
  ∧ q = q_0
  ∧ i = 1

TypeInvariant ≜
  ∧ q ∈ Q
  ∧ i ∈ ℕ

Step ≜
  ∧ i ∈ DOMAIN w
  ∧ q' = delta[q, w[i]]
  ∧ i' = i + 1

Terminate ≜
  ∧ i ∉ DOMAIN w
  ∧ UNCHANGED ⟨q, i⟩

Next ≜
  ∧ ∨ Step
    ∨ Terminate
  ∧ UNCHANGED w

Accepts(input) ≜ (w = input) ⇒ ◇□(q ∈ F)

=============================================================================
