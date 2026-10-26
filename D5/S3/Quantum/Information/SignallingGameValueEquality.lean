/- GID: D5/S3/Quantum/Information/SignallingGameValueEquality
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SignallingGameValueEquality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The signalling game has classical, quantum and no-signalling value 1/max(m,n). -/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Weil.ZetaLinear.RankTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.SignallingGameValueEquality

open Finset Matrix
open scoped BigOperators Kronecker ComplexOrder
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

/-- Nonnegative normalized conditional probabilities with both no-signalling marginals.
The argument order is Alice's answer, Bob's answer, Alice's question, Bob's question. -/
def IsNoSignalling {m n : ℕ} (p : Fin n → Fin m → Fin m → Fin n → ℝ) : Prop :=
  (∀ a b x y, 0 ≤ p a b x y) ∧
  (∀ x y, ∑ a, ∑ b, p a b x y = 1) ∧
  (∀ a x y z, ∑ b, p a b x y = ∑ b, p a b x z) ∧
  (∀ b x z y, ∑ a, p a b x y = ∑ a, p a b z y)

/-- Uniform questions; each player must answer the other player's question. -/
def winProb {m n : ℕ} (p : Fin n → Fin m → Fin m → Fin n → ℝ) : ℝ :=
  (1 / ((m : ℝ) * n)) * ∑ x, ∑ y, p y x x y

/-- The product of the two deterministic local response distributions. -/
def deterministicBox {m n : ℕ} (fa : Fin m → Fin n) (fb : Fin n → Fin m)
    (a : Fin n) (b : Fin m) (x : Fin m) (y : Fin n) : ℝ :=
  (if a = fa x then 1 else 0) * (if b = fb y then 1 else 0)

/-- All winning probabilities of deterministic classical strategies. -/
def classicalValues (m n : ℕ) : Set ℝ :=
  {v | ∃ (fa : Fin m → Fin n) (fb : Fin n → Fin m),
    winProb (deterministicBox fa fb) = v}

/-- A finite bipartite density matrix and a local POVM for each local question. -/
def IsQuantumStrategy {m n da db : ℕ}
    (rho : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin m → Fin n → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin n → Fin m → Matrix (Fin db) (Fin db) ℂ) : Prop :=
  rho.PosSemidef ∧ trace rho = 1 ∧ (∀ x, IsPOVM (a x)) ∧ (∀ y, IsPOVM (b y))

/-- Born's rule for local measurements of a shared bipartite state. -/
def quantumBox {m n da db : ℕ}
    (rho : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin m → Fin n → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin n → Fin m → Matrix (Fin db) (Fin db) ℂ)
    (u : Fin n) (v : Fin m) (x : Fin m) (y : Fin n) : ℝ :=
  (trace (rho * (a x u ⊗ₖ b y v))).re

/-- All winning probabilities over all finite local dimensions, states and local POVMs. -/
def quantumValues (m n : ℕ) : Set ℝ :=
  {v | ∃ (da db : ℕ) (rho : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin m → Fin n → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin n → Fin m → Matrix (Fin db) (Fin db) ℂ),
    IsQuantumStrategy rho a b ∧ winProb (quantumBox rho a b) = v}

/-- All winning probabilities of normalized no-signalling boxes. -/
def noSignallingValues (m n : ℕ) : Set ℝ :=
  {v | ∃ p : Fin n → Fin m → Fin m → Fin n → ℝ,
    IsNoSignalling p ∧ winProb p = v}

/-- For every pair of nonempty question sets all three greatest values equal `1/max(m,n)`. -/
def claim : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    IsGreatest (noSignallingValues m n) (1 / (max m n : ℝ)) ∧
    IsGreatest (quantumValues m n) (1 / (max m n : ℝ)) ∧
    IsGreatest (classicalValues m n) (1 / (max m n : ℝ))

private lemma noSignalling_bound {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {p : Fin n → Fin m → Fin m → Fin n → ℝ} (hp : IsNoSignalling p) :
    winProb p ≤ 1 / (max m n : ℝ) := by
  sorry

private lemma quantum_noSignalling {m n da db : ℕ}
    (rho : Matrix (Fin da × Fin db) (Fin da × Fin db) ℂ)
    (a : Fin m → Fin n → Matrix (Fin da) (Fin da) ℂ)
    (b : Fin n → Fin m → Matrix (Fin db) (Fin db) ℂ)
    (hs : IsQuantumStrategy rho a b) : IsNoSignalling (quantumBox rho a b) := by
  sorry

private lemma deterministic_quantum {m n : ℕ} (fa : Fin m → Fin n) (fb : Fin n → Fin m) :
    ∃ (rho : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)
      (a : Fin m → Fin n → Matrix (Fin 1) (Fin 1) ℂ)
      (b : Fin n → Fin m → Matrix (Fin 1) (Fin 1) ℂ),
      IsQuantumStrategy rho a b ∧ quantumBox rho a b = deterministicBox fa fb := by
  sorry

private lemma optimal_deterministic {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ (fa : Fin m → Fin n) (fb : Fin n → Fin m),
      winProb (deterministicBox fa fb) = 1 / (max m n : ℝ) := by
  sorry

/-- The uniform signalling game has the same sharp value in all three strategy classes. -/
theorem result : claim := by
  intro m n hm hn
  obtain ⟨fa, fb, hv⟩ := optimal_deterministic hm hn
  obtain ⟨rho, a, b, hs, he⟩ := deterministic_quantum fa fb
  have hp := quantum_noSignalling rho a b hs
  have hq : winProb (quantumBox rho a b) = 1 / (max m n : ℝ) := by rw [he, hv]
  refine ⟨⟨⟨_, hp, hq⟩, ?_⟩, ⟨⟨1, 1, rho, a, b, hs, hq⟩, ?_⟩,
    ⟨⟨fa, fb, hv⟩, ?_⟩⟩
  · rintro v ⟨p, hp, rfl⟩
    exact noSignalling_bound hm hn hp
  · rintro v ⟨da, db, rho, a, b, hs, rfl⟩
    exact noSignalling_bound hm hn (quantum_noSignalling rho a b hs)
  · rintro v ⟨fa, fb, rfl⟩
    obtain ⟨rho, a, b, hs, he⟩ := deterministic_quantum fa fb
    rw [← he]
    exact noSignalling_bound hm hn (quantum_noSignalling rho a b hs)

end D5.S3.Quantum.Information.SignallingGameValueEquality
