/- GID: D5/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap
   generality: G
   mirror-B: D5/B/S3/Quantum/RandomCircuits/HammingWeightPatternSpectralGap
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Connected gate patterns have a polynomial spectral gap at fixed Hamming weight. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

open scoped BigOperators
open Matrix Finset

namespace D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap

/-- The computational basis in the Hamming-weight sector. -/
abbrev config (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- A gate exchanges its two qubits, including on the sectors it fixes. -/
def swapConfig {n k : ℕ} (a b : Fin n) (s : config n k) : config n k :=
  ⟨s.val.map (Equiv.swap a b).toEmbedding, (Finset.card_map _).trans s.property⟩

/-- Squared RBS/FBS entries at angle π/4; the FBS signs disappear on squaring. -/
noncomputable def gateMatrix {n k : ℕ} (a b : Fin n) :
    Matrix (config n k) (config n k) ℝ :=
  fun s t => (if s = t then 1 / 2 else 0) +
    (if s = swapConfig a b t then 1 / 2 else 0)

/-- The first gate in the list acts first on a column vector. -/
noncomputable def patternMatrix {n k : ℕ} (pat : List (Fin n × Fin n)) :
    Matrix (config n k) (config n k) ℝ :=
  (pat.map fun e => gateMatrix e.1 e.2).reverse.prod

/-- The undirected qubit graph, with an edge in either orientation for each gate. -/
def qubitGraph {n : ℕ} (pat : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ ∃ e ∈ pat, e = (x, y) ∨ e = (y, x)
  symm := by
    rintro x y ⟨h, e, he, hxy | hyx⟩
    · exact ⟨h.symm, e, he, Or.inr hxy⟩
    · exact ⟨h.symm, e, he, Or.inl hyx⟩
  loopless := by simp

/-- The source's bidirectional strong connectivity, with distinct gate endpoints. -/
def connectedPattern {n : ℕ} (pat : List (Fin n × Fin n)) : Prop :=
  (∀ e ∈ pat, e.1 ≠ e.2) ∧ (qubitGraph pat).Connected

/-- Uniform polynomial lower bound for the gap on the sum-zero subspace. -/
def claim : Prop :=
  ∀ (k c a : ℕ), 1 ≤ k → ∀ pat : (n : ℕ) → List (Fin n × Fin n),
    (∀ n, 2 ≤ n → connectedPattern (pat n) ∧ (pat n).length ≤ c * n ^ a) →
    ∃ d : ℝ, 0 < d ∧ ∃ b : ℕ, ∀ n, k < n → 2 ≤ n →
    ∀ (μ : ℂ) (v : config n k → ℂ), v ≠ 0 → ∑ s, v s = 0 →
      (patternMatrix (pat n)).map (fun x : ℝ => (x : ℂ)) *ᵥ v = μ • v →
      ‖μ‖ ≤ 1 - d / (n : ℝ) ^ b

private lemma swapConfig_involutive {n k : ℕ} (a b : Fin n) :
    Function.Involutive (swapConfig (k := k) a b) := by
  sorry

private def swapEquiv {n k : ℕ} (a b : Fin n) : Equiv.Perm (config n k) :=
  (swapConfig_involutive (k := k) a b).toPerm

private def shuffle {ι : Type*} [Fintype ι] (s : Equiv.Perm ι)
    (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun x => v (s x))

private def average {ι : Type*} [Fintype ι] (s : Equiv.Perm ι)
    (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  (1 / 2 : ℂ) • (v + shuffle s v)

private def run {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (config n k)) : EuclideanSpace ℂ (config n k) :=
  pat.foldl (fun w e => average (swapEquiv e.1 e.2) w) v

private def staticEnergy {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (config n k)) : ℝ :=
  (pat.map fun e => ‖v - average (swapEquiv e.1 e.2) v‖ ^ 2).sum

private def configGraph {n k : ℕ} (pat : List (Fin n × Fin n)) :
    SimpleGraph (config n k) where
  Adj s t := s ≠ t ∧ ∃ e ∈ pat, swapConfig e.1 e.2 s = t
  symm := by
    rintro s t ⟨hne, e, he, h⟩
    exact ⟨hne.symm, e, he, h ▸ swapConfig_involutive e.1 e.2 s⟩
  loopless := by simp

private lemma config_card_le (n k : ℕ) : Fintype.card (config n k) ≤ n ^ k := by
  sorry

private lemma gate_apply {n k : ℕ} (a b : Fin n)
    (v : EuclideanSpace ℂ (config n k)) :
    (gateMatrix a b).map (fun x : ℝ => (x : ℂ)) *ᵥ WithLp.ofLp v =
      WithLp.ofLp (average (swapEquiv a b) v) := by
  sorry

private lemma pattern_apply {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (config n k)) :
    (patternMatrix pat).map (fun x : ℝ => (x : ℂ)) *ᵥ WithLp.ofLp v =
      WithLp.ofLp (run pat v) := by
  sorry

private lemma projection_energy {ι : Type*} [Fintype ι] (s : Equiv.Perm ι)
    (hs : Function.Involutive s) (v : EuclideanSpace ℂ ι) :
    ‖average s v‖ ^ 2 + ‖v - average s v‖ ^ 2 = ‖v‖ ^ 2 := by
  sorry

private lemma energy_control {n k : ℕ} (pat : List (Fin n × Fin n))
    (v : EuclideanSpace ℂ (config n k)) :
    staticEnergy pat v ≤ (pat.length : ℝ) ^ 2 * (‖v‖ ^ 2 - ‖run pat v‖ ^ 2) := by
  sorry

private lemma edge_energy {n k : ℕ} (a b : Fin n)
    (v : EuclideanSpace ℂ (config n k)) :
    ‖v - average (swapEquiv a b) v‖ ^ 2 =
      (1 / 4 : ℝ) * ∑ s, ‖v s - v (swapConfig a b s)‖ ^ 2 := by
  sorry

private lemma configuration_connected {n k : ℕ} (pat : List (Fin n × Fin n))
    (hc : connectedPattern pat) : (configGraph (k := k) pat).Preconnected := by
  sorry

private lemma poincare_bound {n k : ℕ} (pat : List (Fin n × Fin n))
    (hc : connectedPattern pat) (v : EuclideanSpace ℂ (config n k))
    (hv : ∑ s, v s = 0) :
    ‖v‖ ^ 2 ≤ (Fintype.card (config n k) : ℝ) ^ 2 * staticEnergy pat v := by
  sorry

private lemma pattern_length_pos {n : ℕ} (hn : 2 ≤ n)
    (pat : List (Fin n × Fin n)) (hc : connectedPattern pat) : 0 < pat.length := by
  sorry

private lemma spectral_core {n k : ℕ} (hn : 2 ≤ n) (pat : List (Fin n × Fin n))
    (hc : connectedPattern pat) (μ : ℂ) (v : config n k → ℂ) (hv : v ≠ 0)
    (hz : ∑ s, v s = 0)
    (he : (patternMatrix pat).map (fun x : ℝ => (x : ℂ)) *ᵥ v = μ • v) :
    ‖μ‖ ≤ 1 - 1 / (2 * (pat.length : ℝ) ^ 2 * (Fintype.card (config n k) : ℝ) ^ 2) := by
  sorry

private lemma polynomial_gap (k c a : ℕ) (pat : (n : ℕ) → List (Fin n × Fin n))
    (hp : ∀ n, 2 ≤ n → connectedPattern (pat n) ∧ (pat n).length ≤ c * n ^ a) :
    ∀ n, k < n → 2 ≤ n → ∀ (μ : ℂ) (v : config n k → ℂ), v ≠ 0 →
    ∑ s, v s = 0 →
    (patternMatrix (pat n)).map (fun x : ℝ => (x : ℂ)) *ᵥ v = μ • v →
    ‖μ‖ ≤ 1 - (1 / (2 * (max c 1 : ℕ) ^ 2 : ℝ)) /
      (n : ℝ) ^ (2 * a + 2 * k) := by
  sorry

/-- Connected patterns with polynomially many gates have an inverse-polynomial gap. -/
theorem result : claim := by
  intro k c a hk pat hp
  refine ⟨1 / (2 * (max c 1 : ℕ) ^ 2 : ℝ), by positivity, 2 * a + 2 * k, ?_⟩
  exact polynomial_gap k c a pat hp

end D5.S3.Quantum.RandomCircuits.HammingWeightPatternSpectralGap
