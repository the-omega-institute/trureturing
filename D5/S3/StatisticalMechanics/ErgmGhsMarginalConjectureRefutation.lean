/- GID: D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.claim; result=D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.result; claim=D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.claim
   digest: An edge-triangle Gibbs law has marginals above one half and positive third cumulant. -/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The homomorphism-density Hamiltonian and GHS condition are those of
Bianchi, Collet and Magnanini, arXiv:2107.08889v2, Sections 2.1, 3 and 4.
The counterexample concerns the conjecture in the final paragraph of Section 4.
Preregistration: https://github.com/the-omega-institute/trureturing/issues/22390
Admission basis: open-problem-resolution. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation

open scoped BigOperators

/-- The fraction of vertex maps that preserve adjacency. -/
def homDensity {m n : ℕ} (h : SimpleGraph (Fin m)) (g : SimpleGraph (Fin n)) : ℝ :=
  (Nat.card (h →g g) : ℝ) / (n : ℝ) ^ m

/-- The homomorphism-density Hamiltonian for an arbitrary finite graph family. -/
def hamiltonian {n k : ℕ} (h : Fin k → Σ m, SimpleGraph (Fin m))
    (β : Fin k → ℝ) (g : SimpleGraph (Fin n)) : ℝ :=
  (n : ℝ) ^ 2 * ∑ j, β j * homDensity (h j).2 g

/-- The Gibbs probability of a labeled graph, normalized over all simple graphs. -/
def gibbsWeight {n k : ℕ} (h : Fin k → Σ m, SimpleGraph (Fin m))
    (β : Fin k → ℝ) (g : SimpleGraph (Fin n)) : ℝ :=
  Real.exp (hamiltonian h β g) / ∑ g : SimpleGraph (Fin n), Real.exp (hamiltonian h β g)

/-- Expectation under the graph Gibbs law. -/
def expectation {n k : ℕ} (h : Fin k → Σ m, SimpleGraph (Fin m))
    (β : Fin k → ℝ) (f : SimpleGraph (Fin n) → ℝ) : ℝ :=
  ∑ g, gibbsWeight h β g * f g

/-- The indicator of an edge of the complete labeled graph. -/
def edgeIndicator {n : ℕ} (e : (⊤ : SimpleGraph (Fin n)).edgeSet)
    (g : SimpleGraph (Fin n)) : ℝ := by
  classical
  exact if e.val ∈ g.edgeSet then 1 else 0

/-- The third Ursell function, including triples with repeated edges. -/
def u3 {n k : ℕ} (h : Fin k → Σ m, SimpleGraph (Fin m)) (β : Fin k → ℝ)
    (e f g : (⊤ : SimpleGraph (Fin n)).edgeSet) : ℝ :=
  expectation h β (fun a => edgeIndicator e a * edgeIndicator f a * edgeIndicator g a) -
  expectation h β (edgeIndicator e) *
    expectation h β (fun a => edgeIndicator f a * edgeIndicator g a) -
  expectation h β (edgeIndicator f) *
    expectation h β (fun a => edgeIndicator e a * edgeIndicator g a) -
  expectation h β (edgeIndicator g) *
    expectation h β (fun a => edgeIndicator e a * edgeIndicator f a) +
  2 * expectation h β (edgeIndicator e) * expectation h β (edgeIndicator f) *
    expectation h β (edgeIndicator g)

/-- The marginal criterion conjectured for general exponential random graphs.
`Fin (k + 1)` indexes every nonempty finite family, with its first graph an edge. -/
def claim : Prop :=
  ∀ (n k : ℕ) (h : Fin (k + 1) → Σ m, SimpleGraph (Fin m)) (β : Fin (k + 1) → ℝ),
    h 0 = ⟨2, (⊤ : SimpleGraph (Fin 2))⟩ →
    (∀ j, j ≠ 0 → 0 ≤ β j) →
    ((∀ e : (⊤ : SimpleGraph (Fin n)).edgeSet,
      (1 / 2 : ℝ) ≤ expectation h β (edgeIndicator e)) ↔
     ∀ e f g : (⊤ : SimpleGraph (Fin n)).edgeSet, u3 h β e f g ≤ 0)

private def models : Fin 2 → Σ m, SimpleGraph (Fin m) :=
  ![⟨2, ⊤⟩, ⟨3, ⊤⟩]

private def parameters : Fin 2 → ℝ := ![0, Real.log 2 / 2]

private def edge01 : (⊤ : SimpleGraph (Fin 3)).edgeSet := ⟨s(0, 1), by decide⟩
private def edge02 : (⊤ : SimpleGraph (Fin 3)).edgeSet := ⟨s(0, 2), by decide⟩
private def edge12 : (⊤ : SimpleGraph (Fin 3)).edgeSet := ⟨s(1, 2), by decide⟩

private lemma triangle_count (g : SimpleGraph (Fin 3)) :
    Nat.card ((⊤ : SimpleGraph (Fin 3)) →g g) = if g = ⊤ then 6 else 0 := by
  sorry

private lemma hamiltonian_value (g : SimpleGraph (Fin 3)) :
    hamiltonian models parameters g = if g = ⊤ then Real.log 2 else 0 := by
  sorry

private lemma weight_value (g : SimpleGraph (Fin 3)) :
    gibbsWeight models parameters g = if g = ⊤ then 2 / 9 else 1 / 9 := by
  sorry

private lemma marginal_value (e : (⊤ : SimpleGraph (Fin 3)).edgeSet) :
    expectation models parameters (edgeIndicator e) = 5 / 9 := by
  sorry

private lemma joint_values :
    expectation models parameters (fun a => edgeIndicator edge01 a * edgeIndicator edge02 a) =
      1 / 3 ∧
    expectation models parameters (fun a => edgeIndicator edge01 a * edgeIndicator edge12 a) =
      1 / 3 ∧
    expectation models parameters (fun a => edgeIndicator edge02 a * edgeIndicator edge12 a) =
      1 / 3 ∧
    expectation models parameters (fun a =>
      edgeIndicator edge01 a * edgeIndicator edge02 a * edgeIndicator edge12 a) = 2 / 9 := by
  sorry

private lemma ursell_value : u3 models parameters edge01 edge02 edge12 = 7 / 729 := by
  rw [u3, marginal_value, marginal_value, marginal_value,
    joint_values.1, joint_values.2.1, joint_values.2.2.1, joint_values.2.2.2]
  norm_num

/-- All three edge marginals exceed one half, but their third Ursell function is positive. -/
theorem result : ¬ claim := by
  intro h
  have hβ : ∀ j : Fin 2, j ≠ 0 → 0 ≤ parameters j := by
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  have hm : ∀ e : (⊤ : SimpleGraph (Fin 3)).edgeSet,
      (1 / 2 : ℝ) ≤ expectation models parameters (edgeIndicator e) := by
    intro e
    rw [marginal_value]
    norm_num
  have hu := (h 3 1 models parameters rfl hβ).mp hm edge01 edge02 edge12
  rw [ursell_value] at hu
  norm_num at hu

end D5.S3.StatisticalMechanics.ErgmGhsMarginalConjectureRefutation
