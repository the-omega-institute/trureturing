/- GID: D5/S3/ConceptDynamics/Coding/InertGroupBlockConjugacy
   generality: G
   utility: original fixed-block conjugacy from actual dimension-group inertness
   digest: Inertness supplies the exact least-positive thresholds and rational cutoff, and every admissible exponent feeds the unchanged equal-power construction with derived positivity and natural power equality.
-/
import D5.S3.ConceptDynamics.Coding.FreeExpansionDimensionGroup
import D5.S3.ConceptDynamics.Coding.FixedBlockRigidity
import D5.S3.FiniteGroups.RationalGroupMatrixCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity
open D5.S3.ConceptDynamics.Coding.FreeExpansionDimensionGroup (Inert inert_iff_uniformizes)
open D5.S3.FiniteGroups.NaturalGroupMatrixUniformization
open D5.S3.FiniteGroups.RationalGroupAlgebraSplitting (RationalDecomposition)
open D5.S3.FiniteGroups.RationalGroupMatrixCutoff

namespace D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy

variable {H : Type*} [Group H] [Fintype H] {n : ℕ}
variable [TopologicalSpace H] [DiscreteTopology H]

/-- The exact original construction at one exponent. Positivity and equality
of natural powers are outputs. Both rational expressions use the same actual
augmentation matrix. The final four clauses name the unchanged constructor. -/
def AtExponent (A B : GroupMat H n n) (k : ℕ) : Prop :=
  ∃ hk : 0 < k, ∃ hpower : A^k = B^k,
    (rationalMatrix (A^k) = fun i j => (((matrixAugmentation A)^k) i j : ℚ) •
      D5.S3.FiniteGroups.RationalGroupAlgebraSplitting.average H) ∧
    (rationalMatrix (B^k) = fun i j => (((matrixAugmentation A)^k) i j : ℚ) •
      D5.S3.FiniteGroups.RationalGroupAlgebraSplitting.average H) ∧
    (∀ x, original181History A B hk
      (fiber_counts_of_equal_power A B hk hpower) x =
      equalPowerHomeomorph A B hk hpower x) ∧
    (∀ a x, equalPowerHomeomorph A B hk hpower (groupHistory A a x) =
      groupHistory B a (equalPowerHomeomorph A B hk hpower x)) ∧
    (∀ x, equalPowerHomeomorph A B hk hpower
      ((shift (expandedGraph A))^[k] x) =
      (shift (expandedGraph B))^[k]
        (equalPowerHomeomorph A B hk hpower x)) ∧
    ((∀ x, equalPowerHomeomorph A B hk hpower (shift (expandedGraph A) x) =
      shift (expandedGraph B) (equalPowerHomeomorph A B hk hpower x)) → A = B)

private theorem atExponent_of_tau_le (A B : GroupMat H n n)
    (hA : Essential (baseGraph A)) (hB : Essential (baseGraph B))
    (haug : matrixAugmentation A = matrixAugmentation B) {k : ℕ}
    (hkTau : max (tau A) (tau B) ≤ (k : WithTop ℕ)) : AtExponent A B k := by
  obtain ⟨hk,hpower⟩ := equal_power_of_tau_le A B haug hkTau
  have huniform := ((tau_le_iff_uniform_power A k).mp
    ((le_max_left _ _).trans hkTau)).2
  have hrat : rationalMatrix (A^k) = fun i j =>
      (((matrixAugmentation A)^k) i j : ℚ) •
        D5.S3.FiniteGroups.RationalGroupAlgebraSplitting.average H := by
    simpa only [map_pow] using uniform_rational_expression (A^k) huniform
  refine ⟨hk,hpower,hrat,?_,?_⟩
  · rw [← hpower]
    exact hrat
  · exact equalPower_attachment A B hA hB hk hpower

/-- The full original threshold theorem. Inertness concerns the actual
stationary dimension group. Every rational decomposition retains its own
nontrivial matrix orders; no replacement degree or cutoff is assumed.
The same fixed alignment is constructed separately for each admissible k. -/
theorem original18_1 (A B : GroupMat H n n)
    (hA : Essential (baseGraph A)) (hB : Essential (baseGraph B))
    (hInertA : Inert A) (hInertB : Inert B)
    (haug : matrixAugmentation A = matrixAugmentation B) :
    (Subsingleton H → tau A = 1 ∧ tau B = 1 ∧ A = B) ∧
    (∀ W : RationalDecomposition H, 0 < n →
      max (tau A) (tau B) ≤ (n*bH W : WithTop ℕ)) ∧
    (∀ k : ℕ, max (tau A) (tau B) ≤ (k : WithTop ℕ) → AtExponent A B k) := by
  have huniformA := (inert_iff_uniformizes A).mp hInertA
  have huniformB := (inert_iff_uniformizes B).mp hInertB
  refine ⟨?_,?_,?_⟩
  · intro hH
    letI : Subsingleton H := hH
    have huA : UniformMatrix A := by
      intro i j g
      rw [Subsingleton.elim g 1]
    have huB : UniformMatrix B := by
      intro i j g
      rw [Subsingleton.elim g 1]
    have htA := (tau_eq_one_iff_uniform A).mpr huA
    have htB := (tau_eq_one_iff_uniform B).mpr huB
    refine ⟨htA,htB,?_⟩
    have hp := (equal_power_of_tau_le A B haug (k := 1) (by simp [htA,htB])).2
    simpa only [pow_one] using hp
  · intro W hn
    exact max_le (tau_le_cutoff W hn A huniformA) (tau_le_cutoff W hn B huniformB)
  · intro k hkTau
    exact atExponent_of_tau_le A B hA hB haug hkTau

end D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy
