/- GID: D5/S0/Observation/ThreeReadBudget
   generality: G
   mirror-B: D5/B/S0/Observation/ThreeReadBudget
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The unbounded three-read budget forces quadratic nonnegativity and vanishing three-read observations. -/

import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Observation.ThreeReadBudget

noncomputable section

abbrev BilinearReading (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  LinearMap.BilinForm ℝ V

/-- The three-time aggregate `I + U + U²` from C133 Definition 2.1. -/
def threeReadSum {V : Type*} [AddCommGroup V] [Module ℝ V]
    (U : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  (LinearMap.id : V →ₗ[ℝ] V) + U + U.comp U

/-- The quadratic self-reading associated to a bilinear reading. -/
def threeReadQuadratic {V : Type*} [AddCommGroup V] [Module ℝ V]
    (R : BilinearReading V) (f : V) : ℝ :=
  R f f

/-- The vectors invisible in every first-slot comparison of `R`. -/
def threeReadNullspace {V : Type*} [AddCommGroup V] [Module ℝ V]
    (R : BilinearReading V) : Set V :=
  {h | ∀ f, R f h = 0}

/-- C133's budget, with the natural rewrite multiplier cast to the real scalars. -/
def ThreeReadBudget {V : Type*} [AddCommGroup V] [Module ℝ V]
    (R : BilinearReading V) (U : V →ₗ[ℝ] V) : Prop :=
  ∀ f g : V, ∀ n : ℕ,
    2 * R f (U g + (n : ℝ) • threeReadSum U g) ≤
      threeReadQuadratic R f + threeReadQuadratic R g

private theorem budget_expand {V : Type*} [AddCommGroup V] [Module ℝ V]
    (R : BilinearReading V) (U : V →ₗ[ℝ] V) (f g : V) (n : ℕ) :
    R f (U g + (n : ℝ) • threeReadSum U g) =
      R f (U g) + (n : ℝ) * R f (threeReadSum U g) := by
  simp only [map_add, map_smul, smul_eq_mul]

/-!
The source theorem's first necessity step is isolated here.  It keeps the full
arbitrary-module and arbitrary-bilinear-form hypotheses of C133; the later
symmetry, isometry, and quotient-complex clauses are separate results in the
source volume and are not silently folded into this statement.

proof_shape: content.
admission_basis: escape-witness.
budget_expand has proof_shape: bind-only and is consumed by
three_read_budget_nullspace on its affine-budget contradiction path.
escape_witness: the Archimedean unbounded-multiplier argument produces the new
nullspace conclusion; it is not an application or restatement of a frozen
declaration.
-/
theorem three_read_budget_nullspace
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (R : BilinearReading V) (U : V →ₗ[ℝ] V)
    (hbudget : ThreeReadBudget R U) :
    (∀ f, 0 ≤ threeReadQuadratic R f) ∧
      Set.range (threeReadSum U) ⊆ threeReadNullspace R := by
  constructor
  · intro f
    have h := hbudget f 0 0
    simpa [threeReadQuadratic, threeReadSum] using h
  · intro h hmem
    rcases hmem with ⟨g, rfl⟩
    change ∀ f, R f (threeReadSum U g) = 0
    intro f
    have hupper : ∀ f, R f (threeReadSum U g) ≤ 0 := by
      intro f
      by_contra hnot
      have hpos : 0 < R f (threeReadSum U g) := lt_of_not_ge hnot
      obtain ⟨n, hn⟩ := exists_nat_gt
        ((threeReadQuadratic R f + threeReadQuadratic R g -
            2 * R f (U g)) / (2 * R f (threeReadSum U g)))
      have hden : 0 < 2 * R f (threeReadSum U g) := by positivity
      have hmul := (div_lt_iff₀ hden).mp hn
      have hb := hbudget f g n
      rw [budget_expand] at hb
      nlinarith [hmul, hb]
    have hneg := hupper (-f)
    have hneg' : -R f (threeReadSum U g) ≤ 0 := by
      simpa only [map_neg, LinearMap.neg_apply] using hneg
    exact le_antisymm (hupper f) (by linarith)

#print axioms three_read_budget_nullspace

end

end D5.S0.Observation.ThreeReadBudget
