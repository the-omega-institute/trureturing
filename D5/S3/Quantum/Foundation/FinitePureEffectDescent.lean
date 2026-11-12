/- GID: D5/S3/Quantum/Foundation/FinitePureEffectDescent
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FinitePureEffectDescent
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Full finite pure relations characterize original proper effects. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! Finite pure coordinates and descent to the entire original proper interval. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.FinitePureEffectDescent

open CircuitBalancedConfirmation

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A]

/-- The coordinate map uses every extreme point of the original normalized base. -/
def coordinates (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) [Fintype (pure C u)] :
    (pure C u → ℝ) →ₗ[ℝ] A :=
  Fintype.linearCombination ℝ (fun p : pure C u => (p : A))

/-- Original midpoint gluing of actual proper-effect exclusions, for all mixed states. -/
def zeroGluing (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ) : Prop :=
  ∀ (p : pure C u) (x y : A), x ∈ base C u → y ∈ base C u →
    (∃ f, confirms C u p f ∧ f x = 0) →
    (∃ f, confirms C u p f ∧ f y = 0) →
    ∃ f, confirms C u p f ∧ f ((1 / 2 : ℝ) • (x + y)) = 0

private theorem extension_sum {I M : Type*} [Fintype I] [DecidableEq I] [AddCommMonoid M]
    [Module ℝ M] (s : Finset I) (c : s → ℝ) (f : I → M) :
    (∑ q, (if h : q ∈ s then c ⟨q,h⟩ else 0) • f q) =
      ∑ q : s, c q • f q := by
  classical
  calc
    _ = ∑ q ∈ s, (if h : q ∈ s then c ⟨q,h⟩ else 0) • f q := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro q _ hq
      simp [hq]
    _ = ∑ q : s, (if h : (q : I) ∈ s then c ⟨q,h⟩ else 0) • f q :=
      (Finset.sum_coe_sort s _).symm
    _ = _ := Finset.sum_congr rfl (fun q _ => by rw [dif_pos q.property])

/-- Original closedness, strict normalization and generation imply surjectivity;
finite pure spanning is a conclusion. -/
theorem coordinates_surjective (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    [Fintype (pure C u)] (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) :
    Function.Surjective (coordinates C u) := by
  apply LinearMap.range_eq_top.mp
  simpa [coordinates, Fintype.range_linearCombination, Subtype.range_coe_subtype] using
    pure_span (base_compact hclosed hstrict) hstrict hspan

/-- Every full-kernel-annihilating assignment in the unit cube descends to an
original proper effect, and every original proper effect has these properties. -/
theorem full_effect_iff (C : PointedCone ℝ A) (u : A →ₗ[ℝ] ℝ)
    [Fintype (pure C u)] (hclosed : IsClosed (C : Set A))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set A) = ⊤) (v : pure C u → ℝ) :
    (∃! f : A →ₗ[ℝ] ℝ, proper C u f ∧ ∀ p : pure C u, f p = v p) ↔
      (∀ p, 0 ≤ v p ∧ v p ≤ 1) ∧
      (∀ w, coordinates C u w = 0 → ∑ p, w p * v p = 0) := by
  classical
  constructor
  · rintro ⟨f, ⟨hf, he⟩, _⟩
    refine ⟨fun p => ?_, fun w hw => ?_⟩
    · simpa [he p, (pure_mem p).2] using hf p (pure_mem p).1
    · have hh := congrArg f hw
      simpa [coordinates, Fintype.linearCombination_apply, map_sum, map_smul,
        smul_eq_mul, he] using hh
  · rintro ⟨hbound, hker⟩
    have hbal : balanced (pure C u) v := by
      intro s c hc
      let w : pure C u → ℝ := fun q => if h : q ∈ s then c ⟨q,h⟩ else 0
      have hw : coordinates C u w = 0 := by
        change (∑ q, w q • (q : A)) = 0
        rw [show (∑ q, w q • (q : A)) = ∑ q : s, c q • (q.1 : A) from
          extension_sum s c (fun q : pure C u => (q : A))]
        exact hc.2.1
      have hh := hker w hw
      have hE := extension_sum s c v
      change (∑ q, w q * v q) = ∑ q : s, c q * v q.1 at hE
      rw [hE] at hh
      exact hh
    obtain ⟨f, hf⟩ := descends hbal (pure_span (base_compact hclosed hstrict) hstrict hspan)
    refine ⟨f, ⟨cone_bound (base_compact hclosed hstrict) hstrict ?_, hf⟩, ?_⟩
    · intro p
      rw [hf]
      exact hbound p
    · intro g hg
      apply LinearMap.ext
      intro x
      obtain ⟨w,rfl⟩ := coordinates_surjective C u hclosed hstrict hspan x
      simp only [coordinates, Fintype.linearCombination_apply, map_sum, map_smul,
        smul_eq_mul, hf, hg.2]

omit [FiniteDimensional ℝ A] in
/-- Applying the original unit detects the affine normalization of every relation. -/
theorem relation_sum_zero {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    [Fintype (pure C u)] (w : pure C u → ℝ) (hw : coordinates C u w = 0) :
    ∑ p, w p = 0 := by
  have hh := congrArg u hw
  simpa [coordinates, Fintype.linearCombination_apply, map_sum, map_smul,
    (pure_mem _).2] using hh

omit [FiniteDimensional ℝ A] in
/-- A lower bound witnessed by an original confirmer is the attained original
comparison, for any original state, including mixed barycenters. -/
theorem attained_comparison {C : PointedCone ℝ A} {u : A →ₗ[ℝ] ℝ}
    {p x : A} (hx : x ∈ C) (f : A →ₗ[ℝ] ℝ) (hf : confirms C u p f)
    (hlower : ∀ g, confirms C u p g → f x ≤ g x) :
    comparison C u p x = f x := by
  apply le_antisymm
  · exact csInf_le ⟨0, by rintro r ⟨g,hg,rfl⟩; exact (hg.1 x hx).1⟩ ⟨f,hf,rfl⟩
  · exact le_csInf ⟨f x,f,hf,rfl⟩ (by rintro r ⟨g,hg,rfl⟩; exact hlower g hg)

end D5.S3.Quantum.Foundation.FinitePureEffectDescent
