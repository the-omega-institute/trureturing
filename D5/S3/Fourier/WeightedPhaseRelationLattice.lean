/- GID: D5/S3/Fourier/WeightedPhaseRelationLattice
   generality: G
   mirror-B: D5/B/S3/Fourier/WeightedPhaseRelationLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Fourier/TorusOrbitClosure]
   utility: none
   digest: The complete integer relation lattice controls weighted common-time phase deficit. -/

import D5.S3.Fourier.TorusOrbitClosure
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The real-time phase orbit closure is the annihilator of its integer relations. -/

open Set
open Matrix
open scoped BigOperators Matrix

namespace D5.S3.Fourier.WeightedPhaseRelationLattice

private theorem exists_nonresonant_step {J : Type*} [Fintype J] (γ : J → ℝ) :
    ∃ s ∈ Ioo (0 : ℝ) 1, ∀ (k : J → ℤ) (m : ℤ),
      (∑ j, (k j : ℝ) * γ j) * s = (m : ℝ) * (2 * Real.pi) →
        (∑ j, (k j : ℝ) * γ j) = 0 := by
  let dot (k : J → ℤ) : ℝ := ∑ j, (k j : ℝ) * γ j
  let bad : (J → ℤ) × ℤ → ℝ := fun p => (p.2 : ℝ) * (2 * Real.pi) / dot p.1
  have hcount : (range bad).Countable := countable_range bad
  have hnot : ¬ Ioo (0 : ℝ) 1 ⊆ range bad := by
    intro hsub
    exact (not_le_of_gt zero_lt_one) (Cardinal.Real.Ioo_countable_iff.mp (hcount.mono hsub))
  obtain ⟨s, hs, hgood⟩ := not_subset.mp hnot
  refine ⟨s, hs, fun k m h => ?_⟩
  by_contra hne
  apply hgood
  refine ⟨(k, m), ?_⟩
  change (m : ℝ) * (2 * Real.pi) / dot k = s
  exact (div_eq_iff hne).2 (by simpa [dot, mul_comm s] using h.symm)

private theorem circle_character_exp {J : Type*} [Fintype J] (k : J → ℤ) (θ : J → ℝ) :
    (∏ j, Circle.exp (θ j) ^ k j) = Circle.exp (∑ j, (k j : ℝ) * θ j) := by
  simp_rw [← Circle.exp_intCast_mul]
  exact (map_sum Circle.expHom _ _).symm

private theorem mem_closure_real_phase_orbit {J : Type*} [Fintype J]
    (γ : J → ℝ) (z : J → Circle) :
    z ∈ closure (range (fun (t : ℝ) (j : J) => Circle.exp (γ j * t))) ↔
      ∀ k : J → ℤ, (∑ j, (k j : ℝ) * γ j) = 0 → (∏ j, z j ^ k j) = 1 := by
  let orbit (t : ℝ) (j : J) := Circle.exp (γ j * t)
  change z ∈ closure (range orbit) ↔ _
  have hchar (k : J → ℤ) (t : ℝ) :
      (∏ j, orbit t j ^ k j) = Circle.exp ((∑ j, (k j : ℝ) * γ j) * t) := by
    simp only [orbit, circle_character_exp, ← mul_assoc, ← Finset.sum_mul]
  constructor
  · intro hz k hk
    have hc : Continuous (fun w : J → Circle => ∏ j, w j ^ k j) := by
      exact continuous_finsetProd _ fun j _ => (continuous_apply j).zpow (k j)
    apply closure_minimal (t := {w | (∏ j, w j ^ k j) = 1}) ?_
      (isClosed_eq hc continuous_const) hz
    rintro _ ⟨t, rfl⟩
    change (∏ j, orbit t j ^ k j) = 1
    rw [hchar, hk, zero_mul, Circle.exp_zero]
  · intro hz
    obtain ⟨s, _, hs⟩ := exists_nonresonant_step γ
    have hd : z ∈ closure (range (fun n : ℕ => orbit s ^ n)) := by
      apply (D5.S3.Fourier.TorusOrbitClosure.result (orbit s) z).2
      intro k hk
      rw [hchar] at hk
      obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hk
      exact hz k (hs k m hm)
    refine closure_mono ?_ hd
    rintro _ ⟨n, rfl⟩
    refine ⟨(n : ℝ) * s, ?_⟩
    funext j
    change Circle.exp (γ j * ((n : ℝ) * s)) = Circle.exp (γ j * s) ^ n
    rw [mul_left_comm, Circle.exp_natCast_mul]

/-- The real-time orbit closure is the common kernel of exactly the zero-dot-product
integer characters. -/
theorem closure_real_phase_orbit {J : Type*} [Fintype J] (γ : J → ℝ) :
    closure (range (fun (t : ℝ) (j : J) => Circle.exp (γ j * t))) =
      {p | ∀ k : J → ℤ, (∑ j, (k j : ℝ) * γ j) = 0 → (∏ j, p j ^ k j) = 1} := by
  ext p
  exact mem_closure_real_phase_orbit γ p

/-- For every real lift centered at the sine-maximizing phase, membership in the
continuous orbit closure is equivalent to the affine congruences for the complete
integer relation rows. -/
theorem centered_lift_iff {J A : Type*} [Fintype J] [Finite A]
    (γ : J → ℝ) (K : Matrix A J ℤ)
    (hK : ∀ k : J → ℤ, k ∈ Submodule.span ℤ (range K.row) ↔
      (∑ j, (k j : ℝ) * γ j) = 0) (x : J → ℝ) :
    (fun j => Circle.exp (x j + Real.pi / 2)) ∈
      closure (range (fun (t : ℝ) (j : J) => Circle.exp (γ j * t))) ↔
    ∃ z : A → ℤ, (K.map (Int.cast : ℤ → ℝ)) *ᵥ x =
      fun a => (z a : ℝ) * (2 * Real.pi) -
        (Real.pi / 2) * ((K.map (Int.cast : ℤ → ℝ)) *ᵥ (1 : J → ℝ)) a := by
  classical
  let := Fintype.ofFinite A
  let R := K.map (Int.cast : ℤ → ℝ)
  let θ : J → ℝ := fun j => x j + Real.pi / 2
  have hshift (a : A) : (R *ᵥ θ) a = (R *ᵥ x) a + (Real.pi / 2) * (R *ᵥ 1) a := by
    simp only [Matrix.mulVec, dotProduct, θ, Pi.one_apply, mul_one, mul_add, Finset.sum_add_distrib,
      Finset.sum_mul, mul_comm (Real.pi / 2)]
  rw [closure_real_phase_orbit]
  change (∀ k : J → ℤ, (∑ j, (k j : ℝ) * γ j) = 0 →
      (∏ j, Circle.exp (θ j) ^ k j) = 1) ↔ _
  constructor
  · intro h
    have hr (a : A) : ∃ m : ℤ, (R *ᵥ θ) a = (m : ℝ) * (2 * Real.pi) := by
      apply Circle.exp_eq_one.mp
      change Circle.exp (∑ j, ((K.row a j : ℤ) : ℝ) * θ j) = 1
      rw [← circle_character_exp (K.row a) θ]
      exact h _ ((hK _).mp (Submodule.subset_span (mem_range_self a)))
    choose z hz using hr
    exact ⟨z, funext fun a => eq_sub_of_add_eq ((hshift a).symm.trans (hz a))⟩
  · rintro ⟨z, hz⟩ k hk
    have hr (a : A) : (R *ᵥ θ) a = (z a : ℝ) * (2 * Real.pi) := by
      rw [hshift, congrFun hz a, sub_add_cancel]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp ((hK k).mpr hk)
    rw [circle_character_exp]
    apply Circle.exp_eq_one.mpr
    refine ⟨∑ a, c a * z a, ?_⟩
    calc
      (∑ j, (k j : ℝ) * θ j) = ∑ a, (c a : ℝ) * (R *ᵥ θ) a := by
        have hentry (j : J) : k j = ∑ a, c a * K a j := by
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
            using (congrFun hc j).symm
        simp only [hentry, Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum,
          Matrix.mulVec, dotProduct, R, Matrix.map_apply, mul_assoc]
        exact Finset.sum_comm
      _ = ((∑ a, c a * z a : ℤ) : ℝ) * (2 * Real.pi) := by
        simp only [hr, Int.cast_sum, Int.cast_mul, Finset.sum_mul, mul_assoc]

private theorem exists_weighted_fiber_minimum {J A : Type*} [Fintype J] [Fintype A]
    [DecidableEq J] [DecidableEq A] (R : Matrix A J ℝ) (w : J → ℝ)
    (hw : ∀ j, 0 < w j) (hR : LinearIndependent ℝ R.row) (b : A → ℝ) :
    let M := diagonal w
    let G := R * M⁻¹ * Rᵀ
    ∃ x : J → ℝ, R *ᵥ x = b ∧ x ⬝ᵥ (M *ᵥ x) = b ⬝ᵥ (G⁻¹ *ᵥ b) ∧
      ∀ y : J → ℝ, R *ᵥ y = b → x ⬝ᵥ (M *ᵥ x) ≤ y ⬝ᵥ (M *ᵥ y) := by
  intro M G
  have hM : M.PosDef := .diagonal hw
  have hG : G.PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hM.inv.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff.mpr hR)
  let u := G⁻¹ *ᵥ b
  let x := M⁻¹ *ᵥ (Rᵀ *ᵥ u)
  have hx : R *ᵥ x = b := by
    change R *ᵥ (M⁻¹ *ᵥ (Rᵀ *ᵥ u)) = b
    rw [mulVec_mulVec (Rᵀ *ᵥ u), mulVec_mulVec u]
    change G *ᵥ (G⁻¹ *ᵥ b) = b
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit),
      one_mulVec]
  have hMx : M *ᵥ x = Rᵀ *ᵥ u := by
    change M *ᵥ (M⁻¹ *ᵥ (Rᵀ *ᵥ u)) = Rᵀ *ᵥ u
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit),
      one_mulVec]
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hMx, dotProduct_transpose_mulVec, hx, dotProduct_comm]
  · intro y hy
    let v := y - x
    have hv : R *ᵥ v = 0 := by simp [v, mulVec_sub, hy, hx]
    have hvx : v ⬝ᵥ (M *ᵥ x) = 0 := by
      rw [hMx, dotProduct_transpose_mulVec, hv, dotProduct_zero]
    have hxv : x ⬝ᵥ (M *ᵥ v) = 0 := by
      have hMtranspose : Mᵀ = M := diagonal_transpose w
      rwa [← hMtranspose, dotProduct_transpose_mulVec]
    have hvv : 0 ≤ v ⬝ᵥ (M *ᵥ v) := by
      simpa only [star_trivial] using hM.posSemidef.dotProduct_mulVec_nonneg v
    have hyx : y = x + v := by simp [v]
    conv_rhs => rw [hyx]
    simp only [mulVec_add, add_dotProduct, dotProduct_add, hvx, hxv, add_zero, zero_add]
    exact le_add_of_nonneg_right hvv

#print axioms closure_real_phase_orbit
#print axioms centered_lift_iff

end D5.S3.Fourier.WeightedPhaseRelationLattice
