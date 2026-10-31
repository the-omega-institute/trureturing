/- GID: D5/S3/Geometry/Hyperideal/LengthGramDualImage
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramDualImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.NonsingularInverse]
   utility: none
   digest: The realizing hyperbolic range is exactly the dual/cap Lorentz sign region. -/

/-
proof_shape: range_eq_dualCapRegion: content
admission_basis: escape-witness.
escape_witness: matrix_det_ne_zero, the realizing matrix is shown invertible from
the negative Gram determinant before the coefficient reconstruction.
Escape audit unfinished: issue https://github.com/the-omega-institute/trureturing/issues/24926
tracks the missing faithful four-slot Reg mirror.
-/

import D5.S3.Geometry.Hyperideal.LengthGramRadialImage
import D5.S3.Geometry.Hyperideal.LengthGramDualPairing
import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import D5.S3.Geometry.Hyperideal.LorentzGramDeterminant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramDualPairing
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.Hyperideal.LengthGramRadialImage
open D5.S3.Geometry.Hyperideal.LorentzGramDeterminant
open D5.S3.Geometry.HyperbolicUpperHalfSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.Geometry.Hyperideal.LengthGramDualImage

abbrev V := Fin 4 → ℝ

def dualCapRegion (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    Set HyperbolicThreeSpace :=
  {p | ∀ i, 0 ≤ lorentz (lift p) (dualVector (lengthGram l) M i) ∧
    lorentz (lift p) (M i) ≤ 0}

private lemma lorentz_symm (x y : V) : lorentz x y = lorentz y x := by
  unfold lorentz
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma lorentz_vecMul_linear
    (M : Matrix (Fin 4) (Fin 4) ℝ) (x : V) (z : V) :
    lorentz (x ᵥ* M) z = ∑ i, x i * lorentz (M i) z := by
  unfold Matrix.vecMul lorentz
  simp only [dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma gram_quadratic_vecMul
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, lorentz (M i) (M j) = lengthGram l i j) (x : V) :
    gramQuadratic l x = lorentz (x ᵥ* M) (x ᵥ* M) := by
  calc
    gramQuadratic l x = ∑ i, x i * ∑ j, x j * lorentz (M i) (M j) := by
      unfold gramQuadratic
      apply Finset.sum_congr rfl
      intro i hi
      apply congrArg (fun q => x i * q)
      apply Finset.sum_congr rfl
      intro j hj
      rw [hM]
      ring
    _ = ∑ i, x i * lorentz (M i) (x ᵥ* M) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [lorentz_symm, lorentz_vecMul_linear]
      apply Finset.sum_congr rfl
      intro j hj
      rw [lorentz_symm, hM]
    _ = lorentz (x ᵥ* M) (x ᵥ* M) := by
      rw [lorentz_vecMul_linear]

private lemma lorentz_vecMul_cap
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (x : V) (i : Fin 4) :
    lorentz (x ᵥ* M) (M i) = ∑ j, lengthGram l i j * x j := by
  rw [lorentz_vecMul_linear]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lorentz_symm, hM]
  ring

private lemma lorentz_vecMul_dual
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hdet : (lengthGram l).det < 0) (x : V) (i : Fin 4) :
    lorentz (x ᵥ* M) (dualVector (lengthGram l) M i) = x i := by
  calc
    lorentz (x ᵥ* M) (dualVector (lengthGram l) M i) =
        ∑ j, x j * lorentz (M j) (dualVector (lengthGram l) M i) :=
      lorentz_vecMul_linear M x _
    _ = ∑ j, x j * (if i = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [lorentz_symm, dual_pairing l M hM hdet i j]
    _ = x i := by simp

private lemma matrix_det_ne_zero
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hdet : (lengthGram l).det < 0) : M.det ≠ 0 := by
  intro hzero
  have hfactor := length_gram_determinant_factorization l M hM
  rw [hzero] at hfactor
  exact (ne_of_lt hdet) (by simpa using hfactor)

private lemma radial_lift_unit
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hl : ∀ k, 0 < l k)
    (v : cutBody l) :
    lorentz (radial l v.val ᵥ* M) (radial l v.val ᵥ* M) = -1 := by
  rw [← gram_quadratic_vecMul l M hM]
  obtain ⟨_, _, _, _, _, _, _, _, hnormalized, _⟩ := shared_radial_body l hl
  exact hnormalized v.val v.property

private lemma radial_lift_time
    (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hl : ∀ k, 0 < l k) (hrows : ∀ i, 0 ≤ M i 3) (v : cutBody l) :
    0 < (radial l v.val ᵥ* M) 3 := by
  have hrad (i : Fin 4) : 0 ≤ radial l v.val i :=
    div_nonneg (v.property.1.1 i) (Real.sqrt_nonneg _)
  have hnonneg : 0 ≤ (radial l v.val ᵥ* M) 3 := by
    change 0 ≤ ∑ i, radial l v.val i * M i 3
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hrad i) (hrows i)
  have hunit := radial_lift_unit l M hM hl v
  simp [lorentz, Fin.sum_univ_succ] at hunit
  nlinarith [sq_nonneg ((radial l v.val ᵥ* M) 0),
    sq_nonneg ((radial l v.val ᵥ* M) 1),
    sq_nonneg ((radial l v.val ᵥ* M) 2)]

theorem range_eq_dualCapRegion
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hdet : (lengthGram l).det < 0)
    (hrows : ∀ i, 0 ≤ M i 3)
    (f : cutBody l → HyperbolicThreeSpace)
    (hcoord : ∀ v, (f v).coordinates.val =
      WithLp.toLp 2
        (Complex.mk ((radial l v.val ᵥ* M) 0 /
          ((radial l v.val ᵥ* M) 3 - (radial l v.val ᵥ* M) 2))
          ((radial l v.val ᵥ* M) 1 /
          ((radial l v.val ᵥ* M) 3 - (radial l v.val ᵥ* M) 2)),
         1 / ((radial l v.val ᵥ* M) 3 - (radial l v.val ᵥ* M) 2))) :
    range f = dualCapRegion l M := by
  have hMdet : M.det ≠ 0 := matrix_det_ne_zero l M hM hdet
  have hMinv : M⁻¹ * M = 1 :=
    Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hMdet)
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    let y : V := radial l v.val ᵥ* M
    have hyunit : lorentz y y = -1 := by
      exact radial_lift_unit l M hM hl v
    have hyt : 0 < y 3 := by
      exact radial_lift_time l M hM hl hrows v
    have hlf : lift (f v) = y := by
      apply lift_of_coordinates (f v) y hyunit hyt
      simpa [y] using hcoord v
    intro i
    constructor
    · rw [hlf]
      change 0 ≤ lorentz (radial l v.val ᵥ* M)
        (dualVector (lengthGram l) M i)
      have hpair := lorentz_vecMul_dual l M hM hdet (radial l v.val) i
      rw [hpair]
      exact div_nonneg (v.property.1.1 i) (Real.sqrt_nonneg _)
    · rw [hlf]
      change lorentz (radial l v.val ᵥ* M) (M i) ≤ 0
      have hpair := lorentz_vecMul_cap l M hM (radial l v.val) i
      rw [hpair]
      change (∑ j, lengthGram l i j *
        (v.val j / Real.sqrt (-gramQuadratic l v.val))) ≤ 0
      have hdiv : (∑ j, lengthGram l i j *
          (v.val j / Real.sqrt (-gramQuadratic l v.val))) =
          (∑ j, lengthGram l i j * v.val j) /
            Real.sqrt (-gramQuadratic l v.val) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hdiv]
      exact div_nonpos_of_nonpos_of_nonneg (v.property.2 i) (Real.sqrt_nonneg _)
  · intro hp
    have hYunit : lorentz (lift p) (lift p) = -1 := lift_unit p
    let x : V := lift p ᵥ* M⁻¹
    have hxm : x ᵥ* M = lift p := by
      dsimp [x]
      calc
        (lift p ᵥ* M⁻¹) ᵥ* M = lift p ᵥ* (M⁻¹ * M) :=
          Matrix.vecMul_vecMul _ _ _
        _ = lift p ᵥ* 1 := by rw [hMinv]
        _ = lift p := Matrix.vecMul_one _
    have hxq : gramQuadratic l x = -1 := by
      rw [gram_quadratic_vecMul l M hM, hxm, hYunit]
    have hxnonneg : ∀ i, 0 ≤ x i := by
      intro i
      have hpair := lorentz_vecMul_dual l M hM hdet x i
      have hregion := hp i |>.1
      rw [hxm] at hpair
      exact hpair ▸ hregion
    have hxsupport : ∀ i, ∑ j, lengthGram l i j * x j ≤ 0 := by
      intro i
      have hpair := lorentz_vecMul_cap l M hM x i
      have hregion := hp i |>.2
      rw [hxm] at hpair
      exact hpair ▸ hregion
    have hx : x ∈ halfspaceSlice l := ⟨hxq, hxnonneg, hxsupport⟩
    have hx' : x ∈ radial l '' cutBody l := by
      rw [radial_image_halfspace_slice l hl]
      exact hx
    obtain ⟨v, hv, hrad⟩ := hx'
    let vv : cutBody l := ⟨v, hv⟩
    let y : V := radial l vv.val ᵥ* M
    have hyunit : lorentz y y = -1 := radial_lift_unit l M hM hl vv
    have hyt : 0 < y 3 := radial_lift_time l M hM hl hrows vv
    have hym : y = lift p := by
      dsimp [y]
      rw [hrad, hxm]
    have hlf : lift (f vv) = lift p := by
      calc
        lift (f vv) = y := by
          apply lift_of_coordinates (f vv) y hyunit hyt
          simpa [y] using hcoord vv
        _ = lift p := hym
    exact ⟨vv, lift_injective hlf⟩

#print axioms range_eq_dualCapRegion
end D5.S3.Geometry.Hyperideal.LengthGramDualImage
