/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorTransversality
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.FDeriv.Star]
   utility: none
   digest: All-length fixed-target real transversality at an actual interior witness. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Star
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversalityCertificate
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.ZPow

/-! The targets are the native actual environments and remain fixed under
variation of the trial parameter. All differentiation is over the real field.
Algebraic inverse transfer carries no positivity assertion. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality

open scoped Matrix ComplexOrder BigOperators Matrix.Norms.Elementwise
open Matrix
open PeriodicMPSParentIntersection (Bond)
open OpenBoundaryMPSDensityRecovery (transfer)
open OpenBoundaryMPSInteriorCommonCore (dualTransfer)
open OpenBoundaryMPSInteriorRootRealization
open OpenBoundaryMPSInteriorTransversalityCertificate

def fixedSector : Sector := ⟨2, 0, 1⟩
def leftBoundary : Fin 2 → ℂ := ![1, 1]
def rightBoundary : Fin 2 → ℂ := ![1, Complex.I]

private lemma fixed_regular : Regular fixedSector := by
  norm_num [Regular, fixedSector, delta, alpha, beta, Complex.normSq_apply]

private lemma G_one : G fixedSector 1 = !![1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [G, fixedSector, alpha, beta]

private lemma G_one_det : (G fixedSector 1).det ≠ 0 := by
  rw [G_one]
  norm_num [det_fin_two]

private lemma transfer_psd {X : Bond} (h : X.PosSemidef) :
    (transfer (core fixedSector 1) X).PosSemidef := by
  simpa only [transfer, Fin.sum_univ_two] using
    (h.mul_mul_conjTranspose_same (core fixedSector 1 0)).add
      (h.mul_mul_conjTranspose_same (core fixedSector 1 1))

private lemma dual_psd {X : Bond} (h : X.PosSemidef) :
    (dualTransfer (core fixedSector 1) X).PosSemidef := by
  simpa only [dualTransfer, Fin.sum_univ_two] using
    (h.conjTranspose_mul_mul_same (core fixedSector 1 0)).add
      (h.conjTranspose_mul_mul_same (core fixedSector 1 1))

private lemma transfer_pd {X : Bond} (h : X.PosDef) :
    (transfer (core fixedSector 1) X).PosDef := by
  have hW : (G fixedSector 1 * X * (G fixedSector 1)ᴴ).PosDef := by
    apply (h.posSemidef.mul_mul_conjTranspose_same _).posDef_iff_det_ne_zero.mpr
    simpa only [det_mul, det_conjTranspose] using
      mul_ne_zero (mul_ne_zero G_one_det (h.posSemidef.posDef_iff_det_ne_zero.mp h)) (star_ne_zero.mpr G_one_det)
  simpa only [transfer, Fin.sum_univ_two, core, Matrix.cons_val_zero] using
    hW.add_posSemidef (h.posSemidef.mul_mul_conjTranspose_same (core fixedSector 1 1))

private lemma dual_pd {X : Bond} (h : X.PosDef) :
    (dualTransfer (core fixedSector 1) X).PosDef := by
  have hW : ((G fixedSector 1)ᴴ * X * G fixedSector 1).PosDef := by
    apply (h.posSemidef.conjTranspose_mul_mul_same _).posDef_iff_det_ne_zero.mpr
    simpa only [det_mul, det_conjTranspose] using
      mul_ne_zero (mul_ne_zero (star_ne_zero.mpr G_one_det) (h.posSemidef.posDef_iff_det_ne_zero.mp h)) G_one_det
  simpa only [dualTransfer, Fin.sum_univ_two, core, Matrix.cons_val_zero] using
    hW.add_posSemidef (h.posSemidef.conjTranspose_mul_mul_same (core fixedSector 1 1))

private lemma left_seed :
    dualTransfer (core fixedSector 1) (vecMulVec (star leftBoundary) leftBoundary) =
      !![8, 4; 4, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dualTransfer, core, B, G, fixedSector, leftBoundary, alpha, beta,
      mul_apply, Fin.sum_univ_two, conjTranspose_apply, vecMulVec_apply]

private lemma right_seed :
    transfer (core fixedSector 1) (vecMulVec rightBoundary (star rightBoundary)) =
      !![10, 2 * Complex.I; -2 * Complex.I, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [transfer, core, B, G, fixedSector, rightBoundary, alpha, beta,
      Matrix.add_apply, mul_apply, Fin.sum_univ_two, conjTranspose_apply, vecMulVec_apply,
      Pi.star_apply, Matrix.diagonal_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Fin.isValue, Fin.reduceFinMk]
  all_goals norm_num [map_ofNat, Complex.I_sq]
  all_goals ring

private lemma left_pd (p : ℕ) (hp : 1 ≤ p) :
    (leftTarget fixedSector 1 leftBoundary p).PosDef := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  induction n with
  | zero =>
      apply (dual_psd (posSemidef_vecMulVec_star_self _)).posDef_iff_det_ne_zero.mpr
      rw [left_seed]
      norm_num [det_fin_two]
  | succ n ih =>
      simpa only [leftTarget, Function.iterate_succ_apply'] using dual_pd (ih (by omega))

private lemma right_pd (q : ℕ) (hq : 1 ≤ q) :
    (rightTarget fixedSector 1 rightBoundary q).PosDef := by
  have hi : ((transfer (core fixedSector 1))^[q]
      (vecMulVec rightBoundary (star rightBoundary))).PosDef := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    induction n with
    | zero =>
        apply (transfer_psd (posSemidef_vecMulVec_self_star _)).posDef_iff_det_ne_zero.mpr
        rw [right_seed]
        norm_num [det_fin_two]
        ring_nf
        norm_num [Complex.I_sq]
    | succ n ih => simpa only [Function.iterate_succ_apply'] using transfer_pd (ih (by omega))
  have hsq : IsUnit (G fixedSector 1 ^ 2).det := by
    rw [det_pow]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ G_one_det)
  apply (hi.posSemidef.mul_mul_conjTranspose_same _).posDef_iff_det_ne_zero.mpr
  simpa only [det_mul, det_conjTranspose] using
    mul_ne_zero (mul_ne_zero hsq.ne_zero (hi.posSemidef.posDef_iff_det_ne_zero.mp hi)) (star_ne_zero.mpr hsq.ne_zero)


private def entry (i j : Fin 2) : Bond →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℂ) j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → ℂ) i)

@[simp] private lemma entry_apply (i j : Fin 2) (X : Bond) : entry i j X = X i j := rfl

private lemma matrix_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bond} {d : E →L[ℝ] Bond} {x : E}
    (h : ∀ i j, HasFDerivAt (fun y => f y i j) ((entry i j).comp d) x) :
    HasFDerivAt f d x := by
  apply hasFDerivAt_pi''
  intro i
  apply hasFDerivAt_pi''
  intro j
  simpa only [entry, ContinuousLinearMap.comp_assoc] using h i j

private def mulD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Bond) (a b : E →L[ℝ] Bond) : E →L[ℝ] Bond :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    ∑ k : Fin 2, ((B k j) • ((entry i k).comp a) + (A i k) • ((entry k j).comp b))

private lemma mulD_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Bond) (a b : E →L[ℝ] Bond) (h : E) :
    mulD A B a b h = a h * B + A * b h := by
  ext i j
  change (∑ k : Fin 2, (B k j * a h i k + A i k * b h k j)) = _
  simp only [mul_apply, Matrix.add_apply, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma matrix_mul_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → Bond} {a b : E →L[ℝ] Bond} {x : E}
    (hf : HasFDerivAt f a x) (hg : HasFDerivAt g b x) :
    HasFDerivAt (fun y => f y * g y) (mulD (f x) (g x) a b) x := by
  apply matrix_deriv
  intro i j
  have hi := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((entry i k).hasFDerivAt.comp x hf).mul ((entry k j).hasFDerivAt.comp x hg))
  convert! hi using 1
  ext h
  change (∑ k : Fin 2, (g x k j * a h i k + f x i k * b h k j)) =
    ∑ k : Fin 2, (f x i k * b h k j + g x k j * a h i k)
  apply Finset.sum_congr rfl
  intro k _
  ring

private def daggerD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →L[ℝ] Bond) : E →L[ℝ] Bond :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.comp ((entry j i).comp a)

private lemma daggerD_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →L[ℝ] Bond) (h : E) : daggerD a h = (a h)ᴴ := by
  ext i j
  rfl

private lemma matrix_star_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bond} {a : E →L[ℝ] Bond} {x : E} (hf : HasFDerivAt f a x) :
    HasFDerivAt (fun y => (f y)ᴴ) (daggerD a) x := by
  apply matrix_deriv
  intro i j
  exact ((entry j i).hasFDerivAt.comp x hf).star

private lemma inverse_G_entries {z : ℂ} (hz : z ≠ 0) :
    (G fixedSector z)⁻¹ = !![1/2, 1/2; z⁻¹/2, -z⁻¹/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G, fixedSector, alpha, beta, Matrix.inv_def, Ring.inverse_eq_inv,
      adjugate_fin_two, det_fin_two]
  all_goals field_simp
  all_goals ring

private def inverseGD : ℂ →L[ℝ] Bond :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    if i = 0 then 0 else if j = 0 then
      (-(1/2 : ℂ)) • ContinuousLinearMap.id ℝ ℂ else
      (1/2 : ℂ) • ContinuousLinearMap.id ℝ ℂ

private lemma inverseGD_apply (w : ℂ) : inverseGD w = !![0, 0; -w/2, w/2] := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · calc
      inverseGD w 1 0 = (-(1/2 : ℂ)) • w := rfl
      _ = -w/2 := by rw [smul_eq_mul]; ring
  · calc
      inverseGD w 1 1 = (1/2 : ℂ) • w := rfl
      _ = w/2 := by rw [smul_eq_mul]; ring

private lemma inverse_G_deriv : HasFDerivAt (fun z => (G fixedSector z)⁻¹) inverseGD 1 := by
  have hi : HasFDerivAt (fun z : ℂ => z⁻¹) (-ContinuousLinearMap.id ℝ ℂ) 1 := by
    convert! (hasFDerivAt_inv (by norm_num : (1 : ℂ) ≠ 0)).restrictScalars ℝ using 1
    ext w
    simp
  have he : HasFDerivAt (fun z : ℂ => !![1/2, 1/2; z⁻¹/2, -z⁻¹/2]) inverseGD 1 := by
    apply matrix_deriv
    intro i j
    fin_cases i <;> fin_cases j
    · convert! hasFDerivAt_const (𝕜 := ℝ) (1/2 : ℂ) (1 : ℂ) using 1 <;> ext w <;> rfl
    · convert! hasFDerivAt_const (𝕜 := ℝ) (1/2 : ℂ) (1 : ℂ) using 1 <;> ext w <;> rfl
    · convert! hi.mul_const (2 : ℂ)⁻¹ using 1
      ext w
      change (inverseGD w) 1 0 = _
      rw [inverseGD_apply]
      simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
      ring
    · convert! (hi.neg).mul_const (2 : ℂ)⁻¹ using 1
      ext w
      change (inverseGD w) 1 1 = _
      rw [inverseGD_apply]
      simp only [Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
      ring
  apply he.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0)] with z hz
  exact inverse_G_entries hz

private def schurD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →L[ℝ] Bond) : E →L[ℝ] Bond :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (1 / (1 + (![2, 0] : Fin 2 → ℂ) i * (![2, 0] : Fin 2 → ℂ) j)) •
      ((entry i j).comp a)

private lemma schurD_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E →L[ℝ] Bond) (h : E) :
    schurD a h = diagonalInverse fixedSector (a h) := by
  ext i j
  change (1 / (1 + (![2, 0] : Fin 2 → ℂ) i * (![2, 0] : Fin 2 → ℂ) j)) * a h i j = _
  fin_cases i <;> fin_cases j <;> simp [diagonalInverse, fixedSector] <;> ring

private lemma schur_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bond} {a : E →L[ℝ] Bond} {x : E} (hf : HasFDerivAt f a x) :
    HasFDerivAt (fun y => diagonalInverse fixedSector (f y)) (schurD a) x := by
  apply matrix_deriv
  intro i j
  convert! ((entry i j).hasFDerivAt.comp x hf).mul_const
    ((1 + (![2, 0] : Fin 2 → ℂ) i * (![2, 0] : Fin 2 → ℂ) j)⁻¹) using 1
  · funext y
    change f y i j / (1 + (![2, 0] : Fin 2 → ℂ) i * star ((![2, 0] : Fin 2 → ℂ) j)) = _
    change _ = f y i j * (1 + (![2, 0] : Fin 2 → ℂ) i * (![2, 0] : Fin 2 → ℂ) j)⁻¹
    fin_cases i <;> fin_cases j <;> norm_num [map_ofNat, div_eq_mul_inv]
  · ext h
    change (schurD a h) i j = _
    rw [schurD_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, entry_apply]
    fin_cases i <;> fin_cases j <;> norm_num [diagonalInverse, fixedSector, smul_eq_mul,
      map_ofNat, div_eq_mul_inv, mul_comm]

private lemma star_schur (X : Bond) :
    diagonalStarInverse fixedSector X = diagonalInverse fixedSector X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalStarInverse, diagonalInverse, fixedSector]

private def jointED (X : Bond) : (ℂ × Bond) →L[ℝ] Bond :=
  let g := (G fixedSector 1)⁻¹
  let dg := inverseGD.comp (ContinuousLinearMap.fst ℝ ℂ Bond)
  let dx := schurD (ContinuousLinearMap.snd ℝ ℂ Bond)
  mulD (g * diagonalInverse fixedSector X) gᴴ
    (mulD g (diagonalInverse fixedSector X) dg dx) (daggerD dg)

private def jointSD (X : Bond) : (ℂ × Bond) →L[ℝ] Bond :=
  let g := (G fixedSector 1)⁻¹
  let dg := inverseGD.comp (ContinuousLinearMap.fst ℝ ℂ Bond)
  let dx := ContinuousLinearMap.snd ℝ ℂ Bond
  schurD (mulD (gᴴ * X) g (mulD gᴴ X (daggerD dg) dx) dg)

private lemma joint_inverse_transfer (X : Bond) :
    HasFDerivAt (fun u : ℂ × Bond => inverseTransfer fixedSector u.1 u.2)
      (jointED X) (1, X) := by
  have hg := inverse_G_deriv.comp ((1 : ℂ), X)
    ((ContinuousLinearMap.fst ℝ ℂ Bond).hasFDerivAt (x := ((1 : ℂ), X)))
  convert! matrix_mul_deriv (matrix_mul_deriv hg
    (schur_deriv ((ContinuousLinearMap.snd ℝ ℂ Bond).hasFDerivAt (x := ((1 : ℂ), X))))) (matrix_star_deriv hg) using 1

private lemma joint_inverse_dual (X : Bond) :
    HasFDerivAt (fun u : ℂ × Bond => inverseDualTransfer fixedSector u.1 u.2)
      (jointSD X) (1, X) := by
  have hg := inverse_G_deriv.comp ((1 : ℂ), X)
    ((ContinuousLinearMap.fst ℝ ℂ Bond).hasFDerivAt (x := ((1 : ℂ), X)))
  convert! (show HasFDerivAt _ _ _ from
    schur_deriv (matrix_mul_deriv
      (matrix_mul_deriv (matrix_star_deriv hg) ((ContinuousLinearMap.snd ℝ ℂ Bond).hasFDerivAt (x := ((1 : ℂ), X)))) hg)) using 1
  funext u
  exact star_schur _


private def e0 : Bond →L[ℝ] Bond :=
  (jointED 0).comp (ContinuousLinearMap.inr ℝ ℂ Bond)
private def s0 : Bond →L[ℝ] Bond :=
  (jointSD 0).comp (ContinuousLinearMap.inr ℝ ℂ Bond)

private lemma e0_apply (X : Bond) : e0 X = inverseTransfer fixedSector 1 X := by
  simp [e0, jointED, mulD_apply, daggerD_apply, schurD_apply, inverseTransfer]

private lemma s0_apply (X : Bond) : s0 X = inverseDualTransfer fixedSector 1 X := by
  simp [s0, jointSD, mulD_apply, daggerD_apply, schurD_apply,
    inverseDualTransfer, star_schur]

private def radial : Bond →L[ℝ] Bond :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    if i = 0 ∧ j = 0 then 0 else if i = 1 ∧ j = 1 then (2 : ℂ) • entry i j
    else entry i j

private def angular : Bond →L[ℝ] Bond :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    if i = j then 0 else if i = 0 then -Complex.I • entry i j else Complex.I • entry i j

private lemma radial_apply (X : Bond) : radial X = !![0, X 0 1; X 1 0, 2 * X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · exact smul_eq_mul (2 : ℂ) (X 1 1)

private lemma angular_apply (X : Bond) :
    angular X = !![0, -Complex.I * X 0 1; Complex.I * X 1 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact smul_eq_mul (-Complex.I) (X 0 1)
  · exact smul_eq_mul Complex.I (X 1 0)
  · rfl

private lemma jointED_apply (X H : Bond) (w : ℂ) :
    jointED X (w, H) = e0 H - w.re • radial (e0 X) - w.im • angular (e0 X) := by
  simp only [jointED, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', mulD_apply, daggerD_apply, schurD_apply,
    inverseGD_apply, e0_apply, inverseTransfer, inverse_G_entries (by norm_num : (1 : ℂ) ≠ 0)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [radial_apply, angular_apply, diagonalInverse, fixedSector,
      mul_apply, Fin.sum_univ_two, conjTranspose_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.isValue, Fin.reduceFinMk,
      RCLike.star_def, map_add, map_sub, map_mul, map_inv₀]
  all_goals apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im, map_ofNat] <;> ring

private lemma jointSD_apply (X H : Bond) (w : ℂ) :
    jointSD X (w, H) = s0 H - w.re • s0 (radial X) + w.im • s0 (angular X) := by
  simp only [jointSD, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', mulD_apply, daggerD_apply, schurD_apply,
    inverseGD_apply, s0_apply, inverseDualTransfer, star_schur,
    inverse_G_entries (by norm_num : (1 : ℂ) ≠ 0)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [radial_apply, angular_apply, diagonalInverse, fixedSector,
      mul_apply, Fin.sum_univ_two, conjTranspose_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.isValue, Fin.reduceFinMk,
      RCLike.star_def, map_add, map_sub, map_mul, map_inv₀]
  all_goals apply Complex.ext <;>
    norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im, map_ofNat] <;> ring

private def jet (A B : Bond) : ℂ →L[ℝ] Bond :=
  Complex.reCLM.smulRight A + Complex.imCLM.smulRight B

private lemma jet_apply (A B : Bond) (w : ℂ) : jet A B w = w.re • A + w.im • B := rfl

private lemma inverse_transfer_jet {f : ℂ → Bond} {A B : Bond}
    (hf : HasFDerivAt f (jet A B) 1) :
    HasFDerivAt (fun z => inverseTransfer fixedSector z (f z))
      (jet (e0 A - radial (e0 (f 1))) (e0 B - angular (e0 (f 1)))) 1 := by
  convert! (joint_inverse_transfer (f 1)).comp 1 ((hasFDerivAt_id 1).prodMk hf) using 1
  ext w
  simp [jointED_apply, jet_apply, map_add, map_smul, smul_sub]
  abel

private lemma inverse_dual_jet {f : ℂ → Bond} {A B : Bond}
    (hf : HasFDerivAt f (jet A B) 1) :
    HasFDerivAt (fun z => inverseDualTransfer fixedSector z (f z))
      (jet (s0 A - s0 (radial (f 1))) (s0 B + s0 (angular (f 1)))) 1 := by
  convert! (joint_inverse_dual (f 1)).comp 1 ((hasFDerivAt_id 1).prodMk hf) using 1
  ext w
  simp [jointSD_apply, jet_apply, map_add, map_smul, smul_sub]
  abel




private def hc (x : Fin 3 → ℝ) (v : ℝ) : Bond :=
  !![((x 0 + x 1)/2 : ℝ), ((x 2 : ℂ) + Complex.I * v)/2;
     ((x 2 : ℂ) - Complex.I * v)/2, ((x 0 - x 1)/2 : ℝ)]

private lemma s0_hc (x : Fin 3 → ℝ) (v : ℝ) :
    s0 (hc x v) = hc ![(3*x 0-2*x 2)/10, (-2*x 0+3*x 2)/10, x 1/2] (-v/2) := by
  rw [s0_apply, inverseDualTransfer, star_schur, inverse_G_entries (by norm_num : (1 : ℂ) ≠ 0)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hc, diagonalInverse, fixedSector, mul_apply, Fin.sum_univ_two,
      conjTranspose_apply, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div]
  all_goals norm_num [map_ofNat, Matrix.vecMul, dotProduct, mul_apply, Fin.sum_univ_two,
    diagonalInverse, fixedSector, hc]
  all_goals ring

private lemma e0_hc (x : Fin 3 → ℝ) (v : ℝ) :
    e0 (hc x v) = hc ![(3*x 0-2*x 1)/10, x 2/2, (-2*x 0+3*x 1)/10] (-v/2) := by
  rw [e0_apply, inverseTransfer, inverse_G_entries (by norm_num : (1 : ℂ) ≠ 0)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hc, diagonalInverse, fixedSector, mul_apply, Fin.sum_univ_two,
      conjTranspose_apply, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div]
  all_goals norm_num [map_ofNat, Matrix.vecMul, dotProduct, mul_apply, Fin.sum_univ_two,
    diagonalInverse, fixedSector, hc]
  all_goals ring

private lemma dual_hc (x : Fin 3 → ℝ) (v : ℝ) :
    dualTransfer (core fixedSector 1) (hc x v) =
      hc ![6*x 0+4*x 1, 2*x 2, 4*x 0+6*x 1] (-2*v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [dualTransfer, core, B, G, fixedSector, alpha, beta, hc,
      Matrix.add_apply, mul_apply, Fin.sum_univ_two, conjTranspose_apply,
      Pi.star_apply, Matrix.diagonal_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Fin.isValue, Fin.reduceFinMk]
  all_goals push_cast
  all_goals simp [star_add, star_sub, star_mul]
  all_goals ring

private lemma transfer_hc (x : Fin 3 → ℝ) (v : ℝ) :
    transfer (core fixedSector 1) (hc x v) =
      hc ![6*x 0+4*x 2, 4*x 0+6*x 2, 2*x 1] (-2*v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [transfer, core, B, G, fixedSector, alpha, beta, hc,
      Matrix.add_apply, mul_apply, Fin.sum_univ_two, conjTranspose_apply,
      Pi.star_apply, Matrix.diagonal_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Fin.isValue, Fin.reduceFinMk]
  all_goals push_cast
  all_goals simp [star_add, star_sub, star_mul]
  all_goals ring

private lemma radial_hc (x : Fin 3 → ℝ) (v : ℝ) :
    radial (hc x v) = hc ![x 0-x 1, x 1-x 0, x 2] v := by
  rw [radial_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc] <;> push_cast <;> ring

private lemma angular_hc (x : Fin 3 → ℝ) (v : ℝ) :
    angular (hc x v) = hc ![0, 0, v] (-x 2) := by
  rw [angular_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private def lread : Bond →L[ℝ] ℝ :=
  Complex.reCLM.comp (entry 0 0 + entry 1 1 - entry 0 1 - entry 1 0)
private def rread : Bond →L[ℝ] ℝ :=
  Complex.reCLM.comp (entry 0 0 + entry 1 1 + Complex.I • (entry 1 0 - entry 0 1))

private lemma lread_hc (x : Fin 3 → ℝ) (v : ℝ) : lread (hc x v) = x 0 - x 2 := by
  change ((hc x v) 0 0 + (hc x v) 1 1 - (hc x v) 0 1 - (hc x v) 1 0).re = _
  simp [hc]
  ring
private lemma rread_hc (x : Fin 3 → ℝ) (v : ℝ) : rread (hc x v) = x 0 + v := by
  change ((hc x v) 0 0 + (hc x v) 1 1 + Complex.I * ((hc x v) 1 0 - (hc x v) 0 1)).re = _
  simp [hc, Complex.mul_re, Complex.mul_im]
  ring


private def leftSum (A : Bond →L[ℝ] Bond) (n m : ℕ) : Bond :=
  ∑ k ∈ Finset.range n, (s0^(k+1)) (A (leftTarget fixedSector 1 leftBoundary (m+k+1)))

private lemma leftSum_succ (A : Bond →L[ℝ] Bond) (n m : ℕ) :
    leftSum A (n+1) m = s0 (leftSum A n (m+1)) +
      s0 (A (leftTarget fixedSector 1 leftBoundary (m+1))) := by
  unfold leftSum
  rw [Finset.sum_range_succ', map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ', ContinuousLinearMap.mul_apply]
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma left_partial (n m : ℕ) :
    trialLeft fixedSector n (leftTarget fixedSector 1 leftBoundary (n+m)) 1 =
      leftTarget fixedSector 1 leftBoundary m := by
  unfold trialLeft leftTarget
  rw [Function.iterate_add_apply]
  exact Function.LeftInverse.iterate
    (inverse_dual_left fixed_regular (by norm_num : (1 : ℂ) ≠ 0)) n _

private lemma left_jets (n m : ℕ) :
    HasFDerivAt
      (trialLeft fixedSector n (leftTarget fixedSector 1 leftBoundary (n+m)))
      (jet (-leftSum radial n m) (leftSum angular n m)) 1 := by
  induction n generalizing m with
  | zero =>
      have hz : jet (-leftSum radial 0 m) (leftSum angular 0 m) = 0 := by
        apply ContinuousLinearMap.ext
        intro w
        rw [jet_apply]
        simp [leftSum]
      rw [hz]
      convert! hasFDerivAt_const (𝕜 := ℝ)
        (leftTarget fixedSector 1 leftBoundary m) (1 : ℂ) using 1
      funext z
      simp only [trialLeft, Function.iterate_zero_apply, Nat.zero_add]
  | succ n ih =>
      have hh := inverse_dual_jet (ih (m+1))
      rw [left_partial] at hh
      convert! hh using 1
      · funext z
        simp only [trialLeft, Function.iterate_succ_apply']
        simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · rw [leftSum_succ, leftSum_succ]
        simp only [map_neg, neg_add_rev]
        congr 1 <;> abel

private lemma G_square_one : G fixedSector 1 ^ 2 = (2 : ℂ) • (1 : Bond) := by
  rw [G_one]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pow_two, mul_apply, Fin.sum_univ_two]

private lemma right_target_scale (q : ℕ) :
    rightTarget fixedSector 1 rightBoundary q = (4 : ℝ) •
      ((transfer (core fixedSector 1))^[q] (vecMulVec rightBoundary (star rightBoundary))) := by
  rw [rightTarget, G_square_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, conjTranspose_apply]
  all_goals ring

private lemma central_jets (X : Bond) :
    HasFDerivAt
      (fun z : ℂ => (G fixedSector z ^ 2)⁻¹ * ((4 : ℝ) • X) *
        ((G fixedSector z ^ 2)⁻¹)ᴴ)
      (jet (-(radial X + e0 (radial (transfer (core fixedSector 1) X))))
        (-(angular X + e0 (angular (transfer (core fixedSector 1) X))))) 1 := by
  have hh := matrix_mul_deriv inverse_G_deriv inverse_G_deriv
  have h := matrix_mul_deriv
    (matrix_mul_deriv hh (hasFDerivAt_const (𝕜 := ℝ) ((4 : ℝ) • X) (1 : ℂ)))
    (matrix_star_deriv hh)
  convert! h using 1
  · funext z
    rw [← Matrix.inv_pow']
    simp only [pow_two]
  · ext w i j
    simp only [mulD_apply, daggerD_apply, inverseGD_apply,
      inverse_G_entries (by norm_num : (1 : ℂ) ≠ 0), jet_apply,
      e0_apply, inverseTransfer]
    fin_cases i <;> fin_cases j <;>
      simp only [radial_apply, angular_apply, diagonalInverse, fixedSector,
        transfer, core, G, B, alpha, beta, mul_apply, Fin.sum_univ_two,
        conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Matrix.diagonal_apply, Fin.isValue, Fin.reduceFinMk]
    all_goals apply Complex.ext <;>
      norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
        Complex.normSq_apply, RCLike.star_def, map_ofNat, Matrix.vecMul, dotProduct,
        mul_apply, Fin.sum_univ_two, diagonalInverse, fixedSector, Matrix.neg_apply,
        Matrix.zero_apply, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, conjTranspose_apply,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> ring


private def rightSum (A : Bond →L[ℝ] Bond) (n m : ℕ) : Bond :=
  ∑ k ∈ Finset.range (n+2), (e0^k) (A
    ((transfer (core fixedSector 1))^[m+k] (vecMulVec rightBoundary (star rightBoundary))))

private lemma rightSum_succ (A : Bond →L[ℝ] Bond) (n m : ℕ) :
    rightSum A (n+1) m = e0 (rightSum A n (m+1)) +
      A ((transfer (core fixedSector 1))^[m] (vecMulVec rightBoundary (star rightBoundary))) := by
  unfold rightSum
  rw [show n+1+2 = (n+2)+1 by omega, Finset.sum_range_succ', map_sum]
  simp only [Nat.add_zero, pow_zero, ContinuousLinearMap.one_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ', ContinuousLinearMap.mul_apply]
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private lemma central_value (X : Bond) :
    (G fixedSector 1 ^ 2)⁻¹ * ((4 : ℝ) • X) * ((G fixedSector 1 ^ 2)⁻¹)ᴴ = X := by
  rw [← Matrix.inv_pow', inverse_G_entries (by norm_num : (1 : ℂ) ≠ 0)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pow_two, mul_apply, Fin.sum_univ_two, conjTranspose_apply,
      Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.isValue, Fin.reduceFinMk]
  all_goals norm_num [map_ofNat, Matrix.vecMul, dotProduct, mul_apply, Fin.sum_univ_two,
    diagonalInverse, fixedSector]
  all_goals ring

private lemma right_partial (n m : ℕ) :
    trialRight fixedSector n (rightTarget fixedSector 1 rightBoundary (n+m)) 1 =
      (transfer (core fixedSector 1))^[m] (vecMulVec rightBoundary (star rightBoundary)) := by
  rw [trialRight, right_target_scale, central_value, Function.iterate_add_apply]
  exact Function.LeftInverse.iterate
    (inverse_transfer_left fixed_regular (by norm_num : (1 : ℂ) ≠ 0)) n _

private lemma right_jets (n m : ℕ) :
    HasFDerivAt
      (trialRight fixedSector n (rightTarget fixedSector 1 rightBoundary (n+m)))
      (jet (-rightSum radial n m) (-rightSum angular n m)) 1 := by
  induction n generalizing m with
  | zero =>
      rw [right_target_scale]
      have h := central_jets
        ((transfer (core fixedSector 1))^[m] (vecMulVec rightBoundary (star rightBoundary)))
      have hz : jet (-rightSum radial 0 m) (-rightSum angular 0 m) =
          jet (-(radial ((transfer (core fixedSector 1))^[m]
            (vecMulVec rightBoundary (star rightBoundary))) +
            e0 (radial (transfer (core fixedSector 1) ((transfer (core fixedSector 1))^[m]
              (vecMulVec rightBoundary (star rightBoundary)))))))
            (-(angular ((transfer (core fixedSector 1))^[m]
              (vecMulVec rightBoundary (star rightBoundary))) +
              e0 (angular (transfer (core fixedSector 1) ((transfer (core fixedSector 1))^[m]
                (vecMulVec rightBoundary (star rightBoundary))))))) := by
        congr 1 <;> simp [rightSum, Finset.sum_range_succ, Function.iterate_succ_apply',
          pow_zero, pow_one]
      rw [hz]
      convert! h using 1
      funext z
      simp only [trialRight, Function.iterate_zero_apply, Nat.zero_add]
  | succ n ih =>
      have hh := inverse_transfer_jet (ih (m+1))
      rw [right_partial] at hh
      have he : e0 ((transfer (core fixedSector 1))^[m+1]
          (vecMulVec rightBoundary (star rightBoundary))) =
          (transfer (core fixedSector 1))^[m] (vecMulVec rightBoundary (star rightBoundary)) := by
        rw [Function.iterate_succ_apply', e0_apply]
        exact inverse_transfer_left fixed_regular (by norm_num) _
      rw [he] at hh
      convert! hh using 1
      · funext z
        simp only [trialRight, Function.iterate_succ_apply']
        simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · rw [rightSum_succ, rightSum_succ]
        simp only [map_neg, neg_add_rev]
        congr 1 <;> abel

private lemma left_forward_coords (n : ℕ) :
    leftTarget fixedSector 1 leftBoundary n =
      hc (fun i => 2^(n+1) * (lv n i : ℝ)) 0 := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [leftTarget, leftBoundary, hc, lv, vecMulVec_apply]
  | succ n ih =>
      simp only [leftTarget, Function.iterate_succ_apply']
      change dualTransfer (core fixedSector 1) (leftTarget fixedSector 1 leftBoundary n) = _
      rw [ih, dual_hc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hc, lv, pow_succ]
      all_goals push_cast
      all_goals ring

private lemma right_forward_coords (n : ℕ) :
    (transfer (core fixedSector 1))^[n] (vecMulVec rightBoundary (star rightBoundary)) =
      hc (fun i => 2^(n+1) * (ry n i : ℝ)) (-2 * (-2)^n) := by
  induction n with
  | zero => ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [rightBoundary, hc, ry, vecMulVec_apply] <;> ring
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, transfer_hc]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hc, ry, pow_succ]
      all_goals push_cast
      all_goals ring

private lemma left_inverse_read (n : ℕ) (x : Fin 3 → ℝ) (v : ℝ) :
    lread ((s0^n) (hc x v)) = (∑ i : Fin 3, (lu n i : ℝ) * x i) / 10^n := by
  induction n generalizing x v with
  | zero => simp [lread_hc, lu, Fin.sum_univ_three]; ring
  | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, s0_hc, ih]
      rw [lu]
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
        pow_succ]
      field_simp
      ring

private lemma lu_lv_orthogonal (n : ℕ) : ∑ i : Fin 3, lu n i * lv n i = 0 := by
  induction n with
  | zero => norm_num [lu, lv, Fin.sum_univ_three]
  | succ n ih =>
      rw [lu, lv]
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one] at ih ⊢
      linear_combination 5 * ih

private lemma right_inverse_coords (n : ℕ) (u v : ℝ) :
    (e0^(n+1)) (hc ![0,0,u] v) =
      hc (fun i => u * (rx n i : ℝ) / (2 * 10^n)) ((-1/2)^(n+1) * v) := by
  induction n with
  | zero =>
      rw [pow_one, e0_hc]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [hc, rx] <;> ring
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, e0_hc, rx]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hc, pow_succ, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div]
      all_goals push_cast
      all_goals field_simp
      all_goals ring

private def leftSlope (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.range p, 2 * ((lu (k+1) 0 : ℝ) * (lv (k+1) 1 : ℝ) +
    (lu (k+1) 1 : ℝ) * (lv (k+1) 0 : ℝ)) / 5^(k+1)
private def rightSlope (q : ℕ) : ℝ :=
  ∑ k ∈ Finset.range q, 2 * (-1)^(k+2) *
    ((rx (k+1) 0 : ℝ) / 5^(k+1) + (ry (k+2) 2 : ℝ))

private lemma U_scale (n : ℕ) : (U n : ℝ) = 5^n * leftSlope n := by
  induction n with
  | zero => simp [U, leftSlope]
  | succ n ih =>
      rw [U]
      push_cast
      rw [ih]
      simp only [leftSlope, Finset.sum_range_succ, pow_succ]
      field_simp <;> ring

private lemma V_scale (n : ℕ) : (V n : ℝ) = 5^n * rightSlope n := by
  induction n with
  | zero => simp [V, rightSlope]
  | succ n ih =>
      rw [V]
      push_cast
      rw [ih]
      simp only [rightSlope, Finset.sum_range_succ, pow_succ]
      field_simp <;> ring


private lemma ten_pow (n : ℕ) : (10 : ℝ)^n = 2^n * 5^n := by
  rw [← mul_pow]
  norm_num

private lemma left_radial_term (n : ℕ) :
    lread ((s0^n) (radial (leftTarget fixedSector 1 leftBoundary n))) =
      -2 * ((lu n 0 : ℝ) * (lv n 1 : ℝ) + (lu n 1 : ℝ) * (lv n 0 : ℝ)) / 5^n := by
  rw [left_forward_coords, radial_hc, left_inverse_read]
  have ho : ∑ i : Fin 3, (lu n i : ℝ) * (lv n i : ℝ) = 0 := by
    exact_mod_cast lu_lv_orthogonal n
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one] at ho ⊢
  rw [ten_pow, pow_succ]
  field_simp
  linear_combination ho

private lemma left_angular_term (n : ℕ) :
    lread ((s0^n) (angular (leftTarget fixedSector 1 leftBoundary n))) = 0 := by
  rw [left_forward_coords, angular_hc, left_inverse_read]
  simp [Fin.sum_univ_three]

private lemma left_read (p : ℕ) :
    lread (-leftSum radial p 0) = leftSlope p ∧ lread (leftSum angular p 0) = 0 := by
  simp only [leftSum, map_sum, map_neg, Nat.zero_add]
  constructor
  · simp only [left_radial_term, leftSlope, ← Finset.sum_neg_distrib, neg_div,
      neg_mul, neg_neg]
  · simp only [left_angular_term, Finset.sum_const_zero]

private lemma right_angular_term (n : ℕ) :
    rread ((e0^(n+2)) (angular ((transfer (core fixedSector 1))^[n+2]
      (vecMulVec rightBoundary (star rightBoundary))))) =
      -(2 * (-1)^(n+2) * ((rx (n+1) 0 : ℝ)/5^(n+1) + (ry (n+2) 2 : ℝ))) := by
  rw [right_forward_coords, angular_hc,
    show n+2 = (n+1)+1 by omega, right_inverse_coords, rread_hc]
  try simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  rw [ten_pow]
  simp only [show (-2 : ℝ) = -1 * 2 by ring, mul_pow, div_pow, pow_succ]
  field_simp
  ring

private lemma right_angular_initial :
    rread (angular (vecMulVec rightBoundary (star rightBoundary))) = 0 ∧
      rread (e0 (angular (transfer (core fixedSector 1)
        (vecMulVec rightBoundary (star rightBoundary))))) = 0 := by
  have h0 := right_forward_coords 0
  have h1 := right_forward_coords 1
  simp only [Function.iterate_zero_apply, Function.iterate_one] at h0 h1
  constructor
  · rw [h0, angular_hc, rread_hc]
    norm_num [ry]
  · rw [h1, angular_hc, e0_hc, rread_hc]
    norm_num [ry]

private lemma right_read (q : ℕ) : rread (-rightSum angular q 0) = rightSlope q := by
  have he (n : ℕ) :
      (∑ k ∈ Finset.range (n+2), rread ((e0^k) (angular
        ((transfer (core fixedSector 1))^[k] (vecMulVec rightBoundary (star rightBoundary)))))) =
        -rightSlope n := by
    induction n with
    | zero =>
        simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
          pow_zero, pow_one, ContinuousLinearMap.one_apply, Function.iterate_zero_apply,
          Function.iterate_one, zero_add, rightSlope, neg_zero]
        rw [right_angular_initial.1, right_angular_initial.2]
        ring
    | succ n ih =>
        rw [show n+1+2 = (n+2)+1 by omega, Finset.sum_range_succ, ih,
          right_angular_term]
        simp only [rightSlope, Finset.sum_range_succ]
        ring
  simp only [rightSum, map_neg, map_sum, Nat.zero_add]
  rw [he]
  exact neg_neg _

private def detD (X : Bond) (a : ℂ →L[ℝ] Bond) : ℂ →L[ℝ] ℂ :=
  X 1 1 • ((entry 0 0).comp a) + X 0 0 • ((entry 1 1).comp a) -
    (X 1 0 • ((entry 0 1).comp a) + X 0 1 • ((entry 1 0).comp a))

private lemma determinant_deriv {f : ℂ → Bond} {a : ℂ →L[ℝ] Bond}
    (hf : HasFDerivAt f a 1) : HasFDerivAt (fun z => (f z).det) (detD (f 1) a) 1 := by
  have h i j := (entry i j).hasFDerivAt.comp 1 hf
  convert! ((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0)) using 1
  · funext z
    exact det_fin_two _
  · ext w
    simp [detD, entry_apply]
    ring

private def tri (L C R : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight ((L : ℂ) + Complex.I * C) +
    Complex.imCLM.smulRight (Complex.I * R)

private lemma tri_apply (L C R : ℝ) (w : ℂ) :
    tri L C R w = ((L*w.re : ℝ) : ℂ) + Complex.I * ((C*w.re+R*w.im : ℝ) : ℂ) := by
  simp [tri]
  push_cast
  ring

private lemma residual_deriv (p q : ℕ) :
    HasFDerivAt
      (residual fixedSector p q (leftTarget fixedSector 1 leftBoundary p)
        (rightTarget fixedSector 1 rightBoundary q))
      (tri (leftSlope p) (rread (-rightSum radial q 0)) (rightSlope q)) 1 := by
  have hl := left_jets p 0
  have hr := right_jets q 0
  simp only [Nat.add_zero] at hl hr
  have hdl := Complex.reCLM.hasFDerivAt.comp 1 (determinant_deriv hl)
  have hdr := Complex.reCLM.hasFDerivAt.comp 1 (determinant_deriv hr)
  have hc (f : ℂ → ℝ) (d : ℂ →L[ℝ] ℝ) (h : HasFDerivAt f d 1) :=
    Complex.ofRealCLM.hasFDerivAt.comp 1 h
  have h := (hc _ _ hdl).add ((hc _ _ hdr).const_mul Complex.I)
  convert! h using 1
  ext w
  rw [left_at_target fixed_regular (by norm_num : (1 : ℂ) ≠ 0),
    right_at_target fixed_regular (by norm_num : (1 : ℂ) ≠ 0)]
  simp only [tri_apply, ContinuousLinearMap.comp_apply, detD, jet_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, entry_apply]
  have hll := left_read p
  have hrr := right_read q
  simp only [lread, rread, ContinuousLinearMap.comp_apply, entry_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, Complex.reCLM_apply, Matrix.neg_apply,
    Complex.add_re, Complex.sub_re, Complex.neg_re, smul_eq_mul, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
    Complex.sub_im, Complex.neg_im] at hll hrr
  apply Complex.ext <;>
    simp [lread, rread, entry_apply, leftBoundary, rightBoundary, vecMulVec_apply,
      Complex.mul_re, Complex.mul_im]
  · linear_combination -(w.re) * hll.1 - w.im * hll.2
  · linear_combination -(w.im) * hrr

private def triInverse (L C R : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight ((1/L : ℝ) : ℂ) +
    Complex.reCLM.smulRight (Complex.I * ((-C/(L*R) : ℝ) : ℂ)) +
    Complex.imCLM.smulRight (Complex.I * ((1/R : ℝ) : ℂ))

private lemma triInverse_apply (L C R : ℝ) (w : ℂ) :
    triInverse L C R w = ((w.re/L : ℝ) : ℂ) +
      Complex.I * (((w.im-C*w.re/L)/R : ℝ) : ℂ) := by
  simp only [triInverse, ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, Complex.real_smul, div_eq_mul_inv,
    _root_.mul_inv_rev, map_mul, map_neg, Complex.ofReal_sub]
  push_cast
  ring

private def triEquiv (L C R : ℝ) (hL : L ≠ 0) (hR : R ≠ 0) : ℂ ≃L[ℝ] ℂ where
  toLinearEquiv :=
    { (tri L C R).toLinearMap with
      invFun := triInverse L C R
      left_inv := by
        intro w
        apply Complex.ext <;> simp [triInverse_apply, tri_apply, Complex.mul_re, Complex.mul_im]
        all_goals field_simp [hL, hR] <;> ring
      right_inv := by
        intro w
        apply Complex.ext <;> simp [triInverse_apply, tri_apply, Complex.mul_re, Complex.mul_im]
        all_goals field_simp [hL, hR] <;> ring }
  continuous_toFun := (tri L C R).continuous
  continuous_invFun := (triInverse L C R).continuous

/-- One actual fixed-target witness, uniformly in both positive exterior lengths.
The integer certificate is consumed in constructing the ordinary real inverse derivative. -/
theorem interior_q2_fixed_target_witness (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (leftTarget fixedSector 1 leftBoundary p).PosDef ∧
    (rightTarget fixedSector 1 rightBoundary q).PosDef ∧
    trialLeft fixedSector p (leftTarget fixedSector 1 leftBoundary p) 1 =
      vecMulVec (star leftBoundary) leftBoundary ∧
    trialRight fixedSector q (rightTarget fixedSector 1 rightBoundary q) 1 =
      vecMulVec rightBoundary (star rightBoundary) ∧
    residual fixedSector p q (leftTarget fixedSector 1 leftBoundary p)
      (rightTarget fixedSector 1 rightBoundary q) 1 = 0 ∧
    ∃ (L C R : ℝ) (e : ℂ ≃L[ℝ] ℂ) (u v : ℤ),
      (∀ w, e w = ((L*w.re : ℝ) : ℂ) + Complex.I * ((C*w.re+R*w.im : ℝ) : ℂ)) ∧
      HasFDerivAt (residual fixedSector p q (leftTarget fixedSector 1 leftBoundary p)
        (rightTarget fixedSector 1 rightBoundary q)) (e : ℂ →L[ℝ] ℂ) 1 ∧
      (!![L, 0; C, R] : Matrix (Fin 2) (Fin 2) ℝ).det = L*R ∧ L*R ≠ 0 ∧
      5^p*L = (u : ℝ) ∧ 5^q*R = (v : ℝ) ∧
      5^(p+q)*(L*R) = ((u*v : ℤ) : ℝ) ∧
      ((u*v : ℤ) : ZMod 5) = 2*(-1)^(q+1)*3^q := by
  obtain ⟨hu, hv, hmod⟩ := certificate_nonzero p q hp hq
  have huR : (U p : ℝ) ≠ 0 := by exact_mod_cast hu
  have hvR : (V q : ℝ) ≠ 0 := by exact_mod_cast hv
  have hL : leftSlope p ≠ 0 := by intro h; apply huR; rw [U_scale, h, mul_zero]
  have hR : rightSlope q ≠ 0 := by intro h; apply hvR; rw [V_scale, h, mul_zero]
  refine ⟨left_pd p hp, right_pd q hq,
    left_at_target fixed_regular (by norm_num) p leftBoundary,
    right_at_target fixed_regular (by norm_num) q rightBoundary,
    residual_at_target fixed_regular (by norm_num) p q leftBoundary rightBoundary, ?_⟩
  refine ⟨leftSlope p, rread (-rightSum radial q 0), rightSlope q,
    triEquiv (leftSlope p) (rread (-rightSum radial q 0)) (rightSlope q) hL hR, U p, V q, ?_⟩
  refine ⟨?_, ?_, ?_, mul_ne_zero hL hR,
    (U_scale p).symm, (V_scale q).symm, ?_, hmod⟩
  · exact tri_apply _ _ _
  · exact residual_deriv p q
  · simp [det_fin_two]
  · rw [Int.cast_mul, U_scale, V_scale, pow_add]
    ring

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorTransversality
