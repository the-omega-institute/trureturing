/- GID: D5/S3/Quantum/QuantumChannels/OriginalQutritGap
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/OriginalQutritGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original qutrit commutator bounds on the full complex traceless space. -/

import D5.S3.Quantum.Matrix.CommutatorGap
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
The original two-swap qutrit channel acts on the complete complex matrix space.

admission_basis: escape-witness
proof_shape: original_two_sided: content
escape_witness: the public two-sided estimate, obtained by the live two-loss
estimate for the same original conjugation between the two copies of lambda squared.
The finite coordinate identities, centering and scalar normalization are inline
suppliers, not separate admission witnesses. All definitions below are consumed
by original_two_sided through its statement or proof.

Direct frozen mathematical suppliers:
* D5/S3/Quantum/Matrix/CartesianVariance:
  sha256:06de6afacfd131644997a44d75eadad1545751e1aa16e915f5a150f1f7a8413e
* D5/S3/Quantum/Matrix/CommutatorGap:
  sha256:3bde7128103bfd666f7f53a158f9bc0aca510c55c6be24d1349fdc75a28d9f2b
* D5/S3/Weil/ZetaLinear/RankTrace:
  sha256:462372f25ef2d3c4c436e96621fb80749b1992250c27989866e6ba4a1756b29b

Utility is none: the result is a uniform analytic estimate on the continuous
unitary family, not an enumeration, checker, numeric reduction or finite instance.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexInnerProductSpace ComplexOrder

namespace D5.S3.Quantum.QuantumChannels.OriginalQutritGap

open D5.S3.Quantum.Matrix.CartesianVariance
open D5.S3.Quantum.Matrix.CommutatorGap

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ
abbrev HS := EuclideanSpace ℂ (Fin 3 × Fin 3)

def U : Mat := !![1,0,0; 0,0,1; 0,1,0]
def W : Mat := !![0,1,0; 1,0,0; 0,0,1]
def xi : Fin 3 → ℂ := fun _ => (Real.sqrt 3 : ℂ)⁻¹
def Pxi : Mat := Matrix.vecMulVec xi (star xi)

def conjugation (A : Mat) : Mat →ₗ[ℂ] Mat where
  toFun X := A * X * Aᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

def dephase : Mat →ₗ[ℂ] Mat :=
  (1/2 : ℂ) • (LinearMap.id + conjugation W)

def lambda : Mat →ₗ[ℂ] Mat := (conjugation U).comp dephase

def thetaMatrix (N : Matrix.unitaryGroup (Fin 3) ℂ) : Mat →ₗ[ℂ] Mat :=
  lambda.comp (lambda.comp ((conjugation N).comp (lambda.comp lambda)))

def traceHS : HS →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin 3) ℂ ℂ).comp (vectorize 3).symm.toLinearMap

def H0 : Submodule ℂ HS := traceHS.ker

-- The transported subtype map uses finite-dimensional continuity synthesis.
set_option synthInstance.maxHeartbeats 100000 in
def theta (N : Matrix.unitaryGroup (Fin 3) ℂ) : H0 →L[ℂ] H0 := by
  let L := (vectorize 3).toLinearMap.comp
    ((thetaMatrix N).comp (vectorize 3).symm.toLinearMap)
  have ht (X : Mat) : (lambda X).trace = X.trace := by
    change (U * ((1/2 : ℂ) • (X + W * X * Wᴴ)) * Uᴴ).trace = X.trace
    simp only [
      Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fin.sum_univ_succ]
    norm_num [U, W]
    <;> ring
  have hn (X : Mat) : (conjugation (N : Mat) X).trace = X.trace := by
    change ((N : Mat) * X * (N : Mat)ᴴ).trace = X.trace
    have hunit : (N : Mat)ᴴ * (N : Mat) = 1 := Unitary.star_mul_self_of_mem N.property
    rw [Matrix.trace_mul_cycle, hunit, Matrix.one_mul]
  exact (L.restrict (by
    intro x hx
    change (thetaMatrix N ((vectorize 3).symm x)).trace = 0
    change (((vectorize 3).symm x).trace = 0) at hx
    simpa only [thetaMatrix, LinearMap.comp_apply, ht, hn] using hx)).toContinuousLinearMap

def delta (N : Matrix.unitaryGroup (Fin 3) ℂ) : ℝ :=
  ‖vectorize 3 ((N : Mat) * Pxi - Pxi * (N : Mat))‖ ^ 2

-- Coordinate expansion of the complex energy identity and the norm estimate
-- are kept inside the theorem; these options are local to their elaboration.
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem original_two_sided (N : Matrix.unitaryGroup (Fin 3) ℂ) :
    delta N / 8 ≤ 1 - ‖theta N‖ ^ 2 ∧
      1 - ‖theta N‖ ^ 2 ≤ (3/2 : ℝ) * delta N := by
  let M : Mat := Matrix.of (fun i j => if i = j then 0 else (Real.sqrt 6 : ℂ)⁻¹)
  let v : HS := vectorize 3 M
  let A : HS →ₗ[ℂ] HS := (vectorize 3).toLinearMap.comp
    (lambda.comp (lambda.comp (vectorize 3).symm.toLinearMap))
  let R : HS →ₗ[ℂ] HS := (vectorize 3).toLinearMap.comp
    ((conjugation N).comp (vectorize 3).symm.toLinearMap)
  have hl (X : Mat) : lambda X =
      !![(X 0 0 + X 1 1)/2, (X 0 2 + X 1 2)/2, (X 0 1 + X 1 0)/2;
         (X 2 0 + X 2 1)/2, X 2 2, (X 2 1 + X 2 0)/2;
         (X 1 0 + X 0 1)/2, (X 1 2 + X 0 2)/2, (X 1 1 + X 0 0)/2] := by
    change U * ((1/2 : ℂ) • (X + W * X * Wᴴ)) * Uᴴ = _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ, U, W]
    <;> norm_num <;> ring
  have energy (X : Mat) :
      4 * ‖vectorize 3 (lambda (lambda X))‖ ^ 2 =
        ‖vectorize 3 (dephase X)‖ ^ 2 + ‖X.trace‖ ^ 2 +
          (1/2 : ℝ) * ‖X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1‖ ^ 2 := by
    simp only [hl, vectorize_norm_sq, frobSq_eq_sum]
    simp only [dephase, conjugation, LinearMap.smul_apply,
      LinearMap.add_apply, LinearMap.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.add_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, U, W]
    norm_num [Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, Pi.add_apply,
      Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    <;> ring
  have hv : ‖v‖ = 1 := by
    change ‖vectorize 3 M‖ = 1
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [vectorize_norm_sq, frobSq_eq_sum]
    norm_num [M, Fin.sum_univ_succ,
      Complex.normSq_apply, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
      ← inv_pow]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  have hr (x : HS) : ‖R x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    let X := (vectorize 3).symm x
    change ‖vectorize 3 ((N : Mat) * X * (N : Mat)ᴴ)‖ ^ 2 = ‖x‖ ^ 2
    rw [vectorize_norm_sq, ← (vectorize 3).apply_symm_apply x, vectorize_norm_sq]
    change RHLinalg.frobSq ((N : Mat) * X * ((star N : Matrix.unitaryGroup (Fin 3) ℂ) : Mat)) = _
    rw [frobSq_unitary_right, frobSq_unitary_left]
  have hav : A v = v := by
    change vectorize 3 (lambda (lambda M)) = vectorize 3 M
    congr 1
    simp only [hl]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [M] <;> ring
  let q : HS →ₗ[ℂ] HS := LinearMap.id - (innerₛₗ ℂ v).smulRight v
  have hq (x : HS) : q x = x - inner ℂ v x • v := rfl
  have horth (x : HS) : inner ℂ v (q x) = 0 := by
    rw [hq, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
    simp
  have hpyth (x : HS) : ‖x‖ ^ 2 = ‖inner ℂ v x‖ ^ 2 + ‖q x‖ ^ 2 := by
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      (inner ℂ v x • v) (q x) (by simp [inner_smul_left, horth])
    have he : inner ℂ v x • v + q x = x := by rw [hq]; module
    rw [he, norm_smul, hv, mul_one] at hh
    simpa only [pow_two] using hh
  have hqle (x : HS) : ‖q x‖ ≤ ‖x‖ := by
    have := hpyth x
    nlinarith [sq_nonneg ‖inner ℂ v x‖, norm_nonneg (q x), norm_nonneg x]
  have hs6 : (Real.sqrt 6 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne'
  have hcn (K : Matrix.unitaryGroup (Fin 3) ℂ) (X : Mat) :
      ‖vectorize 3 ((K : Mat) * X * (K : Mat)ᴴ)‖ = ‖vectorize 3 X‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [vectorize_norm_sq, vectorize_norm_sq]
    change RHLinalg.frobSq ((K : Mat) * X * ((star K : Matrix.unitaryGroup (Fin 3) ℂ) : Mat)) = _
    rw [frobSq_unitary_right, frobSq_unitary_left]
  have hw : W ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [W, Matrix.mul_apply, Fin.sum_univ_succ]
  have hb (X : Mat) : ‖vectorize 3 (dephase X)‖ ≤ ‖vectorize 3 X‖ := by
    calc
      ‖vectorize 3 (dephase X)‖ = (1/2 : ℝ) *
          ‖vectorize 3 X + vectorize 3 (W * X * Wᴴ)‖ := by
        change ‖vectorize 3 ((1/2 : ℂ) • (X + W * X * Wᴴ))‖ = _
        rw [map_smul, map_add, norm_smul]
        norm_num
      _ ≤ (1/2 : ℝ) * (‖vectorize 3 X‖ + ‖vectorize 3 (W * X * Wᴴ)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ = ‖vectorize 3 X‖ := by rw [hcn ⟨W, hw⟩ X]; ring
  have hpair (X : Mat) : (Real.sqrt 6 : ℂ) * inner ℂ v (vectorize 3 X) =
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    change (Real.sqrt 6 : ℂ) * inner ℂ (vectorize 3 M) (vectorize 3 X) = _
    rw [matrix_pairing]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]
    norm_num [M]
    field_simp
    <;> ring
  have htv : traceHS v = 0 := by
    change M.trace = 0
    norm_num [M, Matrix.trace, Fin.sum_univ_succ]
  have htA (x : HS) : traceHS (A x) = traceHS x := by
    let X := (vectorize 3).symm x
    change (lambda (lambda X)).trace = X.trace
    simp only [hl, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ]
    norm_num
    ring
  have htR (x : HS) : traceHS (R x) = traceHS x := by
    let X := (vectorize 3).symm x
    change ((N : Mat) * X * (N : Mat)ᴴ).trace = X.trace
    have hunit : (N : Mat)ᴴ * (N : Mat) = 1 := Unitary.star_mul_self_of_mem N.property
    rw [Matrix.trace_mul_cycle, hunit, Matrix.one_mul]
  have hai (x : HS) : inner ℂ v (A x) = inner ℂ v x := by
    apply mul_left_cancel₀ hs6
    let X := (vectorize 3).symm x
    have hx : vectorize 3 X = x := (vectorize 3).apply_symm_apply x
    rw [← hx]
    change (Real.sqrt 6 : ℂ) * inner ℂ v (vectorize 3 (lambda (lambda X))) = _
    rw [hpair, hpair]
    simp only [hl]
    norm_num
    ring
  have htq (x : HS) : traceHS (q x) = traceHS x := by
    rw [hq, map_sub, map_smul, htv, smul_zero, sub_zero]
  have henergy (x : HS) (ht : traceHS x = 0) :
      4 * ‖A x‖ ^ 2 ≤ ‖x‖ ^ 2 + 3 * ‖inner ℂ v x‖ ^ 2 := by
    let X := (vectorize 3).symm x
    have hx : vectorize 3 X = x := (vectorize 3).apply_symm_apply x
    have he := energy X
    have hp := congrArg (fun z : ℂ => ‖z‖ ^ 2) (hpair X)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), hx] at hp
    have htr : X.trace = 0 := ht
    rw [htr, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at he
    have hbn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hb X)
    change 4 * ‖vectorize 3 (lambda (lambda X))‖ ^ 2 ≤ _
    rw [hx] at hbn
    nlinarith
  have hloss (x : HS) (ht : traceHS x = 0) :
      (3/4 : ℝ) * ‖q x‖ ^ 2 ≤ ‖x‖ ^ 2 - ‖A x‖ ^ 2 := by
    nlinarith [henergy x ht, hpyth x]
  have hhalf (x : HS) (ht : traceHS x = 0) : ‖A (q x)‖ ≤ ‖q x‖ / 2 := by
    have he := henergy (q x) (by rw [htq, ht])
    rw [horth, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at he
    nlinarith [norm_nonneg (A (q x)), norm_nonneg (q x)]
  let eta : ℝ := ‖q (R v)‖
  have heta0 : 0 ≤ eta := norm_nonneg _
  have heta1 : eta ≤ 1 := by
    have hh := hqle (R v)
    rwa [hr, hv] at hh
  have heta2 : eta ^ 2 ≤ 1 := by nlinarith
  have scalar (a h b e : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) (hb : 0 ≤ b)
      (he : 0 ≤ e) (he1 : e ^ 2 ≤ 1) (htri : a * e ≤ b + h / 2)
      (hpy : a ^ 2 + h ^ 2 = 1) : e ^ 2 ≤ (9/4 : ℝ) * (h ^ 2 + b ^ 2) := by
    have hs : (a * e) ^ 2 ≤ (b + h / 2) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg ha he) (by linarith only [hb, hh])).mpr htri
    have hcs : a ^ 2 * e ^ 2 ≤ (5/4 : ℝ) * (h ^ 2 + b ^ 2) := by
      nlinarith only [hs, sq_nonneg (b / 2 - h)]
    have hm := mul_le_mul_of_nonneg_left he1 (sq_nonneg h)
    have hmu := congrArg (fun z : ℝ => z * e ^ 2) hpy
    nlinarith only [hcs, hm, hmu, sq_nonneg b]
  have hpoint (x : HS) (ht : traceHS x = 0) (hx : ‖x‖ = 1) :
      eta ^ 2 / 3 ≤ 1 - ‖A (R (A x))‖ ^ 2 := by
    let a := inner ℂ v x
    let h := ‖q x‖
    let beta := ‖q (R (A x))‖
    have hh0 : 0 ≤ h := norm_nonneg _
    have hb0 : 0 ≤ beta := norm_nonneg _
    have hxdec : x = a • v + q x := by rw [hq]; module
    have hdec : A x = a • v + A (q x) := by
      calc
        A x = A (a • v + q x) := congrArg A hxdec
        _ = _ := by rw [map_add, map_smul, hav]
    have hadd : q (R (A x)) = a • q (R v) + q (R (A (q x))) := by
      simp only [hdec, map_add, map_smul]
    have hid : a • q (R v) = q (R (A x)) - q (R (A (q x))) := by
      rw [hadd]
      module
    have hrem : ‖q (R (A (q x)))‖ ≤ h / 2 := by
      calc
        _ ≤ ‖R (A (q x))‖ := hqle _
        _ = ‖A (q x)‖ := hr _
        _ ≤ h / 2 := hhalf x ht
    have htri : ‖a‖ * eta ≤ beta + h / 2 := by
      have hh := norm_sub_le (q (R (A x))) (q (R (A (q x))))
      rw [← hid, norm_smul] at hh
      change ‖a‖ * eta ≤ beta + ‖q (R (A (q x)))‖ at hh
      generalize ht : ‖q (R (A (q x)))‖ = tail at hh hrem
      linarith only [hh, hrem]
    have hpy : ‖a‖ ^ 2 + h ^ 2 = 1 := by
      have hh := hpyth x
      rw [hx] at hh
      simpa only [one_pow] using hh.symm
    have he : eta ^ 2 ≤ (9/4 : ℝ) * (h ^ 2 + beta ^ 2) :=
      scalar ‖a‖ h beta eta (norm_nonneg a) hh0 hb0 heta0 heta2 htri hpy
    have h1 := hloss x ht
    have h2 := hloss (R (A x)) (by rw [htR, htA, ht])
    rw [hr] at h2
    rw [hx] at h1
    change (3/4 : ℝ) * h ^ 2 ≤ _ at h1
    change (3/4 : ℝ) * beta ^ 2 ≤ _ at h2
    nlinarith only [h1, h2, he]
  have htheta (x : H0) : ((theta N) x : HS) = A (R (A (x : HS))) := by
    change vectorize 3 (thetaMatrix N ((vectorize 3).symm (x : HS))) = _
    simp only [A, R, thetaMatrix, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hnormbound : ‖theta N‖ ≤ Real.sqrt (1 - eta ^ 2 / 3) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (Real.sqrt_nonneg _)
    intro x hx
    have ht : traceHS (x : HS) = 0 := x.property
    have hp := hpoint x ht hx
    have hs := Real.sq_sqrt (show 0 ≤ 1 - eta ^ 2 / 3 by nlinarith)
    have hval : ‖theta N x‖ = ‖A (R (A (x : HS)))‖ := by
      change ‖((theta N) x : HS)‖ = _
      rw [htheta]
    rw [hval]
    nlinarith [norm_nonneg (A (R (A (x : HS)))), Real.sqrt_nonneg (1 - eta ^ 2 / 3)]
  have hlower : eta ^ 2 / 3 ≤ 1 - ‖theta N‖ ^ 2 := by
    have hs := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hnormbound
    rw [Real.sq_sqrt (show 0 ≤ 1 - eta ^ 2 / 3 by nlinarith)] at hs
    linarith
  have hupper : 1 - ‖theta N‖ ^ 2 ≤ eta ^ 2 := by
    let vv : H0 := ⟨v, htv⟩
    have htest := (theta N).unit_le_opNorm (x := vv) (show ‖vv‖ ≤ 1 by
      change ‖v‖ ≤ 1
      rw [hv])
    change ‖((theta N) vv : HS)‖ ≤ _ at htest
    rw [htheta] at htest
    change ‖A (R (A v))‖ ≤ _ at htest
    rw [hav] at htest
    have hi := norm_inner_le_norm (𝕜 := ℂ) v (A (R v))
    rw [hai, hv, one_mul] at hi
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hi.trans htest)
    have hp := hpyth (R v)
    rw [hr, hv] at hp
    change 1 ^ 2 = ‖inner ℂ v (R v)‖ ^ 2 + eta ^ 2 at hp
    nlinarith
  have hs6sq : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hs3mul : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hPe : Pxi = Matrix.of (fun _ _ => (1/3 : ℂ)) := by
    ext i j
    change (Real.sqrt 3 : ℂ)⁻¹ * star ((Real.sqrt 3 : ℂ)⁻¹) = (1/3 : ℂ)
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    rw [← mul_inv, hs3mul]
    norm_num
  let c : ℂ := (Real.sqrt 6 : ℂ) / 3
  let p : HS := vectorize 3 Pxi
  let e : HS := vectorize 3 (1 : Mat)
  have hc2 : ‖c‖ ^ 2 = (2/3 : ℝ) := by
    norm_num [c, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  have hpM : Pxi = (1/3 : ℂ) • (1 : Mat) + c • M := by
    rw [hPe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [c, M, Matrix.smul_apply, Matrix.add_apply]
    <;> field_simp <;> ring
  have hp : p = (1/3 : ℂ) • e + c • v := by
    change vectorize 3 Pxi = _
    rw [hpM, map_add, map_smul, map_smul]
  have hnright : (N : Mat) * (N : Mat)ᴴ = 1 := Unitary.mul_star_self_of_mem N.property
  have heR : R e = e := by
    change vectorize 3 ((N : Mat) * 1 * (N : Mat)ᴴ) = vectorize 3 (1 : Mat)
    rw [Matrix.mul_one, hnright]
  have heinner (x : HS) : inner ℂ e x = traceHS x := by
    obtain ⟨X, rfl⟩ := (vectorize 3).surjective x
    change inner ℂ (vectorize 3 (1 : Mat)) (vectorize 3 X) = X.trace
    rw [matrix_pairing, Matrix.conjTranspose_one, Matrix.one_mul]
  have hee : inner ℂ e e = (3 : ℂ) := by
    rw [heinner]
    change (1 : Mat).trace = 3
    norm_num [Matrix.trace, Fin.sum_univ_succ]
  have hev : inner ℂ e v = 0 := by rw [heinner, htv]
  have heRv : inner ℂ e (R v) = 0 := by rw [heinner, htR, htv]
  have hve : inner ℂ v e = 0 := by rw [← inner_conj_symm, hev]; simp
  have hpformula : inner ℂ p (R p) = (1/3 : ℂ) + (2/3 : ℂ) * inner ℂ v (R v) := by
    rw [hp, map_add, map_smul, map_smul, heR]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      hee, hev, heRv, hve]
    norm_num [c, _root_.map_ofNat]
    linear_combination (inner ℂ v (R v) / 9) * hs6sq
  have hPpos : Pxi.PosSemidef := Matrix.posSemidef_vecMulVec_self_star xi
  have hPherm : Pxiᴴ = Pxi := hPpos.isHermitian.eq
  have hpos : 0 ≤ (inner ℂ p (R p)).re := by
    change 0 ≤ (inner ℂ (vectorize 3 Pxi)
      (vectorize 3 ((N : Mat) * Pxi * (N : Mat)ᴴ))).re
    rw [matrix_pairing, hPherm]
    exact RHLinalg.trace_mul_nonneg_of_posSemidef hPpos
      (hPpos.mul_mul_conjTranspose_same (N : Mat))
  let t : ℝ := (inner ℂ v (R v)).re
  have htlow : -(1/2 : ℝ) ≤ t := by
    rw [hpformula] at hpos
    norm_num [Complex.mul_re] at hpos
    change -(1/2 : ℝ) ≤ (inner ℂ v (R v)).re
    linarith only [hpos]
  have hMherm : Mᴴ = M := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [M, Matrix.conjTranspose_apply]
    · change star (if j = i then (0 : ℂ) else (Real.sqrt 6 : ℂ)⁻¹) =
        if i = j then 0 else (Real.sqrt 6 : ℂ)⁻¹
      rw [if_neg (Ne.symm h), if_neg h, star_inv₀]
      rw [show star (Real.sqrt 6 : ℂ) = (Real.sqrt 6 : ℂ) from Complex.conj_ofReal _]
  have hRMherm : ((N : Mat) * M * (N : Mat)ᴴ)ᴴ = (N : Mat) * M * (N : Mat)ᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hMherm,
      Matrix.mul_assoc]
  have htstar : star (inner ℂ v (R v)) = inner ℂ v (R v) := by
    change star (inner ℂ (vectorize 3 M)
      (vectorize 3 ((N : Mat) * M * (N : Mat)ᴴ))) =
        inner ℂ (vectorize 3 M) (vectorize 3 ((N : Mat) * M * (N : Mat)ᴴ))
    simp only [matrix_pairing, hMherm, ← Matrix.trace_conjTranspose]
    rw [Matrix.conjTranspose_mul, hMherm, hRMherm, Matrix.trace_mul_comm]
  have htim : (inner ℂ v (R v)).im = 0 := by
    have hh := congrArg Complex.im htstar
    simp only [Complex.star_def, Complex.conj_im] at hh
    linarith only [hh]
  have htreal : inner ℂ v (R v) = (t : ℂ) := by
    apply Complex.ext <;> simp [t, htim]
  have hcomm : delta N = ‖R p - p‖ ^ 2 := by
    change ‖vectorize 3 ((N : Mat) * Pxi - Pxi * (N : Mat))‖ ^ 2 =
      ‖vectorize 3 ((N : Mat) * Pxi * (N : Mat)ᴴ) - vectorize 3 Pxi‖ ^ 2
    rw [← map_sub]
    simp only [vectorize_norm_sq]
    have hh := frobSq_unitary_right ((N : Mat) * Pxi - Pxi * (N : Mat)) (star N)
    change RHLinalg.frobSq (((N : Mat) * Pxi - Pxi * (N : Mat)) * (N : Mat)ᴴ) = _ at hh
    rw [Matrix.sub_mul, Matrix.mul_assoc Pxi, hnright, Matrix.mul_one] at hh
    exact hh.symm
  have hpdiff : R p - p = c • (R v - v) := by
    rw [hp, map_add, map_smul, map_smul, heR]
    module
  have hdnorm : delta N = (2/3 : ℝ) * ‖R v - v‖ ^ 2 := by
    rw [hcomm, hpdiff, norm_smul, mul_pow, hc2]
  have hdiff : ‖R v - v‖ ^ 2 = 2 - 2 * t := by
    rw [norm_sub_sq (𝕜 := ℂ), hr, hv, inner_re_symm]
    change 1 ^ 2 - 2 * t + 1 ^ 2 = 2 - 2 * t
    ring
  have hd : delta N = (4/3 : ℝ) * (1 - t) := by rw [hdnorm, hdiff]; ring
  have hd0 : 0 ≤ delta N := sq_nonneg _
  have hd2 : delta N ≤ 2 := by nlinarith only [hd, htlow]
  have htδ : t = 1 - 3 * delta N / 4 := by linarith only [hd]
  have hetat : eta ^ 2 = 1 - t ^ 2 := by
    have hh := hpyth (R v)
    rw [hr, hv, htreal, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hh
    change 1 ^ 2 = t ^ 2 + eta ^ 2 at hh
    linarith only [hh]
  have hetapoly : eta ^ 2 = (3 * delta N / 4) * (2 - 3 * delta N / 4) := by
    rw [hetat, htδ]
    ring
  have hetaδlow : (3/8 : ℝ) * delta N ≤ eta ^ 2 := by
    have hh := mul_nonneg hd0 (sub_nonneg.mpr hd2)
    nlinarith only [hetapoly, hh]
  have hetaδup : eta ^ 2 ≤ (3/2 : ℝ) * delta N := by
    nlinarith only [hetapoly, sq_nonneg (delta N)]
  constructor
  · linarith only [hlower, hetaδlow]
  · linarith only [hupper, hetaδup]

end D5.S3.Quantum.QuantumChannels.OriginalQutritGap
