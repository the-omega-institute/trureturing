/- GID: D5/S3/Quantum/QuantumChannels/OriginalQutritWash
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/OriginalQutritWash
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native fixed-DU wash contracts every complex traceless qutrit input. -/

import D5.S3.Quantum.QuantumChannels.OriginalQutritGap
import D5.S3.Quantum.Entanglement.QutritWeylBlochNormSeparableBound
import D5.S3.Quantum.Tomography.PurityPythagorasDecomposition

/-! The fixed control mixes the invariant centered line into its contracting complement.
All norms in the statement are transported complex Hilbert--Schmidt norms. -/

noncomputable section
open Matrix
open scoped BigOperators ComplexInnerProductSpace ComplexOrder

namespace D5.S3.Quantum.QuantumChannels.OriginalQutritWash
open D5.S3.Quantum.Matrix.CartesianVariance
open D5.S3.Quantum.Matrix.CommutatorGap
open OriginalQutritGap

/-- The diagonal factor specifies the installed control, not a separate callable control. -/
def D : Mat := !![1,0,0; 0,1,0; 0,0,-1]

private theorem du_unitary : D * U ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [D, U, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

/-- The single installed unitary is DU. -/
def N : Matrix.unitaryGroup (Fin 3) ℂ := ⟨D * U, du_unitary⟩

/-- Four unread source calls surrounding the installed control. -/
def wash : Mat →ₗ[ℂ] Mat := thetaMatrix N

private theorem lambda_entries (X : Mat) : lambda X =
    !![(X 0 0 + X 1 1)/2, (X 0 2 + X 1 2)/2, (X 0 1 + X 1 0)/2;
       (X 2 0 + X 2 1)/2, X 2 2, (X 2 1 + X 2 0)/2;
       (X 1 0 + X 0 1)/2, (X 1 2 + X 0 2)/2, (X 1 1 + X 0 0)/2] := by
  change U * ((1/2 : ℂ) • (X + W * X * Wᴴ)) * Uᴴ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, U, W]
  <;> norm_num <;> ring

private theorem lambda_trace (X : Mat) : (lambda X).trace = X.trace := by
  rw [lambda_entries]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ]
  norm_num
  ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Uniform complex Hilbert--Schmidt contraction, all natural iterates, and the
original centered density prefactor for the installed DU wash. -/
theorem explicit_wash_bound :
    (∀ X : Mat, X.trace = 0 →
      ‖vectorize 3 (wash X)‖ ^ 2 ≤ (5/12 : ℝ) * ‖vectorize 3 X‖ ^ 2 ∧
      ∀ n : ℕ, ‖vectorize 3 ((wash : Mat → Mat)^[n] X)‖ ≤
        (2/3 : ℝ)^n * ‖vectorize 3 X‖) ∧
    (∀ σ : Mat, σ.PosSemidef → σ.trace = 1 → ∀ n : ℕ,
      ‖vectorize 3 ((wash : Mat → Mat)^[n] σ - (1/3 : ℂ) • (1 : Mat))‖ ≤
        Real.sqrt (2/3) * (2/3 : ℝ)^n) := by
  let M : Mat := Matrix.of (fun i j => if i = j then 0 else (Real.sqrt 6 : ℂ)⁻¹)
  let v : HS := vectorize 3 M
  let A : HS →ₗ[ℂ] HS := (vectorize 3).toLinearMap.comp
    (lambda.comp (lambda.comp (vectorize 3).symm.toLinearMap))
  let R : HS →ₗ[ℂ] HS := (vectorize 3).toLinearMap.comp
    ((conjugation N).comp (vectorize 3).symm.toLinearMap)
  have hv : ‖v‖ = 1 := by
    change ‖vectorize 3 M‖ = 1
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    rw [vectorize_norm_sq, frobSq_eq_sum]
    norm_num [M, Fin.sum_univ_succ, Complex.normSq_apply,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6), ← inv_pow]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  have hcn (K : Matrix.unitaryGroup (Fin 3) ℂ) (X : Mat) :
      ‖vectorize 3 ((K : Mat) * X * (K : Mat)ᴴ)‖ = ‖vectorize 3 X‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [vectorize_norm_sq, vectorize_norm_sq]
    change RHLinalg.frobSq ((K : Mat) * X * ((star K : Matrix.unitaryGroup (Fin 3) ℂ) : Mat)) = _
    rw [frobSq_unitary_right, frobSq_unitary_left]
  have hr (x : HS) : ‖R x‖ = ‖x‖ := by
    change ‖vectorize 3 ((N : Mat) * (vectorize 3).symm x * (N : Mat)ᴴ)‖ = _
    rw [hcn, (vectorize 3).apply_symm_apply]
  have htv : traceHS v = 0 := by
    change M.trace = 0
    norm_num [M, Matrix.trace, Fin.sum_univ_succ]
  have htA (x : HS) : traceHS (A x) = traceHS x := by
    change (lambda (lambda ((vectorize 3).symm x))).trace = _
    rw [lambda_trace, lambda_trace]
    rfl
  have hnleft : (N : Mat)ᴴ * (N : Mat) = 1 := Unitary.star_mul_self_of_mem N.property
  have hnright : (N : Mat) * (N : Mat)ᴴ = 1 := Unitary.mul_star_self_of_mem N.property
  have htR (x : HS) : traceHS (R x) = traceHS x := by
    change ((N : Mat) * (vectorize 3).symm x * (N : Mat)ᴴ).trace = _
    rw [Matrix.trace_mul_cycle, hnleft, Matrix.one_mul]
    rfl
  have hav : A v = v := by
    change vectorize 3 (lambda (lambda M)) = vectorize 3 M
    congr 1
    simp only [lambda_entries]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [M] <;> ring
  have hs6 : (Real.sqrt 6 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 6)).ne'
  have hpair (X : Mat) : (Real.sqrt 6 : ℂ) * inner ℂ v (vectorize 3 X) =
      X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1 := by
    change (Real.sqrt 6 : ℂ) * inner ℂ (vectorize 3 M) (vectorize 3 X) = _
    rw [matrix_pairing]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]
    norm_num [M]
    field_simp
    <;> ring
  have hai (x : HS) : inner ℂ v (A x) = inner ℂ v x := by
    apply mul_left_cancel₀ hs6
    obtain ⟨X, rfl⟩ := (vectorize 3).surjective x
    change (Real.sqrt 6 : ℂ) * inner ℂ v (vectorize 3 (lambda (lambda X))) = _
    rw [hpair, hpair]
    simp only [lambda_entries]
    norm_num
    ring
  have henergy (x : HS) (ht : traceHS x = 0) :
      4 * ‖A x‖ ^ 2 ≤ ‖x‖ ^ 2 + 3 * ‖inner ℂ v x‖ ^ 2 := by
    obtain ⟨X, rfl⟩ := (vectorize 3).surjective x
    have he : 4 * ‖vectorize 3 (lambda (lambda X))‖ ^ 2 =
        ‖vectorize 3 (dephase X)‖ ^ 2 + ‖X.trace‖ ^ 2 +
          (1/2 : ℝ) * ‖X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1‖ ^ 2 := by
      simp only [lambda_entries, vectorize_norm_sq, frobSq_eq_sum]
      simp only [dephase, conjugation, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.smul_apply,
        Matrix.add_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, U, W]
      norm_num [Matrix.vecHead, Matrix.vecTail, Pi.smul_apply, Pi.add_apply,
        Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      <;> ring
    have hw : W ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff']
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [W, Matrix.mul_apply, Fin.sum_univ_succ]
    have hb : ‖vectorize 3 (dephase X)‖ ≤ ‖vectorize 3 X‖ := by
      calc
        _ = (1/2 : ℝ) * ‖vectorize 3 X + vectorize 3 (W * X * Wᴴ)‖ := by
          change ‖vectorize 3 ((1/2 : ℂ) • (X + W * X * Wᴴ))‖ = _
          rw [map_smul, map_add, norm_smul]
          norm_num
        _ ≤ (1/2 : ℝ) * (‖vectorize 3 X‖ + ‖vectorize 3 (W * X * Wᴴ)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
        _ = ‖vectorize 3 X‖ := by rw [hcn ⟨W, hw⟩ X]; ring
    have hp := congrArg (fun z : ℂ => ‖z‖ ^ 2) (hpair X)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)] at hp
    change X.trace = 0 at ht
    rw [ht, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at he
    have hbn := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb
    change 4 * ‖vectorize 3 (lambda (lambda X))‖ ^ 2 ≤ _
    nlinarith
  let q : HS →ₗ[ℂ] HS := LinearMap.id - (innerₛₗ ℂ v).smulRight v
  have hq (x : HS) : q x = x - inner ℂ v x • v := rfl
  have horth (x : HS) : inner ℂ v (q x) = 0 := by
    rw [hq, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hv]
    simp
  have htq (x : HS) : traceHS (q x) = traceHS x := by
    rw [hq, map_sub, map_smul, htv, smul_zero, sub_zero]
  have hpyth (x : HS) : ‖x‖ ^ 2 = ‖inner ℂ v x‖ ^ 2 + ‖q x‖ ^ 2 := by
    have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      (inner ℂ v x • v) (q x) (by simp [horth])
    have he : inner ℂ v x • v + q x = x := by rw [hq]; module
    rw [he, norm_smul, hv, mul_one] at hh
    simpa only [pow_two] using hh
  have hnval : (N : Mat) = !![1,0,0; 0,0,1; 0,-1,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [N, D, U, Matrix.mul_apply, Fin.sum_univ_succ]
  have hs6sq : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hoverlap : inner ℂ v (R v) = (-1/3 : ℂ) := by
    change inner ℂ (vectorize 3 M) (vectorize 3 ((N : Mat) * M * (N : Mat)ᴴ)) = _
    rw [matrix_pairing, hnval]
    norm_num [M, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.vecHead, Matrix.vecTail, Matrix.vecMul, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    field_simp
    first | linear_combination hs6sq | linear_combination -hs6sq
  let w : HS := vectorize 3 ((N : Mat)ᴴ * M * (N : Mat)) + (1/3 : ℂ) • v
  have hw2 : ‖w‖ ^ 2 = (8/9 : ℝ) := by
    change ‖vectorize 3 ((N : Mat)ᴴ * M * (N : Mat)) +
      (1/3 : ℂ) • vectorize 3 M‖ ^ 2 = _
    rw [← map_smul, ← map_add, vectorize_norm_sq, frobSq_eq_sum]
    rw [hnval]
    norm_num [M, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.add_apply, Matrix.smul_apply, Fin.sum_univ_succ,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, ← inv_pow]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  have hwinner (z : HS) (hz : inner ℂ v z = 0) : inner ℂ v (R z) = inner ℂ w z := by
    obtain ⟨Z, rfl⟩ := (vectorize 3).surjective z
    change inner ℂ (vectorize 3 M) (vectorize 3 ((N : Mat) * Z * (N : Mat)ᴴ)) = _
    simp only [w, inner_add_left, inner_smul_left, hz, mul_zero, add_zero]
    rw [matrix_pairing, matrix_pairing]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  have hbound (X : Mat) (ht : X.trace = 0) :
      ‖vectorize 3 (wash X)‖ ^ 2 ≤ (5/12 : ℝ) * ‖vectorize 3 X‖ ^ 2 := by
    let x : HS := vectorize 3 X
    let a : ℂ := inner ℂ v x
    let z : HS := A (q x)
    have htx : traceHS x = 0 := ht
    have hz : inner ℂ v z = 0 := by change inner ℂ v (A (q x)) = 0; rw [hai, horth]
    have hzhalf : ‖z‖ ^ 2 ≤ (1/4 : ℝ) * ‖q x‖ ^ 2 := by
      have hh := henergy (q x) (by rw [htq]; exact htx)
      rw [horth, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hh
      change 4 * ‖z‖ ^ 2 ≤ _ at hh
      linarith
    have hdec : A x = a • v + z := by
      have hx : x = a • v + q x := by rw [hq]; module
      calc
        A x = A (a • v + q x) := congrArg A hx
        _ = _ := by rw [map_add, map_smul, hav]
    have hnorm : ‖A x‖ ^ 2 = ‖a‖ ^ 2 + ‖z‖ ^ 2 := by
      have hh := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (𝕜 := ℂ) (a • v) z (by simp [hz])
      rw [hdec]
      simpa only [pow_two, norm_smul, hv, mul_one] using hh
    have hc : ‖inner ℂ v (R z)‖ ^ 2 ≤ (8/9 : ℝ) * ‖z‖ ^ 2 := by
      rw [hwinner z hz]
      have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        (norm_inner_le_norm (𝕜 := ℂ) w z)
      rwa [mul_pow, hw2] at hh
    have hinner : inner ℂ v (R (A x)) = -a/3 + inner ℂ v (R z) := by
      rw [hdec, map_add, map_smul, inner_add_right, inner_smul_right, hoverlap]
      ring
    have hsum : ‖inner ℂ v (R (A x))‖ ^ 2 ≤
        (2/9 : ℝ) * ‖a‖ ^ 2 + 2 * ‖inner ℂ v (R z)‖ ^ 2 := by
      rw [hinner]
      have ht := norm_add_le (-a/3) (inner ℂ v (R z))
      have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
      norm_num [norm_div, norm_neg] at hs
      nlinarith [sq_nonneg (‖a‖/3 - ‖inner ℂ v (R z)‖)]
    have he := henergy (R (A x)) (by rw [htR, htA]; exact htx)
    rw [hr, hnorm] at he
    have hp := hpyth x
    change ‖x‖ ^ 2 = ‖a‖ ^ 2 + ‖q x‖ ^ 2 at hp
    have heq : vectorize 3 (wash X) = A (R (A x)) := by
      simp only [wash, thetaMatrix, A, R, x, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [heq]
    change ‖A (R (A x))‖ ^ 2 ≤ (5/12 : ℝ) * ‖x‖ ^ 2
    nlinarith [sq_nonneg ‖q x‖]
  have htrace (X : Mat) : (wash X).trace = X.trace := by
    change (lambda (lambda (conjugation N (lambda (lambda X))))).trace = _
    simp only [lambda_trace]
    change ((N : Mat) * lambda (lambda X) * (N : Mat)ᴴ).trace = _
    rw [Matrix.trace_mul_cycle, hnleft,
      Matrix.one_mul, lambda_trace, lambda_trace]
  have hunit : wash (1 : Mat) = 1 := by
    have hl : lambda (1 : Mat) = 1 := by
      rw [lambda_entries]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    change lambda (lambda (conjugation N (lambda (lambda (1 : Mat))))) = 1
    rw [hl, hl]
    change lambda (lambda ((N : Mat) * 1 * (N : Mat)ᴴ)) = 1
    rw [Matrix.mul_one, hnright, hl, hl]
  have hstep (X : Mat) (ht : X.trace = 0) :
      ‖vectorize 3 (wash X)‖ ≤ (2/3 : ℝ) * ‖vectorize 3 X‖ := by
    have hh := hbound X ht
    nlinarith [norm_nonneg (vectorize 3 (wash X)), norm_nonneg (vectorize 3 X),
      sq_nonneg ‖vectorize 3 X‖]
  have hitertrace (X : Mat) (n : ℕ) :
      ((wash : Mat → Mat)^[n] X).trace = X.trace := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', htrace, ih]
  have hpowers (X : Mat) (ht : X.trace = 0) (n : ℕ) :
      ‖vectorize 3 ((wash : Mat → Mat)^[n] X)‖ ≤
        (2/3 : ℝ)^n * ‖vectorize 3 X‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        _ ≤ (2/3 : ℝ) * ‖vectorize 3 ((wash : Mat → Mat)^[n] X)‖ :=
          hstep _ (by rw [hitertrace]; exact ht)
        _ ≤ (2/3 : ℝ) * ((2/3 : ℝ)^n * ‖vectorize 3 X‖) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  refine ⟨fun X ht => ⟨hbound X ht, hpowers X ht⟩, ?_⟩
  intro σ hpos htr n
  let C : Mat := (1/3 : ℂ) • (1 : Mat)
  have hcfix : wash C = C := by simp only [C, map_smul, hunit]
  have hcenter (k : ℕ) : (wash : Mat → Mat)^[k] (σ - C) =
      (wash : Mat → Mat)^[k] σ - C := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, map_sub, hcfix,
        Function.iterate_succ_apply']
  have hctr : (σ - C).trace = 0 := by
    simp [C, Matrix.trace_sub, Matrix.trace_smul, htr, Matrix.trace_one]
  have hpur := D5.S3.Quantum.Entanglement.QutritWeylBlochNormSeparableBound.density_purity
    σ ⟨hpos, htr⟩
  have hcentered : ‖vectorize 3 (σ - C)‖ ^ 2 ≤ (2/3 : ℝ) := by
    letI := D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixNormedAddCommGroup (d := 3)
    letI := D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixComplexInnerProductSpace (d := 3)
    have hn (Y : Mat) : ‖vectorize 3 Y‖ ^ 2 = ‖Y‖ ^ 2 := by
      rw [vectorize_norm_sq, InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
        D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.matrix_inner_eq_trace_conjTranspose_mul]
      rfl
    have hh := D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.centered_hermitian_norm_sq
      σ hpos.isHermitian
    have hp : RHLinalg.frobSq σ ≤ 1 := by
      rw [frobSq_eq_sum, Finset.sum_comm]
      simpa only [Complex.normSq_eq_norm_sq] using hpur
    have hps : (σ * σ).trace.re ≤ 1 := by
      change (σᴴ * σ).trace.re ≤ 1 at hp
      rwa [hpos.isHermitian.eq] at hp
    rw [hn]
    change ‖σ - (1/3 : ℂ) • (1 : Mat)‖ ^ 2 ≤ _
    rw [htr] at hh
    norm_num at hh
    linarith
  have hnorm : ‖vectorize 3 (σ - C)‖ ≤ Real.sqrt (2/3) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2/3),
      norm_nonneg (vectorize 3 (σ - C)), Real.sqrt_nonneg (2/3)]
  have hh := hpowers (σ - C) hctr n
  rw [hcenter] at hh
  change ‖vectorize 3 ((wash : Mat → Mat)^[n] σ - C)‖ ≤ _
  calc
    _ ≤ (2/3 : ℝ)^n * ‖vectorize 3 (σ - C)‖ := hh
    _ ≤ (2/3 : ℝ)^n * Real.sqrt (2/3) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := mul_comm _ _

end D5.S3.Quantum.QuantumChannels.OriginalQutritWash
