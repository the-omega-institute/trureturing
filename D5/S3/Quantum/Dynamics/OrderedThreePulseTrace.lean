/- GID: D5/S3/Quantum/Dynamics/OrderedThreePulseTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/OrderedThreePulseTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dimension-free ordered three-pulse real trace deviation under Frobenius bounds. -/

import Mathlib
import D5.S3.Quantum.GNSMatrix

namespace D5.S3.Quantum.Dynamics.OrderedThreePulseTrace

open scoped Matrix.Norms.L2Operator
open Matrix

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

local instance (priority := 2000) : NormedAddCommGroup (Matrix I I ℂ) :=
  Matrix.instL2OpNormedAddCommGroup
local instance (priority := 2000) : NormedSpace ℂ (Matrix I I ℂ) :=
  Matrix.instL2OpNormedSpace
local instance (priority := 2000) : NormedRing (Matrix I I ℂ) :=
  Matrix.instL2OpNormedRing
local instance (priority := 2000) : NormedAlgebra ℂ (Matrix I I ℂ) :=
  Matrix.instL2OpNormedAlgebra
local instance (priority := 2000) : NormedAlgebra ℚ (Matrix I I ℂ) :=
  NormedAlgebra.restrictScalars ℚ ℂ (Matrix I I ℂ)

noncomputable def pulse0 (X : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ :=
  ∫ r in (0 : ℝ)..1, NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) * X

set_option maxHeartbeats 1000000 in
-- The local ordered-product estimates elaborate as one kernel-checked theorem.
set_option synthInstance.maxHeartbeats 100000 in
theorem ordered_three_pulse_real_trace_bound
    (A B C : Matrix I I ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm) (hC : C.IsSymm)
    (L : ℝ) (hL : 0 ≤ L)
    (hAn : @norm (Matrix I I ℝ) Matrix.frobeniusNormedAddCommGroup.toNorm A ≤ L)
    (hBn : @norm (Matrix I I ℝ) Matrix.frobeniusNormedAddCommGroup.toNorm B ≤ L)
    (hCn : @norm (Matrix I I ℝ) Matrix.frobeniusNormedAddCommGroup.toNorm C ≤ L)
    (t : ℝ) (ht : 0 < t) :
    (∀ X : Matrix I I ℂ, pulse0 X 0 = X) ∧
    (∀ X : Matrix I I ℂ, ∀ s : ℝ, s ≠ 0 →
      pulse0 X s = ((s : ℂ) * Complex.I)⁻¹ •
        (NormedSpace.exp (((s : ℂ) * Complex.I) • X) - 1)) ∧
    |(Matrix.trace (pulse0 (A.map Complex.ofReal) t *
        pulse0 (B.map Complex.ofReal) t *
        pulse0 (C.map Complex.ofReal) t)).re - Matrix.trace (A * B * C)| ≤
      (5 / 4 : ℝ) * L ^ 5 * t ^ 2 := by
  let frobMap : Matrix I I ℂ →L[ℂ] EuclideanSpace ℂ (I × I) :=
    (show Matrix I I ℂ →ₗ[ℂ] EuclideanSpace ℂ (I × I) from
      { toFun := fun M => WithLp.toLp 2 (fun ij => M ij.1 ij.2)
        map_add' := by intro A B; ext ij; rfl
        map_smul' := by intro c A; ext ij; rfl }).toContinuousLinearMap

  have frobMap_norm_eq (M : Matrix I I ℂ) :
      ‖frobMap M‖ = @norm (Matrix I I ℂ) Matrix.frobeniusNormedAddCommGroup.toNorm M := by
    rw [Matrix.frobenius_norm_def]
    change ‖WithLp.toLp 2 (fun ij : I × I => M ij.1 ij.2)‖ = _
    simp [PiLp.norm_eq_of_L2, Fintype.sum_prod_type, Real.sqrt_eq_rpow]

  have frobMap_norm_mul_le (A B : Matrix I I ℂ) :
      ‖frobMap (A * B)‖ ≤ ‖frobMap A‖ * ‖frobMap B‖ := by
    simpa only [frobMap_norm_eq] using Matrix.frobenius_norm_mul A B

  have frobMap_norm_unitary_left (U A : Matrix I I ℂ) (hU : Uᴴ * U = 1) :
      ‖frobMap (U * A)‖ = ‖frobMap A‖ := by
    have hNorm (M : Matrix I I ℂ) :
        ((‖frobMap M‖ ^ 2 : ℝ) : ℂ) = Matrix.trace (Mᴴ * M) := by
      simpa only [frobMap_norm_eq] using
        (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace M)
    have hStar : (U * A)ᴴ * (U * A) = Aᴴ * A := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U A, hU, one_mul]
    have hSq : ‖frobMap (U * A)‖ ^ 2 = ‖frobMap A‖ ^ 2 := by
      have hTrace : ((‖frobMap (U * A)‖ ^ 2 : ℝ) : ℂ) =
          ((‖frobMap A‖ ^ 2 : ℝ) : ℂ) := by
        calc
          _ = Matrix.trace ((U * A)ᴴ * (U * A)) := hNorm (U * A)
          _ = Matrix.trace (Aᴴ * A) := congrArg Matrix.trace hStar
          _ = _ := (hNorm A).symm
      exact_mod_cast hTrace
    nlinarith [norm_nonneg (frobMap (U * A)), norm_nonneg (frobMap A)]

  let pulse1 (X : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ :=
    ∫ r in (0 : ℝ)..1,
      NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X)))*
        ((((r : ℂ) * Complex.I) • X) * X)

  let pulse2 (X : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ :=
    ∫ r in (0 : ℝ)..1,
      NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
        ((((r : ℂ) * Complex.I) • X) * ((((r : ℂ) * Complex.I) • X) * X))

  have op_norm_phase_left (X A : Matrix I I ℂ) (hX : X.IsHermitian)
      (r s : ℝ) :
      ‖NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) * A‖ = ‖A‖ := by
    let G : Matrix I I ℂ := s • ((((r : ℂ) * Complex.I) • X))
    have hGstar : Gᴴ = -G := by
      ext i j
      simp [G, Matrix.conjTranspose_apply, Matrix.smul_apply, hX.apply]
    have hSkew : G ∈ skewAdjoint (Matrix I I ℂ) := by
      change star G = -G
      simpa only [Matrix.star_eq_conjTranspose] using hGstar
    exact CStarRing.norm_mem_unitary_mul A
      (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hSkew)

  have frob_norm_phase_left (X A : Matrix I I ℂ) (hX : X.IsHermitian)
      (r s : ℝ) :
      ‖frobMap (NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) * A)‖ =
        ‖frobMap A‖ := by
    let G : Matrix I I ℂ := s • ((((r : ℂ) * Complex.I) • X))
    have hGstar : Gᴴ = -G := by
      ext i j
      simp [G, Matrix.conjTranspose_apply, Matrix.smul_apply, hX.apply]
    have hSkew : G ∈ skewAdjoint (Matrix I I ℂ) := by
      change star G = -G
      simpa only [Matrix.star_eq_conjTranspose] using hGstar
    have hU : (NormedSpace.exp G)ᴴ * NormedSpace.exp G = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        (Unitary.mem_iff.mp (NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hSkew)).1
    exact frobMap_norm_unitary_left (NormedSpace.exp G) A hU

  have op_norm_phase_first_le (X : Matrix I I ℂ) (hX : X.IsHermitian)
      (r s : ℝ) (hr : 0 ≤ r) :
      ‖NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
        ((((r : ℂ) * Complex.I) • X) * X)‖ ≤ r * ‖X‖ ^ 2 := by
    let G : Matrix I I ℂ := (((r : ℂ) * Complex.I) • X)
    have hG : ‖G‖ = r * ‖X‖ := by
      simp [G, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    rw [op_norm_phase_left X (G * X) hX r s]
    calc
      ‖G * X‖ ≤ ‖G‖ * ‖X‖ := norm_mul_le G X
      _ = r * ‖X‖ ^ 2 := by rw [hG]; ring

  have op_norm_phase_second_le (X : Matrix I I ℂ) (hX : X.IsHermitian)
      (r s : ℝ) (hr : 0 ≤ r) :
      ‖NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
        ((((r : ℂ) * Complex.I) • X) * ((((r : ℂ) * Complex.I) • X) * X))‖
        ≤ r ^ 2 * ‖X‖ ^ 3 := by
    let G : Matrix I I ℂ := (((r : ℂ) * Complex.I) • X)
    have hG : ‖G‖ = r * ‖X‖ := by
      simp [G, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    rw [op_norm_phase_left X (G * (G * X)) hX r s]
    calc
      ‖G * (G * X)‖ ≤ ‖G‖ * ‖G * X‖ := norm_mul_le G (G * X)
      _ ≤ ‖G‖ * (‖G‖ * ‖X‖) := by
        gcongr
        exact norm_mul_le G X
      _ = r ^ 2 * ‖X‖ ^ 3 := by rw [hG]; ring

  have op_pulse0_bound (X : Matrix I I ℂ) (hX : X.IsHermitian) (s : ℝ) :
      ‖pulse0 X s‖ ≤ ‖X‖ := by
    unfold pulse0
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun r : ℝ => NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) * X)
      (C := ‖X‖) (a := 0) (b := 1) (by
        intro r hr
        exact le_of_eq (op_norm_phase_left X X hX r s))
    simpa using h

  have op_pulse1_bound (X : Matrix I I ℂ) (hX : X.IsHermitian) (s : ℝ) :
      ‖pulse1 X s‖ ≤ ‖X‖ ^ 2 / 2 := by
    unfold pulse1
    have hBound : IntervalIntegrable (fun r : ℝ => r * ‖X‖ ^ 2)
        MeasureTheory.volume 0 1 :=
      (continuous_id.mul continuous_const).intervalIntegrable _ _
    have h := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun r : ℝ =>
        NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
          ((((r : ℂ) * Complex.I) • X) * X))
      (g := fun r : ℝ => r * ‖X‖ ^ 2) (a := 0) (b := 1)
      (by norm_num) (Filter.Eventually.of_forall (by
        intro r hr
        exact op_norm_phase_first_le X hX r s hr.1.le)) hBound
    simpa [div_eq_mul_inv, mul_comm] using h

  have op_pulse2_bound (X : Matrix I I ℂ) (hX : X.IsHermitian) (s : ℝ) :
      ‖pulse2 X s‖ ≤ ‖X‖ ^ 3 / 3 := by
    unfold pulse2
    have hBound : IntervalIntegrable (fun r : ℝ => r ^ 2 * ‖X‖ ^ 3)
        MeasureTheory.volume 0 1 :=
      ((continuous_id.pow 2).mul continuous_const).intervalIntegrable _ _
    have h := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun r : ℝ =>
        NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
          ((((r : ℂ) * Complex.I) • X) * ((((r : ℂ) * Complex.I) • X) * X)))
      (g := fun r : ℝ => r ^ 2 * ‖X‖ ^ 3) (a := 0) (b := 1)
      (by norm_num) (Filter.Eventually.of_forall (by
        intro r hr
        exact op_norm_phase_second_le X hX r s hr.1.le)) hBound
    simpa [div_eq_mul_inv, mul_comm, show (2 : ℝ) + 1 = 3 by norm_num] using h

  have frob_norm_phase_first_le (X : Matrix I I ℂ) (hX : X.IsHermitian)
      (r s : ℝ) (hr : 0 ≤ r) :
      ‖frobMap (NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
        ((((r : ℂ) * Complex.I) • X) * X))‖ ≤ r * ‖frobMap X‖ ^ 2 := by
    let G : Matrix I I ℂ := (((r : ℂ) * Complex.I) • X)
    have hG : ‖frobMap G‖ = r * ‖frobMap X‖ := by
      simp [G, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    rw [frob_norm_phase_left X (G * X) hX r s]
    calc
      ‖frobMap (G * X)‖ ≤ ‖frobMap G‖ * ‖frobMap X‖ :=
        frobMap_norm_mul_le G X
      _ = r * ‖frobMap X‖ ^ 2 := by rw [hG]; ring

  have frob_norm_phase_second_le (X : Matrix I I ℂ) (hX : X.IsHermitian)
      (r s : ℝ) (hr : 0 ≤ r) :
      ‖frobMap (NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
        ((((r : ℂ) * Complex.I) • X) * ((((r : ℂ) * Complex.I) • X) * X)))‖
        ≤ r ^ 2 * ‖frobMap X‖ ^ 3 := by
    let G : Matrix I I ℂ := (((r : ℂ) * Complex.I) • X)
    have hG : ‖frobMap G‖ = r * ‖frobMap X‖ := by
      simp [G, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    rw [frob_norm_phase_left X (G * (G * X)) hX r s]
    calc
      ‖frobMap (G * (G * X))‖ ≤ ‖frobMap G‖ * ‖frobMap (G * X)‖ :=
        frobMap_norm_mul_le G (G * X)
      _ ≤ ‖frobMap G‖ * (‖frobMap G‖ * ‖frobMap X‖) := by
        gcongr
        exact frobMap_norm_mul_le G X
      _ = r ^ 2 * ‖frobMap X‖ ^ 3 := by rw [hG]; ring

  have frob_pulse0_bound (X : Matrix I I ℂ) (hX : X.IsHermitian) (s : ℝ) :
      ‖frobMap (pulse0 X s)‖ ≤ ‖frobMap X‖ := by
    have hCont : Continuous (fun r : ℝ =>
        NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) * X) := by
      fun_prop
    have hMap : frobMap (pulse0 X s) =
        ∫ r in (0 : ℝ)..1,
          frobMap (NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) * X) := by
      exact (frobMap.intervalIntegral_comp_comm (μ := MeasureTheory.volume)
        (hCont.intervalIntegrable _ _)).symm
    rw [hMap]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun r : ℝ => frobMap
        (NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) * X))
      (C := ‖frobMap X‖) (a := 0) (b := 1) (by
        intro r hr
        exact le_of_eq (frob_norm_phase_left X X hX r s))
    simpa using h

  have frob_pulse1_bound (X : Matrix I I ℂ) (hX : X.IsHermitian) (s : ℝ) :
      ‖frobMap (pulse1 X s)‖ ≤ ‖frobMap X‖ ^ 2 / 2 := by
    have hCont : Continuous (fun r : ℝ =>
        NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
          ((((r : ℂ) * Complex.I) • X) * X)) := by
      fun_prop
    have hMap : frobMap (pulse1 X s) =
        ∫ r in (0 : ℝ)..1,
          frobMap (NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
            ((((r : ℂ) * Complex.I) • X) * X)) := by
      exact (frobMap.intervalIntegral_comp_comm (μ := MeasureTheory.volume)
        (hCont.intervalIntegrable _ _)).symm
    rw [hMap]
    have hBound : IntervalIntegrable (fun r : ℝ => r * ‖frobMap X‖ ^ 2)
        MeasureTheory.volume 0 1 :=
      (continuous_id.mul continuous_const).intervalIntegrable _ _
    have h := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun r : ℝ => frobMap
        (NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
          ((((r : ℂ) * Complex.I) • X) * X)))
      (g := fun r : ℝ => r * ‖frobMap X‖ ^ 2) (a := 0) (b := 1)
      (by norm_num) (Filter.Eventually.of_forall (by
        intro r hr
        exact frob_norm_phase_first_le X hX r s hr.1.le)) hBound
    simpa [div_eq_mul_inv, mul_comm] using h

  have frob_pulse2_bound (X : Matrix I I ℂ) (hX : X.IsHermitian) (s : ℝ) :
      ‖frobMap (pulse2 X s)‖ ≤ ‖frobMap X‖ ^ 3 / 3 := by
    have hCont : Continuous (fun r : ℝ =>
        NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
          ((((r : ℂ) * Complex.I) • X) * ((((r : ℂ) * Complex.I) • X) * X))) := by
      fun_prop
    have hMap : frobMap (pulse2 X s) =
        ∫ r in (0 : ℝ)..1,
          frobMap (NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
            ((((r : ℂ) * Complex.I) • X) * ((((r : ℂ) * Complex.I) • X) * X))) := by
      exact (frobMap.intervalIntegral_comp_comm (μ := MeasureTheory.volume)
        (hCont.intervalIntegrable _ _)).symm
    rw [hMap]
    have hBound : IntervalIntegrable (fun r : ℝ => r ^ 2 * ‖frobMap X‖ ^ 3)
        MeasureTheory.volume 0 1 :=
      ((continuous_id.pow 2).mul continuous_const).intervalIntegrable _ _
    have h := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun r : ℝ => frobMap
        (NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) *
          ((((r : ℂ) * Complex.I) • X) * ((((r : ℂ) * Complex.I) • X) * X))))
      (g := fun r : ℝ => r ^ 2 * ‖frobMap X‖ ^ 3) (a := 0) (b := 1)
      (by norm_num) (Filter.Eventually.of_forall (by
        intro r hr
        exact frob_norm_phase_second_le X hX r s hr.1.le)) hBound
    simpa [div_eq_mul_inv, mul_comm, show (2 : ℝ) + 1 = 3 by norm_num] using h

  have trace_mul_frob_le (A B : Matrix I I ℂ) :
      ‖Matrix.trace (A * B)‖ ≤ ‖frobMap A‖ * ‖frobMap B‖ := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt
      (Finset.univ : Finset (I × I))
      (fun ij => ‖A ij.1 ij.2‖) (fun ij => ‖B ij.2 ij.1‖)
    have hNorm : ‖Matrix.trace (A * B)‖ ≤
        ∑ ij : I × I, ‖A ij.1 ij.2‖ * ‖B ij.2 ij.1‖ := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      calc
        ‖∑ i, ∑ j, A i j * B j i‖ ≤ ∑ i, ∑ j, ‖A i j * B j i‖ := by
          calc
            ‖∑ i, ∑ j, A i j * B j i‖ ≤ ∑ i, ‖∑ j, A i j * B j i‖ :=
              norm_sum_le _ _
            _ ≤ ∑ i, ∑ j, ‖A i j * B j i‖ := by
              gcongr with i
              exact norm_sum_le _ _
        _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖B j i‖ := by
          gcongr with i j
          exact norm_mul_le _ _
        _ = ∑ ij : I × I, ‖A ij.1 ij.2‖ * ‖B ij.2 ij.1‖ := by
          rw [Fintype.sum_prod_type]
    calc
      ‖Matrix.trace (A * B)‖ ≤ _ := hNorm
      _ ≤ √(∑ ij : I × I, ‖A ij.1 ij.2‖ ^ 2) *
        √(∑ ij : I × I, ‖B ij.2 ij.1‖ ^ 2) := h
      _ = ‖frobMap A‖ * ‖frobMap B‖ := by
        have hA : √(∑ ij : I × I, ‖A ij.1 ij.2‖ ^ 2) = ‖frobMap A‖ := by
          rw [frobMap_norm_eq, Matrix.frobenius_norm_def]
          simp [Real.sqrt_eq_rpow, Fintype.sum_prod_type]
        have hB : √(∑ ij : I × I, ‖B ij.2 ij.1‖ ^ 2) = ‖frobMap B‖ := by
          rw [frobMap_norm_eq, Matrix.frobenius_norm_def]
          simp only [Real.sqrt_eq_rpow, Fintype.sum_prod_type]
          congr 1
          convert Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
            (f := fun i j : I => ‖B j i‖ ^ (2 : ℕ)) using 1;
            simp only [Real.rpow_two]
        rw [hA, hB]

  have trace_triple_frob_le (A B C : Matrix I I ℂ) :
      ‖Matrix.trace (A * B * C)‖ ≤
        ‖frobMap A‖ * ‖frobMap B‖ * ‖frobMap C‖ := by
    calc
      ‖Matrix.trace (A * B * C)‖ ≤ ‖frobMap (A * B)‖ * ‖frobMap C‖ :=
        trace_mul_frob_le (A * B) C
      _ ≤ ‖frobMap A‖ * ‖frobMap B‖ * ‖frobMap C‖ :=
        mul_le_mul_of_nonneg_right (frobMap_norm_mul_le A B) (norm_nonneg (frobMap C))

  have op_pulse0_hasDerivAt (X : Matrix I I ℂ) (hX : X.IsHermitian) (s : ℝ) :
      HasDerivAt (pulse0 X) (pulse1 X s) s := by
    let F : ℝ → ℝ → Matrix I I ℂ := fun x r =>
      NormedSpace.exp (x • ((((r : ℂ) * Complex.I) • X))) * X
    let F' : ℝ → ℝ → Matrix I I ℂ := fun x r =>
      NormedSpace.exp (x • ((((r : ℂ) * Complex.I) • X))) *
        (((((r : ℂ) * Complex.I) • X)) * X)
    let bound : ℝ → ℝ := fun r => r * ‖X‖ ^ 2
    have hCont (x : ℝ) : Continuous (F x) := by
      dsimp [F]
      fun_prop
    have hCont' (x : ℝ) : Continuous (F' x) := by
      dsimp [F']
      fun_prop
    have hBoundInt : IntervalIntegrable bound MeasureTheory.volume 0 1 :=
      (continuous_id.mul continuous_const).intervalIntegrable _ _
    have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound) (x₀ := s)
      (s := Set.univ) (a := 0) (b := 1) (μ := MeasureTheory.volume)
      (Filter.univ_mem) (Filter.Eventually.of_forall (fun x =>
        (hCont x).aestronglyMeasurable))
      ((hCont s).intervalIntegrable _ _)
      ((hCont' s).aestronglyMeasurable)
      (Filter.Eventually.of_forall (by
        intro r hr x hx
        have hr0 : 0 ≤ r := by
          simpa only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1)] using hr.1.le
        exact op_norm_phase_first_le X hX r x hr0))
      hBoundInt (Filter.Eventually.of_forall (by
        intro r hr x hx
        dsimp [F, F']
        simpa only [Matrix.mul_assoc] using
          (hasDerivAt_exp_smul_const ((((r : ℂ) * Complex.I) • X)) x).mul_const X))
    convert h.2 using 1 <;> rfl

  have op_pulse1_hasDerivAt (X : Matrix I I ℂ) (hX : X.IsHermitian) (s : ℝ) :
      HasDerivAt (pulse1 X) (pulse2 X s) s := by
    let G : ℝ → Matrix I I ℂ := fun r => (((r : ℂ) * Complex.I) • X)
    let F : ℝ → ℝ → Matrix I I ℂ := fun x r =>
      NormedSpace.exp (x • G r) * (G r * X)
    let F' : ℝ → ℝ → Matrix I I ℂ := fun x r =>
      NormedSpace.exp (x • G r) * (G r * (G r * X))
    let bound : ℝ → ℝ := fun r => r ^ 2 * ‖X‖ ^ 3
    have hCont (x : ℝ) : Continuous (F x) := by
      dsimp [F, G]
      fun_prop
    have hCont' (x : ℝ) : Continuous (F' x) := by
      dsimp [F', G]
      fun_prop
    have hBoundInt : IntervalIntegrable bound MeasureTheory.volume 0 1 :=
      ((continuous_id.pow 2).mul continuous_const).intervalIntegrable _ _
    have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound) (x₀ := s)
      (s := Set.univ) (a := 0) (b := 1) (μ := MeasureTheory.volume)
      (Filter.univ_mem) (Filter.Eventually.of_forall (fun x =>
        (hCont x).aestronglyMeasurable))
      ((hCont s).intervalIntegrable _ _)
      ((hCont' s).aestronglyMeasurable)
      (Filter.Eventually.of_forall (by
        intro r hr x hx
        have hr0 : 0 ≤ r := by
          simpa only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1)] using hr.1.le
        exact op_norm_phase_second_le X hX r x hr0))
      hBoundInt (Filter.Eventually.of_forall (by
        intro r hr x hx
        dsimp [F, F']
        simpa only [Matrix.mul_assoc] using
          (hasDerivAt_exp_smul_const (G r) x).mul_const (G r * X)))
    convert h.2 using 1 <;> rfl

  let triple0 (A B C : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ :=
    pulse0 A s * pulse0 B s * pulse0 C s

  let triple1 (A B C : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ :=
    (pulse1 A s * pulse0 B s + pulse0 A s * pulse1 B s) * pulse0 C s +
      (pulse0 A s * pulse0 B s) * pulse1 C s

  let triple2 (A B C : Matrix I I ℂ) (s : ℝ) : Matrix I I ℂ :=
    ((pulse2 A s * pulse0 B s + pulse1 A s * pulse1 B s) +
        (pulse1 A s * pulse1 B s + pulse0 A s * pulse2 B s)) * pulse0 C s +
      (pulse1 A s * pulse0 B s + pulse0 A s * pulse1 B s) * pulse1 C s +
      (pulse1 A s * pulse0 B s + pulse0 A s * pulse1 B s) * pulse1 C s +
      (pulse0 A s * pulse0 B s) * pulse2 C s

  have triple0_hasDerivAt (A B C : Matrix I I ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (s : ℝ) :
      HasDerivAt (triple0 A B C) (triple1 A B C s) s := by
    have hAB := (op_pulse0_hasDerivAt A hA s).mul (op_pulse0_hasDerivAt B hB s)
    have hABC := hAB.mul (op_pulse0_hasDerivAt C hC s)
    convert hABC using 1 <;> first | rfl | (simp [triple0, triple1])

  have triple1_hasDerivAt (A B C : Matrix I I ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (s : ℝ) :
      HasDerivAt (triple1 A B C) (triple2 A B C s) s := by
    have hAB := (op_pulse1_hasDerivAt A hA s).mul (op_pulse0_hasDerivAt B hB s)
    have hBA := (op_pulse0_hasDerivAt A hA s).mul (op_pulse1_hasDerivAt B hB s)
    have h00 := (op_pulse0_hasDerivAt A hA s).mul (op_pulse0_hasDerivAt B hB s)
    have hC0 := op_pulse0_hasDerivAt C hC s
    have hC1 := op_pulse1_hasDerivAt C hC s
    have h := ((hAB.add hBA).mul hC0).add (h00.mul hC1)
    convert h using 1 <;> first | rfl | (simp [triple1, triple2]; abel)

  let traceCLM : Matrix I I ℂ →L[ℝ] ℂ :=
    (Matrix.traceLinearMap I ℝ ℂ).toContinuousLinearMap

  let scalar0 (A B C : Matrix I I ℂ) (s : ℝ) : ℂ :=
    Matrix.trace (triple0 A B C s)

  let scalar1 (A B C : Matrix I I ℂ) (s : ℝ) : ℂ :=
    Matrix.trace (triple1 A B C s)

  let scalar2 (A B C : Matrix I I ℂ) (s : ℝ) : ℂ :=
    Matrix.trace (triple2 A B C s)

  have scalar0_hasDerivAt (A B C : Matrix I I ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (s : ℝ) :
      HasDerivAt (scalar0 A B C) (scalar1 A B C s) s := by
    have h := traceCLM.hasFDerivAt.comp_hasDerivAt s
      (triple0_hasDerivAt A B C hA hB hC s)
    convert h using 1 <;> rfl

  have scalar1_hasDerivAt (A B C : Matrix I I ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) (s : ℝ) :
      HasDerivAt (scalar1 A B C) (scalar2 A B C s) s := by
    have h := traceCLM.hasFDerivAt.comp_hasDerivAt s
      (triple1_hasDerivAt A B C hA hB hC s)
    convert h using 1 <;> rfl

  have scalar2_eq_sum (A B C : Matrix I I ℂ) (s : ℝ) :
      scalar2 A B C s =
        Matrix.trace (pulse2 A s * pulse0 B s * pulse0 C s) +
        Matrix.trace (pulse0 A s * pulse2 B s * pulse0 C s) +
        Matrix.trace (pulse0 A s * pulse0 B s * pulse2 C s) +
        Matrix.trace (pulse1 A s * pulse1 B s * pulse0 C s) +
        Matrix.trace (pulse1 A s * pulse1 B s * pulse0 C s) +
        Matrix.trace (pulse1 A s * pulse0 B s * pulse1 C s) +
        Matrix.trace (pulse1 A s * pulse0 B s * pulse1 C s) +
        Matrix.trace (pulse0 A s * pulse1 B s * pulse1 C s) +
        Matrix.trace (pulse0 A s * pulse1 B s * pulse1 C s) := by
    simp only [scalar2, triple2, add_mul, Matrix.trace_add]
    abel

  have norm_nine_sum_le (a b c d e f g h i : ℂ) :
      ‖a + b + c + d + e + f + g + h + i‖ ≤
        ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ + ‖h‖ + ‖i‖ := by
    have h1 := norm_add_le a b
    have h2 := norm_add_le (a + b) c
    have h3 := norm_add_le (a + b + c) d
    have h4 := norm_add_le (a + b + c + d) e
    have h5 := norm_add_le (a + b + c + d + e) f
    have h6 := norm_add_le (a + b + c + d + e + f) g
    have h7 := norm_add_le (a + b + c + d + e + f + g) h
    have h8 := norm_add_le (a + b + c + d + e + f + g + h) i
    linarith

  have scalar2_bound (A B C : Matrix I I ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian)
      {L : ℝ} (hL : 0 ≤ L)
      (hAn : ‖frobMap A‖ ≤ L) (hBn : ‖frobMap B‖ ≤ L)
      (hCn : ‖frobMap C‖ ≤ L) (s : ℝ) :
      ‖scalar2 A B C s‖ ≤ (5 / 2 : ℝ) * L ^ 5 := by
    have hA0 : ‖frobMap (pulse0 A s)‖ ≤ L :=
      (frob_pulse0_bound A hA s).trans hAn
    have hB0 : ‖frobMap (pulse0 B s)‖ ≤ L :=
      (frob_pulse0_bound B hB s).trans hBn
    have hC0 : ‖frobMap (pulse0 C s)‖ ≤ L :=
      (frob_pulse0_bound C hC s).trans hCn
    have hA1 : ‖frobMap (pulse1 A s)‖ ≤ L ^ 2 / 2 := by
      calc
        _ ≤ ‖frobMap A‖ ^ 2 / 2 := frob_pulse1_bound A hA s
        _ ≤ L ^ 2 / 2 := by gcongr
    have hB1 : ‖frobMap (pulse1 B s)‖ ≤ L ^ 2 / 2 := by
      calc
        _ ≤ ‖frobMap B‖ ^ 2 / 2 := frob_pulse1_bound B hB s
        _ ≤ L ^ 2 / 2 := by gcongr
    have hC1 : ‖frobMap (pulse1 C s)‖ ≤ L ^ 2 / 2 := by
      calc
        _ ≤ ‖frobMap C‖ ^ 2 / 2 := frob_pulse1_bound C hC s
        _ ≤ L ^ 2 / 2 := by gcongr
    have hA2 : ‖frobMap (pulse2 A s)‖ ≤ L ^ 3 / 3 := by
      calc
        _ ≤ ‖frobMap A‖ ^ 3 / 3 := frob_pulse2_bound A hA s
        _ ≤ L ^ 3 / 3 := by gcongr
    have hB2 : ‖frobMap (pulse2 B s)‖ ≤ L ^ 3 / 3 := by
      calc
        _ ≤ ‖frobMap B‖ ^ 3 / 3 := frob_pulse2_bound B hB s
        _ ≤ L ^ 3 / 3 := by gcongr
    have hC2 : ‖frobMap (pulse2 C s)‖ ≤ L ^ 3 / 3 := by
      calc
        _ ≤ ‖frobMap C‖ ^ 3 / 3 := frob_pulse2_bound C hC s
        _ ≤ L ^ 3 / 3 := by gcongr
    have t200 : ‖Matrix.trace (pulse2 A s * pulse0 B s * pulse0 C s)‖
        ≤ L ^ 5 / 3 := by
      calc
        _ ≤ ‖frobMap (pulse2 A s)‖ * ‖frobMap (pulse0 B s)‖ *
            ‖frobMap (pulse0 C s)‖ := trace_triple_frob_le _ _ _
        _ ≤ (L ^ 3 / 3) * L * L := by gcongr
        _ = L ^ 5 / 3 := by ring
    have t020 : ‖Matrix.trace (pulse0 A s * pulse2 B s * pulse0 C s)‖
        ≤ L ^ 5 / 3 := by
      calc
        _ ≤ ‖frobMap (pulse0 A s)‖ * ‖frobMap (pulse2 B s)‖ *
            ‖frobMap (pulse0 C s)‖ := trace_triple_frob_le _ _ _
        _ ≤ L * (L ^ 3 / 3) * L := by gcongr
        _ = L ^ 5 / 3 := by ring
    have t002 : ‖Matrix.trace (pulse0 A s * pulse0 B s * pulse2 C s)‖
        ≤ L ^ 5 / 3 := by
      calc
        _ ≤ ‖frobMap (pulse0 A s)‖ * ‖frobMap (pulse0 B s)‖ *
            ‖frobMap (pulse2 C s)‖ := trace_triple_frob_le _ _ _
        _ ≤ L * L * (L ^ 3 / 3) := by gcongr
        _ = L ^ 5 / 3 := by ring
    have t110 : ‖Matrix.trace (pulse1 A s * pulse1 B s * pulse0 C s)‖
        ≤ L ^ 5 / 4 := by
      calc
        _ ≤ ‖frobMap (pulse1 A s)‖ * ‖frobMap (pulse1 B s)‖ *
            ‖frobMap (pulse0 C s)‖ := trace_triple_frob_le _ _ _
        _ ≤ (L ^ 2 / 2) * (L ^ 2 / 2) * L := by gcongr
        _ = L ^ 5 / 4 := by ring
    have t101 : ‖Matrix.trace (pulse1 A s * pulse0 B s * pulse1 C s)‖
        ≤ L ^ 5 / 4 := by
      calc
        _ ≤ ‖frobMap (pulse1 A s)‖ * ‖frobMap (pulse0 B s)‖ *
            ‖frobMap (pulse1 C s)‖ := trace_triple_frob_le _ _ _
        _ ≤ (L ^ 2 / 2) * L * (L ^ 2 / 2) := by gcongr
        _ = L ^ 5 / 4 := by ring
    have t011 : ‖Matrix.trace (pulse0 A s * pulse1 B s * pulse1 C s)‖
        ≤ L ^ 5 / 4 := by
      calc
        _ ≤ ‖frobMap (pulse0 A s)‖ * ‖frobMap (pulse1 B s)‖ *
            ‖frobMap (pulse1 C s)‖ := trace_triple_frob_le _ _ _
        _ ≤ L * (L ^ 2 / 2) * (L ^ 2 / 2) := by gcongr
        _ = L ^ 5 / 4 := by ring
    rw [scalar2_eq_sum]
    calc
      _ ≤ ‖Matrix.trace (pulse2 A s * pulse0 B s * pulse0 C s)‖ +
        ‖Matrix.trace (pulse0 A s * pulse2 B s * pulse0 C s)‖ +
        ‖Matrix.trace (pulse0 A s * pulse0 B s * pulse2 C s)‖ +
        ‖Matrix.trace (pulse1 A s * pulse1 B s * pulse0 C s)‖ +
        ‖Matrix.trace (pulse1 A s * pulse1 B s * pulse0 C s)‖ +
        ‖Matrix.trace (pulse1 A s * pulse0 B s * pulse1 C s)‖ +
        ‖Matrix.trace (pulse1 A s * pulse0 B s * pulse1 C s)‖ +
        ‖Matrix.trace (pulse0 A s * pulse1 B s * pulse1 C s)‖ +
        ‖Matrix.trace (pulse0 A s * pulse1 B s * pulse1 C s)‖ :=
          norm_nine_sum_le _ _ _ _ _ _ _ _ _
      _ ≤ L ^ 5 / 3 + L ^ 5 / 3 + L ^ 5 / 3 +
        L ^ 5 / 4 + L ^ 5 / 4 + L ^ 5 / 4 +
        L ^ 5 / 4 + L ^ 5 / 4 + L ^ 5 / 4 := by
          gcongr
      _ = (5 / 2 : ℝ) * L ^ 5 := by ring

  have pulse0_zero (X : Matrix I I ℂ) : pulse0 X 0 = X := by
    simp [pulse0]

  have pulse0_quotient (X : Matrix I I ℂ) (s : ℝ) (hs : s ≠ 0) :
      pulse0 X s = ((s : ℂ) * Complex.I)⁻¹ •
        (NormedSpace.exp (((s : ℂ) * Complex.I) • X) - 1) := by
    let Z : Matrix I I ℂ := ((s : ℂ) * Complex.I) • X
    have harg (r : ℝ) :
        r • Z = s • ((((r : ℂ) * Complex.I) • X)) := by
      ext i j
      simp only [Z, Matrix.smul_apply,
        RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
      simp only [mul_comm, mul_left_comm, mul_assoc]
      congr 2
      exact mul_comm _ _
    have hpoint (r : ℝ) :
        NormedSpace.exp (r • Z) * Z =
          ((s : ℂ) * Complex.I) •
            (NormedSpace.exp (s • ((((r : ℂ) * Complex.I) • X))) * X) := by
      rw [harg]
      simp only [Z, mul_smul_comm]
    have hderiv (r : ℝ) :
        HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Z))
          (NormedSpace.exp (r • Z) * Z) r :=
      hasDerivAt_exp_smul_const Z r
    have hint : IntervalIntegrable
        (fun r : ℝ => NormedSpace.exp (r • Z) * Z)
        MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun r : ℝ => NormedSpace.exp (r • Z))
      (f' := fun r : ℝ => NormedSpace.exp (r • Z) * Z)
      (by intro r hr; exact hderiv r) hint
    have hcoef : (s : ℂ) * Complex.I ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast hs) Complex.I_ne_zero
    have hscaled : ((s : ℂ) * Complex.I) • pulse0 X s =
        NormedSpace.exp Z - 1 := by
      rw [pulse0, ← intervalIntegral.integral_smul]
      simpa only [hpoint, one_smul, zero_smul, NormedSpace.exp_zero,
        sub_eq_add_neg] using hFTC
    calc
      pulse0 X s = ((s : ℂ) * Complex.I)⁻¹ •
          (((s : ℂ) * Complex.I) • pulse0 X s) := by
        rw [smul_smul, inv_mul_cancel₀ hcoef, one_smul]
      _ = _ := by rw [hscaled]

  have pulse1_zero (X : Matrix I I ℂ) :
      pulse1 X 0 = (1 / 2 : ℝ) • (Complex.I • (X * X)) := by
    simp only [pulse1, zero_smul, NormedSpace.exp_zero, one_mul]
    have h (r : ℝ) : ((((r : ℂ) * Complex.I) • X) * X) =
        r • (Complex.I • (X * X)) := by
      rw [smul_mul_assoc, mul_smul]
      rfl
    simp_rw [h]
    rw [intervalIntegral.integral_smul_const]
    norm_num

  have complexify_isHermitian (A : Matrix I I ℝ) (hA : A.IsSymm) :
      (A.map Complex.ofReal).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.map_apply, hA.apply]

  have frob_complexify (A : Matrix I I ℝ) :
      ‖frobMap (A.map Complex.ofReal)‖ =
        @norm (Matrix I I ℝ) Matrix.frobeniusNormedAddCommGroup.toNorm A := by
    rw [frobMap_norm_eq, Matrix.frobenius_norm_def, Matrix.frobenius_norm_def]
    simp [Matrix.map_apply]

  have trace_complexify (A : Matrix I I ℝ) :
      Matrix.trace (A.map Complex.ofReal) = ((Matrix.trace A : ℝ) : ℂ) := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, Complex.ofReal_sum]

  have scalar1_zero_formula (A B C : Matrix I I ℂ) :
      scalar1 A B C 0 = (1 / 2 : ℝ) • (Complex.I •
        (Matrix.trace (A * A * B * C) + Matrix.trace (A * B * B * C) +
          Matrix.trace (A * B * C * C))) := by
    simp only [scalar1, triple1, pulse0_zero, pulse1_zero,
      add_mul, Matrix.trace_add, Matrix.trace_smul]
    simp only [smul_mul_assoc, mul_smul_comm, Matrix.trace_smul, Matrix.mul_assoc]
    module

  have trace_complexify_four (A B C D : Matrix I I ℝ) :
      Matrix.trace (A.map Complex.ofReal * B.map Complex.ofReal *
        C.map Complex.ofReal * D.map Complex.ofReal) =
        ((Matrix.trace (A * B * C * D) : ℝ) : ℂ) := by
    calc
      _ = Matrix.trace ((A * B * C * D).map Complex.ofReal) := by
        congr 1
        ext i j
        simp [Matrix.mul_apply, Complex.ofReal_sum]
      _ = _ := trace_complexify (A * B * C * D)

  have trace_complexify_three (A B C : Matrix I I ℝ) :
      Matrix.trace (A.map Complex.ofReal * B.map Complex.ofReal *
        C.map Complex.ofReal) =
        ((Matrix.trace (A * B * C) : ℝ) : ℂ) := by
    calc
      _ = Matrix.trace ((A * B * C).map Complex.ofReal) := by
        congr 1
        ext i j
        simp [Matrix.mul_apply, Complex.ofReal_sum]
      _ = _ := trace_complexify (A * B * C)

  have scalar1_zero_re (A B C : Matrix I I ℝ) :
      (scalar1 (A.map Complex.ofReal) (B.map Complex.ofReal)
        (C.map Complex.ofReal) 0).re = 0 := by
    rw [scalar1_zero_formula, trace_complexify_four A A B C,
      trace_complexify_four A B B C, trace_complexify_four A B C C]
    simp

  have second_order_comparison
      (g g1 g2 : ℝ → ℝ)
      (hg : ∀ x, HasDerivAt g (g1 x) x)
      (hg1 : ∀ x, HasDerivAt g1 (g2 x) x)
      (hzero : g1 0 = 0)
      {M : ℝ} (hbound : ∀ x, |g2 x| ≤ M)
      {t : ℝ} (ht : 0 ≤ t) :
      |g t - g 0| ≤ M * t ^ 2 / 2 := by
    have hfirst (s : ℝ) (hs : s ∈ Set.Icc 0 t) : |g1 s| ≤ M * s := by
      have h := norm_image_sub_le_of_norm_deriv_le_segment'
        (a := 0) (b := t) (f := g1) (f' := g2) (C := M)
        (by intro x hx; exact (hg1 x).hasDerivWithinAt)
        (by intro x hx; simpa [Real.norm_eq_abs] using hbound x)
        s hs
      simpa [hzero, Real.norm_eq_abs] using h
    let f : ℝ → ℝ := fun x => g x - g 0
    let B : ℝ → ℝ := fun x => M * x ^ 2 / 2
    let B' : ℝ → ℝ := fun x => M * x
    have hfcont : Continuous f := by
      apply continuous_iff_continuousAt.mpr
      intro x
      exact ((hg x).sub_const (g 0)).continuousAt
    have hfderiv (x : ℝ) : HasDerivAt f (g1 x) x := by
      simpa [f] using (hg x).sub_const (g 0)
    have hBderiv (x : ℝ) : HasDerivAt B (B' x) x := by
      convert ((hasDerivAt_id x).pow 2).const_mul (M / 2) using 1 <;>
        first | rfl | (simp [B, B']; ring)
    have hcomp := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (a := 0) (b := t) (f := f) (f' := g1) (B := B) (B' := B')
      hfcont.continuousOn
      (by intro x hx; exact (hfderiv x).hasDerivWithinAt)
      (by simp [f, B]) hBderiv
      (by intro x hx; simpa [Real.norm_eq_abs, B'] using hfirst x ⟨hx.1, hx.2.le⟩)
      (show t ∈ Set.Icc 0 t from ⟨ht, le_refl _⟩)
    simpa [f, B, Real.norm_eq_abs] using hcomp

  refine ⟨fun X => pulse0_zero X, fun X s hs => pulse0_quotient X s hs, ?_⟩
  let Ac : Matrix I I ℂ := A.map Complex.ofReal
  let Bc : Matrix I I ℂ := B.map Complex.ofReal
  let Cc : Matrix I I ℂ := C.map Complex.ofReal
  have hAc : Ac.IsHermitian := complexify_isHermitian A hA
  have hBc : Bc.IsHermitian := complexify_isHermitian B hB
  have hCc : Cc.IsHermitian := complexify_isHermitian C hC
  have hAcNorm : ‖frobMap Ac‖ ≤ L := by
    simpa only [Ac, frob_complexify] using hAn
  have hBcNorm : ‖frobMap Bc‖ ≤ L := by
    simpa only [Bc, frob_complexify] using hBn
  have hCcNorm : ‖frobMap Cc‖ ≤ L := by
    simpa only [Cc, frob_complexify] using hCn
  let g : ℝ → ℝ := fun s => (scalar0 Ac Bc Cc s).re
  let g1 : ℝ → ℝ := fun s => (scalar1 Ac Bc Cc s).re
  let g2 : ℝ → ℝ := fun s => (scalar2 Ac Bc Cc s).re
  have hg (s : ℝ) : HasDerivAt g (g1 s) s := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
      (scalar0_hasDerivAt Ac Bc Cc hAc hBc hCc s)
    convert h using 1 <;> rfl
  have hg1 (s : ℝ) : HasDerivAt g1 (g2 s) s := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
      (scalar1_hasDerivAt Ac Bc Cc hAc hBc hCc s)
    convert h using 1 <;> rfl
  have hg10 : g1 0 = 0 := scalar1_zero_re A B C
  have hbound (s : ℝ) : |g2 s| ≤ (5 / 2 : ℝ) * L ^ 5 := by
    exact (Complex.abs_re_le_norm _).trans
      (scalar2_bound Ac Bc Cc hAc hBc hCc hL hAcNorm hBcNorm hCcNorm s)
  have hg0 : g 0 = Matrix.trace (A * B * C) := by
    simp only [g, scalar0, triple0, pulse0_zero]
    simpa only [Complex.ofReal_re] using congrArg Complex.re
      (trace_complexify_three A B C)
  have h := second_order_comparison g g1 g2 hg hg1 hg10 hbound ht.le
  rw [hg0] at h
  convert h using 1 <;> ring

end
end D5.S3.Quantum.Dynamics.OrderedThreePulseTrace
