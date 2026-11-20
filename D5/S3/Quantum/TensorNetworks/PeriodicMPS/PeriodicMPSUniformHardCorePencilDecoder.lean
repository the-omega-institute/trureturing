/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCorePencilDecoder
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCorePencilDecoder
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformDeterminantPencil, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreOrdinary, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity]
   utility: none
   digest: A determinant pencil extracted from the full tensor gives a continuous ordinary-invariant decoder near the cyclic hard-core tensor. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformDeterminantPencil
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformHardCoreOrdinary
import D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Local decoding of ordinary invariants from the full periodic trace tensor. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCorePencilDecoder

open PeriodicMPSParentIntersection (Bond Word wordMatrix)
open PeriodicMPSUniformDeterminantPencil
open PeriodicMPSUniformHardCoreOrdinary
  (singletonWord pairWord traceWord_vacuum traceWord_singletonWord traceWord_pairWord)
open PeriodicMPSUniformZeroCorner (trace_pow_succ_of_det_eq_zero)
open PeriodicMPSAmbiguityDensity (changePhysical)
open UniformMPSExpectedDimensionRefutation (traceWord)
open D5.S0.Observation.MatrixTracePowerSum (pow_add_two)
open scoped BigOperators Matrix Topology
open Set Filter

open private wordBasis wordMatrix_changePhysical changePhysical_one
  from D5.S3.Quantum.TensorNetworks.PeriodicMPSAmbiguityDensity

noncomputable section

abbrev Tensor (n : ℕ) := Word n → ℂ

/-- Contract the literal tensor against the rows of a physical frame. -/
def contract {n : ℕ} (U : Bond) (T : Tensor n) (w : Word n) : ℂ :=
  ∑ v : Word n, (∏ i, U (w i) (v i)) * T v

theorem contract_traceWord {n : ℕ} (U : Bond) (A : Fin 2 → Bond) (w : Word n) :
    contract U (traceWord 2 2 n A) w = traceWord 2 2 n (changePhysical U A) w := by
  change _ = (wordMatrix (changePhysical U A) w).trace
  rw [wordMatrix_changePhysical]
  simp only [Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, wordBasis, contract, traceWord, wordMatrix]

theorem contract_smul {n : ℕ} (U : Bond) (T : Tensor n) (z : ℂ) (w : Word n) :
    contract U (z • T) w = z * contract U T w := by
  simp only [contract, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem continuous_contract {n : ℕ} (w : Word n) :
    Continuous (fun p : Bond × Tensor n => contract p.1 p.2 w) := by
  unfold contract
  fun_prop

/-- The rotated amplitudes of the vacuum, one final one, and two adjacent final ones. -/
def p0 {n : ℕ} (U : Bond) (T : Tensor n) : ℂ :=
  contract U T (fun _ => 0)

def p1 {n : ℕ} (hn : 3 ≤ n) (U : Bond) (T : Tensor n) : ℂ :=
  contract U T (singletonWord (n - 1) (by omega))

def p2 {n : ℕ} (hn : 3 ≤ n) (U : Bond) (T : Tensor n) : ℂ :=
  contract U T (pairWord (n - 2) 0 (by omega))

private theorem pow_succ_singular (C : Bond) (hC : C.det = 0) (m : ℕ) :
    C ^ (m + 1) = C.trace ^ m • C := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_add_two, hC, zero_smul, sub_zero, ih, smul_smul, pow_succ']

private theorem trace_pow_mul_singular (C D : Bond) (hC : C.det = 0) (m : ℕ) :
    (C ^ (m + 1) * D).trace = C.trace ^ m * (C * D).trace := by
  rw [pow_succ_singular C hC, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- Exact readouts for the two singular generators in the chosen physical frame. -/
theorem p012_singular {n : ℕ} (hn : 3 ≤ n) (U : Bond) (A : Fin 2 → Bond)
    (hC : (changePhysical U A 0).det = 0) (hD : (changePhysical U A 1).det = 0) :
    let C := changePhysical U A 0
    let D := changePhysical U A 1
    let T := traceWord 2 2 n A
    p0 U T = C.trace ^ n ∧
      p1 hn U T = C.trace ^ (n - 2) * (C * D).trace ∧
      p2 hn U T = C.trace ^ (n - 3) * D.trace * (C * D).trace := by
  dsimp only
  let P := changePhysical U A
  refine ⟨?_, ?_, ?_⟩
  · rw [p0, contract_traceWord, traceWord_vacuum]
    simpa only [show n - 1 + 1 = n by omega] using
      trace_pow_succ_of_det_eq_zero (P 0) hC (n - 1)
  · rw [p1, contract_traceWord, traceWord_singletonWord]
    simpa only [show n - 2 + 1 = n - 1 by omega] using
      trace_pow_mul_singular (P 0) (P 1) hC (n - 2)
  · rw [p2, contract_traceWord, traceWord_pairWord P hD]
    simp only [pow_zero, one_mul]
    rw [show n - 2 = (n - 3) + 1 by omega, trace_pow_mul_singular (P 0) (P 1) hC]
    ring

/-- The two ratios survive an arbitrary common rescaling of the tensor. -/
theorem p012_ratios_singular {n : ℕ} (hn : 3 ≤ n) (U : Bond) (A : Fin 2 → Bond)
    (z : ℂ) (T : Tensor n) (hT : T = z • traceWord 2 2 n A)
    (hC : (changePhysical U A 0).det = 0) (hD : (changePhysical U A 1).det = 0)
    (h0 : p0 U T ≠ 0) (h1 : p1 hn U T ≠ 0) :
    let C := changePhysical U A 0
    let D := changePhysical U A 1
    C.trace ≠ 0 ∧
      p2 hn U T / p1 hn U T = D.trace / C.trace ∧
      p1 hn U T / p0 U T = (C * D).trace / C.trace ^ 2 := by
  let C := changePhysical U A 0
  let D := changePhysical U A 1
  obtain ⟨e0, e1, e2⟩ := p012_singular hn U A hC hD
  have f0 : p0 U T = z * C.trace ^ n := by
    rw [hT, p0, contract_smul, ← p0, e0]
  have f1 : p1 hn U T = z * (C.trace ^ (n - 2) * (C * D).trace) := by
    rw [hT, p1, contract_smul]
    exact congrArg (z * ·) e1
  have f2 : p2 hn U T = z * (C.trace ^ (n - 3) * D.trace * (C * D).trace) := by
    rw [hT, p2, contract_smul]
    exact congrArg (z * ·) e2
  have hz : z ≠ 0 := fun h => h0 (by simp [f0, h])
  have hu : C.trace ≠ 0 := fun h => h0 (by simp [f0, h, show n ≠ 0 by omega])
  have hk : (C * D).trace ≠ 0 := fun h => h1 (by simp [f1, h])
  change C.trace ≠ 0 ∧ p2 hn U T / p1 hn U T = D.trace / C.trace ∧
    p1 hn U T / p0 U T = (C * D).trace / C.trace ^ 2
  refine ⟨hu, ?_, ?_⟩
  · rw [f2, f1, show n - 2 = n - 3 + 1 by omega, pow_succ]
    field_simp
  · have hpow : C.trace ^ n = C.trace ^ (n - 2) * C.trace ^ 2 := by
      rw [← pow_add, show n - 2 + 2 = n by omega]
    rw [f1, f0, hpow]
    field_simp

open Polynomial (C X)

/-- The coefficient of the mixed term in the binary determinant pencil. -/
def crossDet (A B : Bond) : ℂ :=
  A.trace * B.trace - (A * B).trace

theorem det_pencil_binary (A : Fin 2 → Bond) (x y : ℂ) :
    (pencil A ![x, y]).det =
      (A 0).det * x ^ 2 + crossDet (A 0) (A 1) * x * y + (A 1).det * y ^ 2 := by
  simp only [pencil, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.det_fin_two,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, crossDet, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem guardedFlattening_smul (n : ℕ) (hn : 7 ≤ n)
    (T : Tensor n) (z : ℂ) (v : Fin 2 → ℂ) :
    guardedFlattening n hn (z • T) v = z • guardedFlattening n hn T v := by
  ext i j
  simp only [guardedFlattening, observedFlattening, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

/-- The guarded determinant with the physical slot contracted by `(1, 1 + X)`. -/
def guardedPolynomial (n : ℕ) (hn : 7 ≤ n) (T : Tensor n) : Polynomial ℂ :=
  Matrix.det (Matrix.of fun i j : Guard =>
    C (guardedFlattening n hn T 1 i j) +
      C (guardedFlattening n hn T ![0, 1] i j) * X)

set_option backward.isDefEq.respectTransparency false in
theorem eval_guardedPolynomial (n : ℕ) (hn : 7 ≤ n) (T : Tensor n) (s : ℂ) :
    (guardedPolynomial n hn T).eval s = (guardedFlattening n hn T ![1, 1+s]).det := by
  change Polynomial.evalRingHom s (guardedPolynomial n hn T) = _
  rw [guardedPolynomial, RingHom.map_det]
  congr 1
  ext i j
  simp [guardedFlattening, observedFlattening, Fin.sum_univ_two]
  ring

/-- Exact polynomial identity valid at every nonzero complex scale and also at scale zero. -/
theorem guardedPolynomial_scaled_traceWord (n : ℕ) (hn : 7 ≤ n)
    (A : Fin 2 → Bond) (z : ℂ) :
    guardedPolynomial n hn (z • traceWord 2 2 n A) =
      C (z ^ 4 * guardCoefficient n A) *
        (C ((pencil A 1).det) +
          C (crossDet (A 0) (A 1) + 2 * (A 1).det) * X + C (A 1).det * X ^ 2) ^ 2 := by
  apply Polynomial.funext
  intro s
  rw [eval_guardedPolynomial, guardedFlattening_smul, Matrix.det_smul,
    det_guardedFlattening_traceWord, det_pencil_binary]
  have hval : (1 : Fin 2 → ℂ) = ![1, 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hval, det_pencil_binary]
  simp [Fintype.card_prod]
  ring

/-- The constant and first two coefficients determine the normalized square root
with constant coefficient one. -/
def pencilCoefficients (n : ℕ) (hn : 7 ≤ n) (T : Tensor n) : ℂ × ℂ :=
  let H := guardedPolynomial n hn T
  let d₁ := H.coeff 1 / (2 * H.coeff 0)
  (d₁, (H.coeff 2 / H.coeff 0 - d₁ ^ 2) / 2)

/-- The decoded homogeneous quadratic, in the original physical labels. -/
def decodedPencil (d : ℂ × ℂ) (x y : ℂ) : ℂ :=
  x ^ 2 + d.1 * x * (y - x) + d.2 * (y - x) ^ 2

private theorem coefficients_of_quadratic_square (k d l e : ℂ) :
    let H := C k * (C d + C l * X + C e * X ^ 2) ^ 2
    H.coeff 0 = k * d ^ 2 ∧ H.coeff 1 = k * (2 * d * l) ∧
      H.coeff 2 = k * (l ^ 2 + 2 * d * e) := by
  dsimp only
  norm_num [Polynomial.coeff_C_mul, pow_two (C d + C l * X + C e * X ^ 2),
    Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ, Polynomial.coeff_C,
    Polynomial.coeff_X_pow, Polynomial.coeff_X]
  refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩ <;> ring

theorem pencilCoefficients_scaled_traceWord (n : ℕ) (hn : 7 ≤ n)
    (A : Fin 2 → Bond) (z : ℂ)
    (hH : (guardedPolynomial n hn (z • traceWord 2 2 n A)).coeff 0 ≠ 0) :
    (pencil A 1).det ≠ 0 ∧
      pencilCoefficients n hn (z • traceWord 2 2 n A) =
        ((crossDet (A 0) (A 1) + 2 * (A 1).det) / (pencil A 1).det,
          (A 1).det / (pencil A 1).det) := by
  obtain ⟨h0, h1, h2⟩ := coefficients_of_quadratic_square (z ^ 4 * guardCoefficient n A)
    (pencil A 1).det (crossDet (A 0) (A 1) + 2 * (A 1).det) (A 1).det
  dsimp only [pencilCoefficients]
  rw [guardedPolynomial_scaled_traceWord] at hH ⊢
  rw [h0] at hH
  obtain ⟨hz4, hk⟩ := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hH).1
  have hz : z ≠ 0 := fun he => hz4 (by simp [he])
  have hd := (pow_ne_zero_iff two_ne_zero).mp (mul_ne_zero_iff.mp hH).2
  refine ⟨hd, ?_⟩
  rw [h0, h1, h2]
  congr 1
  · field_simp
  · field_simp
    ring

theorem decodedPencil_scaled_traceWord (n : ℕ) (hn : 7 ≤ n)
    (A : Fin 2 → Bond) (z : ℂ)
    (hH : (guardedPolynomial n hn (z • traceWord 2 2 n A)).coeff 0 ≠ 0) (x y : ℂ) :
    decodedPencil (pencilCoefficients n hn (z • traceWord 2 2 n A)) x y =
      (pencil A ![x, y]).det / (pencil A 1).det := by
  obtain ⟨hd, hc⟩ := pencilCoefficients_scaled_traceWord n hn A z hH
  have D : (pencil A 1).det = (A 0).det + crossDet (A 0) (A 1) + (A 1).det := by
    have hval : (1 : Fin 2 → ℂ) = ![1, 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hval, det_pencil_binary]
    ring
  rw [hc, decodedPencil, det_pencil_binary]
  field_simp
  linear_combination x ^ 2 * D

private theorem continuous_guardedEntry (n : ℕ) (hn : 7 ≤ n) (v : Fin 2 → ℂ) (i j : Guard) :
    Continuous (fun T : Tensor n => guardedFlattening n hn T v i j) := by
  unfold guardedFlattening observedFlattening
  fun_prop

private theorem continuous_coeff_prod {ι Y : Type*} [TopologicalSpace Y]
    (s : Finset ι) (F : ι → Y → Polynomial ℂ)
    (hF : ∀ i ∈ s, ∀ j, Continuous (fun y => (F i y).coeff j)) (j : ℕ) :
    Continuous (fun y => (∏ i ∈ s, F i y).coeff j) := by
  classical
  induction s using Finset.induction generalizing j with
  | empty => simpa using continuous_const (y := (1 : Polynomial ℂ).coeff j)
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Polynomial.coeff_mul]
    refine continuous_finsetSum _ (fun k _ => ?_)
    exact (hF i (Finset.mem_insert_self i s) k.1).mul
      (ih (fun a ha => hF a (Finset.mem_insert_of_mem ha)) k.2)

set_option backward.isDefEq.respectTransparency false in
theorem continuous_guardedCoeff (n : ℕ) (hn : 7 ≤ n) (j : ℕ) :
    Continuous (fun T : Tensor n => (guardedPolynomial n hn T).coeff j) := by
  classical
  simp only [guardedPolynomial, Matrix.det_apply', Polynomial.finsetSum_coeff,
    ← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, Matrix.of_apply]
  refine continuous_finsetSum _ (fun σ _ => continuous_const.mul ?_)
  apply continuous_coeff_prod
  intro i _ k
  simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
    Polynomial.coeff_X]
  split_ifs <;> simp only [mul_one, mul_zero, add_zero, zero_add]
  all_goals
    first
    | exact continuous_guardedEntry n hn (1 : Fin 2 → ℂ) (σ i) i
    | exact continuous_guardedEntry n hn ![0, 1] (σ i) i
    | exact (continuous_guardedEntry n hn 1 (σ i) i).add
        (continuous_guardedEntry n hn ![0, 1] (σ i) i)
    | exact (continuous_const : Continuous (fun _ : Tensor n => (0 : ℂ)))

theorem continuousAt_pencilCoefficients (n : ℕ) (hn : 7 ≤ n) (T : Tensor n)
    (hH : (guardedPolynomial n hn T).coeff 0 ≠ 0) :
    ContinuousAt (pencilCoefficients n hn) T := by
  have h (j : ℕ) := (continuous_guardedCoeff n hn j).continuousAt (x := T)
  have h₁ : ContinuousAt (fun S => (guardedPolynomial n hn S).coeff 1 /
      (2 * (guardedPolynomial n hn S).coeff 0)) T :=
    (h 1).div (continuousAt_const.mul (h 0)) (mul_ne_zero two_ne_zero hH)
  exact h₁.prodMk (((h 2).div (h 0) hH).sub (h₁.pow 2) |>.div_const 2)

open scoped ContDiff

private def rootEquation (p : (ℂ × ℂ) × ℂ) : ℂ :=
  decodedPencil p.1 1 p.2

private theorem rootEquation_smooth :
    ContDiffAt ℂ ω rootEquation ((1, 0), 0) := by
  unfold rootEquation decodedPencil
  fun_prop

private theorem rootEquation_derivative :
    (fderiv ℂ rootEquation ((1, 0), 0) ∘L ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ) =
      ContinuousLinearMap.id ℂ ℂ := by
  have h := fderiv_comp (x := (0 : ℂ)) (g := rootEquation)
    (rootEquation_smooth.differentiableAt (by simp))
    (hasFDerivAt_prodMk_right (𝕜 := ℂ) ((1, 0) : ℂ × ℂ) (0 : ℂ)).differentiableAt
  have hf : rootEquation ∘ (fun x : ℂ => (((1, 0) : ℂ × ℂ), x)) = id := by
    funext x
    simp [rootEquation, decodedPencil]
  rw [hf, fderiv_id, (hasFDerivAt_prodMk_right (𝕜 := ℂ) ((1, 0) : ℂ × ℂ) (0 : ℂ)).fderiv] at h
  exact h.symm

private theorem rootEquation_invertible :
    (fderiv ℂ rootEquation ((1, 0), 0) ∘L ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ).IsInvertible := by
  rw [rootEquation_derivative]
  exact ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℂ ℂ)

/-- The root `(1, a)` of the normalized homogeneous pencil near `(1, 0)`. -/
def firstRoot : ℂ × ℂ → ℂ :=
  rootEquation_smooth.implicitFunction (by simp) rootEquation_invertible

@[simp] theorem firstRoot_base : firstRoot (1, 0) = 0 :=
  rootEquation_smooth.implicitFunction_apply_self (by simp) rootEquation_invertible

theorem analyticAt_firstRoot : AnalyticAt ℂ firstRoot (1, 0) :=
  (rootEquation_smooth.contDiffAt_implicitFunction (by simp) rootEquation_invertible).analyticAt

theorem eventually_firstRoot :
    ∀ᶠ d : ℂ × ℂ in 𝓝 (1, 0), decodedPencil d 1 (firstRoot d) = 0 := by
  have h := rootEquation_smooth.eventually_apply_implicitFunction (by simp) rootEquation_invertible
  simpa only [firstRoot, rootEquation, decodedPencil, Prod.fst, Prod.snd, one_pow,
    mul_one, zero_mul, add_zero, zero_sub, mul_neg, mul_one, add_neg_cancel] using h

private def swapCoefficients (d : ℂ × ℂ) : ℂ × ℂ :=
  (2 - d.1, 1 - d.1 + d.2)

private theorem swapCoefficients_base : swapCoefficients (1, 0) = (1, 0) := by
  norm_num [swapCoefficients]

private theorem decodedPencil_swap (d : ℂ × ℂ) (x : ℂ) :
    decodedPencil (swapCoefficients d) 1 x = decodedPencil d x 1 := by
  simp only [swapCoefficients, decodedPencil]
  ring

/-- The root `(b, 1)` of the normalized homogeneous pencil near `(0, 1)`. -/
def secondRoot (d : ℂ × ℂ) : ℂ :=
  firstRoot (swapCoefficients d)

@[simp] theorem secondRoot_base : secondRoot (1, 0) = 0 := by
  rw [secondRoot, swapCoefficients_base, firstRoot_base]

private theorem continuous_swapCoefficients : Continuous swapCoefficients := by
  unfold swapCoefficients
  fun_prop

theorem analyticAt_secondRoot : AnalyticAt ℂ secondRoot (1, 0) := by
  have hswap : AnalyticAt ℂ swapCoefficients (1, 0) := by
    apply ContDiffAt.analyticAt
    unfold swapCoefficients
    fun_prop
  unfold secondRoot
  apply AnalyticAt.comp _ hswap
  rw [swapCoefficients_base]
  exact analyticAt_firstRoot

theorem eventually_secondRoot :
    ∀ᶠ d : ℂ × ℂ in 𝓝 (1, 0), decodedPencil d (secondRoot d) 1 = 0 := by
  have h : Tendsto swapCoefficients (𝓝 (1, 0)) (𝓝 (1, 0)) := by
    have hc : ContinuousAt swapCoefficients (1, 0) := continuous_swapCoefficients.continuousAt
    unfold ContinuousAt at hc
    rwa [swapCoefficients_base] at hc
  filter_upwards [h.eventually eventually_firstRoot] with d hd
  rw [secondRoot, ← decodedPencil_swap]
  exact hd

private def frame (a b : ℂ) : Bond := !![1, a; b, 1]

private theorem frame_zero : frame 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frame]

private theorem changePhysical_frame (a b : ℂ) (A : Fin 2 → Bond) :
    changePhysical (frame a b) A 0 = pencil A ![1, a] ∧
      changePhysical (frame a b) A 1 = pencil A ![b, 1] := by
  simp [changePhysical, frame, pencil, Fin.sum_univ_two]

private theorem continuous_frame : Continuous (fun p : ℂ × ℂ => frame p.1 p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp only [frame, Matrix.of_apply] <;> fun_prop

/-- The four affine coordinates obtained by setting the original first trace to one.
The entries are the second trace, the two determinants, and the mixed trace. -/
def ordinaryInvariants (A : Fin 2 → Bond) : ℂ × ℂ × ℂ × ℂ :=
  let t := (A 0).trace
  ((A 1).trace / t, (A 0).det / t ^ 2, (A 1).det / t ^ 2, (A 0 * A 1).trace / t ^ 2)

private def fromFrame (a b v k : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  let t := 1 - a * v
  ((v - b) / t, -a * (v - k) / t ^ 2, -b * (v - k) / t ^ 2,
    ((1 + a * b) * k - b - a * v ^ 2) / t ^ 2)

private theorem inverseFrame (a b : ℂ) (A : Fin 2 → Bond) :
    let C := changePhysical (frame a b) A 0
    let D := changePhysical (frame a b) A 1
    C - a • D = (1 - a * b) • A 0 ∧ D - b • C = (1 - a * b) • A 1 := by
  obtain ⟨hC, hD⟩ := changePhysical_frame a b A
  dsimp only
  rw [hC, hD]
  simp only [pencil, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul]
  constructor <;> module

private theorem det_sub_singular (C D : Bond) (hC : C.det = 0) (hD : D.det = 0) (a : ℂ) :
    (C - a • D).det = -a * crossDet C D := by
  have h := det_pencil_binary ![C, D] 1 (-a)
  simpa [pencil, sub_eq_add_neg, hC, hD, mul_comm] using h

private theorem mixed_sub_singular (C D : Bond) (hC : C.det = 0) (hD : D.det = 0)
    (a b : ℂ) :
    ((C - a • D) * (D - b • C)).trace =
      (1 + a * b) * (C * D).trace - b * C.trace ^ 2 - a * D.trace ^ 2 := by
  have hCC : (C * C).trace = C.trace ^ 2 := by
    simpa only [show 1 + 1 = 2 by decide, pow_two] using trace_pow_succ_of_det_eq_zero C hC 1
  have hDD : (D * D).trace = D.trace ^ 2 := by
    simpa only [show 1 + 1 = 2 by decide, pow_two] using trace_pow_succ_of_det_eq_zero D hD 1
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul, hCC, hDD, Matrix.trace_mul_comm D C]
  ring

private theorem fromFrame_eq_ordinary (a b : ℂ) (A : Fin 2 → Bond)
    (hq : 1 - a * b ≠ 0)
    (hC : (changePhysical (frame a b) A 0).det = 0)
    (hD : (changePhysical (frame a b) A 1).det = 0)
    (hu : (changePhysical (frame a b) A 0).trace ≠ 0)
    (ht : 1 - a * ((changePhysical (frame a b) A 1).trace /
      (changePhysical (frame a b) A 0).trace) ≠ 0) :
    (A 0).trace ≠ 0 ∧
      fromFrame a b ((changePhysical (frame a b) A 1).trace /
        (changePhysical (frame a b) A 0).trace)
        ((changePhysical (frame a b) A 0 * changePhysical (frame a b) A 1).trace /
          (changePhysical (frame a b) A 0).trace ^ 2) = ordinaryInvariants A := by
  let C := changePhysical (frame a b) A 0
  let D := changePhysical (frame a b) A 1
  let E := C - a • D
  let F := D - b • C
  obtain ⟨hE, hF⟩ := inverseFrame a b A
  change E = _ at hE
  change F = _ at hF
  change C.det = 0 at hC
  change D.det = 0 at hD
  change C.trace ≠ 0 at hu
  change 1 - a * (D.trace / C.trace) ≠ 0 at ht
  have he : E.trace = C.trace * (1 - a * (D.trace / C.trace)) := by
    simp only [E, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
    field_simp
  have he' : E.trace ≠ 0 := by rw [he]; exact mul_ne_zero hu ht
  have hA : (A 0).trace ≠ 0 := by
    intro h
    exact he' (by simp [hE, h])
  refine ⟨hA, ?_⟩
  let P : Fin 2 → Bond := ![E, F]
  have hp : ordinaryInvariants P = ordinaryInvariants A := by
    simp only [ordinaryInvariants, P, Matrix.cons_val_zero, Matrix.cons_val_one,
      hE, hF, Matrix.trace_smul, smul_eq_mul, Matrix.det_smul, Fintype.card_fin,
      Matrix.smul_mul, Matrix.mul_smul]
    apply Prod.ext
    · field_simp
    apply Prod.ext
    · field_simp
    apply Prod.ext <;> field_simp
  rw [← hp]
  change fromFrame a b (D.trace / C.trace) ((C * D).trace / C.trace ^ 2) = _
  have hf : F.trace = D.trace - b * C.trace := by simp [F]
  have hed : E.det = -a * crossDet C D := det_sub_singular C D hC hD a
  have hfd : F.det = -b * crossDet C D := by
    change (D - b • C).det = _
    rw [det_sub_singular D C hD hC]
    simp only [crossDet, Matrix.trace_mul_comm D C, mul_comm D.trace C.trace]
  have hm : (E * F).trace = _ := mixed_sub_singular C D hC hD a b
  simp only [fromFrame, ordinaryInvariants, P, Matrix.cons_val_zero, Matrix.cons_val_one,
    he, hf, hed, hfd, hm, crossDet]
  apply Prod.ext
  · field_simp
  apply Prod.ext
  · field_simp
  apply Prod.ext <;> field_simp

/-- The representative of the independent-set tensor with vacuum amplitude one. -/
def witnessTensor (n : ℕ) : Tensor n := traceWord 2 2 n witnessCore

private theorem guardedPolynomial_witness (n : ℕ) (hn : 7 ≤ n) :
    guardedPolynomial n hn (witnessTensor n) = -(1 + X) ^ 2 := by
  apply Polynomial.funext
  intro s
  rw [eval_guardedPolynomial, witnessTensor, det_guardedFlattening_witness]
  simp

private theorem guardedCoeff_zero_witness (n : ℕ) (hn : 7 ≤ n) :
    (guardedPolynomial n hn (witnessTensor n)).coeff 0 = -1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, guardedPolynomial_witness]
  simp

private theorem pencilCoefficients_witness (n : ℕ) (hn : 7 ≤ n) :
    pencilCoefficients n hn (witnessTensor n) = (1, 0) := by
  have h := coefficients_of_quadratic_square (-1) 1 1 0
  norm_num at h
  obtain ⟨h0, h1, h2⟩ := h
  unfold pencilCoefficients
  rw [guardedPolynomial_witness]
  norm_num [h0, h1, h2]

private theorem p012_witness (n : ℕ) (hn : 3 ≤ n) :
    p0 1 (witnessTensor n) = 1 ∧ p1 hn 1 (witnessTensor n) = 1 ∧
      p2 hn 1 (witnessTensor n) = 0 := by
  have hC : (witnessCore 0).det = 0 := by norm_num [witnessCore, Matrix.det_fin_two]
  have hD : (witnessCore 1).det = 0 := by norm_num [witnessCore, Matrix.det_fin_two]
  have hu : (witnessCore 0).trace = 1 := by norm_num [witnessCore, Matrix.trace_fin_two]
  have hv : (witnessCore 1).trace = 0 := by norm_num [witnessCore, Matrix.trace_fin_two]
  have hk : (witnessCore 0 * witnessCore 1).trace = 1 := by
    norm_num [witnessCore, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have h := p012_singular hn 1 witnessCore (by simpa only [changePhysical_one] using hC)
    (by simpa only [changePhysical_one] using hD)
  simpa only [changePhysical_one, hu, hv, hk, one_pow, mul_one, mul_zero, witnessTensor] using h

private def roots (n : ℕ) (hn : 7 ≤ n) (T : Tensor n) : ℂ × ℂ :=
  let d := pencilCoefficients n hn T
  (firstRoot d, secondRoot d)

private def physicalFrame (n : ℕ) (hn : 7 ≤ n) (T : Tensor n) : Bond :=
  frame (roots n hn T).1 (roots n hn T).2

@[simp] private theorem roots_witness (n : ℕ) (hn : 7 ≤ n) :
    roots n hn (witnessTensor n) = (0, 0) := by
  simp [roots, pencilCoefficients_witness]

@[simp] private theorem physicalFrame_witness (n : ℕ) (hn : 7 ≤ n) :
    physicalFrame n hn (witnessTensor n) = 1 := by
  simp [physicalFrame, frame_zero]

private def ratios (n : ℕ) (hn : 7 ≤ n) (T : Tensor n) : ℂ × ℂ :=
  let U := physicalFrame n hn T
  (p2 (by omega) U T / p1 (by omega) U T, p1 (by omega) U T / p0 U T)

/-- The local ordinary invariant decoder on ambient tensor coordinates. -/
def ordinaryDecoder (n : ℕ) (hn : 7 ≤ n) (T : Tensor n) : ℂ × ℂ × ℂ × ℂ :=
  fromFrame (roots n hn T).1 (roots n hn T).2 (ratios n hn T).1 (ratios n hn T).2

@[simp] theorem ordinaryDecoder_witness (n : ℕ) (hn : 7 ≤ n) :
    ordinaryDecoder n hn (witnessTensor n) = (0, 0, 0, 1) := by
  obtain ⟨h0, h1, h2⟩ := p012_witness n (by omega)
  simp [ordinaryDecoder, fromFrame, ratios, h0, h1, h2]

private theorem continuousAt_contract_frame {n : ℕ} {U : Tensor n → Bond} {T : Tensor n}
    (h : ContinuousAt U T) (w : Word n) :
    ContinuousAt (fun S => contract (U S) S w) T := by
  have hc := (continuous_contract w).continuousAt (x := (U T, T))
  exact hc.comp₂ h (continuousAt_id' T)

private theorem continuousAt_ratios (n : ℕ) (hn : 7 ≤ n) (T : Tensor n)
    (h : ContinuousAt (physicalFrame n hn) T)
    (h0 : p0 (physicalFrame n hn T) T ≠ 0) (h1 : p1 (by omega) (physicalFrame n hn T) T ≠ 0) :
    ContinuousAt (ratios n hn) T := by
  have c0 : ContinuousAt (fun S => p0 (physicalFrame n hn S) S) T :=
    continuousAt_contract_frame h (fun _ => 0)
  have c1 : ContinuousAt (fun S => p1 (by omega) (physicalFrame n hn S) S) T :=
    continuousAt_contract_frame h (singletonWord (n - 1) (by omega))
  have c2 : ContinuousAt (fun S => p2 (by omega) (physicalFrame n hn S) S) T :=
    continuousAt_contract_frame h (pairWord (n - 2) 0 (by omega))
  exact (c2.div c1 h1).prodMk (c1.div c0 h0)

private theorem eventually_pencil_roots (n : ℕ) (hn : 7 ≤ n) :
    ∀ᶠ T in 𝓝 (witnessTensor n),
      (guardedPolynomial n hn T).coeff 0 ≠ 0 ∧
      ContinuousAt (roots n hn) T ∧
      decodedPencil (pencilCoefficients n hn T) 1 (roots n hn T).1 = 0 ∧
      decodedPencil (pencilCoefficients n hn T) (roots n hn T).2 1 = 0 := by
  have h0 : (guardedPolynomial n hn (witnessTensor n)).coeff 0 ≠ 0 := by
    rw [guardedCoeff_zero_witness]
    exact neg_ne_zero.mpr one_ne_zero
  have hc : Tendsto (pencilCoefficients n hn) (𝓝 (witnessTensor n)) (𝓝 (1, 0)) := by
    have h := continuousAt_pencilCoefficients n hn (witnessTensor n) h0
    unfold ContinuousAt at h
    rwa [pencilCoefficients_witness] at h
  filter_upwards [(continuous_guardedCoeff n hn 0).continuousAt.eventually_ne h0,
    hc.eventually analyticAt_firstRoot.eventually_continuousAt,
    hc.eventually analyticAt_secondRoot.eventually_continuousAt,
    hc.eventually eventually_firstRoot, hc.eventually eventually_secondRoot] with T hT ha hb hfa hfb
  have h := continuousAt_pencilCoefficients n hn T hT
  exact ⟨hT, (ha.comp h).prodMk (hb.comp h), hfa, hfb⟩

private theorem continuousAt_fromFrame {Y : Type*} [TopologicalSpace Y] {T : Y}
    {a b v k : Y → ℂ} (ha : ContinuousAt a T) (hb : ContinuousAt b T)
    (hv : ContinuousAt v T) (hk : ContinuousAt k T) (ht : 1 - a T * v T ≠ 0) :
    ContinuousAt (fun S => fromFrame (a S) (b S) (v S) (k S)) T := by
  have h := continuousAt_const (y := (1 : ℂ)) |>.sub (ha.mul hv)
  have h₂ := h.pow 2
  have ht₂ := pow_ne_zero 2 ht
  exact ((hv.sub hb).div h ht).prodMk
    (((ha.neg.mul (hv.sub hk)).div h₂ ht₂).prodMk
      (((hb.neg.mul (hv.sub hk)).div h₂ ht₂).prodMk
        (((((continuousAt_const.add (ha.mul hb)).mul hk).sub hb).sub
          (ha.mul (hv.pow 2))).div h₂ ht₂)))

/-- Ordinary invariants of every representing pair in an open neighborhood of the
full independent-set tensor. The equality allows any complex scalar representative. -/
theorem exists_open_ordinaryDecoder (n : ℕ) (hn : 7 ≤ n) :
    ∃ V : Set (Tensor n), IsOpen V ∧ witnessTensor n ∈ V ∧
      ContinuousOn (ordinaryDecoder n hn) V ∧
      ∀ T ∈ V, ∀ (A : Fin 2 → Bond) (z : ℂ), T = z • traceWord 2 2 n A →
        (A 0).trace ≠ 0 ∧ ordinaryDecoder n hn T = ordinaryInvariants A := by
  have hrw := (eventually_pencil_roots n hn).self_of_nhds.2.1
  have hframe : ContinuousAt (physicalFrame n hn) (witnessTensor n) :=
    (continuous_frame.continuousAt (x := roots n hn (witnessTensor n))).comp' hrw
  obtain ⟨hw0, hw1, _⟩ := p012_witness n (by omega)
  have hp0 : p0 (physicalFrame n hn (witnessTensor n)) (witnessTensor n) ≠ 0 := by
    rw [physicalFrame_witness, hw0]
    exact one_ne_zero
  have hp1 : p1 (by omega) (physicalFrame n hn (witnessTensor n)) (witnessTensor n) ≠ 0 := by
    rw [physicalFrame_witness, hw1]
    exact one_ne_zero
  have hc0 : ContinuousAt (fun S => p0 (physicalFrame n hn S) S) (witnessTensor n) :=
    continuousAt_contract_frame hframe (fun _ => 0)
  have hc1 : ContinuousAt (fun S => p1 (by omega) (physicalFrame n hn S) S) (witnessTensor n) :=
    continuousAt_contract_frame hframe (singletonWord (n - 1) (by omega))
  have hq : ContinuousAt (fun S => 1 - (roots n hn S).1 * (roots n hn S).2) (witnessTensor n) :=
    continuousAt_const.sub (hrw.fst.mul hrw.snd)
  have ht : ContinuousAt (fun S => 1 - (roots n hn S).1 * (ratios n hn S).1) (witnessTensor n) :=
    continuousAt_const.sub (hrw.fst.mul (continuousAt_ratios n hn _ hframe hp0 hp1).fst)
  have hneQ : 1 - (roots n hn (witnessTensor n)).1 * (roots n hn (witnessTensor n)).2 ≠ 0 := by simp
  have hneT : 1 - (roots n hn (witnessTensor n)).1 * (ratios n hn (witnessTensor n)).1 ≠ 0 := by simp
  have hLocal : ∀ᶠ T in 𝓝 (witnessTensor n),
      ContinuousAt (ordinaryDecoder n hn) T ∧
      ∀ (A : Fin 2 → Bond) (z : ℂ), T = z • traceWord 2 2 n A →
        (A 0).trace ≠ 0 ∧ ordinaryDecoder n hn T = ordinaryInvariants A := by
    filter_upwards [eventually_pencil_roots n hn, hc0.eventually_ne hp0, hc1.eventually_ne hp1,
      hq.eventually_ne hneQ, ht.eventually_ne hneT] with T hroot hp0' hp1' hq' ht'
    obtain ⟨hH, hr, ha, hb⟩ := hroot
    have hf : ContinuousAt (physicalFrame n hn) T :=
      (continuous_frame.continuousAt (x := roots n hn T)).comp' hr
    have hrat := continuousAt_ratios n hn T hf hp0' hp1'
    refine ⟨continuousAt_fromFrame hr.fst hr.snd hrat.fst hrat.snd ht', ?_⟩
    intro A z hT
    let a := (roots n hn T).1
    let b := (roots n hn T).2
    obtain ⟨hrow0, hrow1⟩ := changePhysical_frame a b A
    have hrootDet (x y : ℂ) (h : decodedPencil (pencilCoefficients n hn T) x y = 0) :
        (pencil A ![x, y]).det = 0 := by
      obtain ⟨hd, _⟩ := pencilCoefficients_scaled_traceWord n hn A z (hT ▸ hH)
      rw [hT, decodedPencil_scaled_traceWord n hn A z (hT ▸ hH)] at h
      exact (div_eq_zero_iff.mp h).resolve_right hd
    have hC : (changePhysical (physicalFrame n hn T) A 0).det = 0 := by
      change (changePhysical (frame a b) A 0).det = 0
      rw [hrow0]
      exact hrootDet 1 a ha
    have hD : (changePhysical (physicalFrame n hn T) A 1).det = 0 := by
      change (changePhysical (frame a b) A 1).det = 0
      rw [hrow1]
      exact hrootDet b 1 hb
    obtain ⟨hu, hv, hk⟩ := p012_ratios_singular (by omega) (physicalFrame n hn T) A z T hT
      hC hD hp0' hp1'
    dsimp only [ordinaryDecoder, ratios]
    rw [hv, hk]
    have ht'' : 1 - a * ((changePhysical (frame a b) A 1).trace /
        (changePhysical (frame a b) A 0).trace) ≠ 0 := by
      change 1 - a * ((changePhysical (physicalFrame n hn T) A 1).trace /
        (changePhysical (physicalFrame n hn T) A 0).trace) ≠ 0
      rw [← hv]
      exact ht'
    exact fromFrame_eq_ordinary a b A hq' hC hD hu ht''
  obtain ⟨V, hV, hOpen, hmem⟩ := mem_nhds_iff.mp hLocal
  exact ⟨V, hOpen, hmem, fun T hT => (hV hT).1.continuousWithinAt, fun T hT => (hV hT).2⟩

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformHardCorePencilDecoder
