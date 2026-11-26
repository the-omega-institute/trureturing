/- GID: D5/S3/Quantum/Divergence/FibonacciQutritBenchmark
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/FibonacciQutritBenchmark
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The classical benchmark forces strict transport of a full-rank contender. -/

import D5.S3.Quantum.Divergence.CanonicalChannelDPI
import D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport
import D5.S3.Quantum.Foundation.FinitePreparationChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Normalized positive-class data processing and strict Fibonacci qutrit improvement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder CStarAlgebra MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FinitePreparationChannel (finite_preparation_quantum_channel)
open D5.S3.Quantum.Divergence.CanonicalChannelDPI (extended_quantum_relative_entropy_channel_dpi)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_log_diagonal)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation (diagonalState)
open D5.S3.Quantum.Divergence.FibonacciQutritSpectralTransport.Transport
  (coordinates compress nullRay)

namespace D5.S3.Quantum.Divergence.FibonacciQutritBenchmark

private abbrev Mat (n : Type*) := Matrix n n ℂ

private abbrev matrix {n : Type*} [Fintype n] [DecidableEq n] (X : DensityState n) : Mat n :=
  CStarMatrix.ofMatrix.symm X.1

private def traceLog {n : Type*} [Fintype n] [DecidableEq n] (A C : Mat n) : ℝ :=
  (A * (CFC.log A - CFC.log C)).trace.re

private def benchmark (a b c : ℝ) : ℝ :=
  (4 / 3 * a + 5 / 3 * b) * Real.log ((4 / 3 * a + 5 / 3 * b) / (a + b)) +
    (7 / 3 * c) * Real.log (7 / 3)

private def positiveInput (a b c : ℝ) : Fin 3 → ℝ := ![4 / 3 * a, 5 / 3 * b, 7 / 3 * c]

private def positiveReference (a b c : ℝ) : Fin 3 → ℝ := ![a, b, c]

private def diagReal {n : Type*} [DecidableEq n] (p : n → ℝ) : Mat n :=
  diagonal fun i => (p i : ℂ)

private theorem diagonal_traceLog {n : Type*} [Fintype n] [DecidableEq n] (p q : n → ℝ) :
    traceLog (diagReal p) (diagReal q) = ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
  unfold traceLog diagReal
  rw [cfc_log_diagonal, cfc_log_diagonal, diagonal_sub, diagonal_mul_diagonal, trace_diagonal]
  simp only [Pi.sub_apply, Pi.mul_apply, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_re]

private def ray (j : Fin 3) : DensityState (Fin 3) :=
  diagonalState (fun i => if i = j then 1 else 0)
    (fun i => by split <;> norm_num) (by simp)

private theorem ray_sum (x y z : ℝ) :
    x • matrix (ray 0) + y • matrix (ray 1) + z • matrix (ray 2) =
      diagReal (![x, y, z] : Fin 3 → ℝ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    fin_cases i <;> simp [ray, diagonalState, diagReal, Complex.real_smul]
  · simp [ray, diagonalState, diagReal, hij]

/-- Merging the first two classes and putting the other two classes on separate rays
attains the classical benchmark with a positive definite reference. -/
theorem classical_benchmark_attained (a b c e : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e) :
    ∃ P Q R : DensityState (Fin 3),
      matrix P * matrix Q = 0 ∧ matrix P * matrix R = 0 ∧ matrix Q * matrix R = 0 ∧
      ((a + b) • matrix P + c • matrix Q + e • matrix R).PosDef ∧
      traceLog ((4 / 3 * a + 5 / 3 * b) • matrix P + (7 / 3 * c) • matrix Q)
        ((a + b) • matrix P + c • matrix Q + e • matrix R) = benchmark a b c := by
  have horth (i j : Fin 3) (h : i ≠ j) : matrix (ray i) * matrix (ray j) = 0 := by
    change diagReal (fun k => if k = i then 1 else 0) *
      diagReal (fun k => if k = j then 1 else 0) = 0
    rw [diagReal, diagReal, diagonal_mul_diagonal]
    ext k l
    by_cases hkl : k = l
    · subst l
      by_cases hki : k = i
      · subst k
        simp [h]
      · simp [hki]
    · simp [Matrix.diagonal_apply_ne _ hkl]
  refine ⟨ray 0, ray 1, ray 2, horth 0 1 (by decide), horth 0 2 (by decide),
    horth 1 2 (by decide), ?_, ?_⟩
  · rw [ray_sum]
    apply Matrix.PosDef.diagonal
    intro i
    apply Complex.zero_lt_real.mpr
    fin_cases i
    · exact add_pos ha hb
    · exact hc
    · exact he
  · rw [← add_zero ((4 / 3 * a + 5 / 3 * b) • matrix (ray 0) + (7 / 3 * c) • matrix (ray 1)),
      ← zero_smul ℝ (matrix (ray 2)), ray_sum, ray_sum, diagonal_traceLog]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      zero_mul, add_zero, benchmark]
    rw [← Real.log_div (by positivity) (by positivity), ← Real.log_div (by positivity) hc.ne',
      mul_div_cancel_right₀ _ hc.ne']

private theorem merge_deficit (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hsmall : b ≤ 4 / 19) :
    ∑ i, positiveInput a b c i * Real.log (positiveInput a b c i / positiveReference a b c i) ≤
      benchmark a b c + 1 / 114 := by
  let u : ℝ := 4 / 3
  let v : ℝ := 5 / 3
  let z := u * a + v * b
  let m := z / (a + b)
  have hz : 0 < z := by dsimp [z, u, v]; positivity
  have hm : 0 < m := div_pos hz (by positivity)
  have hmu : 0 < u / m := div_pos (by norm_num [u]) hm
  have ht := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hmu) hz.le
  rw [Real.log_div (by norm_num [u]) hm.ne'] at ht
  have hscale : z * (u / m - 1) = u * (a + b) - z := by
    dsimp [m]
    field_simp [hz.ne', (add_pos ha hb).ne'] <;> ring
  rw [hscale] at ht
  have hlog := Real.log_div_le_sum_range_add
    (x := (1 / 9 : ℝ)) (by norm_num) (by norm_num) 1
  have hratio : (1 + (1 / 9 : ℝ)) / (1 - 1 / 9) = v / u := by norm_num [u, v]
  rw [hratio] at hlog
  have hlog' : Real.log (v / u) ≤ 9 / 40 := by
    norm_num [Finset.sum_range_succ] at hlog
    linarith
  rw [Real.log_div (by norm_num [v]) (by norm_num [u])] at hlog'
  have hcoeff : v * (Real.log v - Real.log u) - (v - u) ≤ 1 / 24 := by
    dsimp [u, v] at *
    linarith only [hlog']
  have hscaled := mul_le_mul_of_nonneg_left hcoeff hb.le
  have hcap : b * (1 / 24 : ℝ) ≤ 1 / 114 := by linarith
  -- The third class contributes the same term to both sides.
  simp only [positiveInput, positiveReference, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, benchmark]
  have hcRatio (r : ℝ) : r * c * Real.log (r * c / c) = r * c * Real.log r := by
    by_cases hc : c = 0
    · simp [hc]
    · rw [mul_div_cancel_right₀ _ hc]
  rw [mul_div_cancel_right₀ _ ha.ne', mul_div_cancel_right₀ _ hb.ne', hcRatio]
  have hidentity : (u * a * Real.log u + v * b * Real.log v) - z * Real.log m =
      (z * (Real.log u - Real.log m) - (u * (a + b) - z)) +
        b * (v * (Real.log v - Real.log u) - (v - u)) := by
    dsimp [z]
    ring
  have hdelta : (u * a * Real.log u + v * b * Real.log v) - z * Real.log m ≤ 1 / 114 := by
    rw [hidentity]
    simpa only [zero_add] using add_le_add (sub_nonpos.mpr ht) (hscaled.trans hcap)
  change u * a * Real.log u + (v * b * Real.log v + _) ≤ z * Real.log m + _ + 1 / 114
  linarith only [hdelta]

private theorem prepared_traceLog_le {n : Type*} {ι : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    [Fintype ι] [Nonempty ι] (X : ι → DensityState n) (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) (hp₁ : ∑ i, p i = 1)
    (A C : Mat n) (hA : A = ∑ i, p i • matrix (X i)) (hC : C = ∑ i, q i • matrix (X i))
    (hCpos : C.PosDef) :
    traceLog A C ≤ ∑ i, p i * (Real.log (p i) - Real.log (q i)) := by
  classical
  let s := ∑ i, q i
  have hs : 0 < s := Finset.sum_pos (fun i _ => hq i) Finset.univ_nonempty
  let q' (i : ι) := s⁻¹ * q i
  have hq' (i : ι) : 0 < q' i := mul_pos (inv_pos.mpr hs) (hq i)
  have hq'₁ : ∑ i, q' i = 1 := by
    simp only [q', ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  let P := diagonalState p hp hp₁
  let Q := diagonalState q' (fun i => (hq' i).le) hq'₁
  obtain ⟨Φ, hΦ⟩ := finite_preparation_quantum_channel X
  have haction (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) (hr₁ : ∑ i, r i = 1) :
      matrix (Φ.mapState (diagonalState r hr hr₁)) = ∑ i, r i • matrix (X i) := by
    change CStarMatrix.ofMatrix.symm (Φ.toCompletelyPositiveMap (CStarMatrix.ofMatrix
      (diagReal r))) = _
    simpa only [diagReal, Matrix.diagonal_apply_eq, Complex.coe_smul] using hΦ (diagReal r)
  have hP : matrix (Φ.mapState P) = A := (haction p hp hp₁).trans hA.symm
  have hQ : matrix (Φ.mapState Q) = s⁻¹ • C := by
    rw [show Q = diagonalState q' (fun i => (hq' i).le) hq'₁ from rfl, haction, hC, Finset.smul_sum]
    simp only [q', smul_smul]
  have hQpos : (matrix Q).PosDef :=
    Matrix.PosDef.diagonal (fun i => Complex.zero_lt_real.mpr (hq' i))
  have hAtrace : A.trace = 1 := by
    rw [← hP]
    exact (Φ.mapState P).2.2
  have hQoutput : (matrix (Φ.mapState Q)).PosDef := by
    rw [hQ]
    exact hCpos.smul (inv_pos.mpr hs)
  have hdpi := extended_quantum_relative_entropy_channel_dpi Φ P Q
  rw [extendedQuantumRelativeEntropy_eq_coe_of_support (support_of_posDef P Q hQpos),
    extendedQuantumRelativeEntropy_eq_coe_of_support
      (support_of_posDef (Φ.mapState P) (Φ.mapState Q) hQoutput)] at hdpi
  have hreal := WithTop.coe_le_coe.mp hdpi
  change traceLog (matrix (Φ.mapState P)) (matrix (Φ.mapState Q)) ≤
    traceLog (diagReal p) (diagReal q') at hreal
  rw [hP, hQ, diagonal_traceLog] at hreal
  have houtput : traceLog A (s⁻¹ • C) = traceLog A C - Real.log s⁻¹ := by
    unfold traceLog
    rw [CFC.log_smul' C (inv_pos.mpr hs) hCpos.isStrictlyPositive,
      Algebra.algebraMap_eq_smul_one, add_comm (_ • _) (CFC.log C),
      ← sub_sub, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.mul_one, trace_sub, trace_smul, hAtrace, Complex.sub_re, Complex.real_smul]
    simp
  have hlogQ (i : ι) : Real.log (q' i) = Real.log s⁻¹ + Real.log (q i) :=
    Real.log_mul (inv_ne_zero hs.ne') (hq i).ne'
  have hinput :
      ∑ i, p i * (Real.log (p i) - Real.log (q' i)) =
        (∑ i, p i * (Real.log (p i) - Real.log (q i))) - Real.log s⁻¹ := by
    calc
      _ = ∑ i, (p i * (Real.log (p i) - Real.log (q i)) - p i * Real.log s⁻¹) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hlogQ i]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp₁, one_mul]
  rw [houtput, hinput] at hreal
  exact sub_le_sub_iff_right _ |>.mp hreal

/-- Positive-reference DPI and the classical merge deficit give a (1/114) cap.
Every full-rank preparation reaching the benchmark has a strict improvement with
a rank-at-most-two positive reference on the retained coordinates. -/
theorem full_rank_benchmark_comparison (a b c e : ℝ) (X₁ X₂ X₃ X₀ : DensityState (Fin 3))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_hγ : a + b + c + e = 1) (hp : 4 / 3 * a + 5 / 3 * b + 7 / 3 * c = 1)
    (hemax : e ≤ 8 / 19) (hbmax : b ≤ e / 2) (hsmin : 11 / 19 ≤ a + b + c)
    (hemin : (a + b + c) / 3 ≤ e) :
    let C := a • matrix X₁ + b • matrix X₂ + c • matrix X₃
    let A := (4 / 3 * a) • matrix X₁ + (5 / 3 * b) • matrix X₂ + (7 / 3 * c) • matrix X₃
    let B := C + e • matrix X₀
    C.PosDef →
    traceLog A C ≤ benchmark a b c + 1 / 114 ∧
      (benchmark a b c ≤ traceLog A B →
        (A * (CFC.log B - CFC.log C)).trace.re ≤ 1 / 114 ∧
        ∃ (T : Mat (Fin 3) →ₗ[ℝ] Mat (Fin 2 ⊕ Unit))
          (Y₁ Y₂ Y₃ Y₀ : DensityState (Fin 2 ⊕ Unit)),
          matrix Y₁ = T (matrix X₁) ∧ matrix Y₂ = T (matrix X₂) ∧ matrix Y₃ = T (matrix X₃) ∧
          let C' := a • matrix Y₁ + b • matrix Y₂ + c • matrix Y₃
          let A' := (4 / 3 * a) • matrix Y₁ + (5 / 3 * b) • matrix Y₂ + (7 / 3 * c) • matrix Y₃
          let B' := C' + e • matrix Y₀
          C'.rank ≤ 2 ∧ B'.PosDef ∧ traceLog A B < traceLog A' B') := by
  classical
  dsimp only
  let C := a • matrix X₁ + b • matrix X₂ + c • matrix X₃
  let A := (4 / 3 * a) • matrix X₁ + (5 / 3 * b) • matrix X₂ + (7 / 3 * c) • matrix X₃
  let B := C + e • matrix X₀
  change C.PosDef → traceLog A C ≤ _ ∧ _
  intro hCpos
  let X : Fin 3 → DensityState (Fin 3) := ![X₁, X₂, X₃]
  let p := positiveInput a b c
  let q := positiveReference a b c
  have hA : A = ∑ i, p i • matrix (X i) := by
    simp [A, X, p, positiveInput, Fin.sum_univ_succ, add_assoc]
  have hC : C = ∑ i, q i • matrix (X i) := by
    simp [C, X, q, positiveReference, Fin.sum_univ_succ, add_assoc]
  have hq (i : Fin 3) : 0 < q i := by
    fin_cases i <;> simp [q, positiveReference, ha, hb, hc]
  have hratioLower (i : Fin 3) : (4 / 3 : ℝ) * q i ≤ p i := by
    fin_cases i <;> simp [p, q, positiveInput, positiveReference] <;> linarith
  have hratioUpper (i : Fin 3) : p i ≤ (7 / 3 : ℝ) * q i := by
    fin_cases i <;> simp [p, q, positiveInput, positiveReference] <;> linarith
  have hp₀ (i : Fin 3) : 0 ≤ p i :=
    (mul_nonneg (by norm_num) (hq i).le).trans (hratioLower i)
  have hp₁ : ∑ i, p i = 1 := by
    simpa [p, positiveInput, Fin.sum_univ_succ, ← add_assoc] using hp
  have hD := prepared_traceLog_le X p q hp₀ hq hp₁ A C hA hC hCpos
  have hbound : traceLog A C ≤ benchmark a b c + 1 / 114 := by
    have hlog (i : Fin 3) : Real.log (p i) - Real.log (q i) = Real.log (p i / q i) := by
      rw [Real.log_div]
      · have hi := hq i
        exact (lt_of_lt_of_le (by positivity) (hratioLower i)).ne'
      · exact (hq i).ne'
    simp_rw [hlog] at hD
    exact hD.trans (merge_deficit a b c ha hb (by linarith))
  refine ⟨hbound, fun hcompare => ?_⟩
  have hloss : (A * (CFC.log B - CFC.log C)).trace.re ≤ 1 / 114 := by
    have hdiff : (A * (CFC.log B - CFC.log C)).trace.re = traceLog A C - traceLog A B := by
      simp only [traceLog, Matrix.mul_sub, trace_sub, Complex.sub_re]
      ring
    calc
      _ = traceLog A C - traceLog A B := hdiff
      _ ≤ 1 / 114 := by linarith
  refine ⟨hloss, ?_⟩
  have hlo : (4 / 3 : ℝ) • C ≤ A := by
    rw [hA, hC, Finset.smul_sum]
    simp only [smul_smul]
    exact Finset.sum_le_sum fun i _ =>
      smul_le_smul_of_nonneg_right (hratioLower i) (density_posSemidef (X i)).nonneg
  have hhi : A ≤ (7 / 3 : ℝ) • C := by
    rw [hA, hC, Finset.smul_sum]
    simp only [smul_smul]
    exact Finset.sum_le_sum fun i _ =>
      smul_le_smul_of_nonneg_right (hratioUpper i) (density_posSemidef (X i)).nonneg
  have trA : A.trace = 1 := by
    rw [hA, Matrix.trace_sum]
    simp only [Matrix.trace_smul, show ∀ i, (matrix (X i)).trace = 1 from fun i => (X i).2.2,
      Complex.real_smul, mul_one, ← Complex.ofReal_sum, hp₁, Complex.ofReal_one]
  have trC : C.trace.re = a + b + c := by
    change (a • matrix X₁ + b • matrix X₂ + c • matrix X₃).trace.re = _
    simp only [Matrix.trace_add, Matrix.trace_smul, show (matrix X₁).trace = 1 from X₁.2.2,
      show (matrix X₂).trace = 1 from X₂.2.2, show (matrix X₃).trace = 1 from X₃.2.2,
      Complex.real_smul, mul_one, Complex.add_re, Complex.ofReal_re]
  open FibonacciQutritSpectralTransport in
  obtain ⟨U, f, lam, h⟩ := strict_spectral_transport A C (matrix X₀) e hCpos hlo hhi trA
    (density_posSemidef X₀) X₀.2.2 (trC.symm ▸ hsmin) (trC.symm ▸ hemin) hloss
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hrank, hnull, hnullTr, hBpos, hmaps, _, hbetter⟩
  -- Package the transported matrices as actual density states.
  let T := (compress (((coordinates U f C).toBlocks₁₁.trace.re)⁻¹ •
    (coordinates U f C).toBlocks₁₁)).comp (coordinates U f).toLinearMap
  let Y (S : DensityState (Fin 3)) : DensityState (Fin 2 ⊕ Unit) :=
    ⟨CStarMatrix.ofMatrix (T (matrix S)),
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (hmaps _ (density_posSemidef S)).1.nonneg,
      (hmaps _ (density_posSemidef S)).2.1.trans S.2.2⟩
  let Y₀ : DensityState (Fin 2 ⊕ Unit) :=
    ⟨CStarMatrix.ofMatrix _, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hnull.nonneg, hnullTr⟩
  refine ⟨T, Y X₁, Y X₂, Y X₃, Y₀, rfl, rfl, rfl, ?_⟩
  have hTC : T C = a • matrix (Y X₁) + b • matrix (Y X₂) + c • matrix (Y X₃) := by
    simp only [C, map_add, map_smul]
    rfl
  have hTA : T A = (4 / 3 * a) • matrix (Y X₁) + (5 / 3 * b) • matrix (Y X₂) +
      (7 / 3 * c) • matrix (Y X₃) := by
    simp only [A, map_add, map_smul]
    rfl
  rw [← hTC, ← hTA]
  exact ⟨hrank, hBpos, hbetter⟩

#print axioms classical_benchmark_attained
#print axioms full_rank_benchmark_comparison

end D5.S3.Quantum.Divergence.FibonacciQutritBenchmark
