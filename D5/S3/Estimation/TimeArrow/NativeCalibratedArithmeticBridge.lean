/- GID: D5/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeCalibratedArithmeticBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original full posterior and native conditional mass use one shared calibration. -/

import D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
import D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
import D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import D5.S3.DivergenceSupport.LogSumInequality

open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
noncomputable section

open private
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_environment_full_calibration
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibrated_row_parameter
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_group_zero_count_bridge
  D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_group_zero_posterior_approximation
from D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

/-- The native environment fixes the complete sigmoid equation, including
its derivative. The variance is not supplied as an independent surrogate. -/
private theorem native_environment_mean_variance {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)] (k l : ℕ)
    (y z : Fiber S e o)
    (henv : nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1) (x : ℝ) :
    let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
      (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
    let V := nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e z.val i.val 1 = k).card
    let U := (V.filter fun i => count e z.val i.val (-1) = l).card
    let A := nativeRectangleACount S e o k l y
    let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
      fun i => score q r e z.val i.val - z0
    (∑ i : Fin M, Real.sigmoid (x + (score q r e y.val i - z0))) =
      calibratedMean outside r (compensation M q r) V.card R U A x ∧
    (∑ i : Fin M, Real.sigmoid (x + (score q r e y.val i - z0)) *
      (1 - Real.sigmoid (x + (score q r e y.val i - z0)))) =
        calibratedVariance outside r (compensation M q r) V.card R U A x := by
  classical
  dsimp only
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
    (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let A := nativeRectangleACount S e o k l y
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
    fun i => score q r e z.val i.val - z0
  have he := (native_minimal_readout_eq_iff S e o k l y z).mp henv
  have hf (u : ℝ) : (∑ i : Fin M, Real.sigmoid (u + (score q r e y.val i - z0))) =
      calibratedMean outside r (compensation M q r) V.card R U A u := by
    let t := Real.exp (u - z0 + Real.log B0)
    have ht : 0 < t := Real.exp_pos _
    have hc := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_environment_full_calibration
      S r e o k l y z he hq hqm hr hr1 ha ha1 t ht
    dsimp only at hc
    have hx : z0 - Real.log B0 + Real.log t = u := by rw [Real.log_exp]; ring
    change (∑ i : Fin M, t * weight q r e y.val i / (B0 + t * weight q r e y.val i)) =
      calibratedMean outside r (compensation M q r) V.card R U A
        (z0 - Real.log B0 + Real.log t) at hc
    rw [hx] at hc
    rw [← hc]
    apply sum_congr rfl
    intro i _
    rw [← D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibrated_row_parameter
      r e y.val hq hqm hr hr1 ha ha1 t ht i]
    congr 1
    linarith [hx]
  refine ⟨hf x, ?_⟩
  have hfun : (∑ i : Fin M, fun u : ℝ => Real.sigmoid (u + (score q r e y.val i - z0))) =
      calibratedMean outside r (compensation M q r) V.card R U A := by
    ext u
    simp only [Finset.sum_apply]
    exact hf u
  have hd := HasDerivAt.sum (fun i (_ : i ∈ (univ : Finset (Fin M))) =>
    D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.sigmoid_shift_deriv
      (score q r e y.val i - z0) x)
  rw [hfun] at hd
  exact hd.unique (D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.calibration_root_deriv
    outside r (compensation M q r) V.card R U A x)

/-- A half-lattice enlargement removes the parity split uniformly for
positive and negative harmonics. The approximation is for the original mu. -/
private theorem posterior_phase_lattice_reduction (ell t : ℤ) (mu bg x τ err : ℝ)
    (happrox : |mu - (bg + (t : ℝ)) * Real.sigmoid x| ≤ err)
    (hphase : ∃ z : ℤ, |(ell : ℝ) * (1 / 2 - mu) - z| ≤ τ) :
    ∃ z : ℤ, |2 * (ell : ℝ) * ((bg + (t : ℝ)) * Real.sigmoid x - (t : ℝ) / 2) - z| ≤
      2 * τ + 2 * |(ell : ℝ)| * err := by
  obtain ⟨z, hz⟩ := hphase
  refine ⟨ell - 2 * z - ell * t, ?_⟩
  have he : 2 * (ell : ℝ) * ((bg + (t : ℝ)) * Real.sigmoid x - (t : ℝ) / 2) -
      ((ell - 2 * z - ell * t : ℤ) : ℝ) =
        -2 * ((ell : ℝ) * (1 / 2 - mu) - z) -
          2 * (ell : ℝ) * (mu - (bg + (t : ℝ)) * Real.sigmoid x) := by
    push_cast
    ring
  rw [he]
  calc
    _ ≤ |-2 * ((ell : ℝ) * (1 / 2 - mu) - z)| +
        |2 * (ell : ℝ) * (mu - (bg + (t : ℝ)) * Real.sigmoid x)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (-2 * ((ell : ℝ) * (1 / 2 - mu) - z)) 0
          (2 * (ell : ℝ) * (mu - (bg + (t : ℝ)) * Real.sigmoid x)))
    _ = 2 * |(ell : ℝ) * (1 / 2 - mu) - z| +
        2 * |(ell : ℝ)| * |mu - (bg + (t : ℝ)) * Real.sigmoid x| := by
      rw [abs_mul, abs_mul, abs_mul]
      norm_num
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left happrox (by positivity : 0 ≤ 2 * |(ell : ℝ)|)
      linarith

/-- The full original posterior is approximated by the same native shared
root. Its error is proved from frozen posterior odds and the exact all-row
mean and variance identification. -/
private theorem native_environment_posterior_approximation :
    ∃ C : ℝ, 0 < C ∧ ∃ V0 : ℝ, 0 < V0 ∧
      ∀ (M q s : ℕ) (S : Support M q) (r : ℝ) (e : Experiment) (o : Obs M s e),
        ∀ [Fintype (Sites s e)], 1 ≤ q → q < M → 0 < r → r < 1 →
          0 ≤ compensation M q r → compensation M q r < 1 →
          ∀ (k l : ℕ) (y z : Fiber S e o),
            nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z →
            ∀ x : ℝ,
            let All : Support M M := ⟨univ, by simp⟩
            let G := nativeCalibrationCells All e y.val k l 0
            let BG := nativeCalibrationCells All e o k l 0 \ S.val
            let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
              (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
            let V := nativeRectangleRows S e o k l z
            let R := (V.filter fun i => count e z.val i.val 1 = k).card
            let U := (V.filter fun i => count e z.val i.val (-1) = l).card
            let A := nativeRectangleACount S e o k l y
            let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
              fun i => score q r e z.val i.val - z0
            calibratedMean outside r (compensation M q r) V.card R U A x = q →
            V0 ≤ calibratedVariance outside r (compensation M q r) V.card R U A x →
              |(∑ i ∈ G, inclusion q r e y.val i) - ((BG.card : ℝ) + A) * Real.sigmoid x| ≤
                C * ((BG.card : ℝ) + A) /
                  calibratedVariance outside r (compensation M q r) V.card R U A x := by
  classical
  obtain ⟨C, hC, V0, hV0, hp⟩ :=
    D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_group_zero_posterior_approximation
  refine ⟨C, hC, V0, hV0, ?_⟩
  intro M q s S r e o _ hq hqm hr hr1 ha ha1 k l y z henv x
  dsimp only
  let B0 : ℝ := ((M - q : ℕ) : ℝ) / (q : ℝ)
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
    (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  let t := Real.exp (x - z0 + Real.log B0)
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let A := nativeRectangleACount S e o k l y
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
    fun i => score q r e z.val i.val - z0
  let p := fun i : Fin M => t * weight q r e y.val i / (B0 + t * weight q r e y.val i)
  intro hmean hvar
  have ht : 0 < t := Real.exp_pos _
  have hx : z0 - Real.log B0 + Real.log t = x := by rw [Real.log_exp]; ring
  have hrow (i : Fin M) : p i = Real.sigmoid (x + (score q r e y.val i - z0)) := by
    dsimp only [p]
    rw [← D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_calibrated_row_parameter
      r e y.val hq hqm hr hr1 ha ha1 t ht i]
    congr 1
    linarith [hx]
  have hi := native_environment_mean_variance S r e o k l y z henv hq hqm hr hr1 ha ha1 x
  dsimp only at hi
  have hpm : (∑ i, p i) = (q : ℝ) := by
    simp_rw [hrow]
    exact hi.1.trans hmean
  have hpv : (∑ i, p i * (1 - p i)) =
      calibratedVariance outside r (compensation M q r) V.card R U A x := by
    simp_rw [hrow]
    exact hi.2
  have hh := hp M q s r hq hqm hr hr1 ha1 e y.val t ht k l hpm (hpv.symm ▸ hvar)
  dsimp only at hh
  have hgroup := D5.S3.Estimation.TimeArrow.SharedRectangleCalibration.native_group_zero_count_bridge
    S e o k l y
  dsimp only at hgroup
  change |(∑ i ∈ nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e y.val k l 0,
      inclusion q r e y.val i) -
      ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e y.val k l 0).card : ℝ) *
        Real.sigmoid (z0 - Real.log B0 + Real.log t)| ≤
    C * ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e y.val k l 0).card : ℝ) /
      (∑ i, p i * (1 - p i)) at hh
  rw [hx, hpv, hgroup] at hh
  simpa only [Nat.cast_add] using hh


/-- A native original-posterior phase event is dominated by an event of
the exact conditional A-count kernel. The posterior error is derived here,
while the native variance threshold remains an explicit unfinished input. -/
private theorem native_posterior_phase_kernel_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ V0 : ℝ, 0 < V0 ∧
      ∀ (M q s : ℕ) (S : Support M q) (r : ℝ) (e : Experiment) (o : Obs M s e),
        ∀ [Fintype (Sites s e)], 1 ≤ q → q < M → 0 < r → r < 1 →
          0 ≤ compensation M q r → compensation M q r < 1 →
          ∀ (k l : ℕ) (z : Fiber S e o) (θ : ℕ → ℝ) (ell : ℤ) (τ : ℝ),
            letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
            let All : Support M M := ⟨univ, by simp⟩
            let BG := nativeCalibrationCells All e o k l 0 \ S.val
            let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
              (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
            let V := nativeRectangleRows S e o k l z
            let R := (V.filter fun i => count e z.val i.val 1 = k).card
            let U := (V.filter fun i => count e z.val i.val (-1) = l).card
            let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
              fun i => score q r e z.val i.val - z0
            let Env := univ.filter fun y : Fiber S e o =>
              nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
            let Q := fun y : Fiber S e o => ∃ a : ℤ,
              |(ell : ℝ) * (1 / 2 -
                (∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i)) - a| ≤ τ
            let P := fun t : ℕ => ∃ a : ℤ,
              |2 * (ell : ℝ) * (((BG.card : ℝ) + t) * Real.sigmoid (θ t) - (t : ℝ) / 2) - a| ≤
                2 * τ + 2 * |(ell : ℝ)| * (C * ((BG.card : ℝ) + t) /
                  calibratedVariance outside r (compensation M q r) V.card R U t (θ t))
            letI : DecidablePred Q := Classical.decPred Q
            letI : DecidablePred P := Classical.decPred P
            (∀ y ∈ Env, calibratedMean outside r (compensation M q r) V.card R U
              (nativeRectangleACount S e o k l y) (θ (nativeRectangleACount S e o k l y)) = q) →
            (∀ y ∈ Env, V0 ≤ calibratedVariance outside r (compensation M q r) V.card R U
              (nativeRectangleACount S e o k l y) (θ (nativeRectangleACount S e o k l y))) →
            conditionalFiberMass S r e o (Env.filter Q) / conditionalFiberMass S r e o Env ≤
              ∑ t ∈ (range (U + 1)).filter P,
                (if t ≤ U then ((R.choose t : ℝ) * ((V.card - R).choose (U - t) : ℝ)) /
                  (V.card.choose U : ℝ) else 0) := by
  classical
  obtain ⟨C, hC, V0, hV0, hpost⟩ := native_environment_posterior_approximation
  refine ⟨C, hC, V0, hV0, ?_⟩
  intro M q s S r e o _ hq hqm hr hr1 ha ha1 k l z θ ell τ
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  let All : Support M M := ⟨univ, by simp⟩
  let BG := nativeCalibrationCells All e o k l 0 \ S.val
  let z0 := (k : ℝ) * Real.log ((1 + r) / (1 - compensation M q r)) +
    (l : ℝ) * Real.log ((1 - r) / (1 + compensation M q r))
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
    fun i => score q r e z.val i.val - z0
  let Env := univ.filter fun y : Fiber S e o =>
    nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
  intro hmean hvar
  have hh := native_event_mass_le_kernel S r e o hq hqm hr hr1 ha ha1 k l z
    (fun y => ∃ a : ℤ, |(ell : ℝ) * (1 / 2 -
      (∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i)) - a| ≤ τ)
    (fun t : ℕ => ∃ a : ℤ,
      |2 * (ell : ℝ) * (((BG.card : ℝ) + t) * Real.sigmoid (θ t) - (t : ℝ) / 2) - a| ≤
        2 * τ + 2 * |(ell : ℝ)| * (C * ((BG.card : ℝ) + t) /
          calibratedVariance outside r (compensation M q r) V.card R U t (θ t)))
    (by
      intro y henv hphase
      have happrox := hpost M q s S r e o hq hqm hr hr1 ha ha1 k l y z henv
        (θ (nativeRectangleACount S e o k l y)) (hmean y (by simpa only [mem_filter, mem_univ, true_and] using henv))
        (hvar y (by simpa only [mem_filter, mem_univ, true_and] using henv))
      have he := posterior_phase_lattice_reduction ell (nativeRectangleACount S e o k l y)
        (∑ i ∈ nativeCalibrationCells All e y.val k l 0, inclusion q r e y.val i)
        BG.card (θ (nativeRectangleACount S e o k l y)) τ
        (C * ((BG.card : ℝ) + nativeRectangleACount S e o k l y) /
          calibratedVariance outside r (compensation M q r) V.card R U
            (nativeRectangleACount S e o k l y) (θ (nativeRectangleACount S e o k l y)))
        (by simpa only [Int.cast_natCast] using happrox) hphase
      simpa only [Int.cast_natCast] using he
    
    )
  simpa only using hh

/-- Coarse Stirling envelopes used only inside the four-cell atom estimate. -/
private theorem log_factorial_envelopes {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * Real.log n - n + Real.log n / 2 ≤ Real.log (n.factorial : ℝ) ∧
      Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n / 2 + 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · have hl := Stirling.le_log_factorial_stirling hn.ne'
    have hc : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  · have hs := Stirling.log_stirlingSeq'_antitone (show 0 ≤ n - 1 by omega)
    have hi : n - 1 + 1 = n := by omega
    change Real.log (Stirling.stirlingSeq (n - 1 + 1)) ≤
      Real.log (Stirling.stirlingSeq (0 + 1)) at hs
    rw [hi, Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one] at hs
    simp (disch := positivity) only [Real.log_div, Real.log_exp,
      Real.log_sqrt, Real.log_mul] at hs
    linarith

/-- The four positive cells and their row and column margins are one table.
The entropy term in its factorial ratio is nonpositive. -/
private theorem four_cell_entropy (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    (a+b) * Real.log (a+b) + (c+d) * Real.log (c+d) +
      (a+c) * Real.log (a+c) + (b+d) * Real.log (b+d) -
      (a+b+c+d) * Real.log (a+b+c+d) -
      a * Real.log a - b * Real.log b - c * Real.log c - d * Real.log d ≤ 0 := by
  let N := a+b+c+d
  have hN : 0 < N := by dsimp [N]; positivity
  let A : Fin 4 → ℝ := ![a,b,c,d]
  let B : Fin 4 → ℝ := ![(a+b)*(a+c)/N, (a+b)*(b+d)/N,
    (c+d)*(a+c)/N, (c+d)*(b+d)/N]
  have hA (i : Fin 4) : 0 < A i := by fin_cases i <;> simp [A] <;> assumption
  have hB (i : Fin 4) : 0 < B i := by fin_cases i <;> simp [B] <;> positivity
  have hAs : (∑ i, A i) = N := by simp [A, Fin.sum_univ_four, N]
  have hBs : (∑ i, B i) = N := by
    simp [B, Fin.sum_univ_four]
    field_simp
    dsimp [N]
    ring
  have h := D5.S3.DivergenceSupport.LogSumInequality.log_sum_inequality A B
    (fun i => (hA i).le) (fun i => (hB i).le)
    (fun i hi => False.elim ((hB i).ne' hi))
  rw [hAs, hBs, div_self hN.ne', Real.log_one, mul_zero] at h
  simp [A, B, Fin.sum_univ_four] at h
  simp (disch := positivity) only [Real.log_div, Real.log_mul] at h
  dsimp [N] at h
  linarith only [h]

/-- A uniform atom cap on the central table region. The four lower bounds
are for the same table; no independence or unguarded natural subtraction is used. -/
private theorem hypergeometric_central_atom {N R U t : ℕ} (hR : R ≤ N) (hU : U ≤ N)
    (htR : t < R) (htU : t < U) (hfour : U - t < N - R)
    (ht : 0 < t) (γ : ℝ) (hγ : 0 < γ)
    (h0 : γ * N ≤ t) (h1 : γ * N ≤ ((R-t : ℕ) : ℝ))
    (h2 : γ * N ≤ ((U-t : ℕ) : ℝ))
    (h3 : γ * N ≤ ((N-R-(U-t) : ℕ) : ℝ)) :
    ((R.choose t : ℝ) * ((N-R).choose (U-t) : ℝ)) / (N.choose U : ℝ) ≤
      Real.exp 4 / (γ ^ 2 * Real.sqrt N) := by
  have hN : 0 < N := lt_of_lt_of_le (lt_trans ht htR) hR
  have hNR : 0 < N - R := lt_of_le_of_lt (Nat.zero_le _) hfour
  have hNU : 0 < N - U := by omega
  have hRt : 0 < R - t := Nat.sub_pos_of_lt htR
  have hUt : 0 < U - t := Nat.sub_pos_of_lt htU
  have hD : 0 < N - R - (U-t) := Nat.sub_pos_of_lt hfour
  have hRN : (R : ℝ) ≤ N := by exact_mod_cast hR
  have hUN : (U : ℝ) ≤ N := by exact_mod_cast hU
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hU0 : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
  have hNR0 : (0 : ℝ) < (N-R : ℕ) := by exact_mod_cast hNR
  have hNU0 : (0 : ℝ) < (N-U : ℕ) := by exact_mod_cast hNU
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hRt0 : (0 : ℝ) < (R-t : ℕ) := by exact_mod_cast hRt
  have hUt0 : (0 : ℝ) < (U-t : ℕ) := by exact_mod_cast hUt
  have hD0 : (0 : ℝ) < (N-R-(U-t) : ℕ) := by exact_mod_cast hD
  let H : ℝ := ((R.choose t : ℝ) * ((N-R).choose (U-t) : ℝ)) / (N.choose U : ℝ)
  have hH : 0 < H := by
    dsimp [H]
    exact div_pos (mul_pos (by exact_mod_cast Nat.choose_pos htR.le)
      (by exact_mod_cast Nat.choose_pos hfour.le)) (by exact_mod_cast Nat.choose_pos hU)
  have hlogH : Real.log H = Real.log (R.factorial : ℝ) + Real.log ((N-R).factorial : ℝ) +
      Real.log (U.factorial : ℝ) + Real.log ((N-U).factorial : ℝ) -
      Real.log (N.factorial : ℝ) - Real.log (t.factorial : ℝ) -
      Real.log ((R-t).factorial : ℝ) - Real.log ((U-t).factorial : ℝ) -
      Real.log ((N-R-(U-t)).factorial : ℝ) := by
    dsimp [H]
    rw [Nat.cast_choose ℝ htR.le, Nat.cast_choose ℝ hfour.le, Nat.cast_choose ℝ hU]
    simp (disch := positivity) only [Real.log_mul, Real.log_div]
    ring
  have hent := four_cell_entropy (t : ℝ) ((R-t : ℕ) : ℝ) ((U-t : ℕ) : ℝ)
    ((N-R-(U-t) : ℕ) : ℝ) ht0 hRt0 hUt0 hD0
  have hAB : (t : ℝ) + (R-t : ℕ) = R := by exact_mod_cast Nat.add_sub_of_le htR.le
  have hCD : ((U-t : ℕ) : ℝ) + (N-R-(U-t) : ℕ) = (N-R : ℕ) := by
    exact_mod_cast Nat.add_sub_of_le hfour.le
  have hAC : (t : ℝ) + (U-t : ℕ) = U := by exact_mod_cast Nat.add_sub_of_le htU.le
  have hBD : ((R-t : ℕ) : ℝ) + (N-R-(U-t) : ℕ) = (N-U : ℕ) := by
    exact_mod_cast (by omega : R-t+(N-R-(U-t)) = N-U)
  have hAll : (t : ℝ) + (R-t : ℕ) + (U-t : ℕ) + (N-R-(U-t) : ℕ) = N := by
    exact_mod_cast (by omega : t+(R-t)+(U-t)+(N-R-(U-t)) = N)
  rw [hAll, hAB, hCD, hAC, hBD] at hent
  have hlogupper : Real.log H ≤ 4 +
      (Real.log R + Real.log (N-R : ℕ) + Real.log U + Real.log (N-U : ℕ) -
        Real.log N - Real.log t - Real.log (R-t : ℕ) - Real.log (U-t : ℕ) -
        Real.log (N-R-(U-t) : ℕ)) / 2 := by
    rw [hlogH]
    have hRa := (log_factorial_envelopes (by omega : 0 < R)).2
    have hNa := (log_factorial_envelopes hNR).2
    have hUa := (log_factorial_envelopes (by omega : 0 < U)).2
    have hNUa := (log_factorial_envelopes hNU).2
    have hNb := (log_factorial_envelopes hN).1
    have htb := (log_factorial_envelopes ht).1
    have hRb := (log_factorial_envelopes hRt).1
    have hUb := (log_factorial_envelopes hUt).1
    have hDb := (log_factorial_envelopes hD).1
    have htot : (R : ℝ) + (N-R : ℕ) + U + (N-U : ℕ) =
        N + t + (R-t : ℕ) + (U-t : ℕ) + (N-R-(U-t) : ℕ) := by
      exact_mod_cast (by omega : R+(N-R)+U+(N-U) = N+t+(R-t)+(U-t)+(N-R-(U-t)))
    linarith
  have hlR := Real.log_le_log hR0 hRN
  have hlU := Real.log_le_log hU0 hUN
  have hlNR := Real.log_le_log hNR0 (show ((N-R : ℕ) : ℝ) ≤ (N : ℝ) by exact_mod_cast (Nat.sub_le N R))
  have hlNU := Real.log_le_log hNU0 (show ((N-U : ℕ) : ℝ) ≤ (N : ℝ) by exact_mod_cast (Nat.sub_le N U))
  have hγN : 0 < γ * (N : ℝ) := mul_pos hγ hN0
  have hl0 := Real.log_le_log hγN h0
  have hl1 := Real.log_le_log hγN h1
  have hl2 := Real.log_le_log hγN h2
  have hl3 := Real.log_le_log hγN h3
  rw [Real.log_mul hγ.ne' hN0.ne'] at hl0 hl1 hl2 hl3
  have hl : Real.log H ≤ 4 - 2 * Real.log γ - Real.log N / 2 := by linarith
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hexp := Real.exp_le_exp.mpr hl
  rw [Real.exp_log hH] at hexp
  have hrhs : Real.exp (4 - 2 * Real.log γ - Real.log (N : ℝ) / 2) =
      Real.exp 4 / (γ ^ 2 * Real.sqrt N) := by
    rw [show 4 - 2 * Real.log γ - Real.log (N : ℝ) / 2 =
      4 - (Real.log (γ ^ 2) + Real.log (Real.sqrt (N : ℝ))) by
        rw [Real.log_pow, Real.log_sqrt hN0.le]; ring,
      Real.exp_sub, Real.exp_add, Real.exp_log (sq_pos_of_pos hγ), Real.exp_log hsqrt]
  exact hexp.trans_eq hrhs

/-- Balanced numerical margins supply the four interior-cell hypotheses of
the atom estimate throughout one central interval. -/
private theorem hypergeometric_balanced_central_atom {N R U t : ℕ}
    (hN : 0 < N) (hR : R ≤ N) (hU : U ≤ N) (δ w : ℝ) (hδ : 0 < δ)
    (hRlo : δ * N ≤ R) (hRhi : (R : ℝ) ≤ (1-δ)*N)
    (hUlo : δ * N ≤ U) (hUhi : (U : ℝ) ≤ (1-δ)*N)
    (hw : w ≤ δ ^ 2 * N / 2) (ht : |(t : ℝ) - (U : ℝ)*R/N| ≤ w) :
    ((R.choose t : ℝ) * ((N-R).choose (U-t) : ℝ)) / (N.choose U : ℝ) ≤
      Real.exp 4 / ((δ ^ 2 / 2) ^ 2 * Real.sqrt N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := central_four_cells_lower (N : ℝ) R U δ t w hN0 hδ.le
    hRlo hRhi hUlo hUhi ht
  have hγ : 0 < δ ^ 2 / 2 := by positivity
  have hγN : 0 < δ ^ 2 / 2 * (N : ℝ) := mul_pos hγ hN0
  have hs (j : Fin 4) : δ ^ 2 / 2 * (N : ℝ) ≤ cellCounts N R U t j := by
    have hj := hc j
    linarith
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  simp only [cellCounts, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  have ht0 : 0 < t := by exact_mod_cast (hγN.trans_le h0)
  have htR : t < R := by exact_mod_cast (by linarith : (t : ℝ) < R)
  have htU : t < U := by exact_mod_cast (by linarith : (t : ℝ) < U)
  have hf : U-t < N-R := by
    have hsub : (U : ℝ) - t < (N : ℝ) - R := by linarith
    exact_mod_cast (show ((U-t : ℕ) : ℝ) < (N-R : ℕ) by
      rw [Nat.cast_sub htU.le, Nat.cast_sub hR]; exact hsub)
  apply hypergeometric_central_atom hR hU htR htU hf ht0 (δ ^ 2 / 2) hγ h0
  · simpa only [Nat.cast_sub htR.le] using h2
  · simpa only [Nat.cast_sub htU.le] using h1
  · rw [Nat.cast_sub hf.le, Nat.cast_sub hR, Nat.cast_sub htU.le]
    linarith

open D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall

set_option quotPrecheck false in
local notation "H" => fun N R U t : ℕ => if t ≤ U then
  ((R.choose t : ℝ) * ((N-R).choose (U-t) : ℝ)) / (N.choose U : ℝ) else 0

open scoped Classical in
/-- The integer count kernel retains both support guards. Its atom and tail
inputs to the moving-center engine are proved here from the original kernel. -/
private theorem hypergeometric_arithmetic_bound {N R U : ℕ}
    (hN : 1 < N) (hR : R ≤ N) (hU : U ≤ N)
    (δ L s K h : ℝ) (hδ : 0 < δ) (hL : 0 < L) (hs : 0 < s) (hK : 0 ≤ K) (hh : 0 ≤ h)
    (hRlo : δ * N ≤ R) (hRhi : (R : ℝ) ≤ (1-δ)*N)
    (hUlo : δ * N ≤ U) (hUhi : (U : ℝ) ≤ (1-δ)*N)
    (hwide : 1 ≤ L * Real.sqrt N) (hsmall : L * Real.sqrt N ≤ δ ^ 2 * N / 2)
    (g : ℤ → ℝ)
    (hlower : ∀ x ∈ Icc ⌈(U : ℝ)*R/N-L*Real.sqrt N⌉ ⌊(U : ℝ)*R/N+L*Real.sqrt N⌋,
      ∀ y ∈ Icc ⌈(U : ℝ)*R/N-L*Real.sqrt N⌉ ⌊(U : ℝ)*R/N+L*Real.sqrt N⌋,
      x ≤ y → s * ((y-x : ℤ) : ℝ) ≤ g y-g x)
    (hupper : ∀ x ∈ Icc ⌈(U : ℝ)*R/N-L*Real.sqrt N⌉ ⌊(U : ℝ)*R/N+L*Real.sqrt N⌋,
      ∀ y ∈ Icc ⌈(U : ℝ)*R/N-L*Real.sqrt N⌉ ⌊(U : ℝ)*R/N+L*Real.sqrt N⌋,
      x ≤ y → g y-g x ≤ K*s*((y-x : ℤ) : ℝ)) :
    (∑ t ∈ (range (U+1)).filter (fun t : ℕ => ∃ z : ℤ, |g (t : ℤ)-z| ≤ h), H N R U t) ≤
      Real.exp 4 / ((δ ^ 2 / 2) ^ 2 * Real.sqrt N) *
        (K*s*(2*L*Real.sqrt N)+2*h+1) * (2*h/s+1) + 1/(4*L^2) := by
  classical
  let ν : ℝ := (U : ℝ)*R/N
  let w : ℝ := L * Real.sqrt N
  let a : ℤ := ⌈ν-w⌉
  let b : ℤ := ⌊ν+w⌋
  let T := (range (U+1)).map (Nat.castEmbedding : ℕ ↪ ℤ)
  let p : ℤ → ℝ := fun t => if 0 ≤ t then H N R U t.toNat else 0
  let A : ℝ := Real.exp 4 / ((δ ^ 2 / 2) ^ 2 * Real.sqrt N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hp (t : ℤ) : 0 ≤ p t := by dsimp [p]; split_ifs <;> positivity
  have hpc (t : ℕ) : p t = H N R U t := by simp [p]
  have hcentral (t : ℤ) : t ∈ Icc a b ↔ |(t : ℝ)-ν| ≤ w := by
    simp only [mem_Icc, a, b, Int.ceil_le, Int.le_floor, abs_le]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  have hab : a ≤ b := by
    have ha := Int.ceil_lt_add_one (ν-w)
    have hb := Int.sub_one_lt_floor (ν+w)
    have : (a : ℝ) < b := by dsimp [a,b]; dsimp [w] at *; linarith
    exact_mod_cast this.le
  have hmax (t : ℤ) (ht : t ∈ Icc a b) : p t ≤ A := by
    by_cases ht0 : 0 ≤ t
    · dsimp only [p]
      rw [if_pos ht0]
      by_cases htU : t.toNat ≤ U
      · rw [if_pos htU]
        apply hypergeometric_balanced_central_atom (by omega : 0 < N) hR hU δ w hδ
          hRlo hRhi hUlo hUhi hsmall
        have hcast : (t.toNat : ℝ) = (t : ℝ) := by
          exact_mod_cast Int.toNat_of_nonneg ht0
        simpa only [hcast] using (hcentral t).mp ht
      · simp only [if_neg htU]
        exact hA
    · simp only [p, if_neg ht0]
      exact hA
  have hout : T \ Icc a b =
      ((range (U+1)).filter fun t : ℕ => w < |(t : ℝ)-ν|).map (Nat.castEmbedding : ℕ ↪ ℤ) := by
    rw [sdiff_eq_filter, filter_map]
    congr 1
    apply filter_congr
    intro t _
    simp only [Function.comp_apply, Nat.castEmbedding_apply]
    rw [hcentral]
    simp only [Int.cast_natCast, not_le]
  have htail : eventMass p (T \ Icc a b) ≤ 1/(4*L^2) := by
    rw [hout, eventMass, sum_map]
    simp only [Nat.castEmbedding_apply, hpc]
    exact kernel_central_tail hR hU hN L hL
  have he := moving_center_small_ball p g g T a b s K h 0 A (1/(4*L^2)) hab hs hh
    le_rfl hA hp hmax hlower hupper (fun t _ => by simp) htail
  have hleft : eventMass p (T.filter fun t => ∃ z : ℤ, |g t-z| ≤ h) =
      ∑ t ∈ (range (U+1)).filter (fun t : ℕ => ∃ z : ℤ, |g (t : ℤ)-z| ≤ h), H N R U t := by
    rw [eventMass, filter_map, sum_map]
    simp only [Function.comp_apply, Nat.castEmbedding_apply, hpc]
  rw [hleft] at he
  have hwidth : ((b-a : ℤ) : ℝ) ≤ 2*w := by
    have ha := Int.le_ceil (ν-w)
    have hb := Int.floor_le (ν+w)
    dsimp [a,b]
    push_cast
    linarith
  calc
    _ ≤ A * (K*s*((b-a : ℤ) : ℝ)+2*h+1)*(2*h/s+1)+1/(4*L^2) := by
      simpa only [add_zero] using he
    _ ≤ _ := by
      dsimp [A,w] at *
      gcongr
      simpa only [mul_assoc] using hwidth

open scoped Classical in
/-- An arbitrary native predicate only needs lattice containment centrally.
The remaining count values are paid by the original kernel tail. -/
private theorem hypergeometric_predicate_bound {N R U : ℕ}
    (hR : R ≤ N) (hU : U ≤ N) (hN : 1 < N) (L : ℝ) (hL : 0 < L)
    (P : ℕ → Prop) (g : ℤ → ℝ) (h B : ℝ)
    (hpush : ∀ t ∈ range (U+1), |(t : ℝ)-(U : ℝ)*R/N| ≤ L*Real.sqrt N →
      P t → ∃ z : ℤ, |g t-z| ≤ h)
    (hsmall : (∑ t ∈ (range (U+1)).filter (fun t : ℕ => ∃ z : ℤ, |g t-z| ≤ h),
      H N R U t) ≤ B+1/(4*L^2)) :
    (∑ t ∈ (range (U+1)).filter P, H N R U t) ≤ B+1/(2*L^2) := by
  have hpart : (∑ t ∈ (range (U+1)).filter P, H N R U t) ≤
      (∑ t ∈ (range (U+1)).filter (fun t : ℕ => ∃ z : ℤ, |g t-z| ≤ h), H N R U t) +
      ∑ t ∈ (range (U+1)).filter (fun t : ℕ => L*Real.sqrt N <
        |(t : ℝ)-(U : ℝ)*R/N|), H N R U t := by
    simp only [sum_filter]
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro t ht
    have hp : 0 ≤ H N R U t := by dsimp; split_ifs <;> positivity
    by_cases hP : P t
    · rw [if_pos hP]
      by_cases hc : |(t : ℝ)-(U : ℝ)*R/N| ≤ L*Real.sqrt N
      · rw [if_pos (hpush t ht hc hP), if_neg (not_lt.mpr hc)]
        exact le_add_of_nonneg_right (le_refl 0)
      · rw [if_pos (lt_of_not_ge hc)]
        exact le_add_of_nonneg_left (by split_ifs <;> positivity)
    · rw [if_neg hP]
      positivity
  have htail := kernel_central_tail hR hU hN L hL
  have he := hpart.trans (add_le_add hsmall htail)
  have hsum : 1/(4*L^2)+1/(4*L^2) = 1/(2*L^2) := by ring
  linarith only [he,hsum]

/-- Balanced margins give one root curve on an open neighborhood of the
whole central interval, not a collection of separately chosen roots. -/
private theorem balanced_shared_curve {ι : Type*} [Fintype ι] (outside : ι → ℝ)
    (r ε N R U q δ w : ℝ) (hN : 0 < N) (hq : 0 < q)
    (hqM : q < (Fintype.card ι : ℝ) + N) (hδ : 0 < δ) (hw : w ≤ δ^2*N/2)
    (hRlo : δ*N ≤ R) (hRhi : R ≤ (1-δ)*N)
    (hUlo : δ*N ≤ U) (hUhi : U ≤ (1-δ)*N) :
    ∃ θ : ℝ → ℝ, ∀ t : ℝ, |t-U*R/N| ≤ w →
      calibratedMean outside r ε N R U t (θ t) = q ∧
      HasDerivAt θ (-checkerboard r ε (θ t) /
        calibratedVariance outside r ε N R U t (θ t)) t ∧
      (∀ᶠ u in 𝓝 t, calibratedMean outside r ε N R U u (θ u) = q) ∧
      0 < calibratedVariance outside r ε N R U t (θ t) := by
  let ν := U*R/N
  let v := δ^2*N
  have hv : 0 < v := by dsimp [v]; positivity
  have hcells (t : ℝ) (ht : t ∈ Set.Ioo (ν-v) (ν+v)) (j : Fin 4) :
      0 ≤ cellCounts N R U t j := by
    have hc := central_four_cells_lower N R U δ t v hN hδ.le hRlo hRhi hUlo hUhi
      (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) j
    dsimp [v] at hc
    linarith
  obtain ⟨θ,hθ⟩ := shared_calibration_curve outside r ε N R U q (ν-v) (ν+v)
    hN hq hqM hcells
  refine ⟨θ, fun t ht => ?_⟩
  have hti : t ∈ Set.Ioo (ν-v) (ν+v) := by
    have hb := abs_le.mp ht
    dsimp [v,ν] at *
    constructor <;> nlinarith
  have he := hθ t hti
  refine ⟨he.1,he.2.1,?_,he.2.2⟩
  filter_upwards [isOpen_Ioo.mem_nhds hti] with u hu
  exact (hθ u hu).1

open private
  D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.shared_root_uniform_feedback
from D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds

open scoped Classical in
/-- The atom and tail inputs are discharged for the exact count kernel.
Uniform compensated feedback is derived from one base root and its variance;
only the quantitative base budgets remain to be supplied by native environments. -/
private theorem central_calibration_kernel_estimate {ι : Type*} [Fintype ι]
    (outside : ι → ℝ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ d η : ℝ, 0 < d ∧ 0 < η ∧
    ∀ (N R U : ℕ) (q bg δ L s K h ε X m : ℝ),
      1 < N → R ≤ N → U ≤ N → 0 < q → q < (Fintype.card ι : ℝ)+N →
      0 < δ → 0 < L → 0 < s → 0 ≤ K → 0 ≤ h → 0 < m →
      δ*N ≤ R → (R : ℝ) ≤ (1-δ)*N →
      δ*N ≤ U → (U : ℝ) ≤ (1-δ)*N →
      1 ≤ L*Real.sqrt N → L*Real.sqrt N ≤ δ^2*N/2 →
      ∃ θ : ℝ → ℝ,
      (∀ t : ℝ, |t-(U : ℝ)*R/N| ≤ L*Real.sqrt N →
        calibratedMean outside r ε N R U t (θ t) = q ∧
        HasDerivAt θ (-checkerboard r ε (θ t) /
          calibratedVariance outside r ε N R U t (θ t)) t ∧
        (∀ᶠ u in 𝓝 t, calibratedMean outside r ε N R U u (θ u) = q) ∧
        0 < calibratedVariance outside r ε N R U t (θ t)) ∧
      (let ν : ℝ := (U : ℝ)*R/N
       let w : ℝ := L*Real.sqrt N
       let V : ℝ := calibratedVariance outside r ε N R U ν (θ ν)
       w < V → 2*w ≤ (V-w)/2*Real.log 2 → |ε| < η →
       |θ ν|+4*w/(V-w) ≤ X → X < η → 0 ≤ bg+ν-w →
       s ≤ (bg+ν-w)*d/(16*(V+w))-X/4 →
       X/4+(bg+ν+w)/(V-w) ≤ K*s →
       (∑ t ∈ (range (U+1)).filter (fun t : ℕ => ∃ z : ℤ,
         |m*((bg+t)*Real.sigmoid (θ t)-(t : ℝ)/2)-z| ≤ h), H N R U t) ≤
       Real.exp 4 / ((δ^2/2)^2*Real.sqrt N) *
         (K*(m*s)*(2*L*Real.sqrt N)+2*h+1)*(2*h/(m*s)+1)+1/(4*L^2)) := by
  obtain ⟨d,η,hd,hη,huniform⟩ :=
    D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds.shared_root_uniform_feedback outside r hr hr1
  refine ⟨d,η,hd,hη,?_⟩
  intro N R U q bg δ L s K h ε X m hN hR hU hq hqM hδ hL hs hK hh hm
    hRlo hRhi hUlo hUhi hwide hsmall
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨θ,hθ⟩ := balanced_shared_curve outside r ε N R U q δ (L*Real.sqrt N)
    hN0 hq hqM hδ hsmall hRlo hRhi hUlo hUhi
  refine ⟨θ,hθ,?_⟩
  let ν : ℝ := (U : ℝ)*R/N
  let w : ℝ := L*Real.sqrt N
  let V : ℝ := calibratedVariance outside r ε N R U ν (θ ν)
  let a : ℤ := ⌈ν-w⌉
  let b : ℤ := ⌊ν+w⌋
  dsimp only
  intro hvar hbudget hε hX hXη hB hslow hfast
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hbase := (hθ ν (by simpa [ν,w] using hw)).1
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (a : ℝ) (b : ℝ)) : |t-ν| ≤ w := by
    have ha := Int.le_ceil (ν-w)
    have hb := Int.floor_le (ν+w)
    dsimp [a,b] at ht
    exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcurve (t : ℝ) (ht : t ∈ Set.Icc (a : ℝ) (b : ℝ)) :
      DifferentiableAt ℝ θ t ∧
      (∀ᶠ u in 𝓝 t, calibratedMean outside r ε N R U u (θ u) = q) ∧
      0 < calibratedVariance outside r ε N R U t (θ t) := by
    have he := hθ t (hpoint t ht)
    exact ⟨he.2.1.differentiableAt,he.2.2.1,he.2.2.2⟩
  have hfeedback (t : ℝ) (ht : t ∈ interior (Set.Icc (a : ℝ) (b : ℝ))) :
      s ≤ Real.sigmoid (θ t)-1/2 -
        (bg+t)*Real.sigmoid (θ t)*(1-Real.sigmoid (θ t))*checkerboard r ε (θ t) /
          calibratedVariance outside r ε N R U t (θ t) ∧
      Real.sigmoid (θ t)-1/2 -
        (bg+t)*Real.sigmoid (θ t)*(1-Real.sigmoid (θ t))*checkerboard r ε (θ t) /
          calibratedVariance outside r ε N R U t (θ t) ≤ K*s := by
    have hpt := hpoint t (interior_subset ht)
    have hcells (j : Fin 4) : 0 ≤ cellCounts N R U t j := by
      have hc := central_four_cells_lower N R U δ t w hN0 hδ.le
        hRlo hRhi hUlo hUhi hpt j
      linarith
    have htlo : bg+ν-w ≤ bg+t := by linarith [(abs_le.mp hpt).1]
    have hthi : bg+t ≤ bg+ν+w := by linarith [(abs_le.mp hpt).2]
    have he := huniform ε N R U q t ν (θ ν) (θ t) w (bg+t) X hN0 hcells hpt
      hbase (hθ t hpt).1 hvar hbudget hε hX hXη (hB.trans htlo)
    have hden : 0 < 16*(V+w) := by dsimp [V]; linarith
    have hlow : (bg+ν-w)*d/(16*(V+w)) ≤ (bg+t)*d/(16*(V+w)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htlo hd.le) hden.le
    have hhigh : (bg+t)/(V-w) ≤ (bg+ν+w)/(V-w) :=
      div_le_div_of_nonneg_right hthi (sub_pos.mpr hvar).le
    constructor <;> linarith [he.1,he.2]
  obtain ⟨hl,hu⟩ := shared_calibration_increment_bounds outside r ε N R U q bg θ a b s K
    hcurve hfeedback
  apply hypergeometric_arithmetic_bound hN hR hU δ L (m*s) K h hδ hL
    (mul_pos hm hs) hK hh hRlo hRhi hUlo hUhi hwide hsmall
    (fun t : ℤ => m*((bg+t)*Real.sigmoid (θ t)-(t : ℝ)/2))
  · intro x hx y hy hxy
    have he := mul_le_mul_of_nonneg_left (hl x hx y hy hxy) hm.le
    nlinarith only [he]
  · intro x hx y hy hxy
    have he := mul_le_mul_of_nonneg_left (hu x hx y hy hxy) hm.le
    nlinarith only [he]

end
end D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
