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

end
end D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
