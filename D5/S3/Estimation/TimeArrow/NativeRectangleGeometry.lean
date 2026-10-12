/- GID: D5/S3/Estimation/TimeArrow/NativeRectangleGeometry
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeRectangleGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Five actual occupancies give the original rectangle size and balanced margins. -/

import D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy
import D5.S3.Estimation.TimeArrow.NativeRectangleReferenceMass
import D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment
import D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceMass
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeRectangleGeometry
noncomputable section

private theorem native_occupancy_geometry {M q s : ℕ} (S : Support M q)
    (e : Experiment) (o : Obs M s e) (k l : ℕ) (m : ℝ)
    (hcell : ∀ j : Fin 4,
      3/4*m ≤ ((nativeCalibrationCells S e o k l j).card : ℝ) ∧
      ((nativeCalibrationCells S e o k l j).card : ℝ) ≤ 5/4*m)
    (hbg : ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ)
      ≤ 5/4*m) :
    let V := nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)
    let R := (V.filter fun i => count e o i.val 1 = k).card
    let U := (V.filter fun i => count e o i.val (-1) = l).card
    3*m ≤ V.card ∧ (V.card : ℝ) ≤ 5*m ∧
      3/8*(V.card : ℝ) ≤ R ∧ (R : ℝ) ≤ 5/8*(V.card : ℝ) ∧
      3/8*(V.card : ℝ) ≤ U ∧ (U : ℝ) ≤ 5/8*(V.card : ℝ) ∧
      ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ)
        ≤ 5/12*(V.card : ℝ) := by
  have hc := native_calibration_counts_margins S e o k l (⟨o,rfl⟩ : Fiber S e o)
  dsimp only at hc ⊢
  rcases hc with ⟨hN,hR,hU,_⟩
  rw [hN,hR,hU]
  push_cast
  have h0 := hcell 0
  have h1 := hcell 1
  have h2 := hcell 2
  have h3 := hcell 3
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,hbg]

/-- The actual native good event has N comparable to q/lambda, balanced
margins, and background A no larger than N. All five occupancies are
proved under the original pair or path law with one shared failure budget. -/
theorem native_signal_geometry_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ K : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧ 0 < K ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1-κ → compensation M q r ≤ 1-κ →
        1 ≤ L → (L : ℝ)/M ≤ η₀ → A*(L : ℝ)^2/M ≤ 1/2 →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val →
          15 ≤ ((1+r)/2)*(L : ℝ) → 30 ≤ ((1-r)/2)*(L : ℝ) →
          let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
          let l := L-k
          let dA := k*Real.log ((1+r)/(1-compensation M q r)) +
            l*Real.log ((1-r)/(1+compensation M q r)) - Real.log (((M-q : ℕ) : ℝ)/q)
          Real.log (7/8) ≤ -dA → -dA ≤ Real.log (9/8) →
          let c := Real.exp (-1/((1+r)/2)-1)*Real.exp (-1/((1-r)/2)-1) /
            (Real.sqrt ((3/2)*((1+r)/2))*Real.sqrt ((3/2)*((1-r)/2)))
          let C := 2/Real.sqrt (((1+r)/2)*((1-r)/2))
          let m := (q : ℝ)*rowReference S r L i (k,l)
          (∑ o : Obs M (2*M*L) e,
            let V := nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)
            let R := (V.filter fun u => count e o u.val 1 = k).card
            let U := (V.filter fun u => count e o u.val (-1) = l).card
            if ¬(3*c*q/L ≤ V.card ∧ (V.card : ℝ) ≤ 5*C*q/L ∧
                3/8*(V.card : ℝ) ≤ R ∧ (R : ℝ) ≤ 5/8*(V.card : ℝ) ∧
                3/8*(V.card : ℝ) ≤ U ∧ (U : ℝ) ≤ 5/8*(V.card : ℝ) ∧
                ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ)
                  ≤ 5/12*(V.card : ℝ) ∧
                (∀ t : ℕ, 2 ≤ V.card →
                  (∑ x : Obs M (2*M*L) e,
                    if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧
                        nativeRectangleACount S e x k l (⟨x,rfl⟩ : Fiber S e x) = t
                    then probability r e S x else 0) /
                    (∑ x : Obs M (2*M*L) e,
                      if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o
                      then probability r e S x else 0) ≤ K/Real.sqrt V.card))
            then probability r e S o else 0) ≤ 540/m+1215*(A*(L : ℝ)^3/M) := by
  classical
  obtain ⟨A,M₀,η₀,hA,hM₀,hη₀,h⟩ := native_signal_background_occupancy κ hκ hκ1
  obtain ⟨K,hKpos,hK⟩ := hypergeometric_balanced_max_atom (3/8) (by norm_num) (by norm_num)
  refine ⟨A,M₀,η₀,K,hA,hM₀,hη₀,hKpos,?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e i j hi hj hplus hminus
  dsimp only
  intro hdlo hdhi
  let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
  let l := L-k
  let c := Real.exp (-1/((1+r)/2)-1)*Real.exp (-1/((1-r)/2)-1) /
    (Real.sqrt ((3/2)*((1+r)/2))*Real.sqrt ((3/2)*((1-r)/2)))
  let C := 2/Real.sqrt (((1+r)/2)*((1-r)/2))
  let m := (q : ℝ)*rowReference S r L i (k,l)
  have hm := floored_signal_reference_mass S r hr (by linarith only [hrκ,hκ]) hL i hi hplus hminus
  dsimp only at hm
  have hml : c*(q : ℝ)/L ≤ m := by
    have hh := mul_le_mul_of_nonneg_left hm.1 (by positivity : (0 : ℝ) ≤ q)
    simpa only [c,m,mul_div_assoc,div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hh
  have hmu : m ≤ C*(q : ℝ)/L := by
    have hh := mul_le_mul_of_nonneg_left hm.2 (by positivity : (0 : ℝ) ≤ q)
    simpa only [C,m,mul_div_assoc,div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hh
  have hb := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e i j hi hj
    k l rfl rfl hplus hminus hdlo hdhi
  apply le_trans _ hb
  apply sum_le_sum
  intro o _
  by_cases hg : (∀ a : Fin 4,
      3/4*m ≤ ((nativeCalibrationCells S e o k l a).card : ℝ) ∧
      ((nativeCalibrationCells S e o k l a).card : ℝ) ≤ 5/4*m) ∧
      3/4*m ≤ ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ) ∧
      ((nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ) ≤ 5/4*m
  · have hn := native_occupancy_geometry S e o k l m hg.1 hg.2.2
    dsimp only at hn
    have hlo := (mul_le_mul_of_nonneg_left hml (by norm_num : (0 : ℝ) ≤ 3)).trans hn.1
    have hhi := hn.2.1.trans (mul_le_mul_of_nonneg_left hmu (by norm_num : (0 : ℝ) ≤ 5))
    letI : Fintype (Sites (2*M*L) e) := by cases e <;> unfold Sites <;> infer_instance
    let V := nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)
    let R := (V.filter fun u => count e o u.val 1 = k).card
    let U := (V.filter fun u => count e o u.val (-1) = l).card
    have hatom (t : ℕ) (hN : 2 ≤ V.card) :
        (∑ x : Obs M (2*M*L) e,
          if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧
              nativeRectangleACount S e x k l (⟨x,rfl⟩ : Fiber S e x) = t
          then probability r e S x else 0) /
          (∑ x : Obs M (2*M*L) e,
            if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o
            then probability r e S x else 0) ≤ K/Real.sqrt V.card := by
      have he := full_native_four_cell_conditional_law S r e o hq hqm hr
        (by linarith only [hrκ,hκ]) (by unfold compensation; positivity)
        (by linarith only [hcκ,hκ]) k l t
      have hb := hK V.card R U t hN (card_filter_le V _) (card_filter_le V _)
        hn.2.2.1 (by simpa using hn.2.2.2.1)
        hn.2.2.2.2.1 (by simpa using hn.2.2.2.2.2.1)
      dsimp only at he
      rw [he]
      exact hb
    have hgood := And.intro (by simpa [mul_div_assoc] using hlo)
      (And.intro (by simpa [mul_div_assoc] using hhi)
        ⟨hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2,hatom⟩)
    change (if ¬_ then _ else _) ≤ (if ¬_ then _ else _)
    rw [if_neg hgood,if_neg hg]
  · have hp := (finite_support_bayes (s := 2*M*L) hq hqm hr
      (by linarith only [hrκ,hκ]) (by
        unfold compensation
        positivity) (by linarith only [hcκ,hκ]) e).2.2.1 S o
    change (if ¬_ then _ else _) ≤ (if ¬_ then _ else _)
    rw [if_pos hg]
    split_ifs <;> first | exact le_rfl | exact hp.1.le

end
end D5.S3.Estimation.TimeArrow.NativeRectangleGeometry
