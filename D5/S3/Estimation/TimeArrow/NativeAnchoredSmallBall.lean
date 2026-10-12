/- GID: D5/S3/Estimation/TimeArrow/NativeAnchoredSmallBall
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeAnchoredSmallBall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual full-root anchor drives the original posterior phase through the native conditional kernel. -/

import D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback

open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
open D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.NativeAnchoredSmallBall
noncomputable section

set_option quotPrecheck false in
local notation "H" => fun N R U t : ℕ => if t ≤ U then
  ((R.choose t : ℝ)*((N-R).choose (U-t) : ℝ))/(N.choose U : ℝ) else 0

set_option maxHeartbeats 800000 in
/-- The curve certificate supplies the full posterior approximation. The
conditioning remains the original minimal environment, including its tails. -/
theorem native_certified_curve_small_ball :
    ∃ Cpost V0 : ℝ, 0 < Cpost ∧ 0 < V0 ∧
    ∀ (M q s : ℕ) (S : Support M q) (r : ℝ) (e : Experiment) (o : Obs M s e),
    ∀ [Fintype (Sites s e)], 1 ≤ q → q < M → 0 < r → r < 1 →
      0 ≤ compensation M q r → compensation M q r < 1 →
    ∀ (k l : ℕ) (z : Fiber S e o) (θ : ℝ → ℝ) (ell : ℤ) (τ L s0 K D : ℝ),
      letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
      let All : Support M M := ⟨univ,by simp⟩
      let bg : ℝ := (nativeCalibrationCells All e o k l 0 \ S.val).card
      let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
        (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
      let V := nativeRectangleRows S e o k l z
      let R := (V.filter fun i => count e z.val i.val 1 = k).card
      let U := (V.filter fun i => count e z.val i.val (-1) = l).card
      let ν : ℝ := (U : ℝ)*R/V.card
      let w := L*Real.sqrt V.card
      let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
        fun i => score q r e z.val i.val-z0
      let Env := univ.filter fun y : Fiber S e o =>
        nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
      let E := Cpost*(bg+ν+w)/D
      let m := 2*|(ell : ℝ)|
      let h := 2*τ+m*E
      let Q := fun y : Fiber S e o => ∃ a : ℤ, |(ell : ℝ)*(1/2-
        (∑ i ∈ nativeCalibrationCells All e y.val k l 0,inclusion q r e y.val i))-a| ≤ τ
      letI : DecidablePred Q := Classical.decPred Q
      1 < V.card → 0 < L → 0 < s0 → 0 ≤ K → 0 ≤ τ → ell ≠ 0 →
      (V.card : ℝ)/4 ≤ R → (R : ℝ) ≤ 3*V.card/4 →
      (V.card : ℝ)/4 ≤ U → (U : ℝ) ≤ 3*V.card/4 →
      1 ≤ w → w ≤ (V.card : ℝ)/32 → V0 ≤ D →
      (∀ t : ℝ, |t-ν| ≤ w →
        calibratedMean outside r (compensation M q r) V.card R U t (θ t) = q ∧
        D ≤ calibratedVariance outside r (compensation M q r) V.card R U t (θ t) ∧
        ∃ slope : ℝ, s0 ≤ slope ∧ slope ≤ K*s0 ∧
          HasDerivAt (fun u => (bg+u)*Real.sigmoid (θ u)-u/2) slope t) →
      conditionalFiberMass S r e o (Env.filter Q)/conditionalFiberMass S r e o Env ≤
        Real.exp 4/(((1/4 : ℝ)^2/2)^2*Real.sqrt V.card)*
          (K*(m*s0)*(2*L*Real.sqrt V.card)+2*h+1)*(2*h/(m*s0)+1)+1/(2*L^2) := by
  classical
  obtain ⟨Cpost,hC,V0,hV0,hpost⟩ := native_posterior_central_kernel_bound
  refine ⟨Cpost,V0,hC,hV0,?_⟩
  intro M q s S r e o _ hq hqm hr hr1 hε hε1 k l z θ ell τ L s0 K D
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  let All : Support M M := ⟨univ,by simp⟩
  let bg : ℝ := (nativeCalibrationCells All e o k l 0 \ S.val).card
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let ν : ℝ := (U : ℝ)*R/V.card
  let w := L*Real.sqrt V.card
  let Env := univ.filter fun y : Fiber S e o =>
    nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
  let E := Cpost*(bg+ν+w)/D
  let m := 2*|(ell : ℝ)|
  let h := 2*τ+m*E
  let G : ℝ → ℝ := fun t => (bg+t)*Real.sigmoid (θ t)-t/2
  let g : ℤ → ℝ := fun t => m*G t
  let P : ℕ → Prop := fun t => w < |(t : ℝ)-ν| ∨ ∃ a : ℤ,
    |2*(ell : ℝ)*G t-a| ≤ h
  intro hN hL hs hK hτ hell hRlo hRhi hUlo hUhi hwide hsmall hD hcurve
  have hR : R ≤ V.card := card_filter_le _ _
  have hU : U ≤ V.card := card_filter_le _ _
  have hm : 0 < m := by
    have he : (ell : ℝ) ≠ 0 := by exact_mod_cast hell
    dsimp [m]; positivity
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hDpos : 0 < D := hV0.trans_le hD
  have hh : 0 ≤ h := by dsimp [h,E,w,bg]; positivity
  have hp := hpost M q s S r e o hq hqm hr hr1 hε hε1 k l z θ ell τ w D hD
    (fun y _ hc => (hcurve _ hc).1)
    (fun y _ hc => (hcurve _ hc).2.1)
  have hcont : ContinuousOn G (Set.Icc (ν-w) (ν+w)) := by
    intro t ht
    have hc : |t-ν| ≤ w := by rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
    obtain ⟨slope,_,_,hd⟩ := (hcurve t hc).2.2
    exact hd.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ G (interior (Set.Icc (ν-w) (ν+w))) := by
    intro t ht
    have ht' := interior_subset ht
    have hc : |t-ν| ≤ w := by rw [abs_le]; constructor <;> linarith [ht'.1,ht'.2]
    obtain ⟨slope,_,_,hd⟩ := (hcurve t hc).2.2
    exact hd.differentiableAt.differentiableWithinAt
  have hder : ∀ t ∈ interior (Set.Icc (ν-w) (ν+w)), s0 ≤ deriv G t ∧ deriv G t ≤ K*s0 := by
    intro t ht
    have ht' := interior_subset ht
    have hc : |t-ν| ≤ w := by rw [abs_le]; constructor <;> linarith [ht'.1,ht'.2]
    obtain ⟨slope,hlo,hhi,hd⟩ := (hcurve t hc).2.2
    change HasDerivAt G slope t at hd
    rw [hd.deriv]
    exact ⟨hlo,hhi⟩
  have hlo := (convex_Icc (ν-w) (ν+w)).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun t ht => (hder t ht).1)
  have hhi := (convex_Icc (ν-w) (ν+w)).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun t ht => (hder t ht).2)
  have hmem (t : ℤ) (ht : t ∈ Icc ⌈ν-w⌉ ⌊ν+w⌋) :
      (t : ℝ) ∈ Set.Icc (ν-w) (ν+w) :=
    ⟨Int.ceil_le.mp (mem_Icc.mp ht).1,Int.le_floor.mp (mem_Icc.mp ht).2⟩
  have hscalar := hypergeometric_arithmetic_bound hN hR hU (1/4) L (m*s0) K h
    (by norm_num) hL (mul_pos hm hs) hK hh
    (by linarith only [hRlo]) (by linarith only [hRhi])
    (by linarith only [hUlo]) (by linarith only [hUhi]) hwide
    (by nlinarith only [hsmall]) g
    (fun x hx y hy hxy => by
      have he := mul_le_mul_of_nonneg_left (hlo x (hmem x hx) y (hmem y hy)
        (by exact_mod_cast hxy)) hm.le
      simpa only [g,Int.cast_sub,mul_sub,mul_assoc] using he)
    (fun x hx y hy hxy => by
      have he := mul_le_mul_of_nonneg_left (hhi x (hmem x hx) y (hmem y hy)
        (by exact_mod_cast hxy)) hm.le
      simpa only [g,Int.cast_sub,mul_sub,mul_assoc,mul_left_comm K m] using he)
  have hp' : conditionalFiberMass S r e o
      (Env.filter fun y => ∃ a : ℤ, |(ell : ℝ)*(1/2-
        (∑ i ∈ nativeCalibrationCells All e y.val k l 0,inclusion q r e y.val i))-a| ≤ τ)/
      conditionalFiberMass S r e o Env ≤ ∑ t ∈ (range (U+1)).filter P,H V.card R U t := by
    convert hp using 1 <;> congr 1
    ext t
    simp only [mem_filter]
    rfl
  apply hp'.trans
  convert hypergeometric_predicate_bound hR hU hN L hL P g h _ ?_ hscalar using 1
  · congr 1
  · congr 1
    ext t
    simp only [mem_filter]
  intro t _ hc hP
  rcases hP with ht | ⟨a,ha⟩
  · exact False.elim ((not_lt.mpr hc) ht)
  by_cases he : 0 ≤ (ell : ℝ)
  · refine ⟨a,?_⟩
    simpa only [g,m,Int.cast_natCast,abs_of_nonneg he] using ha
  · refine ⟨-a,?_⟩
    have heq : g t-((-a : ℤ) : ℝ) = -(2*(ell : ℝ)*G t-a) := by
      simp only [g,m,Int.cast_natCast,Int.cast_neg,abs_of_neg (lt_of_not_ge he)]
      ring
    rw [heq,abs_neg]
    exact ha

end
end D5.S3.Estimation.TimeArrow.NativeAnchoredSmallBall
