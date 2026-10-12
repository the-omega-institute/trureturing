/- GID: D5/S3/Estimation/TimeArrow/NativeAnchoredSmallBall
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeAnchoredSmallBall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual full-root anchor drives the original posterior phase through the native conditional kernel. -/

import D5.S3.Estimation.TimeArrow.CalibratedArithmeticSmallBall
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

set_option maxHeartbeats 800000 in
private theorem registered_shape_bound (A K e m s τ L u E : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (he : 0 ≤ e) (hm : 2 ≤ m)
    (hs : 0 < s) (hs1 : s ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1/2)
    (hL : 0 < L) (hu : 0 < u) (hE : 0 ≤ E) (hEe : E ≤ e*s) :
    let h := 2*τ+m*E
    let C := 1+A*(8*K+2*K*m*(2*e+1)+(3+2*m*e)*(3+2*e))
    A/u*(K*(m*s)*(2*L*u)+2*h+1)*(2*h/(m*s)+1)+1/(2*L^2) ≤
      C*(L*(s+τ)+(1+τ/s)/u+L^(-2 : ℤ)) := by
  dsimp only
  let h := 2*τ+m*E
  have hm0 : 0 < m := by linarith only [hm]
  have he1 : E ≤ e := hEe.trans (mul_le_of_le_one_right he hs1)
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have h1 : 2*h+1 ≤ 3+2*m*e := by
    dsimp only [h]
    nlinarith only [hτ1,mul_le_mul_of_nonneg_left he1 hm0.le]
  have h2 : 2*h/(m*s)+1 ≤ (3+2*e)*(1+τ/s) := by
    have hcoef : 4 ≤ (3+2*e)*m := by nlinarith only [he,hm]
    have hτm := mul_le_mul_of_nonneg_right hcoef hτ
    have hsm : m*(2*e+1)*s ≤ (3+2*e)*m*s := by
      apply mul_le_mul_of_nonneg_right _ hs.le
      nlinarith only [hm0]
    calc
      _ = (2*h+m*s)/(m*s) := by field_simp <;> ring
      _ ≤ ((3+2*e)*m*(s+τ))/(m*s) := by
        apply div_le_div_of_nonneg_right _ (mul_pos hm0 hs).le
        dsimp only [h]
        nlinarith only [mul_le_mul_of_nonneg_left hEe hm0.le,hτm,hsm]
      _ = _ := by field_simp <;> ring
  have h3 : 2*h+m*s ≤ 4*τ+m*(2*e+1)*s := by
    dsimp only [h]
    nlinarith only [mul_le_mul_of_nonneg_left hEe hm0.le]
  let B1 := A*(8*K+2*K*m*(2*e+1))
  let B2 := A*(3+2*m*e)*(3+2*e)
  have hB1 : 0 ≤ B1 := by dsimp [B1]; positivity
  have hB2 : 0 ≤ B2 := by dsimp [B2]; positivity
  have hfirst : 2*A*K*L*(2*h+m*s) ≤ B1*L*(s+τ) := by
    calc
      _ ≤ 2*A*K*L*(4*τ+m*(2*e+1)*s) := by gcongr
      _ ≤ _ := by dsimp [B1]; nlinarith only [mul_nonneg (by positivity : 0 ≤ 8*A*K*L) hs.le,
        mul_nonneg (by positivity : 0 ≤ 2*A*K*m*(2*e+1)*L) hτ]
  have hsecond : A*(2*h+1)*(2*h/(m*s)+1)/u ≤ B2*(1+τ/s)/u := by
    apply div_le_div_of_nonneg_right _ hu.le
    calc
      _ ≤ A*(3+2*m*e)*((3+2*e)*(1+τ/s)) := by gcongr
      _ = _ := by dsimp [B2]; ring
  have hsplit : A/u*(K*(m*s)*(2*L*u)+2*h+1)*(2*h/(m*s)+1) =
      2*A*K*L*(2*h+m*s)+A*(2*h+1)*(2*h/(m*s)+1)/u := by
    field_simp
    ring
  have htail : 1/(2*L^2) ≤ L^(-2 : ℤ) := by
    rw [zpow_neg, zpow_ofNat]
    simp only [inv_eq_one_div]
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hL)
    nlinarith only [sq_nonneg L]
  have hsum : A/u*(K*(m*s)*(2*L*u)+2*h+1)*(2*h/(m*s)+1)+1/(2*L^2) ≤
      B1*L*(s+τ)+B2*(1+τ/s)/u+L^(-2 : ℤ) := by
    rw [hsplit]
    exact add_le_add (add_le_add hfirst hsecond) htail
  apply hsum.trans
  let C := 1+A*(8*K+2*K*m*(2*e+1)+(3+2*m*e)*(3+2*e))
  have hC1 : B1 ≤ C := by dsimp [B1,B2,C]; nlinarith only [hB2]
  have hC2 : B2 ≤ C := by dsimp [B1,B2,C]; nlinarith only [hB1]
  have hC3 : 1 ≤ C := by dsimp [B1,B2,C]; nlinarith only [hB1,hB2]
  calc
    _ ≤ C*(L*(s+τ))+C*((1+τ/s)/u)+C*L^(-2 : ℤ) := by
      apply add_le_add
      · apply add_le_add
        · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hC1
            (by positivity : 0 ≤ L*(s+τ))
        · simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ 1+τ/s)) hu.le
      · simpa only [one_mul] using mul_le_mul_of_nonneg_right hC3 (by positivity)
    _ = _ := by ring

private theorem native_event_ratio_le_one {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hε : 0 ≤ compensation M q r) (hε1 : compensation M q r < 1)
    (F : Finset (Fiber S e o)) (Q : Fiber S e o → Prop) [DecidablePred Q] :
    conditionalFiberMass S r e o (F.filter Q)/conditionalFiberMass S r e o F ≤ 1 := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  have hprob (y : Fiber S e o) : 0 ≤ probability r e S y.val :=
    ((finite_support_bayes (s := s) hq hqm hr hr1 hε hε1 e).2.2.1 S y.val).1.le
  have htotal : 0 ≤ ∑ y : Fiber S e o,probability r e S y.val :=
    sum_nonneg fun y _ => hprob y
  have hden : 0 ≤ conditionalFiberMass S r e o F := by
    unfold conditionalFiberMass
    exact div_nonneg (sum_nonneg fun y _ => hprob y) htotal
  have hmono : conditionalFiberMass S r e o (F.filter Q) ≤ conditionalFiberMass S r e o F := by
    unfold conditionalFiberMass
    apply div_le_div_of_nonneg_right _ htotal
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun y _ _ => hprob y)
  by_cases hz : conditionalFiberMass S r e o F = 0
  · rw [hz,div_zero]
    norm_num
  · exact (div_le_one₀ (lt_of_le_of_ne hden (Ne.symm hz))).mpr hmono

set_option maxHeartbeats 3000000 in
/-- A single actual full-root anchor proves the registered three-term
arithmetic estimate for every positive L and nonnegative tolerance. All posterior,
variance, feedback, atom and tail inputs are derived on the same fiber. -/
theorem native_anchored_posterior_small_ball :
    ∃ Cpost V0 : ℝ, 0 < Cpost ∧ 0 < V0 ∧
    ∀ (r v : ℝ), 0 < r → r < 1 → 0 < v →
    ∃ a γ η c Cfb : ℝ, 0 < a ∧ 0 < γ ∧ γ ≤ 1/32 ∧ 0 < η ∧ 0 < c ∧ 0 < Cfb ∧
    ∀ ell : ℤ, ell ≠ 0 → ∃ Cell : ℝ, 0 < Cell ∧
    ∀ (M q s : ℕ) (S : Support M q) (e : Experiment) (o : Obs M s e),
    ∀ [Fintype (Sites s e)], ∀ (k l : ℕ) (z : Fiber S e o),
      1 ≤ q → q < M → 0 ≤ compensation M q r → compensation M q r < 1 →
      letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
      let All : Support M M := ⟨univ,by simp⟩
      let bg : ℝ := (nativeCalibrationCells All e o k l 0 \ S.val).card
      let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
        (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
      let V := nativeRectangleRows S e o k l z
      let N : ℝ := V.card
      let R : ℝ := (V.filter fun i => count e z.val i.val 1 = k).card
      let U : ℝ := (V.filter fun i => count e z.val i.val (-1) = l).card
      let Env := univ.filter fun y : Fiber S e o =>
        nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
      let s0 := c*(N/q)
      1 < V.card → N/4 ≤ R → R ≤ 3*N/4 → N/4 ≤ U → U ≤ 3*N/4 →
      max 4 (32/(a*v)) ≤ Real.sqrt N →
      N/q ≤ v/2 → N/q ≤ v*Real.log 2/8 → a*N/q < η →
      |compensation M q r| < η → bg ≤ N → s0 ≤ 1 → V0 ≤ v*q/4 → 1 ≤ γ*s0*Real.sqrt N →
      ∀ (anchor : Fiber S e o) (xStar : ℝ),
        nativeMinimalRectangleReadout S e o k l anchor = nativeMinimalRectangleReadout S e o k l z →
        (∑ i : Fin M,Real.sigmoid (xStar+(score q r e anchor.val i-z0))) = q →
        v*q ≤ ∑ i : Fin M,Real.sigmoid (xStar+(score q r e anchor.val i-z0))*
          (1-Real.sigmoid (xStar+(score q r e anchor.val i-z0))) →
        |xStar| ≤ a*N/(4*q) →
        |(nativeRectangleACount S e o k l anchor : ℝ)-U*R/N| ≤ 2*Real.sqrt N →
        ∀ L τ : ℝ, 0 < L → 0 ≤ τ →
          let Q := fun y : Fiber S e o => ∃ b : ℤ, |(ell : ℝ)*(1/2-
            (∑ i ∈ nativeCalibrationCells All e y.val k l 0,inclusion q r e y.val i))-b| ≤ τ
          letI : DecidablePred Q := Classical.decPred Q
          conditionalFiberMass S r e o (Env.filter Q)/conditionalFiberMass S r e o Env ≤
            Cell*(L*(s0+τ)+(1+τ/s0)/Real.sqrt N+L^(-2 : ℤ)) := by
  classical
  obtain ⟨Cpost,V0,hCpost,hV0,hsmall⟩ := native_certified_curve_small_ball
  refine ⟨Cpost,V0,hCpost,hV0,?_⟩
  intro r v hr hr1 hv
  obtain ⟨a,γ0,η,c,Cfb,ha,hγ0,hη,hc,hCfb,hfeedback⟩ := native_anchored_central_feedback r hr hr1 v hv
  let γ := min γ0 (1/32)
  have hγ : 0 < γ := lt_min hγ0 (by norm_num)
  refine ⟨a,γ,η,c,Cfb,ha,hγ,min_le_right _ _,hη,hc,hCfb,?_⟩
  intro ell hell
  let m := 2*|(ell : ℝ)|
  let A := Real.exp 4/((1/4 : ℝ)^2/2)^2
  let K := Cfb/c
  let errRatio := 12*Cpost/(v*c)
  let Cell := 4+A*(8*K+2*K*m*(2*errRatio+1)+(3+2*m*errRatio)*(3+2*errRatio))
  have hm : 2 ≤ m := by
    have hh : (1 : ℝ) ≤ |(ell : ℝ)| := by exact_mod_cast Int.one_le_abs hell
    dsimp only [m]
    linarith only [hh]
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have herrRatio : 0 < errRatio := by dsimp [errRatio]; positivity
  have hCell : 0 < Cell := by dsimp [Cell]; positivity
  refine ⟨Cell,hCell,?_⟩
  intro M q s S e o _ k l z hq hqm hε hε1
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  dsimp only
  let All : Support M M := ⟨univ,by simp⟩
  let bg : ℝ := (nativeCalibrationCells All e o k l 0 \ S.val).card
  let V := nativeRectangleRows S e o k l z
  let N : ℝ := V.card
  let R : ℝ := (V.filter fun i => count e z.val i.val 1 = k).card
  let U : ℝ := (V.filter fun i => count e z.val i.val (-1) = l).card
  let ν := U*R/N
  let s0 := c*(N/q)
  intro hN hRlo hRhi hUlo hUhi hlarge hsize hsize' hηscale hεη hbgN hs1 hV hscale
    anchor xStar henv hroot hvar hx hstar L τ hL hτ
  have hNnat : 0 < V.card := by
    change 1 < V.card at hN
    omega
  have hN0 : 0 < N := by dsimp [N]; exact_mod_cast hNnat
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hs0 : 0 < s0 := by dsimp [s0]; positivity
  have hbg : 0 ≤ bg := by dsimp [bg]; positivity
  let Env := univ.filter fun y : Fiber S e o =>
    nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l z
  let Q := fun y : Fiber S e o => ∃ b : ℤ, |(ell : ℝ)*(1/2-
    (∑ i ∈ nativeCalibrationCells All e y.val k l 0,inclusion q r e y.val i))-b| ≤ τ
  have hmass1 := native_event_ratio_le_one S r e o hq hqm hr hr1 hε hε1 Env Q
  have hC4 : 4 ≤ Cell := by
    dsimp [Cell]
    have hh : 0 ≤ A*(8*K+2*K*m*(2*errRatio+1)+(3+2*m*errRatio)*(3+2*errRatio)) := by positivity
    linarith only [hh]
  have hC1 : 1 ≤ Cell := (by norm_num : (1 : ℝ) ≤ 4).trans hC4
  have hsum0 : 0 ≤ L*(s0+τ)+(1+τ/s0)/Real.sqrt N+L^(-2 : ℤ) := by positivity
  have htrivial (hx : 1 ≤ Cell*(L*(s0+τ)+(1+τ/s0)/Real.sqrt N+L^(-2 : ℤ))) :
      conditionalFiberMass S r e o (Env.filter Q)/conditionalFiberMass S r e o Env ≤
        Cell*(L*(s0+τ)+(1+τ/s0)/Real.sqrt N+L^(-2 : ℤ)) := hmass1.trans hx
  by_cases hLsmall : L ≤ 2
  · apply htrivial
    have htail : 1 ≤ 4*L^(-2 : ℤ) := by
      rw [zpow_neg,zpow_ofNat]
      simp only [inv_eq_one_div]
      rw [mul_one_div]
      apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
      nlinarith only [hL,hLsmall]
    have hbound := mul_le_mul_of_nonneg_right hC4 (by positivity : 0 ≤ L^(-2 : ℤ))
    have hrest : 0 ≤ Cell*(L*(s0+τ)+(1+τ/s0)/Real.sqrt N) := by positivity
    nlinarith only [htail,hbound,hrest]
  have hL2 : 2 < L := lt_of_not_ge hLsmall
  by_cases hτlarge : 1/2 < τ
  · apply htrivial
    have hmain : 1 ≤ L*(s0+τ) := by nlinarith only [hL2,hτlarge,hs0]
    have hh := mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ L*(s0+τ))
    have hrest : 0 ≤ Cell*((1+τ/s0)/Real.sqrt N+L^(-2 : ℤ)) := by positivity
    nlinarith only [hmain,hh,hrest]
  have hτ1 : τ ≤ 1/2 := le_of_not_gt hτlarge
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsqrt4 : 4 ≤ Real.sqrt N := (le_max_left _ _).trans hlarge
  have hsqrt_eq : (Real.sqrt N)^2 = N := Real.sq_sqrt hN0.le
  by_cases hLlarge : γ*Real.sqrt N < L
  · apply htrivial
    have hh := mul_le_mul_of_nonneg_right hLlarge.le hs0.le
    have hmain : 1 ≤ L*(s0+τ) := by
      have hLτ : 0 ≤ L*τ := mul_nonneg hL.le hτ
      nlinarith only [hscale,hh,hLτ]
    have hh' := mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ L*(s0+τ))
    have hrest : 0 ≤ Cell*((1+τ/s0)/Real.sqrt N+L^(-2 : ℤ)) := by positivity
    nlinarith only [hmain,hh',hrest]
  have hwide : 1 ≤ L*Real.sqrt N := by nlinarith only [hL2,hsqrt4]
  have hcentral : L*Real.sqrt N ≤ γ*N := by
    have hh := mul_le_mul_of_nonneg_right (le_of_not_gt hLlarge) hsqrt.le
    calc
      _ ≤ γ*Real.sqrt N*Real.sqrt N := hh
      _ = γ*N := by rw [mul_assoc,←sq,hsqrt_eq]
  have hγle : γ ≤ γ0 := min_le_left _ _
  have hγsmall : γ ≤ 1/32 := min_le_right _ _
  obtain ⟨θ,hθ,_⟩ := hfeedback M q s S e o k l z hq hqm hε hε1 hN0
    hRlo hRhi hUlo hUhi hlarge hsize hsize' hηscale hεη bg hbg hbgN
    anchor xStar henv hroot hvar hx hstar
  let w := L*Real.sqrt N
  let E := Cpost*(bg+ν+w)/(v*q/4)
  have hwN : w ≤ N/32 := by
    have hh := mul_le_mul_of_nonneg_right hγsmall hN0.le
    dsimp only [w] at *
    nlinarith only [hcentral,hh]
  have htcentral (t : ℝ) (ht : |t-ν| ≤ w) : |t-ν| ≤ γ0*N :=
    ht.trans (hcentral.trans (mul_le_mul_of_nonneg_right hγle hN0.le))
  have hraw := hsmall M q s S r e o hq hqm hr hr1 hε hε1 k l z θ ell τ L s0 K (v*q/4)
    hN hL hs0 hK.le hτ hell hRlo hRhi hUlo hUhi hwide hwN hV
    (fun t ht => by
      have he := hθ t (htcentral t ht)
      obtain ⟨slope,hlo,hhi,hd⟩ := he.2.2.2.2.2.2
      refine ⟨he.1,he.2.2.1,slope,hlo,?_,hd⟩
      have heq : Cfb*(N/q) = K*s0 := by dsimp [K,s0]; field_simp <;> ring
      rwa [←heq])
  have hRbound : R ≤ N := by dsimp [R,N]; exact_mod_cast card_filter_le V _
  have hUbound : U ≤ N := by dsimp [U,N]; exact_mod_cast card_filter_le V _
  have hνbound : ν ≤ N := by
    apply (div_le_iff₀ hN0).mpr
    exact mul_le_mul hUbound hRbound (by dsimp [R]; positivity) hN0.le
  have hnum : bg+ν+w ≤ 3*N := by linarith only [hbgN,hνbound,hwN,hN0]
  have hE0 : 0 ≤ E := by dsimp [E,ν,w,U,R]; positivity
  have hE : E ≤ errRatio*s0 := by
    calc
      _ ≤ Cpost*(3*N)/(v*q/4) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hnum hCpost.le
      _ = _ := by dsimp [errRatio,s0]; field_simp <;> ring
  have hnormalize := registered_shape_bound A K errRatio m s0 τ L (Real.sqrt N) E
    hA.le hK.le herrRatio.le hm hs0 hs1 hτ hτ1 hL (Real.sqrt_pos.mpr hN0) hE0 hE
  apply hraw.trans
  have hnorm :
      A/Real.sqrt N*(K*(m*s0)*(2*L*Real.sqrt N)+2*(2*τ+m*E)+1)*
        (2*(2*τ+m*E)/(m*s0)+1)+1/(2*L^2) ≤
      Cell*(L*(s0+τ)+(1+τ/s0)/Real.sqrt N+L^(-2 : ℤ)) := by
    apply hnormalize.trans
    apply mul_le_mul_of_nonneg_right _ hsum0
    dsimp [Cell]
    linarith only
  simpa only [A,E,w,m,ν,N,R,U,bg,s0,V,All,div_mul_eq_div_div] using hnorm

end
end D5.S3.Estimation.TimeArrow.NativeAnchoredSmallBall

open Filter
open scoped Topology BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceMass
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom
open D5.S3.Estimation.TimeArrow.NativeCalibrationRootBudgets
open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance

namespace D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy
noncomputable section
/-- An exact native cell indicator uses the finite relative law, so no
whole-population tail term is needed for a bounded count cell. -/
theorem native_cell_occupancy_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        ∀ (S : Support M q) (e : Experiment) (I : Finset (Fin M)) (c : ℕ × ℕ),
          (c.1 : ℝ) ≤ 8 * L → (c.2 : ℝ) ≤ 8 * L →
          ∀ m : ℝ, 0 < m →
          7 / 8 * m ≤ ∑ i ∈ I, rowReference S r L i c →
          (∑ i ∈ I, rowReference S r L i c) ≤ 9 / 8 * m →
          (∑ o : Obs M (2 * M * L) e,
            if ¬(3 / 4 * m ≤ ((I.filter fun i =>
                count e o i 1 = c.1 ∧ count e o i (-1) = c.2).card : ℝ) ∧
              ((I.filter fun i => count e o i 1 = c.1 ∧
                count e o i (-1) = c.2).card : ℝ) ≤ 5 / 4 * m)
            then probability r e S o else 0) ≤
              108 / m + 243 * (A * (L : ℝ) ^ 3 / M) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ :=
    native_truncated_weighted_moments κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I c hc1 hc2 m hm hlo hhi
  let a : ℝ := ∑ i ∈ I, rowReference S r L i c
  let Z := fun o : Obs M (2 * M * L) e =>
    ((I.filter fun i => count e o i 1 = c.1 ∧ count e o i (-1) = c.2).card : ℝ)
  have hZ (o : Obs M (2 * M * L) e) :
      (∑ i ∈ I, truncatedRow e {c} (fun _ _ => 1) i o) = Z o := by
    simp only [truncatedRow, sum_singleton]
    exact sum_boole _ _
  have hmoment := (h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall
    S e I {c} (fun _ _ => 1)
    (by simpa only [mem_singleton] using fun d (hd : d = c) => hd ▸ And.intro hc1 hc2)
    (by intros; norm_num)).2
  simp only [sum_singleton, one_mul, hZ] at hmoment
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have hcomp : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hcomp1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hp := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hcomp hcomp1 e).2.1.1 S
  have htail := finite_square_markov (probability r e S) Z a (m / 8)
    ((3 / 2) * a + 3 * (A * (L : ℝ) ^ 3 / M) * a ^ 2) hp (by positivity) hmoment
  have hcontain (o : Obs M (2 * M * L) e)
      (ho : ¬(3 / 4 * m ≤ Z o ∧ Z o ≤ 5 / 4 * m)) : m / 8 < |Z o - a| := by
    by_contra hn
    have hh := abs_le.mp (le_of_not_gt hn)
    apply ho
    dsimp only [a] at hh
    constructor <;> linarith only [hh.1, hh.2, hlo, hhi]
  have hnum : (3 / 2) * a + 3 * (A * (L : ℝ) ^ 3 / M) * a ^ 2 ≤
      (108 / m + 243 * (A * (L : ℝ) ^ 3 / M)) * (m / 8) ^ 2 := by
    have ha0 : 0 ≤ a := by dsimp only [a]; linarith only [hlo, hm]
    have hasq : a ^ 2 ≤ (9 / 8 * m) ^ 2 := by dsimp only [a]; nlinarith only [hhi, ha0, hm]
    have hδ : 0 ≤ A * (L : ℝ) ^ 3 / M := by positivity
    have hh := mul_le_mul_of_nonneg_left hasq (show 0 ≤ 3 * (A * (L : ℝ) ^ 3 / M) by positivity)
    have he : (108 / m + 243 * (A * (L : ℝ) ^ 3 / M)) * (m / 8) ^ 2 =
        (27 / 16) * m + (243 / 64) * (A * (L : ℝ) ^ 3 / M) * m ^ 2 := by
      field_simp
      <;> ring
    rw [he]
    dsimp only [a] at *
    nlinarith only [hh, hhi]
  apply le_trans _ (htail.trans ((div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < m / 8))).mpr hnum))
  apply sum_le_sum
  intro o _
  change (if ¬(3 / 4 * m ≤ Z o ∧ Z o ≤ 5 / 4 * m) then _ else _) ≤ _
  by_cases ho : 3 / 4 * m ≤ Z o ∧ Z o ≤ 5 / 4 * m
  · by_cases ht : m / 8 < |Z o - a| <;> simp [ho, ht, hp o]
  · simp [ho, hcontain o ho]
/-- The four signal cells and background A cell may share arbitrary native
dependence. Only their individual reference means are used in the union bound. -/
theorem native_five_cell_occupancy_budget (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        ∀ (S : Support M q) (e : Experiment) (I : Fin 5 → Finset (Fin M))
          (c : Fin 5 → ℕ × ℕ),
          (∀ j, ((c j).1 : ℝ) ≤ 8 * L ∧ ((c j).2 : ℝ) ≤ 8 * L) →
          ∀ m : ℝ, 0 < m →
          (∀ j, 7 / 8 * m ≤ ∑ i ∈ I j, rowReference S r L i (c j)) →
          (∀ j, (∑ i ∈ I j, rowReference S r L i (c j)) ≤ 9 / 8 * m) →
          (∑ o : Obs M (2 * M * L) e,
            if ¬∀ j, 3 / 4 * m ≤ (((I j).filter fun i =>
                count e o i 1 = (c j).1 ∧ count e o i (-1) = (c j).2).card : ℝ) ∧
              (((I j).filter fun i => count e o i 1 = (c j).1 ∧
                count e o i (-1) = (c j).2).card : ℝ) ≤ 5 / 4 * m
            then probability r e S o else 0) ≤
              540 / m + 1215 * (A * (L : ℝ) ^ 3 / M) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_cell_occupancy_budget κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I c hc m hm hlo hhi
  let Good := fun (o : Obs M (2 * M * L) e) (j : Fin 5) =>
    3 / 4 * m ≤ (((I j).filter fun i => count e o i 1 = (c j).1 ∧
      count e o i (-1) = (c j).2).card : ℝ) ∧
    (((I j).filter fun i => count e o i 1 = (c j).1 ∧
      count e o i (-1) = (c j).2).card : ℝ) ≤ 5 / 4 * m
  have hr1 : r < 1 := by linarith only [hrκ, hκ]
  have hcomp : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hcomp1 : compensation M q r < 1 := by linarith only [hcκ, hκ]
  have hp := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hcomp hcomp1 e).2.1.1 S
  calc
    _ ≤ ∑ o : Obs M (2 * M * L) e, ∑ j : Fin 5,
        if ¬Good o j then probability r e S o else 0 := by
      apply sum_le_sum
      intro o _
      change (if ¬∀ j, Good o j then _ else _) ≤ _
      by_cases ho : ∀ j, Good o j
      · simp [ho]
      · obtain ⟨j, hj⟩ := not_forall.mp ho
        simp only [ho, not_false_eq_true, if_true]
        have hh := single_le_sum
          (f := fun j : Fin 5 => if ¬Good o j then probability r e S o else 0)
          (fun k (_ : k ∈ (univ : Finset (Fin 5))) => by
            split_ifs <;> first | exact hp o | exact le_rfl) (mem_univ j)
        simpa only [hj, not_false_eq_true, if_true] using hh
    _ = ∑ j : Fin 5, ∑ o : Obs M (2 * M * L) e,
        if ¬Good o j then probability r e S o else 0 := sum_comm
    _ ≤ ∑ _j : Fin 5, (108 / m + 243 * (A * (L : ℝ) ^ 3 / M)) := by
      apply sum_le_sum
      intro j _
      exact h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e (I j) (c j)
        (hc j).1 (hc j).2 m hm (hlo j) (hhi j)
    _ = _ := by simp; ring
/-- Simultaneous occupancy is for the actual four signal cells and the
actual background A cell. Its reference comparison preserves the original
compensation and full population sizes. -/
theorem native_signal_background_occupancy (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val → ∀ k l : ℕ,
          k = ⌊((1+r)/2)*(L : ℝ)⌋₊ → l = L-k →
          15 ≤ ((1+r)/2)*(L : ℝ) → 30 ≤ ((1-r)/2)*(L : ℝ) →
          let dA := k * Real.log ((1+r)/(1-compensation M q r)) +
            l * Real.log ((1-r)/(1+compensation M q r)) -
            Real.log (((M-q : ℕ) : ℝ)/q)
          Real.log (7/8) ≤ -dA → -dA ≤ Real.log (9/8) →
          let m := (q : ℝ) * rowReference S r L i (k,l)
          let All : Support M M := ⟨univ, by simp⟩
          (∑ o : Obs M (2*M*L) e,
            if ¬((∀ a : Fin 4,
                3/4*m ≤ ((nativeCalibrationCells S e o k l a).card : ℝ) ∧
                ((nativeCalibrationCells S e o k l a).card : ℝ) ≤ 5/4*m) ∧
              3/4*m ≤ ((nativeCalibrationCells All e o k l 0 \ S.val).card : ℝ) ∧
              ((nativeCalibrationCells All e o k l 0 \ S.val).card : ℝ) ≤ 5/4*m)
            then probability r e S o else 0) ≤
              540/m + 1215*(A*(L : ℝ)^3/M) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_five_cell_occupancy_budget κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e i j hi hj k l hkfloor hlfloor hplus hminus
  have hr1 : r < 1 := by linarith only [hrκ,hκ]
  have hround := original_count_rounding r L hr hr1 hL hplus hminus
  dsimp only at hround
  rw [← hkfloor, ← hlfloor] at hround
  have hkL : (k : ℝ) ≤ L := by exact_mod_cast hround.1
  have hlL : (l : ℝ) ≤ L := by
    exact_mod_cast (show l ≤ L by rw [hlfloor]; omega)
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hk : (k+1 : ℝ) ≤ 8*L := by linarith only [hkL,hLR]
  have hl : (l+1 : ℝ) ≤ 8*L := by linarith only [hlL,hLR]
  dsimp only
  intro hdlo hdhi
  let m := (q : ℝ) * rowReference S r L i (k,l)
  let c : Fin 5 → ℕ × ℕ := ![(k,l),(k+1,l),(k,l+1),(k+1,l+1),(k,l)]
  let I : Fin 5 → Finset (Fin M) := ![S.val,S.val,S.val,S.val,univ \ S.val]
  have hm : 0 < m := mul_pos (by exact_mod_cast (show 0 < q by omega))
    (reference_pos S r κ hκ hr hrκ hcκ hL i (k,l))
  have hsig (a : Fin 4) : (∑ u ∈ S.val,
      rowReference S r L u (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a)) =
      (q : ℝ) * rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a) := by
    calc
      _ = ∑ _u ∈ S.val,
          rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a) :=
        sum_congr rfl fun u hu => by simp only [rowReference,b,if_pos hu,if_pos hi]
      _ = _ := by simp [S.property,nsmul_eq_mul]
  have hbg : (∑ u ∈ univ \ S.val, rowReference S r L u (k,l)) =
      ((M-q : ℕ) : ℝ) * rowReference S r L j (k,l) := by
    calc
      _ = ∑ _u ∈ univ \ S.val, rowReference S r L j (k,l) :=
        sum_congr rfl fun u hu => by
          simp only [rowReference,b,if_neg (mem_sdiff.mp hu).2,if_neg hj]
      _ = _ := by simp [card_sdiff_of_subset (subset_univ S.val),S.property,nsmul_eq_mul]
  have hs := floored_signal_four_reference_ratios S r κ hκ hr hrκ hcκ hL i hi hplus hminus
  dsimp only at hs
  rw [← hkfloor, ← hlfloor] at hs
  have hb := background_reference_cell_ratio S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj k l
  have hexlo := Real.exp_le_exp.mpr hdlo
  have hexhi := Real.exp_le_exp.mpr hdhi
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 7/8)] at hexlo
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 9/8)] at hexhi
  have hsm (a : Fin 4) :
      7/8*m ≤ ∑ u ∈ S.val, rowReference S r L u (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a) ∧
      (∑ u ∈ S.val, rowReference S r L u (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] a)) ≤ 9/8*m := by
    rw [hsig a]
    have hh := And.intro
      (mul_le_mul_of_nonneg_left (hs a).1 (by positivity : (0 : ℝ) ≤ q))
      (mul_le_mul_of_nonneg_left (hs a).2 (by positivity : (0 : ℝ) ≤ q))
    simpa [m, mul_assoc, mul_left_comm] using hh
  have hmean (a : Fin 5) : 7/8*m ≤ ∑ u ∈ I a, rowReference S r L u (c a) ∧
      (∑ u ∈ I a, rowReference S r L u (c a)) ≤ 9/8*m := by
    fin_cases a
    · exact hsm 0
    · exact hsm 1
    · exact hsm 2
    · exact hsm 3
    · change 7/8*m ≤ ∑ u ∈ univ \ S.val, rowReference S r L u (k,l) ∧
        (∑ u ∈ univ \ S.val, rowReference S r L u (k,l)) ≤ 9/8*m
      rw [hbg,hb]
      have hh := And.intro (mul_le_mul_of_nonneg_left hexlo hm.le)
        (mul_le_mul_of_nonneg_left hexhi hm.le)
      simpa only [m,mul_comm] using hh
  have he := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I c
    (by intro a; fin_cases a <;> simp [c] <;> constructor <;> linarith only [hk,hl])
    m hm (fun a => (hmean a).1) (fun a => (hmean a).2)
  convert he using 1
  apply sum_congr rfl
  intro o _
  congr 1
  have hcell (a : Fin 4) : nativeCalibrationCells S e o k l a =
      S.val.filter fun u => count e o u 1 = k + ![0,1,0,1] a ∧
        count e o u (-1) = l + ![0,0,1,1] a := by
    ext u
    simp [nativeCalibrationCells,native_row_cell_iff]
  have hback : nativeCalibrationCells (⟨univ, by simp⟩ : Support M M) e o k l 0 \ S.val =
      (univ \ S.val).filter fun u => count e o u 1 = k ∧ count e o u (-1) = l := by
    ext u
    simp [nativeCalibrationCells,native_row_cell_iff,and_assoc,and_left_comm,and_comm]
  simp_rw [hcell,hback]
  simp only [Fin.forall_fin_succ,Fin.forall_fin_zero,I,c,m,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one,Nat.add_zero,and_true]
  apply propext
  tauto
end
end D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy
open Filter
open scoped Topology BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
open D5.S3.Estimation.TimeArrow.NativeRectangleReferenceMass
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom
open D5.S3.Estimation.TimeArrow.NativeCalibrationRootBudgets
open D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
open D5.S3.Estimation.TimeArrow.NativeRectangleOccupancy

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
open scoped Classical in
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
    simpa only [c,m,k,l,div_div,mul_div_assoc,div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hh
  have hmu : m ≤ C*(q : ℝ)/L := by
    have hh := mul_le_mul_of_nonneg_left hm.2 (by positivity : (0 : ℝ) ≤ q)
    simpa only [C,m,k,l,div_div,mul_div_assoc,div_mul_eq_mul_div,mul_comm,mul_left_comm,mul_assoc] using hh
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
        hn.2.2.1 (by norm_num; exact hn.2.2.2.1)
        hn.2.2.2.2.1 (by norm_num; exact hn.2.2.2.2.2.1)
      dsimp only at he
      rw [he]
      exact hb
    have hgood : 3*c*q/L ≤ V.card ∧ (V.card : ℝ) ≤ 5*C*q/L ∧
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
              then probability r e S x else 0) ≤ K/Real.sqrt V.card) := by
      refine ⟨?_,?_,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2.1,
        hn.2.2.2.2.2.2,hatom⟩
      · simpa only [mul_div_assoc,mul_assoc,V] using hlo
      · simpa only [mul_div_assoc,mul_assoc,V] using hhi
    change (if ¬_ then _ else _) ≤ (if ¬_ then _ else _)
    simp only [k,l,c,C,V,R,U,m,nativeRectangleRows,nativeRectangleACount] at hgood hg ⊢
    simp only [hgood,hg,true_and,and_self,forall_const,not_true_eq_false,if_false]
    split_ifs with hbad
    · exact le_rfl
    · exfalso
      apply hbad
      intro t hN
      convert hatom t hN using 1 <;>
        try simp only [k,l,V,nativeRectangleRows,nativeRectangleACount]
      all_goals congr 3 <;> first | exact Subsingleton.elim _ _ | (ext y <;> simp)
  · have hp := (finite_support_bayes (s := 2*M*L) hq hqm hr
      (by linarith only [hrκ,hκ]) (by
        unfold compensation
        positivity) (by linarith only [hcκ,hκ]) e).2.2.1 S o
    change (if ¬_ then _ else _) ≤ (if ¬_ then _ else _)
    simp only [k,l,c,C,m,nativeRectangleRows,nativeRectangleACount] at hg ⊢
    simp only [hg,not_false_eq_true,if_true]
    split_ifs <;> first | exact le_rfl | exact hp.1.le
end
end D5.S3.Estimation.TimeArrow.NativeRectangleGeometry
