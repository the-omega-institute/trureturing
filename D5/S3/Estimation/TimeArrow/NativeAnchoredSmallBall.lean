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

set_option maxHeartbeats 1000000 in
/-- A single actual full-root anchor proves the registered three-term
arithmetic estimate on every admissible central scale. All posterior,
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
      |compensation M q r| < η → bg ≤ N → s0 ≤ 1 → V0 ≤ v*q/4 →
      ∀ (anchor : Fiber S e o) (xStar : ℝ),
        nativeMinimalRectangleReadout S e o k l anchor = nativeMinimalRectangleReadout S e o k l z →
        (∑ i : Fin M,Real.sigmoid (xStar+(score q r e anchor.val i-z0))) = q →
        v*q ≤ ∑ i : Fin M,Real.sigmoid (xStar+(score q r e anchor.val i-z0))*
          (1-Real.sigmoid (xStar+(score q r e anchor.val i-z0))) →
        |xStar| ≤ a*N/(4*q) →
        |(nativeRectangleACount S e o k l anchor : ℝ)-U*R/N| ≤ 2*Real.sqrt N →
        ∀ L τ : ℝ, 0 < L → 0 ≤ τ → τ ≤ 1/2 →
          1 ≤ L*Real.sqrt N → L*Real.sqrt N ≤ γ*N →
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
  let Cell := 1+A*(8*K+2*K*m*(2*errRatio+1)+(3+2*m*errRatio)*(3+2*errRatio))
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
  intro hN hRlo hRhi hUlo hUhi hlarge hsize hsize' hηscale hεη hbgN hs1 hV
    anchor xStar henv hroot hvar hx hstar L τ hL hτ hτ1 hwide hcentral
  have hNnat : 0 < V.card := by
    change 1 < V.card at hN
    omega
  have hN0 : 0 < N := by dsimp [N]; exact_mod_cast hNnat
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hs0 : 0 < s0 := by dsimp [s0]; positivity
  have hbg : 0 ≤ bg := by dsimp [bg]; positivity
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
  simpa only [A,Cell,E,w,m,ν,N,R,U,bg,s0,V,All,div_mul_eq_div_div] using hnormalize

end
end D5.S3.Estimation.TimeArrow.NativeAnchoredSmallBall
