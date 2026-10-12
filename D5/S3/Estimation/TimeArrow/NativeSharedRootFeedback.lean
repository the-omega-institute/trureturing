/- GID: D5/S3/Estimation/TimeArrow/NativeSharedRootFeedback
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeSharedRootFeedback
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An actual complete-root anchor controls one central calibration curve and its positive compensated response. -/

import D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge

open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.RectangleCalibrationBounds
open D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
noncomputable section

set_option maxHeartbeats 800000 in
/-- Constants depend on the original amplitude alone. A single complete
anchor supplies the root and variance budgets for every central histogram;
the compensated derivative is then bounded by positive multiples of N/q. -/
theorem anchored_central_shared_calibration (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ d η : ℝ, 0 < d ∧ 0 < η ∧
    ∀ (ι : Type*) [Fintype ι] (outside : ι → ℝ),
    ∀ (ε N R U q bg ρ γ a v B tStar xStar : ℝ),
      0 < N → 0 < q → q < (Fintype.card ι : ℝ) + N →
      0 < ρ → 0 ≤ γ → γ ≤ ρ^2/2 → 0 < v → 0 ≤ bg → bg ≤ B*N →
      ρ*N ≤ R → R ≤ (1-ρ)*N → ρ*N ≤ U → U ≤ (1-ρ)*N →
      calibratedMean outside r ε N R U tStar xStar = q →
      v*q ≤ calibratedVariance outside r ε N R U tStar xStar →
      |tStar-U*R/N| ≤ 2*Real.sqrt N →
      γ*N+2*Real.sqrt N ≤ v*q/2 →
      2*(γ*N+2*Real.sqrt N) ≤ v*q/4*Real.log 2 →
      |xStar|+8*(γ*N+2*Real.sqrt N)/(v*q) ≤ a*N/q →
      a ≤ ρ^2*d/8 → a*N/q < η → |ε| < η →
      ∃ θ : ℝ → ℝ, ∀ t : ℝ, |t-U*R/N| ≤ γ*N →
        calibratedMean outside r ε N R U t (θ t) = q ∧
        |θ t| ≤ a*N/q ∧
        |θ t-xStar| ≤ 8*(γ*N+2*Real.sqrt N)/(v*q) ∧
        v*q/4 ≤ calibratedVariance outside r ε N R U t (θ t) ∧
        calibratedVariance outside r ε N R U t (θ t) ≤ q ∧
        HasDerivAt θ (-checkerboard r ε (θ t) /
          calibratedVariance outside r ε N R U t (θ t)) t ∧
        (∀ᶠ u in 𝓝 t, calibratedMean outside r ε N R U u (θ u) = q) ∧
        ∃ z : ℝ, (ρ^2*d/32)*(N/q) ≤ z ∧
          z ≤ (a/4+2*(B+1)/v)*(N/q) ∧
          HasDerivAt (fun u => (bg+u)*Real.sigmoid (θ u)-u/2) z t := by
  obtain ⟨d,η,hd,hη,hη2,hnegative⟩ := compensated_feedback_box hr hr1
  refine ⟨d,η,hd,hη,?_⟩
  intro ι _ outside ε N R U q bg ρ γ a v B tStar xStar
    hN hq hqM hρ hγ hγρ hv hbg hbgB hR hR' hU hU' hanchor hV
    hstar hw hsmall hprecision ha hηscale hε
  let w := γ*N+2*Real.sqrt N
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hcentral : γ*N ≤ ρ^2*N/2 := by nlinarith only [hγρ,hN]
  obtain ⟨θ,hθ⟩ := balanced_shared_curve outside r ε N R U q ρ (γ*N)
    hN hq hqM hρ hcentral hR hR' hU hU'
  refine ⟨θ,fun t ht => ?_⟩
  have hc0 := central_four_cells_lower N R U ρ t (γ*N) hN hρ.le hR hR' hU hU' ht
  have hc (j : Fin 4) : 0 ≤ cellCounts N R U t j := by
    have hh := hc0 j
    nlinarith only [hh,hcentral,sq_nonneg ρ,hN]
  have hdist : |t-tStar| ≤ w := by
    calc
      |t-tStar| = |(t-U*R/N)+(U*R/N-tStar)| := by congr 1; ring
      _ ≤ |t-U*R/N|+|U*R/N-tStar| := abs_add_le _ _
      _ ≤ w := by rw [abs_sub_comm (U*R/N) tStar]; exact add_le_add ht hstar
  have hgap : 0 < calibratedVariance outside r ε N R U tStar xStar-w := by
    have hvq := mul_pos hv hq
    dsimp only [w] at *
    linarith only [hw,hV,hvq]
  have hbudget : 2*w ≤
      (calibratedVariance outside r ε N R U tStar xStar-w)/2*Real.log 2 := by
    have hlog := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hh : v*q/4 ≤ (calibratedVariance outside r ε N R U tStar xStar-w)/2 := by
      linarith only [hw,hV]
    exact hsmall.trans (mul_le_mul_of_nonneg_right hh hlog)
  have he := hθ t ht
  have hb := shared_root_central_bootstrap outside r ε N R U q t tStar xStar (θ t) w
    hN hc hdist hanchor he.1 (by linarith only [hgap]) hbudget
  have hmove : |θ t-xStar| ≤ 8*w/(v*q) := by
    have hden : v*q/2 ≤ calibratedVariance outside r ε N R U tStar xStar-w := by
      linarith only [hw,hV]
    calc
      _ ≤ 4*w/(calibratedVariance outside r ε N R U tStar xStar-w) := hb.2.1
      _ ≤ 4*w/(v*q/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = 8*w/(v*q) := by ring
  have hx : |θ t| ≤ a*N/q := by
    calc
      |θ t| = |xStar+(θ t-xStar)| := by congr 1; ring
      _ ≤ |xStar|+|θ t-xStar| := abs_add_le _ _
      _ ≤ a*N/q := by linarith only [hmove,hprecision]
  have hlow : v*q/4 ≤ calibratedVariance outside r ε N R U t (θ t) := by
    linarith only [hb.2.2.1,hw,hV]
  have hhigh : calibratedVariance outside r ε N R U t (θ t) ≤ q := by
    rw [← he.1]
    unfold calibratedVariance calibratedMean
    apply add_le_add
    · apply sum_le_sum
      intro i _
      exact mul_le_of_le_one_right (Real.sigmoid_nonneg _)
        (by linarith only [Real.sigmoid_nonneg (θ t+outside i)])
    · apply sum_le_sum
      intro j _
      exact mul_le_of_le_one_right (mul_nonneg (hc j) (Real.sigmoid_nonneg _))
        (by linarith only [Real.sigmoid_nonneg (θ t+offsets r ε j)])
  have hB0 : 0 ≤ bg+t := by
    have hh := hc 0
    change 0 ≤ t at hh
    linarith only [hbg,hh]
  have htlo : ρ^2*N/2 ≤ t := by
    have hh := hc0 0
    change ρ^2*N-γ*N ≤ t at hh
    linarith only [hh,hcentral]
  have hthi : t ≤ N := by
    have hh := hc 1
    change 0 ≤ U-t at hh
    nlinarith only [hh,hU',hρ,hN]
  have hBlo : ρ^2*N/2 ≤ bg+t := by linarith only [htlo,hbg]
  have hBhi : bg+t ≤ (B+1)*N := by nlinarith only [hbgB,hthi]
  have hfeedback := compensated_feedback_bounds r ε (θ t) (bg+t)
    (calibratedVariance outside r ε N R U t (θ t)) d (v*q/4) q (a*N/q)
    (by positivity) hlow hhigh hB0 hd.le
    (hnegative ε (θ t) hε (hx.trans_lt hηscale)) hx
    (hx.trans (hηscale.le.trans hη2))
  let z := Real.sigmoid (θ t)-1/2-(bg+t)*Real.sigmoid (θ t)*
    (1-Real.sigmoid (θ t))*checkerboard r ε (θ t)/
      calibratedVariance outside r ε N R U t (θ t)
  have hzlo : (ρ^2*d/32)*(N/q) ≤ z := by
    have hh : ρ^2*N/2*d/(8*q) ≤ (bg+t)*d/(8*q) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBlo hd.le) (by positivity)
    have hh' : a*N/q/4 ≤ (ρ^2*d/8)*N/q/4 := by
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha hN.le) hq.le)
        (by norm_num)
    calc
      _ = ρ^2*N/2*d/(8*q)-(ρ^2*d/8)*N/q/4 := by field_simp; ring
      _ ≤ (bg+t)*d/(8*q)-a*N/q/4 := sub_le_sub hh hh'
      _ ≤ z := hfeedback.1
  have hzhi : z ≤ (a/4+2*(B+1)/v)*(N/q) := by
    have hh : (bg+t)/(2*(v*q/4)) ≤ ((B+1)*N)/(2*(v*q/4)) :=
      div_le_div_of_nonneg_right hBhi (by positivity)
    have heq : a*N/q/4+((B+1)*N)/(2*(v*q/4)) =
        (a/4+2*(B+1)/v)*(N/q) := by field_simp; ring
    dsimp only [z]
    linarith only [hfeedback.2,hh,heq]
  refine ⟨he.1,hx,hmove,hlow,hhigh,he.2.1,he.2.2.1,z,hzlo,hzhi,?_⟩
  exact compensated_group_deriv outside r ε N R U q bg t (θ t) _ θ
    he.2.1 rfl he.2.2.1 (ne_of_gt he.2.2.2)

set_option maxHeartbeats 800000 in
private theorem anchor_scale_budget (N q v a γ xStar : ℝ)
    (hN : 0 < N) (hq : 0 < q) (hv : 0 < v) (ha : 0 < a)
    (hγ1 : γ ≤ 1/2) (hγa : γ ≤ a*v/32)
    (hlarge : max 4 (32/(a*v)) ≤ Real.sqrt N)
    (hsize : N/q ≤ v/2) (hsize' : N/q ≤ v*Real.log 2/8)
    (hx : |xStar| ≤ a*N/(4*q)) :
    γ*N+2*Real.sqrt N ≤ v*q/2 ∧
      2*(γ*N+2*Real.sqrt N) ≤ v*q/4*Real.log 2 ∧
      |xStar|+8*(γ*N+2*Real.sqrt N)/(v*q) ≤ a*N/q := by
  have hs := Real.sq_sqrt hN.le
  have hs0 := Real.sqrt_nonneg N
  have hs4 : 4 ≤ Real.sqrt N := (le_max_left _ _).trans hlarge
  have hsav : 32/(a*v) ≤ Real.sqrt N := (le_max_right _ _).trans hlarge
  have hw : γ*N+2*Real.sqrt N ≤ N := by nlinarith only [hs,hs4,hγ1,hN]
  have hqsize := (div_le_iff₀ hq).mp hsize
  have hqsize' := (div_le_iff₀ hq).mp hsize'
  have hroot : 8*(γ*N+2*Real.sqrt N)/(v*q) ≤ 3*a*N/(4*q) := by
    apply (div_le_div_iff₀ (mul_pos hv hq) (by positivity : (0 : ℝ) < 4*q)).mpr
    have hg := mul_le_mul_of_nonneg_right hγa hN.le
    have hs' := (div_le_iff₀ (mul_pos ha hv)).mp hsav
    have hs'' := mul_le_mul_of_nonneg_right hs' hs0
    have hsbound : 32*Real.sqrt N ≤ N*a*v := by
      calc
        _ ≤ Real.sqrt N*a*v*Real.sqrt N := by simpa only [mul_assoc] using hs''
        _ = N*a*v := by
          rw [show Real.sqrt N*a*v*Real.sqrt N = (Real.sqrt N)^2*a*v by ring,hs]
    have hh : 8*(γ*N+2*Real.sqrt N) ≤ 3*a*N*v/4 := by
      nlinarith only [hg,hsbound]
    have hh' := mul_le_mul_of_nonneg_right hh hq.le
    nlinarith only [hh']
  refine ⟨?_,?_,?_⟩
  · linarith only [hw,hqsize]
  · linarith only [hw,hqsize']
  · have he : a*N/(4*q)+3*a*N/(4*q) = a*N/q := by field_simp; ring
    linarith only [hx,hroot,he]

set_option maxHeartbeats 800000 in
/-- The native outside function and anchor are taken from one actual
collapsed fiber. The same full calibration curve is used at every real
central histogram, in either experiment; no posterior is reconditioned. -/
theorem native_anchored_central_feedback (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (v : ℝ) (hv : 0 < v) :
    ∃ a γ η c C : ℝ, 0 < a ∧ 0 < γ ∧ 0 < η ∧ 0 < c ∧ 0 < C ∧
    ∀ (M q s : ℕ) (S : Support M q) (e : Experiment) (o : Obs M s e),
    ∀ [Fintype (Sites s e)], ∀ (k l : ℕ) (z : Fiber S e o),
      1 ≤ q → q < M → 0 ≤ compensation M q r → compensation M q r < 1 →
      let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
        (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
      let V := nativeRectangleRows S e o k l z
      let N : ℝ := V.card
      let R : ℝ := (V.filter fun i => count e z.val i.val 1 = k).card
      let U : ℝ := (V.filter fun i => count e z.val i.val (-1) = l).card
      let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
        fun i => score q r e z.val i.val-z0
      0 < N → N/4 ≤ R → R ≤ 3*N/4 → N/4 ≤ U → U ≤ 3*N/4 →
      max 4 (32/(a*v)) ≤ Real.sqrt N →
      N/q ≤ v/2 → N/q ≤ v*Real.log 2/8 → a*N/q < η →
      |compensation M q r| < η →
      ∀ bg : ℝ, 0 ≤ bg → bg ≤ N →
      ∀ (anchor : Fiber S e o) (xStar : ℝ),
        nativeMinimalRectangleReadout S e o k l anchor =
          nativeMinimalRectangleReadout S e o k l z →
        (∑ i : Fin M, Real.sigmoid (xStar+(score q r e anchor.val i-z0))) = q →
        v*q ≤ ∑ i : Fin M, Real.sigmoid (xStar+(score q r e anchor.val i-z0))*
          (1-Real.sigmoid (xStar+(score q r e anchor.val i-z0))) →
        |xStar| ≤ a*N/(4*q) →
        |(nativeRectangleACount S e o k l anchor : ℝ)-U*R/N| ≤ 2*Real.sqrt N →
        ∃ θ : ℝ → ℝ, (∀ t : ℝ, |t-U*R/N| ≤ γ*N →
          calibratedMean outside r (compensation M q r) N R U t (θ t) = q ∧
          |θ t| ≤ a*N/q ∧
          v*q/4 ≤ calibratedVariance outside r (compensation M q r) N R U t (θ t) ∧
          calibratedVariance outside r (compensation M q r) N R U t (θ t) ≤ q ∧
          HasDerivAt θ (-checkerboard r (compensation M q r) (θ t)/
            calibratedVariance outside r (compensation M q r) N R U t (θ t)) t ∧
          (∀ᶠ u in 𝓝 t, calibratedMean outside r (compensation M q r) N R U u (θ u) = q) ∧
          ∃ slope : ℝ, c*(N/q) ≤ slope ∧ slope ≤ C*(N/q) ∧
            HasDerivAt (fun u => (bg+u)*Real.sigmoid (θ u)-u/2) slope t) ∧
          ∀ y : Fiber S e o,
            nativeMinimalRectangleReadout S e o k l y =
              nativeMinimalRectangleReadout S e o k l z →
            |(nativeRectangleACount S e o k l y : ℝ)-U*R/N| ≤ γ*N →
            let x := θ (nativeRectangleACount S e o k l y)
            (∑ i : Fin M, Real.sigmoid (x+(score q r e y.val i-z0))) = q ∧
            v*q/4 ≤ ∑ i : Fin M, Real.sigmoid (x+(score q r e y.val i-z0))*
              (1-Real.sigmoid (x+(score q r e y.val i-z0))) ∧
            (∑ i : Fin M, Real.sigmoid (x+(score q r e y.val i-z0))*
              (1-Real.sigmoid (x+(score q r e y.val i-z0)))) ≤ q ∧
            ∀ u : ℝ, (∑ i : Fin M, Real.sigmoid (u+(score q r e y.val i-z0))) = q → u = x := by
  obtain ⟨d,η,hd,hη,hcal⟩ := anchored_central_shared_calibration r hr hr1
  let a := min 1 (d/128)
  let γ := min (1/64) (a*v/32)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hγ : 0 < γ := lt_min (by norm_num) (by positivity)
  refine ⟨a,γ,η,d/512,a/4+4/v,ha,hγ,hη,by positivity,by positivity,?_⟩
  intro M q s S e o _ k l z hq hqm he he1
  dsimp only
  intro hN hR hR' hU hU' hlarge hsize hsize' hηscale hε bg hbg hbgN
    anchor xStar henv hroot hvar hprecision hstar
  let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
    (l : ℝ)*Real.log ((1-r)/(1+compensation M q r))
  let V := nativeRectangleRows S e o k l z
  let N : ℝ := V.card
  let R : ℝ := (V.filter fun i => count e z.val i.val 1 = k).card
  let U : ℝ := (V.filter fun i => count e z.val i.val (-1) = l).card
  let outside : {i : Fin M // nativeRowCell S e z.val k l i = none} → ℝ :=
    fun i => score q r e z.val i.val-z0
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hi := native_environment_mean_variance S r e o k l anchor z henv hq hqm hr hr1 he he1 xStar
  dsimp only at hi
  have hanchor : calibratedMean outside r (compensation M q r) N R U
      (nativeRectangleACount S e o k l anchor) xStar = q := by
    rw [←hi.1]
    exact hroot
  have hV : v*q ≤ calibratedVariance outside r (compensation M q r) N R U
      (nativeRectangleACount S e o k l anchor) xStar := by
    rw [←hi.2]
    exact hvar
  have hpartition := native_outside_rectangle_card S e o k l z
  have hqM : (q : ℝ) <
      (Fintype.card {i : Fin M // nativeRowCell S e z.val k l i = none} : ℝ)+N := by
    have hh : q < Fintype.card {i : Fin M // nativeRowCell S e z.val k l i = none}+V.card := by
      rwa [hpartition]
    dsimp only [N]
    exact_mod_cast hh
  have hb := anchor_scale_budget N q v a γ xStar hN hqR hv ha
    ((min_le_left _ _).trans (by norm_num)) (min_le_right _ _) hlarge hsize hsize' hprecision
  obtain ⟨θ,hθ⟩ := hcal _ outside (compensation M q r) N R U q bg (1/4) γ a v 1
    (nativeRectangleACount S e o k l anchor) xStar hN hqR hqM (by norm_num)
    hγ.le (by have hh := min_le_left (1/64 : ℝ) (a*v/32); dsimp only [γ]; linarith only [hh])
    hv hbg (by simpa using hbgN)
    (by linarith only [hR]) (by linarith only [hR'])
    (by linarith only [hU]) (by linarith only [hU']) hanchor hV hstar
    hb.1 hb.2.1 hb.2.2 (by have hh := min_le_right (1 : ℝ) (d/128); dsimp only [a]; linarith only [hh])
    hηscale hε
  refine ⟨θ,?_,?_⟩
  · intro t ht
    have ht' := hθ t ht
    rcases ht'.2.2.2.2.2.2.2 with ⟨slope,hlo,hhi,hder⟩
    refine ⟨ht'.1,ht'.2.1,ht'.2.2.2.1,ht'.2.2.2.2.1,ht'.2.2.2.2.2.1,
      ht'.2.2.2.2.2.2.1,slope,?_,?_,hder⟩
    · convert hlo using 1 <;> ring
    · convert hhi using 1 <;> ring
  · intro y hy ht
    have hi := native_environment_mean_variance S r e o k l y z hy hq hqm hr hr1 he he1
      (θ (nativeRectangleACount S e o k l y))
    dsimp only at hi
    have ht' := hθ (nativeRectangleACount S e o k l y) ht
    refine ⟨hi.1.trans ht'.1,?_,?_,?_⟩
    · rw [hi.2]
      exact ht'.2.2.2.1
    · rw [hi.2]
      exact ht'.2.2.2.2.1
    · intro u hu
      have hiu := native_environment_mean_variance S r e o k l y z hy hq hqm hr hr1 he he1 u
      dsimp only at hiu
      have hc (j : Fin 4) : 0 ≤ cellCounts N R U (nativeRectangleACount S e o k l y) j := by
        have hh := central_four_cells_lower N R U (1/4) (nativeRectangleACount S e o k l y)
          (γ*N) hN (by norm_num) (by linarith only [hR]) (by linarith only [hR'])
          (by linarith only [hU]) (by linarith only [hU']) ht j
        have hg : γ ≤ 1/64 := min_le_left _ _
        nlinarith only [hh,hg,hN]
      exact (unique_shared_root outside r (compensation M q r) N R U q
        (nativeRectangleACount S e o k l y) hN hqR hqM hc).unique
          (hiu.1.symm.trans hu) ht'.1

end
end D5.S3.Estimation.TimeArrow.NativeSharedRootFeedback
