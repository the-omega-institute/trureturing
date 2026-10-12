/- GID: D5/S3/Estimation/TimeArrow/NativeOriginalSmallBall
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeOriginalSmallBall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original growth supplies shared-root arithmetic bounds on native environment values. -/

import D5.S3.Estimation.TimeArrow.NativeGrowthRounding
import D5.S3.Estimation.TimeArrow.NativeOriginalWindowSequence

open scoped BigOperators Topology
open Finset Filter
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeGrowthRounding
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.SharedRectangleCalibration
open D5.S3.Estimation.TimeArrow.NativeAnchoredSmallBall
open D5.S3.Estimation.TimeArrow.OriginalScoreWindow
open D5.S3.Estimation.TimeArrow.NativeOriginalWindowSequence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.NativeOriginalSmallBall
noncomputable section

/-- Complete calibration exists for every full observation, including empty rectangles. -/
private theorem complete_root {M q s : ℕ} (r : ℝ) (e : Experiment)
    (o : Obs M s e) (hq : 1 ≤ q) (hqm : q < M) :
    ∃ x : ℝ, (∑ i : Fin M, Real.sigmoid (x+score q r e o i-
      Real.log (((M-q : ℕ) : ℝ)/q))) = q := by
  obtain ⟨x,hx⟩ := exists_calibration_root
    (fun i : Fin M => score q r e o i-Real.log (((M-q : ℕ) : ℝ)/q))
    0 0 0 0 0 q 0 (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq))
    (by simpa using (show (q : ℝ) < M by exact_mod_cast hqm))
  refine ⟨x,?_⟩
  simpa [calibratedMean,cellCounts,Fin.sum_univ_four,add_sub_assoc] using hx

/-- The same returned feedback constants satisfy every scalar-engine size input
throughout the original rectangle comparison interval. -/
private theorem original_engine_scales (r β v a γ c η V0 cN CN : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hv : 0 < v) (ha : 0 < a) (hγ : 0 < γ) (hc : 0 < c)
    (hη : 0 < η) (hcN : 0 < cN) :
    ∀ᶠ n in atTop, ∀ N : ℕ,
      cN*(signalSize r β (scale n) : ℝ)/scale n ≤ N →
      (N : ℝ) ≤ CN*(signalSize r β (scale n) : ℝ)/scale n →
      1 < N ∧ max 4 (32/(a*v)) ≤ Real.sqrt N ∧
      (N : ℝ)/signalSize r β (scale n) ≤ v/2 ∧
      (N : ℝ)/signalSize r β (scale n) ≤ v*Real.log 2/8 ∧
      a*((N : ℝ)/signalSize r β (scale n)) < η ∧
      c*((N : ℝ)/signalSize r β (scale n)) ≤ 1 ∧
      V0 ≤ v*(signalSize r β (scale n) : ℝ)/4 ∧
      1 ≤ γ*(c*((N : ℝ)/signalSize r β (scale n)))*Real.sqrt N := by
  let δ := min (v/2) (min (v*Real.log 2/8) (min (η/(2*a)) (min (1/c) (γ*c))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδv : δ ≤ v/2 := min_le_left _ _
  have hδlog : δ ≤ v*Real.log 2/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hδa : δ ≤ η/(2*a) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδc : δ ≤ 1/c := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδγ : δ ≤ γ*c := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  filter_upwards [original_rectangle_feedback_scales r β cN CN δ
    (max 4 (32/(a*v))) hr hr1 hβ hβ1 hcN hδ,
    ((original_populations_tendsto r β hr hr1 hβ hβ1).1).eventually
      (eventually_ge_atTop (max 1 (4*V0/v)))] with n hn hq
  intro N hlo hhi
  obtain ⟨hlarge,hsize,hinv⟩ := hn N hlo hhi
  have hN0 : (0 : ℝ) < N := by
    have hh := (le_max_left 4 (32/(a*v))).trans hlarge
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hq0 : (0 : ℝ) < signalSize r β (scale n) :=
    (by norm_num : (0 : ℝ) < 1).trans_le ((le_max_left _ _).trans hq)
  have hN : 1 < N := by
    have hh := (le_max_left 4 (32/(a*v))).trans hlarge
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    have hh' : (1 : ℝ) < N := by nlinarith [Real.sqrt_nonneg (N : ℝ)]
    exact_mod_cast hh'
  refine ⟨hN,hlarge,hsize.trans hδv,hsize.trans hδlog,?_,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left (hsize.trans hδa) ha.le
    have he : a*(η/(2*a)) = η/2 := by field_simp <;> ring
    rw [he] at hh
    linarith only [hh,hη]
  · exact (mul_le_mul_of_nonneg_left (hsize.trans hδc) hc.le).trans_eq
      (by field_simp)
  · have hh := (div_le_iff₀ hv).mp ((le_max_right _ _).trans hq)
    nlinarith only [hh]
  · have hh := (div_le_iff₀ (mul_pos hN0 (Real.sqrt_pos.mpr hN0))).mp
      (hinv.trans hδγ)
    rw [show γ*(c*((N : ℝ)/signalSize r β (scale n)))*Real.sqrt N =
      (γ*c*((N : ℝ)*Real.sqrt N))/signalSize r β (scale n) by ring]
    apply (le_div_iff₀ hq0).mpr
    simpa only [one_mul] using hh


open scoped Classical in
set_option maxHeartbeats 4000000 in
/-- The original growth and floor sequence supplies the full native arithmetic
estimate on environment values with a uniform vanishing failure budget. The
conditional law is the original minimal readout, with no success flag added. -/
theorem original_native_environment_small_ball (r β : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hβ : 1/2 < β) (hβ1 : β < 1)
    (hα : Real.log (1+r)/(-Real.log (1-r)) = decimalAlpha) :
    ∃ cN CN c : ℝ, 0 < cN ∧ 0 < CN ∧ 0 < c ∧
    ∀ ell : ℤ, ell ≠ 0 → ∃ (Cell : ℝ) (budget : ℕ → ℝ), 0 < Cell ∧
      Tendsto budget atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      let lam := scale n
      let M := population r β lam
      let q := signalSize r β lam
      let k := centralPositive r lam
      let l := centralNegative r lam
      ∀ (S : Support M q) (e : Experiment),
      (∑ o : Obs M (2*M*lam) e,
        let N : ℝ := (nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card
        let s0 := c*(N/q)
        if ¬(cN*(q : ℝ)/lam ≤ N ∧ N ≤ CN*(q : ℝ)/lam ∧
            ∀ L τ : ℝ, 0 < L → 0 ≤ τ →
            (∑ y : Obs M (2*M*lam) e,
              if fullRectangleReadout S e k l y = fullRectangleReadout S e k l o ∧
                (∃ b : ℤ, |(ell : ℝ)*(1/2-
                  originalGroupPosteriorMean q r (Real.log ((M : ℝ)/q)) (Real.sqrt ((lam : ℝ)/q))
                    ((k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
                      l*Real.log ((1-r)/(1+compensation M q r))) e y)-b| ≤ τ)
              then probability r e S y else 0)/
              (∑ y : Obs M (2*M*lam) e,
                if fullRectangleReadout S e k l y = fullRectangleReadout S e k l o
                then probability r e S y else 0) ≤
              Cell*(L*(s0+τ)+(1+τ/s0)/Real.sqrt N+L^(-2 : ℤ)))
        then probability r e S o else 0) ≤ budget n := by
  classical
  have hβ0 : 0 < β := by linarith only [hβ]
  obtain ⟨cN,CN,bgBudget,hcN,hCN,hbgBudget,hgeometry⟩ :=
    original_rectangle_scale_budget r β hr hr1 hβ0 hβ1
  obtain ⟨vr,A,hvr,hA,hroots⟩ := original_complete_root_budget r β hr hr1 hβ hβ1
  let v := vr/4
  have hv : 0 < v := by dsimp [v]; positivity
  obtain ⟨Cpost,V0,hCpost,hV0,hsmall⟩ := original_full_env_small_ball
  obtain ⟨a,γ,η,c,Cfb,ha,hγ,hγsmall,hη,hc,hCfb,hsmall⟩ := hsmall r v hr hr1 hv
  let κ₀ := a*cN/4
  have hκ₀ : 0 < κ₀ := by dsimp [κ₀]; positivity
  obtain ⟨hrootBudget,hroots⟩ := hroots κ₀ hκ₀
  refine ⟨cN,CN,c,hcN,hCN,hc,?_⟩
  intro ell hell
  obtain ⟨Cell,hCell,hsmall⟩ := hsmall ell hell
  let budget := fun n => 16/15*(bgBudget n+rootFailureBudget r β vr κ₀ A n)
  have hbudget : Tendsto budget atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (hbgBudget.add hrootBudget).const_mul (16/15)
  refine ⟨Cell,budget,hCell,hbudget,?_⟩
  have hcomp := original_compensation_scales r β hr hr1 0
  simp only [pow_zero,one_mul] at hcomp
  filter_upwards [original_window_sequence_conditions r β hr hr1 hβ hβ1 hα,hgeometry,hroots,
    original_native_scale_conditions r β 1 1 1 hr hr1 hβ0 hβ1 (by norm_num),
    original_engine_scales r β v a γ c η V0 cN CN hr hr1 hβ0 hβ1 hv ha hγ hc hη hcN,
    hcomp.eventually (gt_mem_nhds (lt_min hη (by norm_num : (0 : ℝ) < 1/2))),
    scale_tendsto.eventually (eventually_ge_atTop 1)] with n hwindow hgeometry hroots hn hengine hcomp hlam
  dsimp only
  let lam := scale n
  let M := population r β lam
  let q := signalSize r β lam
  let k := centralPositive r lam
  let l := centralNegative r lam
  obtain ⟨_,hq,hqm,hlam4,_,_,_,_,_,_,_,_,_⟩ := hn
  have hε : 0 ≤ compensation M q r := by dsimp [M,q,compensation]; positivity
  have hεη : |compensation M q r| < η := by
    rw [abs_of_nonneg hε]
    exact hcomp.trans_le (min_le_left _ _)
  have hεhalf : compensation M q r ≤ 1/2 := (hcomp.trans_le (min_le_right _ _)).le
  have hε1 : compensation M q r < 1 := by
    have hh := hcomp.trans_le (min_le_right _ _)
    linarith only [hh]
  intro S e
  letI : Fintype (Sites (2*M*lam) e) := by cases e <;> unfold Sites <;> infer_instance
  have hx (o : Obs M (2*M*lam) e) := complete_root r e o hq hqm
  let x : Obs M (2*M*lam) e → ℝ := fun o => (hx o).choose
  have hxroot (o : Obs M (2*M*lam) e) := (hx o).choose_spec
  let D := fun o : Obs M (2*M*lam) e => ∑ i : Fin M,
    Real.sigmoid (x o+score q r e o i-Real.log (((M-q : ℕ) : ℝ)/q))*
      (1-Real.sigmoid (x o+score q r e o i-Real.log (((M-q : ℕ) : ℝ)/q)))
  let Geom := fun o : Obs M (2*M*lam) e =>
    let V := nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)
    let R := (V.filter fun i => count e o i.val 1 = k).card
    let U := (V.filter fun i => count e o i.val (-1) = l).card
    cN*(q : ℝ)/lam ≤ V.card ∧ (V.card : ℝ) ≤ CN*(q : ℝ)/lam ∧
      3/8*(V.card : ℝ) ≤ R ∧ (R : ℝ) ≤ 5/8*V.card ∧
      3/8*(V.card : ℝ) ≤ U ∧ (U : ℝ) ≤ 5/8*V.card ∧
      ((nativeCalibrationCells (⟨univ,by simp⟩ : Support M M) e o k l 0 \ S.val).card : ℝ)
        ≤ 5/12*V.card
  let Root := fun o : Obs M (2*M*lam) e =>
    |x o+cellLogit r β lam| ≤ κ₀/(lam : ℝ) ∧ v*(q : ℝ) ≤ D o ∧ D o ≤ q ∧
      ∀ i : Fin M, count e o i 1+count e o i (-1) ≤ 8*lam
  let G := fun o => Geom o ∧ Root o
  have hgeo : (∑ o : Obs M (2*M*lam) e,if ¬Geom o then probability r e S o else 0) ≤ bgBudget n := by
    simpa only [Geom,lam,M,q,k,l] using hgeometry S e
  have hroot : (∑ o : Obs M (2*M*lam) e,if ¬Root o then probability r e S o else 0) ≤
      rootFailureBudget r β vr κ₀ A n := by
    have hh := hroots S e x hxroot
    dsimp only at hh
    simpa only [Root,D,v,not_and_or,not_le,not_forall,div_mul_eq_mul_div,lam,M,q] using hh
  have hp := (finite_support_bayes (s := 2*M*lam) hq hqm hr hr1 hε hε1 e).2.1.1 S
  have hG : (∑ o : Obs M (2*M*lam) e,if ¬G o then probability r e S o else 0) ≤
      bgBudget n+rootFailureBudget r β vr κ₀ A n := by
    apply le_trans _ (add_le_add hgeo hroot)
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro o _
    by_cases hg : Geom o <;> by_cases hx : Root o <;>
      simp only [G,hg,hx,true_and,false_and,not_true_eq_false,not_false_eq_true,if_true,if_false] <;>
      linarith only [hp o]
  have hsize (o : Obs M (2*M*lam) e) (ho : G o) :
      1 < (nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card :=
    (hengine _ ho.1.1 ho.1.2.1).1
  have hanchors := full_native_environment_anchor_budget S r e hq hqm hr hr1 hε hε1 k l G hsize
  have hpay : (16/15)*(∑ y : Obs M (2*M*lam) e,
      if ¬G y then probability r e S y else 0) ≤
      (16/15)*(bgBudget n+rootFailureBudget r β vr κ₀ A n) :=
    mul_le_mul_of_nonneg_left hG (by norm_num)
  have hfinal : (∑ y : Obs M (2*M*lam) e,
      if ¬∃ z, fullRectangleReadout S e k l z = fullRectangleReadout S e k l y ∧ G z ∧
        (let V := nativeRectangleRows S e z k l (⟨z,rfl⟩ : Fiber S e z)
         let R := (V.filter fun i => count e z i.val 1 = k).card
         let U := (V.filter fun i => count e z i.val (-1) = l).card
         |(nativeRectangleACount S e z k l (⟨z,rfl⟩ : Fiber S e z) : ℝ)-(U : ℝ)*R/V.card| ≤
           2*Real.sqrt V.card)
      then probability r e S y else 0) ≤ budget n := by
    convert hanchors.trans (by
      convert hpay using 1 <;> first | rfl | (congr 1; apply sum_congr rfl; intro y _; split_ifs <;> rfl)) using 1
    all_goals first | rfl | (apply sum_congr rfl; intro y _; split_ifs <;> rfl)
  apply le_trans _ hfinal
  apply sum_le_sum
  intro o _
  dsimp only
  by_cases hz : ∃ z : Obs M (2*M*lam) e,
      fullRectangleReadout S e k l z = fullRectangleReadout S e k l o ∧ G z ∧
      let V := nativeRectangleRows S e z k l (⟨z,rfl⟩ : Fiber S e z)
      let R := (V.filter fun i => count e z i.val 1 = k).card
      let U := (V.filter fun i => count e z i.val (-1) = l).card
      |(nativeRectangleACount S e z k l (⟨z,rfl⟩ : Fiber S e z) : ℝ)-(U : ℝ)*R/V.card| ≤
        2*Real.sqrt V.card
  · obtain ⟨z,henv,hgz,hcentral⟩ := hz
    let V := nativeRectangleRows S e z k l (⟨z,rfl⟩ : Fiber S e z)
    let N : ℝ := V.card
    let R : ℝ := (V.filter fun i => count e z i.val 1 = k).card
    let U : ℝ := (V.filter fun i => count e z i.val (-1) = l).card
    let z0 := (k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
      l*Real.log ((1-r)/(1+compensation M q r))
    let xA := x z+cellLogit r β lam
    have hNcard : V.card = (nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card :=
      congrArg Finset.card (congrArg (fun u => u.2.1) henv)
    obtain ⟨hN,hlarge,hsize,hsize',hηscale,hs1,hV0,hfeedback⟩ :=
      hengine V.card hgz.1.1 hgz.1.2.1
    have hrootA : (∑ i : Fin M,Real.sigmoid (xA+(score q r e z i-z0))) = q := by
      convert hxroot z using 1
      apply sum_congr rfl
      intro i _
      congr 1
      dsimp only [xA,z0,cellLogit,k,l,M,q,lam]
      ring
    have hidentity (i : Fin M) : xA+(score q r e z i-z0) =
        x z+score q r e z i-Real.log (((M-q : ℕ) : ℝ)/q) := by
      dsimp only [xA,z0,cellLogit,k,l,M,q,lam]
      ring
    have hvarA : v*(q : ℝ) ≤ ∑ i : Fin M,Real.sigmoid (xA+(score q r e z i-z0))*
        (1-Real.sigmoid (xA+(score q r e z i-z0))) := by
      simp_rw [hidentity]
      exact hgz.2.2.1
    have hxA : |xA| ≤ a*N/(4*q) := by
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
      have hlam0 : (0 : ℝ) < lam := by exact_mod_cast (show 0 < lam by omega)
      apply hgz.2.1.trans
      dsimp only [κ₀,N]
      apply (le_div_iff₀ (by positivity : 0 < 4*(q : ℝ))).mpr
      have hh := (div_le_iff₀ hlam0).mp hgz.1.1
      change cN*(q : ℝ) ≤ (V.card : ℝ)*lam at hh
      field_simp
      nlinarith [hh]
    obtain ⟨hH,hPQ,hwidth,hζ,hlog,herror,hgrid⟩ := hwindow
    have hbound (L τ : ℝ) (hL : 0 < L) (hτ : 0 ≤ τ) :=
      hsmall M q (2*M*lam) S e z k l (8*lam) (denominator n) (decimalNumerator n)
        (Real.log ((M : ℝ)/q)) (Real.sqrt ((lam : ℝ)/q)) (decimalTail n) hq hqm hε hεhalf
        hN (by dsimp [N,R]; linarith only [hgz.1.2.2.1])
        (by dsimp [N,R]; linarith only [hgz.1.2.2.2.1])
        (by dsimp [N,U]; linarith only [hgz.1.2.2.2.2.1])
        (by dsimp [N,U]; linarith only [hgz.1.2.2.2.2.2.1])
        hlarge hsize hsize' (by simpa only [mul_div_assoc] using hηscale) hεη
        (by
          have hb : ((nativeCalibrationCells (⟨univ,by simp⟩ : Support M M) e z k l 0 \ S.val).card : ℝ) ≤
              5/12*(V.card : ℝ) := by convert hgz.1.2.2.2.2.2.2 using 1 <;> rfl
          exact hb.trans (by nlinarith [Nat.cast_nonneg V.card])) hs1 hV0 hfeedback
        hH hPQ hwidth hζ hlog herror hgrid
        (⟨z,rfl⟩ : Fiber S e z) xA rfl hgz.2.2.2.2 hrootA hvarA hxA hcentral L τ hL hτ
    have hgood : cN*(q : ℝ)/lam ≤ (nativeRectangleRows S e o k l
        (⟨o,rfl⟩ : Fiber S e o)).card ∧
        ((nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card : ℝ) ≤ CN*(q : ℝ)/lam ∧
        ∀ L τ : ℝ, 0 < L → 0 ≤ τ →
        (∑ y : Obs M (2*M*lam) e,
          if fullRectangleReadout S e k l y = fullRectangleReadout S e k l o ∧
            (∃ b : ℤ, |(ell : ℝ)*(1/2-originalGroupPosteriorMean q r (Real.log ((M : ℝ)/q)) (Real.sqrt ((lam : ℝ)/q))
                    ((k : ℝ)*Real.log ((1+r)/(1-compensation M q r))+
                      l*Real.log ((1-r)/(1+compensation M q r))) e y)-b| ≤ τ)
          then probability r e S y else 0)/
          (∑ y : Obs M (2*M*lam) e,
            if fullRectangleReadout S e k l y = fullRectangleReadout S e k l o
            then probability r e S y else 0) ≤
          Cell*(L*(c*((nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card/q)+τ)+
            (1+τ/(c*((nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card/q)))/
              Real.sqrt (nativeRectangleRows S e o k l (⟨o,rfl⟩ : Fiber S e o)).card+L^(-2 : ℤ)) := by
      refine ⟨by simpa only [←hNcard] using hgz.1.1,
        by simpa only [←hNcard] using hgz.1.2.1,?_⟩
      intro L τ hL hτ
      rw [←henv,←hNcard]
      convert hbound L τ hL hτ using 1 <;> first
        | rfl
        | (congr 2; apply sum_congr rfl; intro y _; split_ifs <;> rfl)
    split_ifs with hbad hbad' hbad'
    all_goals first
      | exact le_rfl
      | exact hp o
      | (exfalso; exact hbad hgood)

  · simp only [hz,not_false_eq_true,if_true]
    split_ifs <;> first | exact le_rfl | exact hp o

end
end D5.S3.Estimation.TimeArrow.NativeOriginalSmallBall
