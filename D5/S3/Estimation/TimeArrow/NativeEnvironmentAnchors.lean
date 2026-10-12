/- GID: D5/S3/Estimation/TimeArrow/NativeEnvironmentAnchors
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeEnvironmentAnchors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Central anchors select native environment values without conditioning on a good event. -/

import D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Estimation.TimeArrow.NativeEnvironmentAnchors
noncomputable section

open scoped Classical in
theorem finite_environment_anchor_budget {Ω E : Type*} [Fintype Ω] [DecidableEq E]
    (env : Ω → E) (p : Ω → ℝ) (G C : Ω → Prop) [DecidablePred G] [DecidablePred C]
    (hp : ∀ o, 0 ≤ p o)
    (htail : ∀ z, G z →
      (∑ y : Ω, if env y = env z ∧ ¬C y then p y else 0) ≤
        1/16 * ∑ y : Ω, if env y = env z then p y else 0) :
    (∑ y : Ω, if ¬∃ z, env z = env y ∧ G z ∧ C z then p y else 0) ≤
      16/15 * ∑ y : Ω, if ¬G y then p y else 0 := by
  classical
  let A := fun η : E => ∃ z, env z = η ∧ G z ∧ C z
  let F := (univ : Finset Ω).image env
  have hη (η : E) :
      (∑ y ∈ univ.filter (fun y => env y = η), if ¬A η then p y else 0) ≤
      16/15 * ∑ y ∈ univ.filter (fun y => env y = η), if ¬G y then p y else 0 := by
    let T := univ.filter fun y => env y = η
    have hbad0 : 0 ≤ ∑ y ∈ T, if ¬G y then p y else 0 :=
      sum_nonneg fun y _ => by split_ifs <;> first | exact hp y | positivity
    by_cases hA : A η
    · simp only [hA, not_true_eq_false, if_false, sum_const_zero]
      exact mul_nonneg (by norm_num) hbad0
    · by_cases hG : ∃ z, env z = η ∧ G z
      · obtain ⟨z,hz,hGz⟩ := hG
        have ht := htail z hGz
        rw [hz] at ht
        have hgoodtail : (∑ y ∈ T, if G y then p y else 0) ≤
            ∑ y : Ω, if env y = η ∧ ¬C y then p y else 0 := by
          rw [sum_filter]
          apply sum_le_sum
          intro y _
          by_cases he : env y = η <;> by_cases hg : G y
          · have hc : ¬C y := fun hy => hA ⟨y,he,hg,hy⟩
            simp [he,hg,hc]
          · by_cases hc : C y <;> simp [he,hg,hc,hp y]
          · simp [he,hg]
          · simp [he,hg]
        have hpart : (∑ y ∈ T, if G y then p y else 0) +
            (∑ y ∈ T, if ¬G y then p y else 0) = ∑ y ∈ T, p y := by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro y _
          by_cases hg : G y <;> simp [hg]
        have htot : (∑ y : Ω, if env y = η then p y else 0) = ∑ y ∈ T, p y :=
          (sum_filter _ _).symm
        rw [htot] at ht
        simp only [hA, not_false_eq_true, if_true]
        dsimp only [T] at hpart hgoodtail ht
        linarith only [hpart, hgoodtail, ht]
      · have hn (y : Ω) (hy : y ∈ T) : ¬G y := by
          intro hg
          exact hG ⟨y,(mem_filter.mp hy).2,hg⟩
        simp only [hA, not_false_eq_true, if_true]
        have he : (∑ y ∈ T, if ¬G y then p y else 0) = ∑ y ∈ T, p y :=
          sum_congr rfl fun y hy => if_pos (hn y hy)
        change (∑ y ∈ T, p y) ≤ 16/15 * ∑ y ∈ T, if ¬G y then p y else 0
        rw [he]
        have hh := sum_nonneg (s := T) fun y _ => hp y
        linarith only [hh]
  calc
    _ = ∑ η ∈ F, ∑ y ∈ univ.filter (fun y => env y = η), if ¬A η then p y else 0 := by
      rw [← sum_fiberwise_of_maps_to (fun y (_ : y ∈ (univ : Finset Ω)) =>
        mem_image_of_mem env (mem_univ y)) (fun y => if ¬A (env y) then p y else 0)]
      apply sum_congr rfl
      intro η _
      apply sum_congr rfl
      intro y hy
      rw [(mem_filter.mp hy).2]
    _ ≤ ∑ η ∈ F, 16/15 * ∑ y ∈ univ.filter (fun y => env y = η), if ¬G y then p y else 0 :=
      sum_le_sum fun η _ => hη η
    _ = _ := by
      rw [← mul_sum, sum_fiberwise_of_maps_to (fun y (_ : y ∈ (univ : Finset Ω)) =>
        mem_image_of_mem env (mem_univ y))]

/-- The central native tail in unnormalized original probability weights. -/
theorem native_minimal_central_mass_tail {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)]
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (k l : ℕ) (z : Fiber S e o)
    (hsize : 1 < (nativeRectangleRows S e o k l z).card) :
    letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
    let env := nativeMinimalRectangleReadout S e o k l
    let C := fun y : Fiber S e o =>
      let V := nativeRectangleRows S e o k l y
      let R := (V.filter fun i => count e y.val i.val 1 = k).card
      let U := (V.filter fun i => count e y.val i.val (-1) = l).card
      |(nativeRectangleACount S e o k l y : ℝ) - (U : ℝ)*R/V.card| ≤
        2*Real.sqrt V.card
    (∑ y : Fiber S e o, if env y = env z ∧ ¬C y then probability r e S y.val else 0) ≤
      1/16 * ∑ y : Fiber S e o, if env y = env z then probability r e S y.val else 0 := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  letI : Nonempty (Fiber S e o) := ⟨⟨o,rfl⟩⟩
  dsimp only
  let env := nativeMinimalRectangleReadout S e o k l
  let C := fun y : Fiber S e o =>
    let V := nativeRectangleRows S e o k l y
    let R := (V.filter fun i => count e y.val i.val 1 = k).card
    let U := (V.filter fun i => count e y.val i.val (-1) = l).card
    |(nativeRectangleACount S e o k l y : ℝ) - (U : ℝ)*R/V.card| ≤ 2*Real.sqrt V.card
  let p := fun y : Fiber S e o => probability r e S y.val
  have hprob := (finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.1 S
  have hp : ∀ y, 0 ≤ p y := fun y => (hprob y.val).1.le
  have htotal : 0 < ∑ y : Fiber S e o, p y :=
    sum_pos (fun y _ => (hprob y.val).1) univ_nonempty
  let V := nativeRectangleRows S e o k l z
  let R := (V.filter fun i => count e z.val i.val 1 = k).card
  let U := (V.filter fun i => count e z.val i.val (-1) = l).card
  let Env := univ.filter fun y : Fiber S e o => env y = env z
  have henvpos : 0 < ∑ y ∈ Env, p y := by
    apply (hprob z.val).1.trans_le
    exact single_le_sum (fun y _ => hp y) (by simp [Env])
  have hc (y : Fiber S e o) (hy : y ∈ Env) :
      ¬C y ↔ 2*Real.sqrt V.card <
        |(nativeRectangleACount S e o k l y : ℝ) - (U : ℝ)*R/V.card| := by
    have he := (native_minimal_readout_eq_iff S e o k l y z).mp (mem_filter.mp hy).2
    have hV := congrArg (fun v => v.1.card) he
    have hR := congrArg (fun v => v.2.2.1) he
    have hU := congrArg (fun v => v.2.2.2) he
    change (nativeRectangleRows S e o k l y).card = V.card at hV
    change ((nativeRectangleRows S e o k l y).filter fun i => count e y.val i.val 1 = k).card = R at hR
    change ((nativeRectangleRows S e o k l y).filter fun i => count e y.val i.val (-1) = l).card = U at hU
    simp only [C,hV,hR,hU,not_le]
  have ht := (native_minimal_central_tail S r e o hq hqm hr hr1 ha ha1 k l z
    2 (by norm_num) hsize).1
  have hevent : (univ.filter fun y : Fiber S e o => env y = env z ∧ ¬C y) =
      Env.filter fun y => 2*Real.sqrt V.card <
        |(nativeRectangleACount S e o k l y : ℝ) - (U : ℝ)*R/V.card| := by
    ext y
    simp only [Env,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨he,hy⟩
      exact ⟨he,(hc y (by simp [Env,he])).mp hy⟩
    · rintro ⟨he,hy⟩
      exact ⟨he,(hc y (by simp [Env,he])).mpr hy⟩
  change conditionalFiberMass S r e o
      (Env.filter fun y => 2*Real.sqrt V.card <
        |(nativeRectangleACount S e o k l y : ℝ) - (U : ℝ)*R/V.card|) /
      conditionalFiberMass S r e o Env ≤ 1/(4*(2:ℝ)^2) at ht
  simp only [conditionalFiberMass] at ht
  rw [div_div_div_cancel_right₀ (by
    convert htotal.ne' using 1
    congr 1
    ext y
    simp [p])] at ht
  norm_num only at ht
  have hh := (div_le_iff₀ (by simpa only [p] using henvpos)).mp ht
  rw [← sum_filter, hevent, ← sum_filter]
  simpa only [p,mul_comm] using hh


end
end D5.S3.Estimation.TimeArrow.NativeEnvironmentAnchors
