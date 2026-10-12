/- GID: D5/S3/Estimation/TimeArrow/NativeEnvironmentAnchors
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeEnvironmentAnchors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Central anchors select native environment values without conditioning on a good event. -/

import D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
import D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
import D5.S3.Estimation.TimeArrow.SharedRectangleCalibration

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

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.RectangleHypergeometricKernel
open D5.S3.Estimation.TimeArrow.NativeRectangleEnvironment
open D5.S3.Estimation.TimeArrow.NativeEnvironmentAnchors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment
noncomputable section

/-- The original complete observation determines its collapsed history,
rectangle membership, and complete outside signal-row counts. -/
def fullRectangleReadout {M q s : ℕ} (S : Support M q) (e : Experiment)
    (k l : ℕ) (o : Obs M s e) :
    (Sites s e → Option (Vertex M)) ×
      (Finset {i : Fin M // i ∈ S.val} × ({i : Fin M // i ∈ S.val} → Option (ℕ × ℕ))) :=
  (collapsedObs S e o,
    nativeMinimalRectangleReadout S e o k l (⟨o,rfl⟩ : Fiber S e o))

/-- The full native sigma-algebra contains no extra good-event flag. -/
def fullRectangleSigma {M q s : ℕ} (S : Support M q) (e : Experiment)
    (k l : ℕ) : MeasurableSpace (Obs M s e) :=
  MeasurableSpace.comap (fullRectangleReadout S e k l) ⊤

open scoped Classical in
private theorem full_environment_sum {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (k l : ℕ) (o : Obs M s e) (P : Obs M s e → Prop) :
    letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
    (∑ x : Obs M s e, if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧ P x
      then probability r e S x else 0) =
    ∑ y : Fiber S e o,
      if nativeMinimalRectangleReadout S e o k l y =
        nativeMinimalRectangleReadout S e o k l (⟨o,rfl⟩ : Fiber S e o) ∧ P y.val
      then probability r e S y.val else 0 := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  let f := fun x : Obs M s e =>
    if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧ P x
    then probability r e S x else 0
  have hcollapse (x : Obs M s e) : fullRectangleReadout S e k l x =
      fullRectangleReadout S e k l o → collapsedObs S e x = collapsedObs S e o :=
    fun h => congrArg Prod.fst h
  calc
    _ = ∑ x ∈ univ.filter (fun x => collapsedObs S e x = collapsedObs S e o), f x := by
      rw [sum_filter]
      apply sum_congr rfl
      intro x _
      by_cases hc : collapsedObs S e x = collapsedObs S e o
      · simp [f,hc]
      · have hh : fullRectangleReadout S e k l x ≠ fullRectangleReadout S e k l o :=
          fun h => hc (hcollapse x h)
        simp [f,hc,hh]
    _ = ∑ y : Fiber S e o, f y.val :=
      sum_subtype _ (by intro x; simp) f
    _ = _ := by
      apply sum_congr rfl
      intro y _
      have he : fullRectangleReadout S e k l y.val = fullRectangleReadout S e k l o ↔
          nativeMinimalRectangleReadout S e o k l y =
            nativeMinimalRectangleReadout S e o k l (⟨o,rfl⟩ : Fiber S e o) := by
        simp only [fullRectangleReadout, Prod.mk.injEq]
        change (collapsedObs S e y.val = collapsedObs S e o ∧ _) ↔ _
        simp only [y.property,true_and]
        rfl
      simp only [f,he]

/-- Conditioning the original pair or path law on the full minimal
environment gives the same hypergeometric kernel, with its support guard. -/
theorem full_native_four_cell_conditional_law {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) (o : Obs M s e) [Fintype (Sites s e)]
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (k l t : ℕ) :
    let z : Fiber S e o := ⟨o,rfl⟩
    let V := nativeRectangleRows S e o k l z
    let R := (V.filter fun i => count e o i.val 1 = k).card
    let U := (V.filter fun i => count e o i.val (-1) = l).card
    (∑ x : Obs M s e,
        if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧
          nativeRectangleACount S e x k l (⟨x,rfl⟩ : Fiber S e x) = t
        then probability r e S x else 0) /
      (∑ x : Obs M s e, if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o
        then probability r e S x else 0) =
      if t ≤ U then ((R.choose t : ℝ)*((V.card-R).choose (U-t) : ℝ))/(V.card.choose U : ℝ)
      else 0 := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  letI : Nonempty (Fiber S e o) := ⟨⟨o,rfl⟩⟩
  dsimp only
  let z : Fiber S e o := ⟨o,rfl⟩
  have ht := native_minimal_four_cell_law S r e o hq hqm hr hr1 ha ha1 k l z t
  have hprob := (finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.1 S
  have htotal : 0 < ∑ y : Fiber S e o, probability r e S y.val :=
    sum_pos (fun y _ => (hprob y.val).1) univ_nonempty
  simp only [conditionalFiberMass] at ht
  rw [div_div_div_cancel_right₀ (by
    convert htotal.ne' using 1
    congr 1
    ext y
    simp)] at ht
  rw [sum_filter,sum_filter] at ht
  have hn := full_environment_sum S r e k l o (fun x =>
    nativeRectangleACount S e x k l (⟨x,rfl⟩ : Fiber S e x) = t)
  simp only [nativeRectangleACount] at hn ⊢
  rw [hn]
  have hd := full_environment_sum S r e k l o (fun _ => True)
  simp only [and_true] at hd
  simp only [Fiber] at hd
  rw [hd]
  simp only [nativeRectangleACount] at ht
  convert ht using 1 <;> simp only [sum_filter,ite_and,z]
  congr 3 <;> first | exact Subsingleton.elim _ _ | (ext y <;> simp)

open scoped Classical in
/-- Good anchors select values of the full minimal environment directly
under the original experiment. No additional good-event conditioning or
fixed tail loss is introduced. -/
theorem full_native_environment_anchor_budget {M q s : ℕ} (S : Support M q)
    (r : ℝ) (e : Experiment) [Fintype (Sites s e)]
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 ≤ compensation M q r) (ha1 : compensation M q r < 1)
    (k l : ℕ) (G : Obs M s e → Prop)
    (hsize : ∀ z, G z →
      1 < (nativeRectangleRows S e z k l (⟨z,rfl⟩ : Fiber S e z)).card) :
    let env := fullRectangleReadout (s := s) S e k l
    let C := fun y : Obs M s e =>
      let V := nativeRectangleRows S e y k l (⟨y,rfl⟩ : Fiber S e y)
      let R := (V.filter fun i => count e y i.val 1 = k).card
      let U := (V.filter fun i => count e y i.val (-1) = l).card
      |(nativeRectangleACount S e y k l (⟨y,rfl⟩ : Fiber S e y) : ℝ) -
        (U : ℝ)*R/V.card| ≤ 2*Real.sqrt V.card
    (∑ y : Obs M s e, if ¬∃ z, env z = env y ∧ G z ∧ C z
      then probability r e S y else 0) ≤
      16/15 * ∑ y : Obs M s e, if ¬G y then probability r e S y else 0 := by
  classical
  dsimp only
  let env := fullRectangleReadout (s := s) S e k l
  let C := fun y : Obs M s e =>
    let V := nativeRectangleRows S e y k l (⟨y,rfl⟩ : Fiber S e y)
    let R := (V.filter fun i => count e y i.val 1 = k).card
    let U := (V.filter fun i => count e y i.val (-1) = l).card
    |(nativeRectangleACount S e y k l (⟨y,rfl⟩ : Fiber S e y) : ℝ) -
      (U : ℝ)*R/V.card| ≤ 2*Real.sqrt V.card
  have hp := (finite_support_bayes (s := s) hq hqm hr hr1 ha ha1 e).2.2.1 S
  apply finite_environment_anchor_budget env (probability r e S) G C
    (fun y => (hp y).1.le)
  intro z hz
  letI : Fintype (Fiber S e z) := by unfold Fiber; infer_instance
  have ht := native_minimal_central_mass_tail S r e z hq hqm hr hr1 ha ha1
    k l (⟨z,rfl⟩ : Fiber S e z) (hsize z hz)
  have hn := full_environment_sum S r e k l z (fun y => ¬C y)
  have hd := full_environment_sum S r e k l z (fun _ => True)
  simp only [and_true] at hd
  have hl : (∑ y : Fiber S e z,
      if nativeMinimalRectangleReadout S e z k l y =
          nativeMinimalRectangleReadout S e z k l (⟨z,rfl⟩ : Fiber S e z) ∧ ¬C y.val
      then probability r e S y.val else 0) ≤
        1/16 * ∑ y : Fiber S e z,
          if nativeMinimalRectangleReadout S e z k l y =
              nativeMinimalRectangleReadout S e z k l (⟨z,rfl⟩ : Fiber S e z)
          then probability r e S y.val else 0 := by
    convert ht using 1 <;> try simp only [C,nativeRectangleRows,nativeRectangleACount]
    all_goals congr 3 <;> first | exact Subsingleton.elim _ _ | (ext y <;> simp)
  have hn' : (∑ y : Obs M s e, if env y = env z ∧ ¬C y
      then probability r e S y else 0) =
      (∑ y : Fiber S e z,
        if nativeMinimalRectangleReadout S e z k l y =
            nativeMinimalRectangleReadout S e z k l (⟨z,rfl⟩ : Fiber S e z) ∧ ¬C y.val
        then probability r e S y.val else 0) := by
    convert hn using 1 <;> try dsimp only [env]
    all_goals congr 3 <;> first | exact Subsingleton.elim _ _ | (ext y <;> simp)
  have hd' : (∑ y : Obs M s e, if env y = env z
      then probability r e S y else 0) =
      (∑ y : Fiber S e z,
        if nativeMinimalRectangleReadout S e z k l y =
            nativeMinimalRectangleReadout S e z k l (⟨z,rfl⟩ : Fiber S e z)
        then probability r e S y.val else 0) := by
    convert hd using 1 <;> try dsimp only [env]
    all_goals congr 3 <;> first | exact Subsingleton.elim _ _ | (ext y <;> simp)
  have hbound := le_of_eq_of_le hn' (le_of_le_of_eq hl (congrArg (fun a : ℝ => 1/16*a) hd'.symm))
  convert hbound using 1
  all_goals congr 3 <;> first | exact Subsingleton.elim _ _ | (ext y <;> simp)

open scoped Classical in
/-- A predicate of complete observations is conditioned on the original
full minimal readout. The collapsed-fiber normalization cancels exactly. -/
theorem full_native_conditional_mass_eq {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (o : Obs M s e)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hε : 0 ≤ compensation M q r) (hε1 : compensation M q r < 1)
    (k l : ℕ) (P : Obs M s e → Prop) :
    letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
    let Env := univ.filter fun y : Fiber S e o =>
      nativeMinimalRectangleReadout S e o k l y = nativeMinimalRectangleReadout S e o k l (⟨o,rfl⟩ : Fiber S e o)
    letI : DecidablePred (fun y : Fiber S e o => P y.val) := Classical.decPred _
    (∑ x : Obs M s e,if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o ∧ P x
      then probability r e S x else 0)/
      (∑ x : Obs M s e,if fullRectangleReadout S e k l x = fullRectangleReadout S e k l o
        then probability r e S x else 0) =
      conditionalFiberMass S r e o (Env.filter fun y => P y.val)/conditionalFiberMass S r e o Env := by
  classical
  letI : Fintype (Fiber S e o) := by unfold Fiber; infer_instance
  letI : Nonempty (Fiber S e o) := ⟨⟨o,rfl⟩⟩
  dsimp only
  have htotal : 0 < ∑ y : Fiber S e o,probability r e S y.val :=
    sum_pos (fun y _ => ((finite_support_bayes (s := s) hq hqm hr hr1 hε hε1 e).2.2.1 S y.val).1) univ_nonempty
  rw [full_environment_sum S r e k l o P]
  have hd := full_environment_sum S r e k l o (fun _ => True)
  simp only [and_true] at hd
  rw [hd]
  unfold conditionalFiberMass
  rw [div_div_div_cancel_right₀ htotal.ne']
  simp only [sum_filter,ite_and]

end
end D5.S3.Estimation.TimeArrow.NativeGlobalRectangleEnvironment

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
open private
  D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
  D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
from D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeReferenceCalibration
noncomputable section

/-- Complete count-level calibration at zero common odds shift. -/
def referenceParameter (M q : ℕ) (r : ℝ) (c : ℕ × ℕ) : ℝ :=
  Real.sigmoid (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
    c.2 * Real.log ((1 - r) / (1 + compensation M q r)) -
    Real.log (((M - q : ℕ) : ℝ) / q))

private theorem reference_factor {M q : ℕ} (S : Support M q) (r : ℝ) (L : ℕ)
    (i : Fin M) (c : ℕ × ℕ) :
    rowReference S r L i c = Real.exp (-(L : ℝ)) *
      (((L : ℝ) * (1 + b r S (.inl i)) / 2) ^ c.1 *
        ((L : ℝ) * (1 - b r S (.inl i)) / 2) ^ c.2) /
          (c.1.factorial * c.2.factorial : ℕ) := by
  unfold rowReference
  push_cast
  have hexp : Real.exp (-((L : ℝ) * (1 + b r S (.inl i)) / 2)) *
      Real.exp (-((L : ℝ) * (1 - b r S (.inl i)) / 2)) = Real.exp (-(L : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-((L : ℝ) * (1 + b r S (.inl i)) / 2)) *
        Real.exp (-((L : ℝ) * (1 - b r S (.inl i)) / 2))) *
      (((L : ℝ) * (1 + b r S (.inl i)) / 2) ^ c.1 *
        ((L : ℝ) * (1 - b r S (.inl i)) / 2) ^ c.2) /
          ((c.1.factorial : ℝ) * c.2.factorial) := by ring
    _ = _ := by rw [hexp]

theorem reference_likelihood_ratio {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) (c : ℕ × ℕ) :
    rowReference S r L i c =
      Real.exp (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
        c.2 * Real.log ((1 - r) / (1 + compensation M q r))) * rowReference S r L j c := by
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  have hp : 0 < (1 + r) / (1 - compensation M q r) := div_pos (by linarith) (by linarith)
  have hm : 0 < (1 - r) / (1 + compensation M q r) := div_pos (by linarith) (by linarith)
  have hexp : Real.exp (c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
      c.2 * Real.log ((1 - r) / (1 + compensation M q r))) =
      ((1 + r) / (1 - compensation M q r)) ^ c.1 *
        ((1 - r) / (1 + compensation M q r)) ^ c.2 := by
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log hp, Real.exp_log hm]
  rw [hexp, reference_factor, reference_factor]
  simp only [b, if_pos hi, if_neg hj, sub_neg_eq_add]
  have hplus : ((1 + r) / (1 - compensation M q r)) *
      ((L : ℝ) * (1 + -compensation M q r) / 2) = (L : ℝ) * (1 + r) / 2 := by
    field_simp [ne_of_gt (sub_pos.mpr hc1)]
    <;> ring
  have hminus : ((1 - r) / (1 + compensation M q r)) *
      ((L : ℝ) * (1 + compensation M q r) / 2) = (L : ℝ) * (1 - r) / 2 := by
    field_simp
    <;> ring
  have he :
      (((1 + r) / (1 - compensation M q r)) ^ c.1 *
        ((1 - r) / (1 + compensation M q r)) ^ c.2) *
      (((L : ℝ) * (1 + -compensation M q r) / 2) ^ c.1 *
        ((L : ℝ) * (1 + compensation M q r) / 2) ^ c.2) =
      ((L : ℝ) * (1 + r) / 2) ^ c.1 * ((L : ℝ) * (1 - r) / 2) ^ c.2 := by
    rw [show ∀ a b d e : ℝ, (a * b) * (d * e) = (a * d) * (b * e) by intros; ring,
      ← mul_pow, ← mul_pow, hplus, hminus]
  calc
    _ = Real.exp (-(L : ℝ)) *
      ((((1 + r) / (1 - compensation M q r)) ^ c.1 *
        ((1 - r) / (1 + compensation M q r)) ^ c.2) *
      (((L : ℝ) * (1 + -compensation M q r) / 2) ^ c.1 *
        ((L : ℝ) * (1 + compensation M q r) / 2) ^ c.2)) /
        (c.1.factorial * c.2.factorial : ℕ) := by rw [he]
    _ = _ := by ring

private theorem pointwise_calibration {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) (c : ℕ × ℕ) :
    ((q : ℝ) * rowReference S r L i c + ((M - q : ℕ) : ℝ) * rowReference S r L j c) *
      referenceParameter M q r c = (q : ℝ) * rowReference S r L i c := by
  let W := c.1 * Real.log ((1 + r) / (1 - compensation M q r)) +
      c.2 * Real.log ((1 - r) / (1 + compensation M q r))
  let B : ℝ := ((M - q : ℕ) : ℝ) / q
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hN : (0 : ℝ) < (M - q : ℕ) := by exact_mod_cast (show 0 < M - q by omega)
  have hB : 0 < B := div_pos hN hqR
  have hR : rowReference S r L i c = Real.exp W * rowReference S r L j c :=
    reference_likelihood_ratio S r κ hκ hr hrκ hcκ hL i j hi hj c
  rw [hR]
  change _ * Real.sigmoid (W - Real.log B) = _
  rw [Real.sigmoid_def, neg_sub, Real.exp_sub, Real.exp_log hB]
  dsimp [B]
  field_simp
  <;> ring

/-- The complete reference mean is exactly q. Its complete calibration
variance is the signal reference expectation of one minus the same parameter. -/
theorem reference_calibration_mean_variance {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hq : 1 ≤ q) (hqm : q < M)
    (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) :
    ((q : ℝ) * (∑' c, referenceParameter M q r c * rowReference S r L i c) +
      ((M - q : ℕ) : ℝ) * (∑' c, referenceParameter M q r c * rowReference S r L j c) = q) ∧
    ((q : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L i c) +
      ((M - q : ℕ) : ℝ) * (∑' c, (referenceParameter M q r c * (1 - referenceParameter M q r c)) *
        rowReference S r L j c) =
      (q : ℝ) * (∑' c, (1 - referenceParameter M q r c) * rowReference S r L i c)) := by
  let p := referenceParameter M q r
  have hp (c : ℕ × ℕ) : 0 ≤ p c ∧ p c ≤ 1 :=
    ⟨Real.sigmoid_nonneg _, Real.sigmoid_le_one _⟩
  have hv (c : ℕ × ℕ) : 0 ≤ p c * (1 - p c) ∧ p c * (1 - p c) ≤ 1 := by
    constructor
    · exact mul_nonneg (hp c).1 (by linarith [(hp c).2])
    · nlinarith [(hp c).1, (hp c).2, sq_nonneg (p c - 1 / 2)]
  have hs (g : ℕ × ℕ → ℝ) (hg : ∀ c, 0 ≤ g c ∧ g c ≤ 1) (k : Fin M) :
      Summable (fun c => g c * rowReference S r L k c) :=
    (D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
      S r κ hκ hr hrκ hcκ hL k g hg).1
  have hpoint := pointwise_calibration S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj
  have hnorm : (∑' c, rowReference S r L i c) = 1 := by
    have hh := D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
      S r κ 1 hκ hr hrκ hcκ hL (by norm_num) i
    simpa using hh.tsum_eq
  constructor
  · have hadd := ((hs p hp i).mul_left (q : ℝ)).tsum_add
      ((hs p hp j).mul_left ((M - q : ℕ) : ℝ))
    rw [← tsum_mul_left, ← tsum_mul_left, ← hadd]
    have he (c : ℕ × ℕ) : (q : ℝ) * (p c * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * (p c * rowReference S r L j c) =
        (q : ℝ) * rowReference S r L i c := by
      have hh := hpoint c
      change (_ * p c) = _ at hh
      nlinarith
    simp_rw [he]
    rw [tsum_mul_left, hnorm, mul_one]
  · have hadd := ((hs (fun c => p c * (1 - p c)) hv i).mul_left (q : ℝ)).tsum_add
      ((hs (fun c => p c * (1 - p c)) hv j).mul_left ((M - q : ℕ) : ℝ))
    rw [← tsum_mul_left, ← tsum_mul_left, ← hadd]
    have he (c : ℕ × ℕ) : (q : ℝ) * ((p c * (1 - p c)) * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * ((p c * (1 - p c)) * rowReference S r L j c) =
        (q : ℝ) * ((1 - p c) * rowReference S r L i c) := by
      have hh := congrArg (fun x : ℝ => x * (1 - p c)) (hpoint c)
      change _ = _ at hh
      nlinarith
    simp_rw [he]
    rw [tsum_mul_left]

private theorem all_row_reference_sum {M q L : ℕ} (S : Support M q) (r : ℝ)
    (g : ℕ × ℕ → ℝ) (i j : Fin M) (hi : i ∈ S.val) (hj : j ∉ S.val) :
    (∑ k : Fin M, ∑' c, g c * rowReference S r L k c) =
      (q : ℝ) * (∑' c, g c * rowReference S r L i c) +
        ((M - q : ℕ) : ℝ) * (∑' c, g c * rowReference S r L j c) := by
  classical
  have hk (k : Fin M) : (∑' c, g c * rowReference S r L k c) =
      if k ∈ S.val then (∑' c, g c * rowReference S r L i c)
      else (∑' c, g c * rowReference S r L j c) := by
    by_cases h : k ∈ S.val
    · rw [if_pos h]
      congr 1
      funext c
      simp only [rowReference, b, if_pos h, if_pos hi]
    · rw [if_neg h]
      congr 1
      funext c
      simp only [rowReference, b, if_neg h, if_neg hj]
  rw [sum_congr rfl (fun k _ => hk k)]
  rw [sum_ite]
  have hsig : (univ.filter fun k : Fin M => k ∈ S.val) = S.val := by ext k; simp
  have hbg : (univ.filter fun k : Fin M => k ∉ S.val).card = M - q := by
    have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin M))) (p := fun k => k ∈ S.val)
    rw [hsig, S.property] at hc
    simp only [card_univ, Fintype.card_fin] at hc
    omega
  simp [hsig, hbg, S.property]

/-- The reference calibration identities control all-row mean and variance
deviations under each original law, with a common restored-tail budget. -/
theorem native_reference_calibration_deviation (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        6 ≤ M → (L : ℝ) / M ≤ 1 / 45 →
        ∀ (S : Support M q) (e : Experiment) (i j : Fin M),
          i ∈ S.val → j ∉ S.val → ∀ b h : ℝ, 0 < b → 0 < h →
          let p := referenceParameter M q r
          let V := ∑ k : Fin M, ∑' c, (p c * (1 - p c)) * rowReference S r L k c
          let P := fun o : Obs M (2 * M * L) e =>
            ∑ k : Fin M, p (count e o k 1, count e o k (-1))
          let D := fun o : Obs M (2 * M * L) e =>
            ∑ k : Fin M, p (count e o k 1, count e o k (-1)) *
              (1 - p (count e o k 1, count e o k (-1)))
          let B := 3 * (q : ℝ) + 8 * (A * (L : ℝ) ^ 3 / M) * (q : ℝ) ^ 2 +
            10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
          0 ≤ V ∧ V ≤ q ∧
            (∑ o, if b < |P o - q| ∨ h < |D o - V| then probability r e S o else 0) ≤
              B / b ^ 2 + B / h ^ 2 := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_full_weighted_deviation κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e i j hi hj b t hb ht
  let p := referenceParameter M q r
  let v := fun c : ℕ × ℕ => p c * (1 - p c)
  let V := ∑ k : Fin M, ∑' c, v c * rowReference S r L k c
  let B := 3 * (q : ℝ) + 8 * (A * (L : ℝ) ^ 3 / M) * (q : ℝ) ^ 2 +
      10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
  have hp (c : ℕ × ℕ) : 0 ≤ p c ∧ p c ≤ 1 :=
    ⟨Real.sigmoid_nonneg _, Real.sigmoid_le_one _⟩
  have hv (c : ℕ × ℕ) : 0 ≤ v c ∧ v c ≤ 1 := by
    dsimp [v]
    constructor
    · exact mul_nonneg (hp c).1 (by linarith [(hp c).2])
    · nlinarith only [(hp c).1, (hp c).2, sq_nonneg (p c - 1 / 2)]
  have hcal := reference_calibration_mean_variance S r κ hκ hr hrκ hcκ hL hq hqm i j hi hj
  have hmean : (∑ k : Fin M, ∑' c, p c * rowReference S r L k c) = (q : ℝ) := by
    rw [all_row_reference_sum S r p i j hi hj]
    exact hcal.1
  have hVar : V = (q : ℝ) * (∑' c, (1 - p c) * rowReference S r L i c) := by
    dsimp [V]
    rw [all_row_reference_sum S r v i j hi hj]
    exact hcal.2
  have hQ (c : ℕ × ℕ) : 0 ≤ rowReference S r L i c :=
    (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hcomplement (c : ℕ × ℕ) : 0 ≤ 1 - p c ∧ 1 - p c ≤ 1 := by
    constructor <;> linarith [(hp c).1, (hp c).2]
  have hs := (D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_weighted_tail
    S r κ hκ hr hrκ hcκ hL i (fun c => 1 - p c) hcomplement).1
  have hnorm := D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets.reference_exponential_sum
    S r κ 1 hκ hr hrκ hcκ hL (by norm_num) i
  have htotal : (∑' c, rowReference S r L i c) = 1 := by simpa using hnorm.tsum_eq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hV0 : 0 ≤ V := by
    rw [hVar]
    exact mul_nonneg hq0 (tsum_nonneg fun c => mul_nonneg (hcomplement c).1 (hQ c))
  have hVq : V ≤ q := by
    rw [hVar]
    have hh := hs.tsum_le_tsum (fun c => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcomplement c).2 (hQ c))
      (by simpa only [one_pow, one_mul] using hnorm.summable)
    rw [htotal] at hh
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hq0
  have hP := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e univ
    (fun _ => p) (fun _ c => hp c) b hb
  simp only [hmean, card_univ, Fintype.card_fin] at hP
  have hD := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e univ
    (fun _ => v) (fun _ c => hv c) t ht
  have hδ : 0 ≤ A * (L : ℝ) ^ 3 / M := by positivity
  have hbudget : 3 * V + 8 * (A * (L : ℝ) ^ 3 / M) * V ^ 2 +
      10 * (M : ℝ) ^ 2 * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) ≤ B := by
    have hsq : V ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith only [hV0, hVq, hq0]
    have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 8 * (A * (L : ℝ) ^ 3 / M) by positivity)
    dsimp [B]
    linarith only [hVq, hh]
  have hD' : (∑ o : Obs M (2 * M * L) e,
      if t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V|
      then probability r e S o else 0) ≤ B / t ^ 2 := by
    apply hD.trans
    simp only [card_univ, Fintype.card_fin]
    exact div_le_div_of_nonneg_right hbudget (sq_nonneg t)
  refine ⟨hV0, hVq, ?_⟩
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  have hprob := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1.1 S
  apply le_trans _ (add_le_add hP hD')
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro o _
  change (if b < |(∑ k : Fin M, p (count e o k 1, count e o k (-1))) - q| ∨
      t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V|
      then probability r e S o else 0) ≤
    (if b < |(∑ k : Fin M, p (count e o k 1, count e o k (-1))) - q|
      then probability r e S o else 0) +
    (if t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V|
      then probability r e S o else 0)
  by_cases hp' : b < |(∑ k : Fin M, p (count e o k 1, count e o k (-1))) - q| <;>
    by_cases hd' : t < |(∑ k : Fin M, v (count e o k 1, count e o k (-1))) - V| <;>
    simp only [hp', hd', or_true, true_or, or_false, false_or, if_true, if_false]
  · exact le_add_of_nonneg_right (hprob o)
  · simp
  · simp
  · simp

end
end D5.S3.Estimation.TimeArrow.NativeReferenceCalibration

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeReferenceCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios
noncomputable section

private theorem row_reference_successors {M q L : ℕ} (S : Support M q) (r : ℝ)
    (i : Fin M) (k l : ℕ) :
    rowReference S r L i (k + 1, l) =
      ((L : ℝ) * (1 + b r S (.inl i)) / 2 / (k + 1)) * rowReference S r L i (k, l) ∧
    rowReference S r L i (k, l + 1) =
      ((L : ℝ) * (1 - b r S (.inl i)) / 2 / (l + 1)) * rowReference S r L i (k, l) := by
  unfold rowReference
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  constructor <;> field_simp <;> ring

/-- Large central signal counts give simultaneous reference ratios for all
four cells, using the original compensated model rather than a new law. -/
theorem signal_four_reference_ratios {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val) (k l : ℕ)
    (hkp : 15 / 16 ≤ ((L : ℝ) * (1 + r) / 2 / (k + 1)))
    (hkp' : ((L : ℝ) * (1 + r) / 2 / (k + 1)) ≤ 1)
    (hlp : 15 / 16 ≤ ((L : ℝ) * (1 - r) / 2 / (l + 1)))
    (hlp' : ((L : ℝ) * (1 - r) / 2 / (l + 1)) ≤ 1) :
    ∀ j : Fin 4,
      7 / 8 * rowReference S r L i (k, l) ≤
        rowReference S r L i (![(k,l), (k+1,l), (k,l+1), (k+1,l+1)] j) ∧
      rowReference S r L i (![(k,l), (k+1,l), (k,l+1), (k+1,l+1)] j) ≤
        9 / 8 * rowReference S r L i (k, l) := by
  have hpos := D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos
    S r κ hκ hr hrκ hcκ hL i (k,l)
  have hk := (row_reference_successors (L := L) S r i k l).1
  have hl := (row_reference_successors (L := L) S r i k l).2
  have hkl := (row_reference_successors (L := L) S r i k (l+1)).1
  simp only [b, if_pos hi] at hk hl hkl
  have hprodlo : 7 / 8 ≤
      ((L : ℝ) * (1 + r) / 2 / (k + 1)) * ((L : ℝ) * (1 - r) / 2 / (l + 1)) := by
    have hh := mul_le_mul hkp hlp (by norm_num : (0 : ℝ) ≤ 15 / 16) (by linarith)
    norm_num at hh
    linarith only [hh]
  have hprodhi :
      ((L : ℝ) * (1 + r) / 2 / (k + 1)) * ((L : ℝ) * (1 - r) / 2 / (l + 1)) ≤ 1 := by
    nlinarith only [hkp, hkp', hlp, hlp',
      mul_nonneg (by linarith : 0 ≤ 1 - ((L : ℝ) * (1 + r) / 2 / (k + 1)))
        (by linarith : 0 ≤ ((L : ℝ) * (1 - r) / 2 / (l + 1)))]
  intro j
  fin_cases j
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k,l) ∧
      rowReference S r L i (k,l) ≤ 9/8 * rowReference S r L i (k,l)
    constructor <;> nlinarith only [hpos]
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k+1,l) ∧
      rowReference S r L i (k+1,l) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hk]
    constructor <;> nlinarith only [hpos, hkp, hkp']
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k,l+1) ∧
      rowReference S r L i (k,l+1) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hl]
    constructor <;> nlinarith only [hpos, hlp, hlp']
  · change 7/8 * rowReference S r L i (k,l) ≤ rowReference S r L i (k+1,l+1) ∧
      rowReference S r L i (k+1,l+1) ≤ 9/8 * rowReference S r L i (k,l)
    rw [hkl, hl, ← mul_assoc]
    exact ⟨mul_le_mul_of_nonneg_right hprodlo hpos.le,
      (mul_le_mul_of_nonneg_right hprodhi hpos.le).trans (by nlinarith only [hpos])⟩

theorem original_count_rounding (r : ℝ) (L : ℕ) (hr : 0 < r) (hr1 : r < 1)
    (hL : 1 ≤ L) (hplus : 15 ≤ ((1+r)/2)*(L : ℝ))
    (hminus : 30 ≤ ((1-r)/2)*(L : ℝ)) :
    let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
    let l := L-k
    k ≤ L ∧ 0 < k ∧ 0 < l ∧
      15/16 ≤ ((L : ℝ)*(1+r)/2/(k+1)) ∧ ((L : ℝ)*(1+r)/2/(k+1)) ≤ 1 ∧
      15/16 ≤ ((L : ℝ)*(1-r)/2/(l+1)) ∧ ((L : ℝ)*(1-r)/2/(l+1)) ≤ 1 := by
  let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
  let l := L-k
  have ha0 : 0 ≤ ((1+r)/2)*(L : ℝ) := by positivity
  have hklo := Nat.floor_le ha0
  have hkhi := Nat.lt_floor_add_one (((1+r)/2)*(L : ℝ))
  change (k : ℝ) ≤ _ at hklo
  change _ < (k : ℝ)+1 at hkhi
  have hkL : k ≤ L := by
    apply Nat.floor_le_of_le
    nlinarith only [hr1, show (0 : ℝ) ≤ L by positivity]
  have hlr : (l : ℝ) = (L : ℝ)-k := by
    exact Nat.cast_sub hkL
  have hkp : 0 < k := by
    have hh : (0 : ℝ) < k := by linarith only [hplus,hkhi]
    exact_mod_cast hh
  have hlp : 0 < l := by
    have hh : (0 : ℝ) < l := by rw [hlr]; linarith only [hminus,hklo]
    exact_mod_cast hh
  refine ⟨hkL,hkp,hlp,?_,?_,?_,?_⟩
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
    nlinarith only [hplus,hklo]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
    linarith only [hkhi]
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < l+1)).mpr
    rw [hlr]
    nlinarith only [hminus,hkhi]
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < l+1)).mpr
    rw [hlr]
    nlinarith only [hklo]

/-- The central four-cell comparison retains the original natural floor
and l=lambda-k. Only explicit lower scale bounds are needed. -/
theorem floored_signal_four_reference_ratios {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1-κ)
    (hcκ : compensation M q r ≤ 1-κ) (hL : 1 ≤ L)
    (i : Fin M) (hi : i ∈ S.val)
    (hplus : 15 ≤ ((1+r)/2)*(L : ℝ)) (hminus : 30 ≤ ((1-r)/2)*(L : ℝ)) :
    let k := ⌊((1+r)/2)*(L : ℝ)⌋₊
    let l := L-k
    ∀ j : Fin 4, 7/8 * rowReference S r L i (k,l) ≤
      rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] j) ∧
      rowReference S r L i (![(k,l),(k+1,l),(k,l+1),(k+1,l+1)] j) ≤
        9/8 * rowReference S r L i (k,l) := by
  have hr1 : r < 1 := by linarith only [hrκ,hκ]
  have hh := original_count_rounding r L hr hr1 hL hplus hminus
  dsimp only at hh ⊢
  exact signal_four_reference_ratios S r κ hκ hr hrκ hcκ hL i hi _ _
    hh.2.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.1 hh.2.2.2.2.2.2

/-- The background A mean is exactly the signal A mean times the negative
original A logit. The finite-size compensation and M-q are preserved. -/
theorem background_reference_cell_ratio {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (hq : 1 ≤ q) (hqm : q < M) (i j : Fin M)
    (hi : i ∈ S.val) (hj : j ∉ S.val) (k l : ℕ) :
    ((M - q : ℕ) : ℝ) * rowReference S r L j (k,l) =
      ((q : ℝ) * rowReference S r L i (k,l)) *
        Real.exp (-(k * Real.log ((1+r)/(1-compensation M q r)) +
          l * Real.log ((1-r)/(1+compensation M q r)) -
          Real.log (((M-q : ℕ) : ℝ) / q))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hMR : (0 : ℝ) < (M-q : ℕ) := by exact_mod_cast (show 0 < M-q by omega)
  rw [reference_likelihood_ratio S r κ hκ hr hrκ hcκ hL i j hi hj (k,l)]
  rw [neg_sub, Real.exp_sub, Real.exp_log (div_pos hMR hqR)]
  field_simp
  <;> ring

end
end D5.S3.Estimation.TimeArrow.NativeRectangleReferenceRatios

open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes

namespace D5.S3.Estimation.TimeArrow.OriginalScoreWindow
noncomputable section
/-- The original complete window keeps its left-open, right-closed endpoints. -/
def originalWindow {M s : ℕ} (q : ℕ) (r center width : ℝ)
    (e : Experiment) (o : Obs M s e) : Finset (Fin M) := by
  classical
  exact univ.filter fun i => center-width < score q r e o i ∧ score q r e o i ≤ center+width
/-- Exact scores index groups inside the complete window. -/
def originalScoreGroup {M s : ℕ} (q : ℕ) (r center width value : ℝ)
    (e : Experiment) (o : Obs M s e) : Finset (Fin M) := by
  classical
  exact (originalWindow q r center width e o).filter fun i => score q r e o i = value
/-- The denominator in inclusion is the complete uniform-size support posterior. -/
def originalGroupPosteriorMean {M s : ℕ} (q : ℕ) (r center width value : ℝ)
    (e : Experiment) (o : Obs M s e) : ℝ :=
  ∑ i ∈ originalScoreGroup q r center width value e o,inclusion q r e o i
/-- A cut on complete signed departure counts, including all background rows. -/
def originalCountCut {M s : ℕ} (H : ℕ) (e : Experiment) (o : Obs M s e) : Prop :=
  ∀ i : Fin M,count e o i 1+count e o i (-1) ≤ H

end
end D5.S3.Estimation.TimeArrow.OriginalScoreWindow
