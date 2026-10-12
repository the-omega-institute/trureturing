/- GID: D5/S3/Estimation/TimeArrow/NativeGlobalRectangleEnvironment
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeGlobalRectangleEnvironment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The full native environment includes the collapsed history and the minimal rectangle readout. -/

import D5.S3.Estimation.TimeArrow.NativeEnvironmentAnchors

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
