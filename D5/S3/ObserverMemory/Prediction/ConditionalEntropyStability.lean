/- GID: D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/ConditionalEntropyStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Full support identifies stability depth with first zero conditional entropy. -/

import D5.S3.Entropy.ConditionalEntropyEquality
import D5.S3.Entropy.Forgetting.CapacityMonotone

/- Library-search audit trail (2026-08-15):
   * Exact pinned-Mathlib hits `Nat.sInf_mem` and `Nat.sInf_def` give the
     membership and minimum semantics of a nonempty set of natural depths;
     both are applied below.
   * Exact pinned-Mathlib support hit `Finset.single_le_sum` proves that a
     pushforward cell containing a strictly positive state has positive mass;
     it is applied below.
   * Pinned Mathlib has no finite `conditionalEntropy` declaration matching
     this result. LeanSearch returned only unrelated binary-entropy and
     measure-level conditional-distribution results.
   * The repository's exact support theorem
     `conditional_entropy_eq_zero_iff_point_mass_on_support` is imported and
     applied. Repository search found no prediction-depth characterization.
-/

namespace D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.ConditionalEntropyEquality
open D5.S3.Entropy.Forgetting.CapacityMonotone

/-- The readout word seen through update times zero through `m`. -/
def futureReadoutWord {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (m : Nat) (y : Y) : Fin (m + 1) -> O :=
  fun k => q ((tau^[k]) y)

/-- Prediction is stable at depth `m` when the word through time `m`
determines the readout at time `m + 1`. -/
def predictionStableAt {Y O : Type*} (tau : Y -> Y) (q : Y -> O)
    (m : Nat) : Prop :=
  forall y y', futureReadoutWord tau q m y = futureReadoutWord tau q m y' ->
    q ((tau^[m + 1]) y) = q ((tau^[m + 1]) y')

/-- The least prediction-stable depth, represented by the natural infimum. -/
noncomputable def predictionStabilityDepth {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) : Nat :=
  sInf {m | predictionStableAt tau q m}

/-- When a stable depth exists, the least depth is itself stable. -/
theorem prediction_stability_depth_is_stable {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O)
    (hstable : exists m, predictionStableAt tau q m) :
    predictionStableAt tau q (predictionStabilityDepth tau q) := by
  exact Nat.sInf_mem hstable

/-- Every stable depth lies above the least stable depth. -/
theorem prediction_stability_depth_le_of_stable {Y O : Type*}
    (tau : Y -> Y) (q : Y -> O) (m : Nat)
    (hm : predictionStableAt tau q m) :
    predictionStabilityDepth tau q <= m := by
  classical
  rw [predictionStabilityDepth]
  have hnonempty : {n | predictionStableAt tau q n}.Nonempty := ⟨m, hm⟩
  rw [Nat.sInf_def hnonempty]
  exact Nat.find_min' hnonempty hm

/-- The joint weight of the readout word through time `m` and the next
readout, induced by the initial state weights. -/
noncomputable def nextReadoutJointLaw {Y O : Type*} [Fintype Y]
    (tau : Y -> Y) (q : Y -> O) (p : Y -> Real) (m : Nat) :
    (Fin (m + 1) -> O) × O -> Real :=
  pushforward
    (fun y => (futureReadoutWord tau q m y, q ((tau^[m + 1]) y))) p

private theorem pushforward_nonneg {X Z : Type*} [Fintype X]
    (f : X -> Z) (p : X -> Real) (hp : forall x, 0 <= p x) (z : Z) :
    0 <= pushforward f p z := by
  classical
  simp only [pushforward]
  exact Finset.sum_nonneg fun x _ => by
    by_cases h : f x = z <;> simp [h, hp x]

private theorem graph_joint_marginal {X A B : Type*}
    [Fintype X] [Fintype B]
    (p : X -> Real) (f : X -> A) (g : X -> B) :
    marginal (pushforward (fun x => (f x, g x)) p) = pushforward f p := by
  classical
  funext a
  simp only [marginal, pushforward]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hfa : f x = a
  · simp [hfa]
  · simp [hfa]

private theorem pushforward_apply_pos {X Z : Type*}
    [Fintype X]
    (p : X -> Real) (f : X -> Z) (hp : forall x, 0 < p x) (x : X) :
    0 < pushforward f p (f x) := by
  classical
  simp only [pushforward]
  let term : X -> Real := fun x' =>
    @ite Real (f x' = f x) (Classical.propDecidable (f x' = f x)) (p x') 0
  change 0 < ∑ x', term x'
  have hx : term x = p x := by simp [term]
  have hle : term x <= ∑ x', term x' := by
    simpa using
      (Finset.single_le_sum
        (s := Finset.univ)
        (f := term)
        (fun x' _ => by
          by_cases h : f x' = f x <;> simp [term, h, (hp x').le])
        (Finset.mem_univ x))
  rw [hx] at hle
  simpa only using lt_of_lt_of_le (hp x) hle

private theorem graph_conditional_entropy_zero_iff {X A B : Type*}
    [Fintype X] [Fintype A] [Fintype B]
    (p : X -> Real) (f : X -> A) (g : X -> B)
    (hfull : forall x, 0 < p x) :
    conditionalEntropy (pushforward (fun x => (f x, g x)) p) = 0 <->
      forall x x', f x = f x' -> g x = g x' := by
  classical
  let joint : A × B -> Real := pushforward (fun x => (f x, g x)) p
  have hjoint_nonneg : forall z, 0 <= joint z :=
    pushforward_nonneg (fun x => (f x, g x)) p fun x => (hfull x).le
  rw [conditional_entropy_eq_zero_iff_point_mass_on_support joint hjoint_nonneg]
  constructor
  · intro hpoint x x' hfx
    have hmarginal : Not (marginal joint (f x) = 0) := by
      rw [graph_joint_marginal p f g]
      exact (pushforward_apply_pos p f hfull x).ne'
    rcases hpoint (f x) hmarginal with ⟨b, hb⟩
    have hcond_x : Not (conditional joint (f x) (g x) = 0) := by
      rw [conditional]
      exact div_ne_zero
        (pushforward_apply_pos p (fun y => (f y, g y)) hfull x).ne' hmarginal
    have hcond_x' : Not (conditional joint (f x) (g x') = 0) := by
      rw [conditional]
      have hcell : 0 < joint (f x, g x') := by
        change 0 < pushforward (fun y => (f y, g y)) p (f x, g x')
        simpa [hfx] using
          pushforward_apply_pos p (fun y => (f y, g y)) hfull x'
      exact div_ne_zero hcell.ne' hmarginal
    have hgx : g x = b := by
      by_contra hne
      have h := congrFun hb (g x)
      rw [if_neg hne] at h
      exact hcond_x h
    have hgx' : g x' = b := by
      by_contra hne
      have h := congrFun hb (g x')
      rw [if_neg hne] at h
      exact hcond_x' h
    exact hgx.trans hgx'.symm
  · intro hstable a hmarginal
    rw [graph_joint_marginal p f g] at hmarginal
    have hexists : exists x, f x = a := by
      by_contra h
      push Not at h
      apply hmarginal
      simp only [pushforward]
      apply Finset.sum_eq_zero
      intro x _
      simp [h x]
    rcases hexists with ⟨x0, hx0⟩
    have hmarginal_joint : Not (marginal joint a = 0) := by
      rw [graph_joint_marginal p f g]
      exact hmarginal
    refine ⟨g x0, ?_⟩
    funext b
    rw [conditional]
    by_cases hb : b = g x0
    · subst b
      have hcell : joint (a, g x0) = marginal joint a := by
        rw [graph_joint_marginal p f g]
        simp only [joint, pushforward]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hfx : f x = a
        · have hg : g x = g x0 := hstable x x0 (hfx.trans hx0.symm)
          simp [hfx, hg]
        · simp [hfx]
      simp [hcell, hmarginal_joint]
    · have hcell : joint (a, b) = 0 := by
        simp only [joint, pushforward]
        apply Finset.sum_eq_zero
        intro x _
        by_cases hfx : f x = a
        · have hg : g x = g x0 := hstable x x0 (hfx.trans hx0.symm)
          simp [hfx, hg, Ne.symm hb]
        · simp [hfx]
      simp [hcell, hb]

/-- Under full support, the least depth at which the next deterministic
readout is fixed by the observed word is exactly the least depth at which its
conditional entropy vanishes. -/
theorem prediction_stability_depth_eq_conditional_entropy_zero
    {Y O : Type*} [Fintype Y] [Fintype O]
    (tau : Y -> Y) (q : Y -> O) (p : Y -> Real)
    (hfull : forall y, 0 < p y) :
    predictionStabilityDepth tau q =
      sInf {m | conditionalEntropy (nextReadoutJointLaw tau q p m) = 0} := by
  apply congrArg sInf
  ext m
  change predictionStableAt tau q m <->
    conditionalEntropy
      (pushforward
        (fun y => (futureReadoutWord tau q m y, q ((tau^[m + 1]) y))) p) = 0
  symm
  exact graph_conditional_entropy_zero_iff p
    (futureReadoutWord tau q m) (fun y => q ((tau^[m + 1]) y)) hfull

/-- A constant Boolean update supplies a full-support instance. -/
example :
    predictionStabilityDepth (fun _ : Bool => false) id =
      sInf {m | conditionalEntropy
        (nextReadoutJointLaw (fun _ : Bool => false) id
          (fun _ => (1 / 2 : Real)) m) = 0} := by
  apply prediction_stability_depth_eq_conditional_entropy_zero
  intro b
  positivity

end D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
