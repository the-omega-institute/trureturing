/- GID: D5/S3/Entropy/Forgetting/CompletionEntropyMinimality
   generality: G
   mirror-B: D5/B/S3/Entropy/Forgetting/CompletionEntropyMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factorization cannot increase a completion's conditional entropy. -/

import D5.S3.Entropy.Forgetting.CapacityMonotone

/- Library-search audit trail (2026-08-15):
   * Loogle queries `conditionalEntropy` and `"conditional entropy"` found no declaration;
     `Real.negMulLog` returned scalar identities, and `Fintype.card_le_of_surjective` returned only
     the cardinality helper rather than a conditional-entropy theorem.
   * LeanSearch query `conditional entropy decreases under a deterministic function` returned
     measure-kernel and topological-entropy results such as
     `ProbabilityTheory.condDistrib_comp_self`,
     `ProbabilityTheory.Kernel.deterministic_map`, and
     `Dynamics.coverEntropyInf_image_le_of_uniformContinuous`, but no finite-law exact hit.
   * Pinned-Mathlib grep for conditional-entropy names combined with deterministic-map terms found
     no match. Repository and digestion-record searches likewise found no exact or rearranged
     duplicate.
   * The proof therefore imports and applies the exact local support theorem
     `deterministic_forgetting_entropy_capacity_monotone`, then uses the frozen finite entropy chain
     rule after proving that the observation marginal is unchanged.
-/

namespace D5.S3.Entropy.Forgetting.CompletionEntropyMinimality

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy

private theorem pushforward_comp {X Y Z : Type*} [Fintype X] [Fintype Y]
    (p : X -> Real) (f : X -> Y) (g : Y -> Z) :
    pushforward g (pushforward f p) = pushforward (g ∘ f) p := by
  classical
  funext z
  simp only [pushforward]
  calc
    (∑ y, if g y = z then ∑ x, if f x = y then p x else 0 else 0) =
        ∑ y, ∑ x, if g y = z then (if f x = y then p x else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : g y = z <;> simp [hy]
    _ = ∑ x, ∑ y, if g y = z then (if f x = y then p x else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ x, if (g ∘ f) x = z then p x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (f x)]
      · simp
      · intro y _ hy
        simp [Ne.symm hy]
      · simp

private theorem pushforward_is_law {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X -> Real) (f : X -> Y)
    (hp : (forall x, 0 ≤ p x) ∧ ∑ x, p x = 1) :
    (forall y, 0 ≤ pushforward f p y) ∧ ∑ y, pushforward f p y = 1 := by
  classical
  constructor
  · intro y
    simp only [pushforward]
    exact Finset.sum_nonneg fun x _ => by
      by_cases h : f x = y <;> simp [h, hp.1 x]
  · simp only [pushforward]
    calc
      (∑ y, ∑ x, if f x = y then p x else 0) =
          ∑ x, ∑ y, if f x = y then p x else 0 := Finset.sum_comm
      _ = ∑ x, p x := by
        apply Finset.sum_congr rfl
        intro x _
        simp
      _ = 1 := hp.2

private theorem marginal_eq_pushforward_fst {O W : Type*} [Fintype O] [Fintype W]
    (p : O × W -> Real) :
    marginal p = pushforward (fun x : O × W => x.1) p := by
  classical
  funext o
  simp only [marginal, pushforward, Fintype.sum_prod_type]
  symm
  rw [Finset.sum_eq_single o]
  · simp
  · intro o' _ ho'
    simp [ho']
  · simp

private theorem marginal_pushforward_first {O W Z : Type*}
    [Fintype O] [Fintype W] [Fintype Z]
    (p : O × W -> Real) (factor : W -> Z) :
    marginal (pushforward (fun x : O × W => (x.1, factor x.2)) p) = marginal p := by
  calc
    marginal (pushforward (fun x : O × W => (x.1, factor x.2)) p) =
        pushforward (fun x : O × Z => x.1)
          (pushforward (fun x : O × W => (x.1, factor x.2)) p) :=
      marginal_eq_pushforward_fst _
    _ = pushforward ((fun x : O × Z => x.1) ∘
          fun x : O × W => (x.1, factor x.2)) p :=
      pushforward_comp _ _ _
    _ = pushforward (fun x : O × W => x.1) p := by rfl
    _ = marginal p := (marginal_eq_pushforward_fst _).symm

/-- If one finite deterministic completion is a surjective factor of another, then its
conditional entropy given the same observation cannot be larger. -/
theorem completion_conditional_entropy_le_of_factorization
    {Y O W Z : Type*}
    [Fintype Y] [Fintype O] [Nonempty O]
    [Fintype W] [Nonempty W] [Fintype Z] [Nonempty Z]
    (p : Y -> Real) (hp : (forall y, 0 ≤ p y) ∧ ∑ y, p y = 1)
    (observation : Y -> O) (otherCompletion : Y -> W)
    (completion : Y -> Z) (factor : W -> Z)
    (hfactor : Function.Surjective factor)
    (hcompletion : completion = factor ∘ otherCompletion) :
    conditionalEntropy
        (pushforward (fun y => (observation y, completion y)) p) ≤
      conditionalEntropy
        (pushforward (fun y => (observation y, otherCompletion y)) p) := by
  classical
  let jointOther : O × W -> Real :=
    pushforward (fun y => (observation y, otherCompletion y)) p
  let jointCompletion : O × Z -> Real :=
    pushforward (fun y => (observation y, completion y)) p
  let forget : O × W -> O × Z := fun x => (x.1, factor x.2)
  have hjointOther :
      (forall x, 0 ≤ jointOther x) ∧ ∑ x, jointOther x = 1 :=
    pushforward_is_law p (fun y => (observation y, otherCompletion y)) hp
  have hjointCompletion :
      (forall x, 0 ≤ jointCompletion x) ∧ ∑ x, jointCompletion x = 1 :=
    pushforward_is_law p (fun y => (observation y, completion y)) hp
  have hforget_surjective : Function.Surjective forget := by
    intro x
    rcases hfactor x.2 with ⟨w, hw⟩
    exact ⟨(x.1, w), Prod.ext rfl hw⟩
  have hforget_joint : pushforward forget jointOther = jointCompletion := by
    dsimp only [jointOther, jointCompletion]
    rw [pushforward_comp]
    apply congrArg (fun f => pushforward f p)
    funext y
    simp [forget, hcompletion]
  have hentropy : shannonEntropy jointCompletion ≤ shannonEntropy jointOther := by
    have h :=
      (deterministic_forgetting_entropy_capacity_monotone
        jointOther forget hjointOther hforget_surjective).1
    rwa [hforget_joint] at h
  have hmarginal : marginal jointCompletion = marginal jointOther := by
    rw [← hforget_joint]
    exact marginal_pushforward_first jointOther factor
  have hchainOther := entropy_chain_rule jointOther hjointOther.1
  have hchainCompletion := entropy_chain_rule jointCompletion hjointCompletion.1
  rw [hmarginal] at hchainCompletion
  change conditionalEntropy jointCompletion ≤ conditionalEntropy jointOther
  linarith

end D5.S3.Entropy.Forgetting.CompletionEntropyMinimality
