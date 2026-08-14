/- GID: D5/S0/Computability/DescriptionComplexity/AffordableRegionAgreement
   generality: G
   mirror-B: D5/B/S0/Computability/DescriptionComplexity/AffordableRegionAgreement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An affordable finite-region patch forces agreement for a loss-minimal candidate. -/

import Mathlib

namespace D5.S0.Computability.DescriptionComplexity.AffordableRegionAgreement

/-- A loss-minimal, complexity-bounded consistent function agrees with the truth
on every region whose patch cost fits the remaining budget. -/
theorem affordable_region_agreement
    {Output Loss : Type*} [Preorder Loss]
    (truth candidate : Nat -> Output)
    (record region : Finset Nat)
    (complexity : (Nat -> Output) -> Nat)
    (price : Finset Nat -> Nat)
    (budget overhead : Nat)
    (loss : (Nat -> Output) -> Loss)
    (candidate_consistent :
      forall n, n ∈ record -> candidate n = truth n)
    (patch_cost :
      complexity (fun n => if n ∈ region then truth n else candidate n) <=
        complexity candidate + price region + overhead)
    (accounting : complexity candidate + overhead <= budget)
    (strict_loss_improvement :
      forall h : Nat -> Output,
        region.Nonempty ->
        (forall n, n ∉ region -> h n = candidate n) ->
        (forall n, n ∈ region -> h n = truth n) ->
        (exists n, n ∈ region ∧ candidate n ≠ truth n) ->
        loss h < loss candidate)
    (loss_minimal :
      forall h : Nat -> Output,
        (forall n, n ∈ record -> h n = truth n) ->
        complexity h <= budget ->
        loss candidate <= loss h)
    (affordable :
      price region <= budget - complexity candidate - overhead) :
    forall n, n ∈ region -> candidate n = truth n := by
  intro n hn
  by_contra hne
  let patched : Nat -> Output := fun m =>
    if m ∈ region then truth m else candidate m
  have patched_outside : forall m, m ∉ region -> patched m = candidate m := by
    intro m hm
    simp [patched, hm]
  have patched_inside : forall m, m ∈ region -> patched m = truth m := by
    intro m hm
    simp [patched, hm]
  have patched_consistent : forall m, m ∈ record -> patched m = truth m := by
    intro m hm
    by_cases hm_region : m ∈ region
    · exact patched_inside m hm_region
    · simpa [patched, hm_region] using candidate_consistent m hm
  have patched_complexity : complexity patched <= budget := by
    have cost_bound :
        complexity patched <= complexity candidate + price region + overhead := by
      simpa [patched] using patch_cost
    omega
  have improves : loss patched < loss candidate :=
    strict_loss_improvement patched ⟨n, hn⟩ patched_outside patched_inside
      ⟨n, hn, hne⟩
  exact (not_lt_of_ge (loss_minimal patched patched_consistent patched_complexity)) improves

/-- Error-set inclusion realizes the strict-improvement premise used above. -/
example {Output : Type*}
    (truth candidate h : Nat -> Output) (region : Finset Nat)
    (unchanged : forall n, n ∉ region -> h n = candidate n)
    (corrected : forall n, n ∈ region -> h n = truth n)
    (disagreement : exists n, n ∈ region ∧ candidate n ≠ truth n) :
    ({n | h n ≠ truth n} : Set Nat) < {n | candidate n ≠ truth n} := by
  rw [Set.lt_iff_ssubset, Set.ssubset_iff_exists]
  constructor
  · intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    by_cases hn_region : n ∈ region
    · exact (hn (corrected n hn_region)).elim
    · intro candidate_eq
      exact hn ((unchanged n hn_region).trans candidate_eq)
  · rcases disagreement with ⟨n, hn, hne⟩
    refine ⟨n, ?_, ?_⟩
    · exact hne
    · simp only [Set.mem_setOf_eq]
      exact fun hn_error => hn_error (corrected n hn)

end D5.S0.Computability.DescriptionComplexity.AffordableRegionAgreement
