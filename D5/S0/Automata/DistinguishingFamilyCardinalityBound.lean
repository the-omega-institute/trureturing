/- GID: D5/S0/Automata/DistinguishingFamilyCardinalityBound
   generality: G
   mirror-B: D5/B/S0/Automata/DistinguishingFamilyCardinalityBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rigid distinguishing continuations are bounded by the output alphabet. -/

import D5.S0.Automata.DFAOStateLowerBound

/- Library-search audit (2026-09-12):
   * Searched Mathlib/Data/Fintype/Card.lean for cardinality bounds and reused
     `Fintype.card_le_of_injective` and `Fintype.card_le_one_iff_subsingleton`.
   * Searched Mathlib/Computability/MyhillNerode.lean and the repository for
     distinguishing-family cardinality results; no matching theorem was found.
   * No hypothesis weakening was found or attempted. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.DistinguishingFamilyCardinalityBound

open D5.S0.Automata.DFAOStateLowerBound

universe u v w z

private lemma continuation_constant
    {Alphabet : Type u} {Output : Type v} {Index : Type z}
    [Nontrivial Index]
    {domain : Set (List Alphabet)} {target : List Alphabet -> Output}
    (certificate : DistinguishingFamily domain target Index)
    (rigid : forall (i : Index) (c c' : List Alphabet),
      certificate.witnessPrefix i ++ c ∈ domain ->
      certificate.witnessPrefix i ++ c' ∈ domain -> c = c') :
    ∃ c : List Alphabet, ∀ i j : Index, i ≠ j ->
      certificate.continuation i j = c := by
  classical
  let i₀ : Index := Classical.choice (inferInstance : Nonempty Index)
  obtain ⟨j₀, hj₀⟩ := exists_ne i₀
  have hj₀' : i₀ ≠ j₀ := Ne.symm hj₀
  refine ⟨certificate.continuation i₀ j₀, ?_⟩
  intro i j hij
  by_cases hi : i = i₀
  · subst i
    apply rigid i₀ (certificate.continuation i₀ j) (certificate.continuation i₀ j₀)
    · exact certificate.left_mem hij
    · exact certificate.left_mem hj₀'
  · have hfirst : certificate.continuation i j =
        certificate.continuation i i₀ :=
      rigid i _ _ (certificate.left_mem hij) (certificate.left_mem hi)
    have hsecond : certificate.continuation i i₀ =
        certificate.continuation i₀ j₀ := by
      exact (rigid i₀ (certificate.continuation i i₀)
        (certificate.continuation i₀ j₀)
        (certificate.right_mem hi) (certificate.left_mem hj₀'))
    exact hfirst.trans hsecond

theorem card_le_card_output_of_rigid_continuations
    {Alphabet : Type u} {Output : Type v} {Index : Type z}
    [Fintype Index] [Fintype Output]
    {domain : Set (List Alphabet)} {target : List Alphabet -> Output}
    (certificate : DistinguishingFamily domain target Index)
    (rigid : forall (i : Index) (c c' : List Alphabet),
      certificate.witnessPrefix i ++ c ∈ domain ->
      certificate.witnessPrefix i ++ c' ∈ domain -> c = c') :
    Fintype.card Index <= Fintype.card Output := by
  classical
  by_cases h : Nontrivial Index
  · letI := h
    obtain ⟨c, hc⟩ := continuation_constant certificate rigid
    refine Fintype.card_le_of_injective (fun i => target (certificate.witnessPrefix i ++ c)) ?_
    intro i j heq
    by_contra hne
    have hne' := certificate.target_ne hne
    apply hne'
    rw [hc i j hne]
    exact heq
  · haveI : Subsingleton Index := not_nontrivial_iff_subsingleton.mp h
    have hi : Fintype.card Index ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    letI : Nonempty Output := ⟨target []⟩
    have ho : 1 ≤ Fintype.card Output := Fintype.card_pos_iff.mpr inferInstance
    exact hi.trans ho

theorem distinguishing_certificate_bounded_by_output_alphabet
    {Alphabet : Type u} {Output : Type v} {State : Type w} {Index : Type z}
    [Fintype Index] [Fintype Output] [Fintype State]
    {domain : Set (List Alphabet)} {target : List Alphabet -> Output}
    (machine : DFAO Alphabet Output State)
    (certificate : DistinguishingFamily domain target Index)
    (correct : machine.CorrectOn domain target)
    (rigid : forall (i : Index) (c c' : List Alphabet),
      certificate.witnessPrefix i ++ c ∈ domain ->
      certificate.witnessPrefix i ++ c' ∈ domain -> c = c') :
    Fintype.card Index <= Fintype.card Output ∧
      Fintype.card Index <= Fintype.card State := by
  exact ⟨card_le_card_output_of_rigid_continuations certificate rigid,
    state_lower_bound_of_distinguishing_family machine domain target certificate correct⟩

#print axioms card_le_card_output_of_rigid_continuations
#print axioms distinguishing_certificate_bounded_by_output_alphabet

end D5.S0.Automata.DistinguishingFamilyCardinalityBound
