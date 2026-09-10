/- GID: D5/S3/ArithSums/DisjointStrictRefinement
   generality: G
   mirror-B: D5/B/S3/ArithSums/DisjointStrictRefinement
   mirror-E: none(waiver:general-finite-sum-criterion)
   anchors: []
   utility: none
   digest: A disjoint strict refinement is nontrivial exactly when a member is an outside sum. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.DisjointStrictRefinement

/-- Each member has one positive strict partition with that member as its sum;
blocks belonging to distinct members are disjoint. Values outside `S` are irrelevant. -/
def IsDisjointStrictRefinement (S : Finset ℕ) (blocks : ℕ → Finset ℕ) : Prop :=
  (∀ s ∈ S, (∀ t ∈ blocks s, 0 < t) ∧ (blocks s).sum id = s) ∧
    ∀ s ∈ S, ∀ r ∈ S, s ≠ r → Disjoint (blocks s) (blocks r)

/-- At least one member receives a block other than its trivial singleton partition. -/
def NontrivialDisjointRefinement (S : Finset ℕ) : Prop :=
  ∃ blocks : ℕ → Finset ℕ, IsDisjointStrictRefinement S blocks ∧
    ∃ s ∈ S, blocks s ≠ {s}

private lemma part_lt_of_nontrivial {T : Finset ℕ} {s t : ℕ}
    (hpos : ∀ u ∈ T, 0 < u) (hsum : T.sum id = s)
    (hne : T ≠ {s}) (ht : t ∈ T) : t < s := by
  have hle : t ≤ s := by
    exact (Finset.single_le_sum (f := id) (fun u _ => Nat.zero_le u) ht).trans hsum.le
  by_contra hnot
  have heq : t = s := by omega
  apply hne
  rw [← heq]
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨ht, ?_⟩
  intro u hu
  by_contra hut
  have he := Finset.sum_erase_add T id ht
  have hu' : u ∈ T.erase t := Finset.mem_erase.mpr ⟨hut, hu⟩
  have hule := Finset.single_le_sum (f := id) (fun v _ => Nat.zero_le v) hu'
  have hp := hpos u hu
  dsimp only [id] at he hule
  change (∑ x ∈ T, x) = s at hsum
  omega

private theorem least_changed_block_disjoint {S : Finset ℕ} {blocks : ℕ → Finset ℕ}
    (hf : IsDisjointStrictRefinement S blocks) {s : ℕ}
    (hs : s ∈ S) (hchanged : blocks s ≠ {s})
    (hleast : ∀ t ∈ S, t < s → blocks t = {t}) : Disjoint (blocks s) S := by
  apply Finset.disjoint_left.mpr
  intro t ht htS
  have hts := part_lt_of_nontrivial (hf.1 s hs).1 (hf.1 s hs).2 hchanged ht
  have hfixed := hleast t htS hts
  exact Finset.disjoint_left.mp (hf.2 s hs t htS (Ne.symm (ne_of_lt hts))) ht
    (by simp [hfixed])

/-- The common pointwise criterion behind OEIS A384350 and A384318:
a nontrivial disjoint family exists exactly when a member is a sum of distinct positive
nonmembers. The empty set is allowed. -/
theorem nontrivial_disjoint_refinement_iff (S : Finset ℕ) (hS : ∀ s ∈ S, 0 < s) :
    NontrivialDisjointRefinement S ↔ ∃ s ∈ S, ∃ T : Finset ℕ,
      (∀ t ∈ T, 0 < t) ∧ Disjoint T S ∧ T.sum id = s := by
  classical
  constructor
  · rintro ⟨blocks, hf, s₀, hs₀, hc₀⟩
    let changed := S.filter fun s => blocks s ≠ {s}
    have hne : changed.Nonempty := ⟨s₀, Finset.mem_filter.mpr ⟨hs₀, hc₀⟩⟩
    let s := changed.min' hne
    have hs : s ∈ S ∧ blocks s ≠ {s} :=
      Finset.mem_filter.mp (Finset.min'_mem changed hne)
    refine ⟨s, hs.1, blocks s, (hf.1 s hs.1).1, ?_, (hf.1 s hs.1).2⟩
    apply least_changed_block_disjoint hf hs.1 hs.2
    intro t ht hts
    by_contra hchange
    have hmin : s ≤ t := Finset.min'_le changed t (Finset.mem_filter.mpr ⟨ht, hchange⟩)
    omega
  · rintro ⟨s, hs, T, hpos, hdisj, hsum⟩
    let blocks : ℕ → Finset ℕ := fun r => if r = s then T else {r}
    refine ⟨blocks, ⟨?_, ?_⟩, s, hs, ?_⟩
    · intro r hr
      by_cases hrs : r = s
      · subst r
        simpa [blocks] using And.intro hpos hsum
      · simp only [blocks, if_neg hrs]
        exact ⟨by simpa using hS r hr, by simp⟩
    · intro r hr q hq hrq
      apply Finset.disjoint_left.mpr
      intro t htr htq
      by_cases hrs : r = s
      · subst r
        have hqs : q ≠ s := Ne.symm hrq
        have htT : t ∈ T := by simpa [blocks] using htr
        have ht : t = q := by simpa [blocks, hqs] using htq
        exact Finset.disjoint_left.mp hdisj htT (ht ▸ hq)
      · have ht : t = r := by simpa [blocks, hrs] using htr
        by_cases hqs : q = s
        · subst q
          have htT : t ∈ T := by simpa [blocks] using htq
          exact Finset.disjoint_left.mp hdisj htT (ht ▸ hr)
        · have ht' : t = q := by simpa [blocks, hqs] using htq
          exact hrq (ht.symm.trans ht')
    · intro heq
      have hsT : s ∈ T := by
        have hmem : s ∈ blocks s := heq ▸ Finset.mem_singleton_self s
        simpa [blocks] using hmem
      exact Finset.disjoint_left.mp hdisj hsT hs

#print axioms nontrivial_disjoint_refinement_iff

private lemma no_refinement_of_bounded_check (S : Finset ℕ) (hS : ∀ s ∈ S, 0 < s)
    (hcheck : ¬∃ s ∈ S, ∃ T ∈ (Finset.range (s + 1)).powerset,
      (∀ t ∈ T, 0 < t) ∧ Disjoint T S ∧ T.sum id = s) :
    ¬NontrivialDisjointRefinement S := by
  intro h
  obtain ⟨s, hs, T, hp, hd, hsum⟩ := (nontrivial_disjoint_refinement_iff S hS).mp h
  apply hcheck
  refine ⟨s, hs, T, Finset.mem_powerset.mpr ?_, hp, hd, hsum⟩
  intro t ht
  have hle : t ≤ s :=
    (Finset.single_le_sum (f := id) (fun u _ => Nat.zero_le u) ht).trans hsum.le
  exact Finset.mem_range.mpr (by omega)

private theorem positive_controls :
    NontrivialDisjointRefinement {3} ∧ NontrivialDisjointRefinement {4} ∧
      NontrivialDisjointRefinement {5} ∧ NontrivialDisjointRefinement {6} ∧
      NontrivialDisjointRefinement {1, 5} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (nontrivial_disjoint_refinement_iff {3} (by decide)).mpr
    exact ⟨3, by decide, {1, 2}, by decide, by decide, by decide⟩
  · apply (nontrivial_disjoint_refinement_iff {4} (by decide)).mpr
    exact ⟨4, by decide, {1, 3}, by decide, by decide, by decide⟩
  · apply (nontrivial_disjoint_refinement_iff {5} (by decide)).mpr
    exact ⟨5, by decide, {2, 3}, by decide, by decide, by decide⟩
  · apply (nontrivial_disjoint_refinement_iff {6} (by decide)).mpr
    exact ⟨6, by decide, {1, 5}, by decide, by decide, by decide⟩
  · apply (nontrivial_disjoint_refinement_iff {1, 5} (by decide)).mpr
    exact ⟨5, by decide, {2, 3}, by decide, by decide, by decide⟩

private theorem negative_controls :
    ¬NontrivialDisjointRefinement {1} ∧ ¬NontrivialDisjointRefinement {2} ∧
      ¬NontrivialDisjointRefinement {1, 2} ∧ ¬NontrivialDisjointRefinement {1, 3} ∧
      ¬NontrivialDisjointRefinement {1, 4} := by
  exact ⟨no_refinement_of_bounded_check {1} (by decide) (by decide),
    no_refinement_of_bounded_check {2} (by decide) (by decide),
    no_refinement_of_bounded_check {1, 2} (by decide) (by decide),
    no_refinement_of_bounded_check {1, 3} (by decide) (by decide),
    no_refinement_of_bounded_check {1, 4} (by decide) (by decide)⟩

private theorem empty_control : ¬NontrivialDisjointRefinement ∅ := by
  rintro ⟨_, _, s, hs, _⟩
  exact Finset.notMem_empty s hs

end D5.S3.ArithSums.DisjointStrictRefinement
