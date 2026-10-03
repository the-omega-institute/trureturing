/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSumInsertion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnBasicSumInsertion
   mirror-E: none(waiver:maximum-sum-cut-witnesses)
   anchors: []
   utility: none
   digest: Indecomposable maximum children are characterized by parent cuts before insertion. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicComponents

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicSumInsertion

open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

theorem indecomposable_maximum_insertion (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (site : ℕ) (hsite : site ≤ p.length) :
    sumIndecomposable (p.insertIdx site (n + 1)) ↔
      ∀ boundary, 0 < boundary → boundary ≤ site →
        ∃ before later, before < boundary ∧ boundary ≤ later ∧ later < p.length ∧
          p.getD later 0 ≤ p.getD before 0 := by
  have htest (word : List ℕ) : sumIndecomposable word ↔
      ∀ boundary, 0 < boundary → boundary < word.length →
        ∃ before later, before < boundary ∧ boundary ≤ later ∧ later < word.length ∧
          word.getD later 0 ≤ word.getD before 0 := by
    constructor
    · intro hindec boundary hpositive hboundary
      obtain ⟨before, later, hbad⟩ := hindec ⟨boundary, hboundary⟩ hpositive
      have hbefore : before.val < boundary := by
        have := before.is_lt
        simp only [List.length_take] at this
        omega
      have hlater : boundary + later.val < word.length := by
        have := later.is_lt
        simp only [List.length_drop] at this
        omega
      refine ⟨before.val, boundary + later.val, hbefore, by omega, hlater, ?_⟩
      simpa only [List.get_eq_getElem, List.getElem_take, List.getElem_drop,
        List.getD_eq_getElem word 0 hlater,
        List.getD_eq_getElem word 0 (by omega : before.val < word.length)] using hbad
    · intro hw boundary hpositive
      obtain ⟨before, later, hbefore, hlater, hbound, hbad⟩ :=
        hw boundary.val hpositive boundary.is_lt
      let first : Fin (word.take boundary.val).length := ⟨before, by
        simp only [List.length_take]
        omega⟩
      let second : Fin (word.drop boundary.val).length := ⟨later - boundary.val, by
        simp only [List.length_drop]
        omega⟩
      refine ⟨first, second, ?_⟩
      have heq : boundary.val + (later - boundary.val) = later := by omega
      simpa only [first, second, List.get_eq_getElem, List.getElem_take, List.getElem_drop,
        heq, List.getD_eq_getElem word 0 hbound,
        List.getD_eq_getElem word 0 (by omega : before < word.length)] using hbad
  let child := p.insertIdx site (n + 1)
  have hlength : child.length = p.length + 1 :=
    List.length_insertIdx_of_le_length hsite _
  have hentry (index : ℕ) (hindex : index < p.length) : p.getD index 0 ≤ n := by
    have hm : p.getD index 0 ∈ p := by
      rw [List.getD_eq_getElem p 0 hindex]
      exact List.getElem_mem hindex
    have hrange := hperm.mem_iff.mp hm
    simp only [List.mem_range', Nat.one_mul] at hrange
    obtain ⟨offset, hoffset, heq⟩ := hrange
    omega
  have hbefore (index : ℕ) (hindex : index < site) :
      child.getD index 0 = p.getD index 0 := by
    rw [List.getD_eq_getElem child 0 (by omega),
      List.getElem_insertIdx_of_lt hindex, List.getD_eq_getElem p 0 (by omega)]
  have hat : child.getD site 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  have hafter (index : ℕ) (hindex : site < index) (hb : index < child.length) :
      child.getD index 0 = p.getD (index - 1) 0 := by
    rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hindex,
      List.getD_eq_getElem p 0 (by omega)]
  change sumIndecomposable child ↔ _
  rw [htest child]
  constructor
  · intro hchild boundary hpositive hboundary
    obtain ⟨before, later, hb, hl, hbound, hbad⟩ :=
      hchild boundary hpositive (by omega)
    rw [hbefore before (by omega)] at hbad
    rcases lt_trichotomy later site with hlt | heq | hgt
    · rw [hbefore later hlt] at hbad
      exact ⟨before, later, hb, hl, by omega, hbad⟩
    · subst later
      rw [hat] at hbad
      have := hentry before (by omega)
      omega
    · rw [hafter later hgt hbound] at hbad
      exact ⟨before, later - 1, hb, by omega, by omega, hbad⟩
  · intro hparent boundary hpositive hboundary
    by_cases hleft : boundary ≤ site
    · obtain ⟨before, later, hb, hl, hbound, hbad⟩ :=
        hparent boundary hpositive hleft
      by_cases hlater : later < site
      · refine ⟨before, later, hb, hl, by omega, ?_⟩
        rwa [hbefore before (by omega), hbefore later hlater]
      · refine ⟨before, later + 1, hb, by omega, by omega, ?_⟩
        rwa [hbefore before (by omega), hafter (later + 1) (by omega) (by omega),
          Nat.add_sub_cancel]
    · refine ⟨site, boundary, by omega, le_rfl, hboundary, ?_⟩
      rw [hat, hafter boundary (by omega) hboundary]
      exact Nat.le_trans (hentry (boundary - 1) (by omega)) (by omega)

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicSumInsertion
