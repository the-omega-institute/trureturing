/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnBasicTenThirteenPatterns
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnBasicTenThirteenPatterns
   mirror-E: none(waiver:maximum-pattern-witnesses)
   anchors: []
   utility: none
   digest: Maximum insertion creates exactly the crossing witnesses for 2413 and 2431. -/

import D5.S3.Combinatorics.Fishburn.FishburnBasicFourPatterns
import D5.S3.Combinatorics.Fishburn.FishburnBasicParents

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicTenThirteenPatterns

open D5.S3.Combinatorics Nonnesting

theorem maximum_crossing_pattern_tests (n : ℕ) (p : List ℕ)
    (hperm : p.Perm (List.range' 1 n)) (site : ℕ) (hsite : site ≤ p.length) :
    (NonnestingDefs.Occurs [2, 4, 1, 3] (p.insertIdx site (n + 1)) ↔
      NonnestingDefs.Occurs [2, 4, 1, 3] p ∨
      ∃ first second third, first < site ∧ site ≤ second ∧ second < third ∧
        third < p.length ∧ p.getD second 0 < p.getD first 0 ∧
        p.getD first 0 < p.getD third 0) ∧
    (NonnestingDefs.Occurs [2, 4, 3, 1] (p.insertIdx site (n + 1)) ↔
      NonnestingDefs.Occurs [2, 4, 3, 1] p ∨
      ∃ first second third, first < site ∧ site ≤ second ∧ second < third ∧
        third < p.length ∧ p.getD third 0 < p.getD first 0 ∧
        p.getD first 0 < p.getD second 0) := by
  let child := p.insertIdx site (n + 1)
  have hlength : child.length = p.length + 1 :=
    List.length_insertIdx_of_le_length hsite _
  have hbound : ∀ value ∈ p, value ≤ n := by
    intro value hvalue
    have hm := hperm.mem_iff.mp hvalue
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨offset, hoffset, hvalue⟩ := hm
    omega
  have hentry (index : ℕ) (hindex : index < p.length) : p.getD index 0 ≤ n := by
    rw [List.getD_eq_getElem p 0 hindex]
    exact hbound _ (List.getElem_mem hindex)
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
  have hmaxpos (index : ℕ) (hb : index < child.length)
      (hv : child.getD index 0 = n + 1) : index = site := by
    rcases lt_trichotomy index site with hleft | heq | hright
    · rw [hbefore index hleft] at hv
      have := hentry index (by omega)
      omega
    · exact heq
    · rw [hafter index hright hb] at hv
      have := hentry (index - 1) (by omega)
      omega
  have hfilter : ∀ (word : List ℕ) (gap : ℕ), gap ≤ word.length →
      (∀ value ∈ word, value ≠ n + 1) →
      (word.insertIdx gap (n + 1)).filter (· != n + 1) = word := by
    intro word gap
    induction gap generalizing word with
    | zero =>
      intro _ hword
      simp only [List.insertIdx_zero, List.filter_cons, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte]
      apply List.filter_eq_self.mpr
      intro value hvalue
      simpa using hword value hvalue
    | succ gap ih =>
      cases word with
      | nil => simp
      | cons head tail =>
        intro hgap hword
        have hhead := hword head (by simp)
        have htail : ∀ value ∈ tail, value ≠ n + 1 := by
          intro value hvalue
          exact hword value (by simp [hvalue])
        simpa [List.insertIdx_succ_cons, hhead] using
          congrArg (head :: ·) (ih tail (by simpa using hgap) htail)
  have hfiltered : child.filter (· != n + 1) = p :=
    hfilter p site hsite (fun value hv => by have := hbound value hv; omega)
  have hindices : ∀ (word : List ℕ) (low middle high top : ℕ),
      [low, middle, high, top].Sublist word →
      ∃ first second third fourth, first < second ∧ second < third ∧ third < fourth ∧
        fourth < word.length ∧ word.getD first 0 = low ∧ word.getD second 0 = middle ∧
        word.getD third 0 = high ∧ word.getD fourth 0 = top := by
    intro word low middle high top hsub
    obtain ⟨positions, hpositions⟩ :=
      List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
    let first := positions ⟨0, by simp⟩
    let second := positions ⟨1, by simp⟩
    let third := positions ⟨2, by simp⟩
    let fourth := positions ⟨3, by simp⟩
    refine ⟨first.val, second.val, third.val, fourth.val, ?_, ?_, ?_, fourth.is_lt,
      ?_, ?_, ?_, ?_⟩
    · exact positions.strictMono (by change (0 : ℕ) < 1; omega)
    · exact positions.strictMono (by change (1 : ℕ) < 2; omega)
    · exact positions.strictMono (by change (2 : ℕ) < 3; omega)
    · rw [List.getD_eq_get]
      simpa [first] using (hpositions ⟨0, by simp⟩).symm
    · rw [List.getD_eq_get]
      simpa [second] using (hpositions ⟨1, by simp⟩).symm
    · rw [List.getD_eq_get]
      simpa [third] using (hpositions ⟨2, by simp⟩).symm
    · rw [List.getD_eq_get]
      simpa [fourth] using (hpositions ⟨3, by simp⟩).symm
  have hselected : ∀ (word : List ℕ) (positions : List ℕ),
      positions.Pairwise (· < ·) → (∀ index ∈ positions, index < word.length) →
      (positions.map (fun index => word.getD index 0)).Sublist word := by
    intro word positions horder hb
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    let select : Fin (positions.map (fun index => word.getD index 0)).length →
        Fin word.length := fun index =>
      ⟨positions[index.val]'(by simpa using index.is_lt),
        hb _ (List.getElem_mem (by simpa using index.is_lt))⟩
    have hmono : StrictMono select := by
      intro first second hlt
      exact List.pairwise_iff_getElem.mp horder first.val second.val
        (by simpa using first.is_lt) (by simpa using second.is_lt) hlt
    refine ⟨OrderEmbedding.ofStrictMono select hmono, ?_⟩
    intro index
    simp only [List.get_eq_getElem, List.getElem_map, OrderEmbedding.coe_ofStrictMono]
    exact List.getD_eq_getElem word 0 _
  have hcore : ∀ pattern : List ℕ, pattern.Perm [1, 2, 3, 4] →
      (ArrowWilfDefs.Contains pattern [] 4 child ↔
      ArrowWilfDefs.Contains pattern [] 4 p ∨
      ∃ values : ℕ → ℕ,
        (∀ rank, 1 ≤ rank → rank < 4 → values rank < values (rank + 1)) ∧
        (pattern.map values).Sublist child ∧ values 4 = n + 1) := by
    intro pattern hpattern
    have hranks : ∀ rank ∈ pattern, 1 ≤ rank ∧ rank ≤ 4 := by
      intro rank hrank
      have := hpattern.mem_iff.mp hrank
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      omega
    have hfull : ∀ rank, 1 ≤ rank → rank ≤ 4 → rank ∈ pattern := by
      intro rank hlow hhigh
      apply hpattern.mem_iff.mpr
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    constructor
    · rintro ⟨values, hstep, hmem, hsub, _⟩
      by_cases htop : values 4 = n + 1
      · exact Or.inr ⟨values, hstep, hsub, htop⟩
      · left
        have htopmem : values 4 ∈ p :=
          (List.eq_or_mem_of_mem_insertIdx (hmem 4 (by omega) (by omega))).resolve_left htop
        have htopbound := hbound _ htopmem
        have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
        have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
        have h34 : values 3 < values 4 := hstep 3 (by omega) (by omega)
        have hsmall : ∀ rank, 1 ≤ rank → rank ≤ 4 → values rank ≠ n + 1 := by
          intro rank hlow hhigh
          have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 ∨ rank = 4 := by omega
          rcases hc with rfl | rfl | rfl | rfl <;> omega
        refine ⟨values, hstep, ?_, ?_, by simp⟩
        · intro rank hlow hhigh
          exact (List.eq_or_mem_of_mem_insertIdx (hmem rank hlow hhigh)).resolve_left
            (hsmall rank hlow hhigh)
        · have hf := hsub.filter (· != n + 1)
          rw [hfiltered] at hf
          have hself : (pattern.map values).filter (· != n + 1) = pattern.map values := by
            apply List.filter_eq_self.mpr
            intro value hvalue
            obtain ⟨rank, hrank, rfl⟩ := List.mem_map.mp hvalue
            simpa using hsmall rank (hranks rank hrank).1 (hranks rank hrank).2
          rwa [hself] at hf
    · rintro (⟨values, hstep, hmem, hsub, _⟩ | ⟨values, hstep, hsub, _⟩)
      · refine ⟨values, hstep, ?_, hsub.trans (List.sublist_insertIdx p site (n + 1)),
          by simp⟩
        intro rank hlow hhigh
        exact List.subset_insertIdx p site (n + 1) (hmem rank hlow hhigh)
      · refine ⟨values, hstep, ?_, hsub, by simp⟩
        intro rank hlow hhigh
        exact hsub.subset (List.mem_map.mpr ⟨rank, hfull rank hlow hhigh, rfl⟩)
  have h241 := hcore [2, 4, 1, 3] (by decide)
  have h243 := hcore [2, 4, 3, 1] (by decide)
  change (ArrowWilfDefs.Contains [2, 4, 1, 3] [] 4 child ↔ _) ∧
    (ArrowWilfDefs.Contains [2, 4, 3, 1] [] 4 child ↔ _)
  constructor
  · rw [h241]
    apply or_congr_right
    constructor
    · rintro ⟨values, hstep, hsub, htop⟩
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
      simp only [List.map_cons, List.map_nil] at hsub
      obtain ⟨first, second, third, fourth, hfs, hst, htf, hf, h2, h4, h1, h3⟩ :=
        hindices child _ _ _ _ hsub
      have hsecond : second = site := hmaxpos second (by omega) (h4.trans htop)
      subst second
      rw [hbefore first hfs] at h2
      rw [hafter third hst (by omega)] at h1
      rw [hafter fourth (by omega) hf] at h3
      exact ⟨first, third - 1, fourth - 1, hfs, by omega, by omega,
        by omega, by omega, by omega⟩
    · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
      let values : ℕ → ℕ := fun rank => if rank = 1 then p.getD second 0
        else if rank = 2 then p.getD first 0
        else if rank = 3 then p.getD third 0 else n + 1
      refine ⟨values, ?_, ?_, by simp [values]⟩
      · intro rank hl hh
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        have := hentry third ht
        rcases hc with rfl | rfl | rfl <;>
          simp only [values, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
      · have hsub := hselected child [first, site, second + 1, third + 1]
          (by simp [List.pairwise_cons]; omega) (by
            intro index hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl <;> omega)
        rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
          hbefore first hf, hat, hafter (second + 1) (by omega) (by omega),
          hafter (third + 1) (by omega) (by omega)] at hsub
        simpa [values] using hsub
  · rw [h243]
    apply or_congr_right
    constructor
    · rintro ⟨values, hstep, hsub, htop⟩
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
      simp only [List.map_cons, List.map_nil] at hsub
      obtain ⟨first, second, third, fourth, hfs, hst, htf, hf, h2, h4, h3, h1⟩ :=
        hindices child _ _ _ _ hsub
      have hsecond : second = site := hmaxpos second (by omega) (h4.trans htop)
      subst second
      rw [hbefore first hfs] at h2
      rw [hafter third hst (by omega)] at h3
      rw [hafter fourth (by omega) hf] at h1
      exact ⟨first, third - 1, fourth - 1, hfs, by omega, by omega,
        by omega, by omega, by omega⟩
    · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
      let values : ℕ → ℕ := fun rank => if rank = 1 then p.getD third 0
        else if rank = 2 then p.getD first 0
        else if rank = 3 then p.getD second 0 else n + 1
      refine ⟨values, ?_, ?_, by simp [values]⟩
      · intro rank hl hh
        have hc : rank = 1 ∨ rank = 2 ∨ rank = 3 := by omega
        have := hentry second (by omega)
        rcases hc with rfl | rfl | rfl <;>
          simp only [values, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff] <;> omega
      · have hsub := hselected child [first, site, second + 1, third + 1]
          (by simp [List.pairwise_cons]; omega) (by
            intro index hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl <;> omega)
        rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil,
          hbefore first hf, hat, hafter (second + 1) (by omega) (by omega),
          hafter (third + 1) (by omega) (by omega)] at hsub
        simpa [values] using hsub

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicTenThirteenPatterns
