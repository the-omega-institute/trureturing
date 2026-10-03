/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentSites
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentSites
   mirror-E: none(waiver:vincular-active-sites)
   anchors: []
   utility: none
   digest: Records identify exactly the active sites preceding the permutation maximum. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentInsertion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentSites

open WeakAscentDefs WeakAscentInsertion

noncomputable def activeSites (p : List ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (p.length + 1)).filter fun site =>
    ¬ ContainsV2413 (p.insertIdx site (p.length + 1))

noncomputable def recordSites (p : List ℕ) : Finset ℕ := by
  classical
  exact (Finset.range p.length).filter fun site =>
    ∀ earlier < site, p.getD earlier 0 < p.getD site 0

theorem active_record_structure (p : List ℕ) (hempty : p ≠ [])
    (hperm : p.Perm (List.range' 1 p.length)) (havoid : ¬ ContainsV2413 p) :
    (activeSites p).filter (· ≤ p.idxOf p.length) = recordSites p ∧
    (∀ site ∈ recordSites p, site ≤ p.idxOf p.length) ∧
    0 ∈ activeSites p ∧ p.length ∈ activeSites p := by
  classical
  have hlength : 0 < p.length := List.length_pos_iff.mpr hempty
  have hmaxmem : p.length ∈ p := by
    apply hperm.mem_iff.mpr
    exact List.mem_range'.mpr ⟨p.length - 1, by omega, by omega⟩
  have hmaxpos : p.idxOf p.length < p.length := List.idxOf_lt_length_iff.mpr hmaxmem
  have hmaxread : p.getD (p.idxOf p.length) 0 = p.length := by
    rw [List.getD_eq_getElem _ _ hmaxpos, List.getElem_idxOf hmaxpos]
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range')
  have value_bound (value : ℕ) (hvalue : value ∈ p) : value ≤ p.length := by
    obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp (hperm.mem_iff.mp hvalue)
    omega
  have read_bound (index : ℕ) (hindex : index < p.length) :
      p.getD index 0 ≤ p.length := by
    rw [List.getD_eq_getElem _ _ hindex]
    exact value_bound _ (List.getElem_mem hindex)
  have strict_bound (index : ℕ) (hindex : index < p.length)
      (hne : index ≠ p.idxOf p.length) : p.getD index 0 < p.length := by
    have hbound := read_bound index hindex
    have hnevalue : p.getD index 0 ≠ p.length := by
      intro heq
      have hsame : p.getD index 0 = p.getD (p.idxOf p.length) 0 := heq.trans hmaxread.symm
      exact hne ((List.getD_inj hindex hmaxpos hnodup).mp hsame)
    omega
  have hmax : ∀ value ∈ p, value < p.length + 1 := by
    intro value hvalue
    have := value_bound value hvalue
    omega
  have criterion (site : ℕ) (hsite : site ≤ p.length) :
      site ∈ activeSites p ↔
      ¬ ∃ earlier later, earlier < site ∧ site < later ∧ later < p.length ∧
        p.getD site 0 < p.getD earlier 0 ∧ p.getD earlier 0 < p.getD later 0 := by
    rw [activeSites, Finset.mem_filter, Finset.mem_range]
    simp only [show site < p.length + 1 by omega, true_and]
    exact active_site_criterion p site (p.length + 1) hsite hmax havoid
  have records_left (site : ℕ) (hsite : site ∈ recordSites p) :
      site ≤ p.idxOf p.length := by
    obtain ⟨hsitebound, hrecord⟩ := Finset.mem_filter.mp hsite
    have hindex := Finset.mem_range.mp hsitebound
    by_contra hnot
    have hbefore : p.idxOf p.length < site := by omega
    have hvalue := hrecord (p.idxOf p.length) hbefore
    rw [hmaxread] at hvalue
    have hbound := read_bound site hindex
    omega
  have records_active (site : ℕ) (hsite : site ∈ recordSites p) : site ∈ activeSites p := by
    obtain ⟨hsitebound, hrecord⟩ := Finset.mem_filter.mp hsite
    have hindex := Finset.mem_range.mp hsitebound
    apply (criterion site (by omega)).mpr
    rintro ⟨earlier, later, hearlier, hlater, hlast, hlow, hmid⟩
    have hreverse := hrecord earlier hearlier
    omega
  refine ⟨?_, records_left, ?_, ?_⟩
  · ext site
    constructor
    · intro hsite
      obtain ⟨hactive, hbefore⟩ := Finset.mem_filter.mp hsite
      have hindex : site < p.length := by omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hindex, ?_⟩
      intro earlier hearlier
      by_contra hnot
      have hearlier' : earlier < p.length := by omega
      have hne : earlier ≠ site := by omega
      have hnevalue : p.getD earlier 0 ≠ p.getD site 0 := by
        intro heq
        exact hne ((List.getD_inj hearlier' hindex hnodup).mp heq)
      have hlow : p.getD site 0 < p.getD earlier 0 := by omega
      by_cases heq : site = p.idxOf p.length
      · rw [heq, hmaxread] at hlow
        have hbound := read_bound earlier hearlier'
        omega
      · have hstrict : site < p.idxOf p.length := by omega
        apply (criterion site (by omega)).mp hactive
        refine ⟨earlier, p.idxOf p.length, hearlier, hstrict, hmaxpos, hlow, ?_⟩
        rw [hmaxread]
        exact strict_bound earlier hearlier' (by omega)
    · intro hsite
      exact Finset.mem_filter.mpr ⟨records_active site hsite, records_left site hsite⟩
  · apply (criterion 0 (by omega)).mpr
    rintro ⟨earlier, later, hearlier, _⟩
    omega
  · apply (criterion p.length (Nat.le_refl _)).mpr
    rintro ⟨earlier, later, hearlier, hlater, hlast, _⟩
    omega

theorem active_sites_insert (p : List ℕ) (site : ℕ)
    (hperm : p.Perm (List.range' 1 p.length)) (havoid : ¬ ContainsV2413 p)
    (hactive : site ∈ activeSites p) :
    activeSites (p.insertIdx site (p.length + 1)) =
      ((recordSites p).filter (· < site) ∪ {site, site + 1}) ∪
        ((activeSites p).filter (site < ·)).image (· + 1) := by
  classical
  let maximum := p.length + 1
  let q := p.insertIdx site maximum
  have hsite : site ≤ p.length := by
    have hbound := (Finset.mem_filter.mp hactive).1
    have hlt := Finset.mem_range.mp hbound
    omega
  have hqavoid : ¬ ContainsV2413 q := (Finset.mem_filter.mp hactive).2
  have hlength : q.length = p.length + 1 := by simp [q, List.length_insertIdx, hsite]
  have hnodup : p.Nodup := hperm.nodup_iff.mpr (List.nodup_range')
  have pbound (value : ℕ) (hvalue : value ∈ p) : value < maximum := by
    obtain ⟨index, hindex, hvalue⟩ := List.mem_range'.mp (hperm.mem_iff.mp hvalue)
    dsimp [maximum]
    omega
  have read_bound (index : ℕ) (hindex : index < p.length) :
      p.getD index 0 < maximum := by
    rw [List.getD_eq_getElem _ _ hindex]
    exact pbound _ (List.getElem_mem hindex)
  have qbound (index : ℕ) (hindex : index < q.length) : q.getD index 0 ≤ maximum := by
    rw [List.getD_eq_getElem _ _ hindex]
    have hmem := List.getElem_mem hindex
    change q[index] ∈ p.insertIdx site maximum at hmem
    rcases (List.mem_insertIdx hsite).mp hmem with heq | hold
    · omega
    · exact Nat.le_of_lt (pbound _ hold)
  have qmaxbound : ∀ value ∈ q, value < q.length + 1 := by
    intro value hvalue
    obtain ⟨index, hindex, heq⟩ := List.mem_iff_getElem.mp hvalue
    have hbound := qbound index hindex
    rw [List.getD_eq_getElem _ _ hindex, heq] at hbound
    dsimp [maximum] at hbound
    omega
  have old_read (index : ℕ) (hindex : index < site) : q.getD index 0 = p.getD index 0 := by
    simp [q, List.getD_eq_getElem?_getD, List.getElem?_insertIdx, hindex]
  have shifted_read (index : ℕ) (hindex : site ≤ index) :
      q.getD (index + 1) 0 = p.getD index 0 := by
    have hnot : ¬ index + 1 < site := by omega
    have hne : index + 1 ≠ site := by omega
    simp [q, List.getD_eq_getElem?_getD, List.getElem?_insertIdx, hnot, hne]
  have maximum_read : q.getD site 0 = maximum := by
    simp [q, List.getD_eq_getElem?_getD, List.getElem?_insertIdx, hsite]
  have pcriterion (index : ℕ) (hindex : index ≤ p.length) :
      index ∈ activeSites p ↔
      ¬ ∃ earlier later, earlier < index ∧ index < later ∧ later < p.length ∧
        p.getD index 0 < p.getD earlier 0 ∧ p.getD earlier 0 < p.getD later 0 := by
    rw [activeSites, Finset.mem_filter, Finset.mem_range]
    simp only [show index < p.length + 1 by omega, true_and]
    exact active_site_criterion p index maximum hindex pbound havoid
  have qcriterion (index : ℕ) (hindex : index ≤ q.length) :
      index ∈ activeSites q ↔
      ¬ ∃ earlier later, earlier < index ∧ index < later ∧ later < q.length ∧
        q.getD index 0 < q.getD earlier 0 ∧ q.getD earlier 0 < q.getD later 0 := by
    rw [activeSites, Finset.mem_filter, Finset.mem_range]
    simp only [show index < q.length + 1 by omega, true_and]
    exact active_site_criterion q index (q.length + 1) hindex qmaxbound hqavoid
  have before_active (index : ℕ) (hindex : index < site) :
      index ∈ activeSites q ↔ index ∈ recordSites p := by
    have hpindex : index < p.length := by omega
    have hqindex : index ≤ q.length := by omega
    constructor
    · intro hindexactive
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpindex, ?_⟩
      intro earlier hearlier
      by_contra hnot
      have hearlierval : p.getD earlier 0 ≠ p.getD index 0 := by
        intro heq
        have hsame := (List.getD_inj (show earlier < p.length by omega)
          hpindex hnodup).mp heq
        omega
      have hlow : p.getD index 0 < p.getD earlier 0 := by omega
      apply (qcriterion index hqindex).mp hindexactive
      refine ⟨earlier, site, hearlier, hindex, by omega, ?_, ?_⟩
      · rw [old_read index hindex, old_read earlier (by omega)]
        exact hlow
      · rw [old_read earlier (by omega), maximum_read]
        exact read_bound earlier (by omega)
    · intro hrecord
      have hrecord' := (Finset.mem_filter.mp hrecord).2
      apply (qcriterion index hqindex).mpr
      rintro ⟨earlier, later, hearlier, hlater, hlast, hlow, hmid⟩
      rw [old_read index hindex, old_read earlier (by omega)] at hlow
      have hreverse := hrecord' earlier hearlier
      omega
  have after_active (index : ℕ) (hlower : site ≤ index) (hupper : index ≤ p.length) :
      index + 1 ∈ activeSites q ↔ index ∈ activeSites p := by
    rw [qcriterion (index + 1) (by omega), pcriterion index hupper]
    have obstruction :
        (∃ earlier later, earlier < index + 1 ∧ index + 1 < later ∧ later < q.length ∧
          q.getD (index + 1) 0 < q.getD earlier 0 ∧ q.getD earlier 0 < q.getD later 0) ↔
        ∃ earlier later, earlier < index ∧ index < later ∧ later < p.length ∧
          p.getD index 0 < p.getD earlier 0 ∧ p.getD earlier 0 < p.getD later 0 := by
      constructor
      · rintro ⟨earlier, later, hearlier, hlater, hlast, hlow, hmid⟩
        have hearlier_ne : earlier ≠ site := by
          intro heq
          rw [heq, maximum_read] at hmid
          have hbound := qbound later hlast
          omega
        have hlater : site ≤ later - 1 := by omega
        have hlaterread : q.getD later 0 = p.getD (later - 1) 0 := by
          have heq : later = later - 1 + 1 := by omega
          conv_lhs => rw [heq]
          exact shifted_read _ hlater
        rw [shifted_read index hlower] at hlow
        rw [hlaterread] at hmid
        by_cases hbefore : earlier < site
        · rw [old_read earlier hbefore] at hlow hmid
          exact ⟨earlier, later - 1, by omega, by omega, by omega, hlow, hmid⟩
        · have hearlierval : q.getD earlier 0 = p.getD (earlier - 1) 0 := by
            have heq : earlier = earlier - 1 + 1 := by omega
            conv_lhs => rw [heq]
            exact shifted_read _ (by omega)
          rw [hearlierval] at hlow hmid
          exact ⟨earlier - 1, later - 1, by omega, by omega, by omega, hlow, hmid⟩
      · rintro ⟨earlier, later, hearlier, hlater, hlast, hlow, hmid⟩
        by_cases hbefore : earlier < site
        · refine ⟨earlier, later + 1, by omega, by omega, by omega, ?_, ?_⟩
          · rw [shifted_read index hlower, old_read earlier hbefore]
            exact hlow
          · rw [old_read earlier hbefore, shifted_read later (by omega)]
            exact hmid
        · refine ⟨earlier + 1, later + 1, by omega, by omega, by omega, ?_, ?_⟩
          · rw [shifted_read index hlower, shifted_read earlier (by omega)]
            exact hlow
          · rw [shifted_read earlier (by omega), shifted_read later (by omega)]
            exact hmid
    exact not_congr obstruction
  have maximum_active : site ∈ activeSites q := by
    apply (qcriterion site (by omega)).mpr
    rintro ⟨earlier, later, hearlier, hlater, hlast, hlow, hmid⟩
    rw [maximum_read] at hlow
    have hbound := qbound earlier (by omega)
    omega
  change activeSites q = _
  ext index
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_image]
  constructor
  · intro hindex
    have hbound : index ≤ q.length := by
      have hrange := (Finset.mem_filter.mp hindex).1
      have := Finset.mem_range.mp hrange
      omega
    by_cases hbefore : index < site
    · exact Or.inl (Or.inl ⟨(before_active index hbefore).mp hindex, hbefore⟩)
    · by_cases heq : index = site
      · exact Or.inl (Or.inr (Or.inl heq))
      · by_cases heq' : index = site + 1
        · exact Or.inl (Or.inr (Or.inr heq'))
        · right
          have hindex' : index = index - 1 + 1 := by omega
          have hactive' : index - 1 ∈ activeSites p := by
            apply (after_active (index - 1) (by omega) (by omega)).mp
            rwa [← hindex']
          exact ⟨index - 1, ⟨hactive', by omega⟩, hindex'.symm⟩
  · intro hindex
    rcases hindex with (⟨hrecord, hbefore⟩ | (heq | heq)) | ⟨old, ⟨hold, hafter⟩, heq⟩
    · exact (before_active index hbefore).mpr hrecord
    · subst index
      exact maximum_active
    · subst index
      exact (after_active site (Nat.le_refl _) hsite).mpr hactive
    · subst index
      have hupper : old ≤ p.length := by
        have hrange := (Finset.mem_filter.mp hold).1
        have := Finset.mem_range.mp hrange
        omega
      exact (after_active old (by omega) hupper).mpr hold

end D5.S3.Combinatorics.WeakAscent.WeakAscentSites
