/- GID: D5/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenSites
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenThirteen/FishburnTenThirteenSites
   mirror-E: none(waiver:suffix-interval-pattern-witnesses)
   anchors: [mathlib/module/Mathlib.Order.Interval.Set.OrdConnected]
   utility: none
   digest: Interval suffixes characterize active cuts and their exact maximum-insertion updates. -/

import D5.S3.Combinatorics.FishburnTenThirteen.FishburnBasicTenThirteenPatterns
import Mathlib.Order.Interval.Set.OrdConnected

open D5.S3.Combinatorics.Fishburn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenSites

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnBasicInsertion
open FishburnBasicTenThirteenPatterns

theorem interval_active_sites (n : ℕ) (p : List ℕ)
    (hparent : p ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]])
    (site : ℕ) (hsite : site ≤ p.length) :
    p.insertIdx site (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]] ↔
      (∀ before later, before + 1 = site → site ≤ later → later < p.length →
        p.getD before 0 ≠ p.getD later 0 + 1) ∧
      Set.OrdConnected {value : ℕ | value ∈ p.drop site} := by
  have hvalues (value : ℕ) (hv : value ∈ p) : 1 ≤ value ∧ value ≤ n := by
    have hr := hparent.1.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hr
    obtain ⟨index, hi, heq⟩ := hr
    omega
  have hmax : ∀ value ∈ p, value < n + 1 := by
    intro value hv
    have := (hvalues value hv).2
    omega
  have hprefix (index : ℕ) (hi : index < site) : p.getD index 0 ∈ p.take site := by
    apply List.mem_take_iff_getElem.mpr
    refine ⟨index, by omega, ?_⟩
    exact (List.getD_eq_getElem p 0 (by omega)).symm
  have hsuffix (index : ℕ) (hlow : site ≤ index) (hhigh : index < p.length) :
      p.getD index 0 ∈ p.drop site := by
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨index - site, by omega, ?_⟩
    have heq : site + (index - site) = index := by omega
    simpa only [heq] using (List.getD_eq_getElem p 0 hhigh).symm
  have hprefixpos (value : ℕ) (hv : value ∈ p.take site) :
      ∃ index, index < site ∧ p.getD index 0 = value := by
    obtain ⟨index, hi, heq⟩ := List.mem_take_iff_getElem.mp hv
    exact ⟨index, by omega, (List.getD_eq_getElem p 0 (by omega)).trans heq⟩
  have hsuffixpos (value : ℕ) (hv : value ∈ p.drop site) :
      ∃ index, site ≤ index ∧ index < p.length ∧ p.getD index 0 = value := by
    obtain ⟨index, hi, heq⟩ := List.mem_drop_iff_getElem.mp hv
    exact ⟨site + index, by omega, by omega,
      (List.getD_eq_getElem p 0 (by omega)).trans heq⟩
  have hdisjoint : ∀ a ∈ p.take site, ∀ b ∈ p.drop site, a ≠ b := by
    have hnd := hparent.1.nodup_iff.mpr (List.nodup_range' 1)
    have happ : (p.take site ++ p.drop site).Nodup := by simpa using hnd
    exact (List.nodup_append.mp happ).2.2
  have hinterval :
      (¬ ∃ first second third, first < site ∧ site ≤ second ∧ second < third ∧
          third < p.length ∧ p.getD second 0 < p.getD first 0 ∧
          p.getD first 0 < p.getD third 0) ∧
      (¬ ∃ first second third, first < site ∧ site ≤ second ∧ second < third ∧
          third < p.length ∧ p.getD third 0 < p.getD first 0 ∧
          p.getD first 0 < p.getD second 0) ↔
        Set.OrdConnected {value : ℕ | value ∈ p.drop site} := by
    constructor
    · rintro ⟨hno241, hno243⟩
      constructor
      intro low hlo high hhi middle hbetween
      change middle ∈ p.drop site
      change low ∈ p.drop site at hlo
      change high ∈ p.drop site at hhi
      have hbounds : low ≤ middle ∧ middle ≤ high := hbetween
      by_contra hmissing
      have hstrict : low < middle ∧ middle < high := by
        constructor
        · by_contra hnot
          have heq : middle = low := by omega
          exact hmissing (heq ▸ hlo)
        · by_contra hnot
          have heq : middle = high := by omega
          exact hmissing (heq ▸ hhi)
      have hlov := hvalues low ((List.drop_sublist site p).subset hlo)
      have hhiv := hvalues high ((List.drop_sublist site p).subset hhi)
      have hmiddle : middle ∈ p := by
        apply hparent.1.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨middle - 1, by omega, by omega⟩
      have hpref : middle ∈ p.take site := by
        have hm : middle ∈ p.take site ++ p.drop site := by simpa using hmiddle
        exact (List.mem_append.mp hm).resolve_right hmissing
      obtain ⟨first, hf, hfirst⟩ := hprefixpos middle hpref
      obtain ⟨lower, hl, hlb, hlower⟩ := hsuffixpos low hlo
      obtain ⟨upper, hu, hub, hupper⟩ := hsuffixpos high hhi
      rcases lt_trichotomy lower upper with horder | heq | horder
      · exact hno241 ⟨first, lower, upper, hf, hl, horder, hub, by omega, by omega⟩
      · subst upper
        omega
      · exact hno243 ⟨first, upper, lower, hf, hu, horder, hlb, by omega, by omega⟩
    · intro hconn
      constructor
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        have hm : p.getD first 0 ∈ p.drop site :=
          hconn.out (hsuffix second hs (by omega)) (hsuffix third (by omega) ht)
            ⟨Nat.le_of_lt hlow, Nat.le_of_lt hhigh⟩
        exact hdisjoint _ (hprefix first hf) _ hm rfl
      · rintro ⟨first, second, third, hf, hs, hst, ht, hlow, hhigh⟩
        have hm : p.getD first 0 ∈ p.drop site :=
          hconn.out (hsuffix third (by omega) ht) (hsuffix second hs (by omega))
            ⟨Nat.le_of_lt hlow, Nat.le_of_lt hhigh⟩
        exact hdisjoint _ (hprefix first hf) _ hm rfl
  have htests := maximum_crossing_pattern_tests n p hparent.1 site hsite
  have hno241 : ¬ NonnestingDefs.Occurs [2, 4, 1, 3] p :=
    hparent.2.2 _ (by simp)
  have hno243 : ¬ NonnestingDefs.Occurs [2, 4, 3, 1] p :=
    hparent.2.2 _ (by simp)
  have hpermchild : (p.insertIdx site (n + 1)).Perm (List.range' 1 (n + 1)) := by
    apply (List.perm_insertIdx (n + 1) p hsite).trans
    apply (hparent.1.cons (n + 1)).trans
    rw [List.range'_concat]
    simpa [Nat.add_comm] using
      (List.perm_append_comm (l₁ := [n + 1]) (l₂ := List.range' 1 n))
  constructor
  · intro hchild
    refine ⟨(isFishburn_insertIdx_max_iff p (n + 1) site hsite hmax).mp hchild.2.1 |>.2,
      hinterval.mp ⟨?_, ?_⟩⟩
    · intro hbad
      exact hchild.2.2 _ (by simp) (htests.1.mpr (Or.inr hbad))
    · intro hbad
      exact hchild.2.2 _ (by simp) (htests.2.mpr (Or.inr hbad))
  · rintro ⟨heligible, hconn⟩
    have hguards := hinterval.mpr hconn
    refine ⟨hpermchild,
      (isFishburn_insertIdx_max_iff p (n + 1) site hsite hmax).mpr
        ⟨hparent.2.1, heligible⟩, ?_⟩
    intro pattern hpattern hbad
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
    rcases hpattern with rfl | rfl
    · exact (htests.1.mp hbad).elim hno241 hguards.1
    · exact (htests.2.mp hbad).elim hno243 hguards.2

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenSites


namespace D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenSiteUpdates

open D5.S3.Combinatorics Nonnesting FishburnDefs FishburnTenThirteenSites

theorem interval_site_updates (n : ℕ) (p : List ℕ) (hn : 0 < n)
    (hparent : p ∈ avoiders n [[2, 4, 1, 3], [2, 4, 3, 1]])
    (site : ℕ) (hsite : site ≤ p.length)
    (hchild : p.insertIdx site (n + 1) ∈
      avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]]) :
    (∀ gap, gap ≤ site →
      ((p.insertIdx site (n + 1)).insertIdx gap (n + 2) ∈
          avoiders (n + 2) [[2, 4, 1, 3], [2, 4, 3, 1]] ↔
        ∀ a ∈ p.take gap, ∀ b ∈ p.drop gap, a < b)) ∧
    ((p.insertIdx site (n + 1)).insertIdx (site + 1) (n + 2) ∈
        avoiders (n + 2) [[2, 4, 1, 3], [2, 4, 3, 1]] ↔ n ∈ p.take site) ∧
    (∀ gap, site < gap → gap ≤ p.length →
      ((p.insertIdx site (n + 1)).insertIdx (gap + 1) (n + 2) ∈
          avoiders (n + 2) [[2, 4, 1, 3], [2, 4, 3, 1]] ↔
        p.insertIdx gap (n + 1) ∈ avoiders (n + 1) [[2, 4, 1, 3], [2, 4, 3, 1]])) := by
  let child := p.insertIdx site (n + 1)
  have hlength : child.length = p.length + 1 :=
    List.length_insertIdx_of_le_length hsite _
  have hvalues (size : ℕ) (word : List ℕ) (hp : word.Perm (List.range' 1 size))
      (value : ℕ) (hv : value ∈ word) : 1 ≤ value ∧ value ≤ size := by
    have hm := hp.mem_iff.mp hv
    simp only [List.mem_range', Nat.one_mul] at hm
    obtain ⟨index, hi, heq⟩ := hm
    omega
  have hdisjoint (size : ℕ) (word : List ℕ) (hp : word.Perm (List.range' 1 size))
      (gap : ℕ) : ∀ a ∈ word.take gap, ∀ b ∈ word.drop gap, a ≠ b := by
    have hnd := hp.nodup_iff.mpr (List.nodup_range' 1)
    have happ : (word.take gap ++ word.drop gap).Nodup := by simpa using hnd
    exact (List.nodup_append.mp happ).2.2
  have hprefix (word : List ℕ) (gap index : ℕ) (hi : index < gap)
      (hb : index < word.length) : word.getD index 0 ∈ word.take gap := by
    apply List.mem_take_iff_getElem.mpr
    exact ⟨index, by omega, (List.getD_eq_getElem word 0 hb).symm⟩
  have hsuffix (word : List ℕ) (gap index : ℕ) (hi : gap ≤ index)
      (hb : index < word.length) : word.getD index 0 ∈ word.drop gap := by
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨index - gap, by omega, ?_⟩
    have heq : gap + (index - gap) = index := by omega
    simpa only [heq] using (List.getD_eq_getElem word 0 hb).symm
  have htop (size : ℕ) (word : List ℕ) (hp : word.Perm (List.range' 1 size))
      (gap : ℕ) (hmaximum : size ∈ word.drop gap) :
      Set.OrdConnected {value : ℕ | value ∈ word.drop gap} ↔
        ∀ a ∈ word.take gap, ∀ b ∈ word.drop gap, a < b := by
    constructor
    · intro hconn a ha b hb
      by_contra hnot
      have hav := hvalues size word hp a ((List.take_sublist gap word).subset ha)
      have hm : a ∈ word.drop gap := hconn.out hb hmaximum ⟨by omega, hav.2⟩
      exact hdisjoint size word hp gap a ha a hm rfl
    · intro hsep
      constructor
      intro low hlo high hhi middle hbetween
      have hlov := hvalues size word hp low ((List.drop_sublist gap word).subset hlo)
      have hhiv := hvalues size word hp high ((List.drop_sublist gap word).subset hhi)
      have hbounds : low ≤ middle ∧ middle ≤ high := hbetween
      have hm : middle ∈ word := by
        apply hp.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨middle - 1, by omega, by omega⟩
      have happ : middle ∈ word.take gap ++ word.drop gap := by simpa using hm
      rcases List.mem_append.mp happ with hpref | hsuf
      · have := hsep middle hpref low hlo
        omega
      · exact hsuf
  have hat : child.getD site 0 = n + 1 := by
    rw [List.getD_eq_getElem child 0 (by omega)]
    exact List.getElem_insertIdx_self _
  have hafter (index : ℕ) (hi : site < index) (hb : index < child.length) :
      child.getD index 0 = p.getD (index - 1) 0 := by
    rw [List.getD_eq_getElem child 0 hb, List.getElem_insertIdx_of_gt hi,
      List.getD_eq_getElem p 0 (by omega)]
  have hdrop (gap : ℕ) (hlo : site ≤ gap) (hhi : gap ≤ p.length) :
      child.drop (gap + 1) = p.drop gap := by
    apply List.ext_getElem
    · simp only [List.length_drop]
      omega
    · intro index hfirst hsecond
      rw [List.getElem_drop, List.getElem_drop]
      simp only [List.length_drop] at hfirst hsecond
      change (p.insertIdx site (n + 1))[gap + 1 + index]'(by
        change gap + 1 + index < child.length
        omega) = p[gap + index]'(by omega)
      rw [List.getElem_insertIdx_of_gt (by omega)]
      congr 1
      omega
  have hbeforesep (gap : ℕ) (hg : gap ≤ site) :
      (∀ a ∈ child.take gap, ∀ b ∈ child.drop gap, a < b) ↔
        ∀ a ∈ p.take gap, ∀ b ∈ p.drop gap, a < b := by
    have htake : child.take gap = p.take gap :=
      List.take_insertIdx_eq_take_of_le p (n + 1) gap site hg
    constructor
    · intro hsep a ha b hb
      have hbchild : b ∈ child := List.subset_insertIdx p site (n + 1)
        ((List.drop_sublist gap p).subset hb)
      have hbapp : b ∈ child.take gap ++ child.drop gap := by simpa using hbchild
      rcases List.mem_append.mp hbapp with hbprefix | hbsuffix
      · rw [htake] at hbprefix
        exact False.elim (hdisjoint n p hparent.1 gap b hbprefix b hb rfl)
      · exact hsep a (htake ▸ ha) b hbsuffix
    · intro hsep a ha b hb
      rw [htake] at ha
      have hamem := (List.take_sublist gap p).subset ha
      have hbmem := (List.drop_sublist gap child).subset hb
      rcases List.eq_or_mem_of_mem_insertIdx hbmem with heq | hbold
      · have := (hvalues n p hparent.1 a hamem).2
        omega
      · have hbapp : b ∈ p.take gap ++ p.drop gap := by simpa using hbold
        rcases List.mem_append.mp hbapp with hbprefix | hbsuffix
        · have hbchildprefix : b ∈ child.take gap := htake ▸ hbprefix
          exact False.elim (hdisjoint (n + 1) child hchild.1 gap b hbchildprefix b hb rfl)
        · exact hsep a ha b hbsuffix
  have hsize : n + 1 + 1 = n + 2 := by omega
  change (∀ gap, gap ≤ site → (child.insertIdx gap (n + 2) ∈ _ ↔ _)) ∧
    (child.insertIdx (site + 1) (n + 2) ∈ _ ↔ _) ∧
    (∀ gap, site < gap → gap ≤ p.length → (child.insertIdx (gap + 1) (n + 2) ∈ _ ↔ _))
  constructor
  · intro gap hg
    have htest := interval_active_sites (n + 1) child hchild gap (by omega)
    rw [hsize] at htest
    have hmaximum : n + 1 ∈ child.drop gap := by
      rw [← hat]
      exact hsuffix child gap site hg (by omega)
    rw [htest]
    constructor
    · rintro ⟨_, hconn⟩
      exact (hbeforesep gap hg).mp ((htop (n + 1) child hchild.1 gap hmaximum).mp hconn)
    · intro hsep
      have hcsep := (hbeforesep gap hg).mpr hsep
      refine ⟨?_, (htop (n + 1) child hchild.1 gap hmaximum).mpr hcsep⟩
      intro before later hbefore hlater hbound heq
      have := hcsep _ (hprefix child gap before (by omega) (by omega)) _
        (hsuffix child gap later hlater hbound)
      omega
  constructor
  · have htest := interval_active_sites (n + 1) child hchild (site + 1) (by omega)
    rw [hsize] at htest
    have hconn := (interval_active_sites n p hparent site hsite).mp hchild |>.2
    rw [htest]
    constructor
    · rintro ⟨heligible, _⟩
      have hnmem : n ∈ p := by
        apply hparent.1.mem_iff.mpr
        simp only [List.mem_range', Nat.one_mul]
        exact ⟨n - 1, by omega, by omega⟩
      have hnapp : n ∈ p.take site ++ p.drop site := by simpa using hnmem
      rcases List.mem_append.mp hnapp with hprefixn | hsuffixn
      · exact hprefixn
      · obtain ⟨index, hi, heq⟩ := List.mem_drop_iff_getElem.mp hsuffixn
        apply False.elim
        apply heligible site (site + index + 1) rfl (by omega) (by omega)
        rw [hat, hafter (site + index + 1) (by omega) (by omega), Nat.add_sub_cancel]
        rw [List.getD_eq_getElem p 0 (by omega), heq]
    · intro hnleft
      refine ⟨?_, ?_⟩
      · intro before later hbefore hlater hbound heq
        have hb : before = site := by omega
        subst before
        rw [hat, hafter later (by omega) hbound] at heq
        have hvalue : p.getD (later - 1) 0 = n := by omega
        have hnright : n ∈ p.drop site := hvalue ▸
          hsuffix p site (later - 1) (by omega) (by omega)
        exact hdisjoint n p hparent.1 site n hnleft n hnright rfl
      · simpa only [hdrop site le_rfl hsite] using hconn
  · intro gap hg hgap
    have hnew := interval_active_sites (n + 1) child hchild (gap + 1) (by omega)
    have hold := interval_active_sites n p hparent gap hgap
    rw [hsize] at hnew
    rw [hnew, hold]
    apply and_congr
    · constructor
      · intro hneweligible before later hbefore hlater hbound heq
        apply hneweligible (before + 1) (later + 1) (by omega) (by omega) (by omega)
        rwa [hafter (before + 1) (by omega) (by omega),
          hafter (later + 1) (by omega) (by omega), Nat.add_sub_cancel]
      · intro holdeligible before later hbefore hlater hbound heq
        apply holdeligible (before - 1) (later - 1) (by omega) (by omega) (by omega)
        rwa [hafter before (by omega) (by omega), hafter later (by omega) hbound] at heq
    · rw [hdrop gap (by omega) hgap]

end D5.S3.Combinatorics.FishburnTenThirteen.FishburnTenThirteenSiteUpdates
