/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenElevenClassicalConstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenElevenClassicalConstruction
   mirror-E: none(waiver:exceptional-classical-pair-construction)
   anchors: []
   utility: none
   digest: Every bounded pair constructs an exceptional classical parent with its extra cut. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenElevenClassicalPairs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenElevenClassicalConstruction

open D5.S3.Combinatorics Nonnesting FishburnClassicalDefs FishburnTenElevenClassicalSites

theorem exceptional_pair_construction (n m k : ℕ)
    (hm : 1 ≤ m) (hmk : m < k) (hk : k ≤ n) :
    let p := k :: (List.range' 1 m).reverse ++
      ((List.range' (m + 1) (n - m)).reverse).erase k
    p ∈ classicalAvoiders n [[1, 2, 3], [3, 2, 4, 1]] ∧
      p.insertIdx (m + 1) (n + 1) ∈
        classicalAvoiders (n + 1) [[1, 2, 3], [3, 2, 4, 1]] := by
  let low := (List.range' 1 m).reverse
  let high := ((List.range' (m + 1) (n - m)).reverse).erase k
  let block := k :: low
  let p := block ++ high
  change p ∈ classicalAvoiders n [[1, 2, 3], [3, 2, 4, 1]] ∧ _
  have hlowmem (value : ℕ) : value ∈ low ↔ 1 ≤ value ∧ value ≤ m := by
    simp only [low, List.mem_reverse, List.mem_range', Nat.one_mul]
    constructor
    · rintro ⟨offset, ho, he⟩
      omega
    · rintro ⟨hl, hh⟩
      exact ⟨value - 1, by omega, by omega⟩
  have hrawnodup : (List.range' (m + 1) (n - m)).reverse.Nodup :=
    List.nodup_reverse.mpr (List.nodup_range' 1)
  have hhighmem (value : ℕ) : value ∈ high ↔ m < value ∧ value ≤ n ∧ value ≠ k := by
    simp only [high, hrawnodup.mem_erase_iff, List.mem_reverse,
      List.mem_range', Nat.one_mul]
    constructor
    · rintro ⟨hne, offset, ho, he⟩
      omega
    · rintro ⟨hl, hh, hne⟩
      exact ⟨hne, value - (m + 1), by omega, by omega⟩
  have hloworder : low.Pairwise (· > ·) := by
    change (List.range' 1 m).reverse.Pairwise (· > ·)
    rw [List.pairwise_reverse]
    exact List.pairwise_lt_range'
  have hhighorder : high.Pairwise (· > ·) := by
    apply List.Pairwise.erase
    rw [List.pairwise_reverse]
    exact List.pairwise_lt_range'
  have hprefixorder : block.Pairwise (· > ·) := by
    change (k :: low).Pairwise (· > ·)
    rw [List.pairwise_cons]
    refine ⟨?_, hloworder⟩
    intro value hv
    have := (hlowmem value).mp hv
    omega
  have hprefnodup : block.Nodup := hprefixorder.imp (fun hgt => Nat.ne_of_gt hgt)
  have hhighnodup : high.Nodup := hhighorder.imp (fun hgt => Nat.ne_of_gt hgt)
  have hnodup : p.Nodup := by
    change (block ++ high).Nodup
    rw [List.nodup_append]
    refine ⟨hprefnodup, hhighnodup, ?_⟩
    intro value hp other hh hequal
    subst other
    have ht := (hhighmem value).mp hh
    have hc : value = k ∨ value ∈ low := by simpa only [block, List.mem_cons] using hp
    rcases hc with heq | hlo
    · exact ht.2.2 heq
    · have := (hlowmem value).mp hlo
      omega
  have hperm : p.Perm (List.range' 1 n) := by
    apply (List.perm_ext_iff_of_nodup hnodup (List.nodup_range' 1)).mpr
    intro value
    simp only [p, List.mem_append, block, List.mem_cons, hlowmem, hhighmem,
      List.mem_range', Nat.one_mul]
    constructor
    · intro hv
      have hb : 1 ≤ value ∧ value ≤ n := by
        rcases hv with (heq | hlo) | hhi <;> omega
      exact ⟨value - 1, by omega, by omega⟩
    · rintro ⟨offset, ho, he⟩
      by_cases heq : value = k
      · exact Or.inl (Or.inl heq)
      · by_cases hlo : value ≤ m
        · exact Or.inl (Or.inr ⟨by omega, hlo⟩)
        · exact Or.inr ⟨by omega, by omega, heq⟩
  have hprefixlen : block.length = m + 1 := by simp [block, low]
  have hlength : p.length = n := by simpa using hperm.length_eq
  have hbefore (index : ℕ) (hi : index < block.length) :
      p.getD index 0 = block.getD index 0 := by
    rw [List.getD_eq_getElem p 0 (by simp only [p, List.length_append]; omega),
      List.getD_eq_getElem block 0 hi]
    exact List.getElem_append_left hi
  have hafter (index : ℕ) (hi : block.length ≤ index) (hb : index < p.length) :
      p.getD index 0 = high.getD (index - block.length) 0 := by
    rw [List.getD_eq_getElem p 0 hb,
      List.getD_eq_getElem high 0 (by simp only [p, List.length_append] at hb; omega)]
    exact List.getElem_append_right hi
  have hprefixdec (first second : ℕ) (hfs : first < second) (hs : second < block.length) :
      p.getD second 0 < p.getD first 0 := by
    rw [hbefore first (by omega), hbefore second hs,
      List.getD_eq_getElem block 0 (by omega : first < block.length),
      List.getD_eq_getElem block 0 hs]
    exact List.pairwise_iff_getElem.mp hprefixorder first second (by omega) hs hfs
  have hhighdec (first second : ℕ) (hf : block.length ≤ first)
      (hfs : first < second) (hs : second < p.length) :
      p.getD second 0 < p.getD first 0 := by
    rw [hafter first hf (by omega), hafter second (by omega) hs,
      List.getD_eq_getElem high 0 (by
        simp only [p, List.length_append] at hs
        omega : first - block.length < high.length),
      List.getD_eq_getElem high 0 (by
        simp only [p, List.length_append] at hs
        omega : second - block.length < high.length)]
    exact List.pairwise_iff_getElem.mp hhighorder (first - block.length)
      (second - block.length) (by simp only [p, List.length_append] at hs; omega)
      (by simp only [p, List.length_append] at hs; omega) (by omega)
  have hprefixsmall (index : ℕ) (hi : 1 ≤ index) (hb : index < block.length) :
      p.getD index 0 ≤ m := by
    rw [hbefore index hb]
    have hlowbound : index - 1 < low.length := by
      simp only [block, List.length_cons] at hb
      omega
    have he : block.getD index 0 = low.getD (index - 1) 0 := by
      have hidx : index = index - 1 + 1 := by omega
      calc
        block.getD index 0 = block.getD (index - 1 + 1) 0 :=
          congrArg (fun pos => block.getD pos 0) hidx
        _ = low.getD (index - 1) 0 := List.getD_cons_succ
    rw [he, List.getD_eq_getElem low 0 hlowbound]
    exact ((hlowmem _).mp (List.getElem_mem hlowbound)).2
  have hhighlarge (index : ℕ) (hi : block.length ≤ index) (hb : index < p.length) :
      m < p.getD index 0 := by
    rw [hafter index hi hb,
      List.getD_eq_getElem high 0 (by simp only [p, List.length_append] at hb; omega)]
    exact ((hhighmem _).mp (List.getElem_mem _)).1
  have hparent : p ∈ classicalAvoiders n [[1, 2, 3], [3, 2, 4, 1]] := by
    refine ⟨hperm, ?_⟩
    intro pattern hp ho
    have hc : pattern = [1, 2, 3] ∨ pattern = [3, 2, 4, 1] := by simpa using hp
    rcases hc with rfl | rfl
    · change ArrowWilfDefs.Contains [1, 2, 3] [] 3 p at ho
      obtain ⟨values, hstep, _, hsub, _⟩ := ho
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
      obtain ⟨positions, hp⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      let first := positions ⟨0, by simp⟩
      let second := positions ⟨1, by simp⟩
      let third := positions ⟨2, by simp⟩
      have hfs : first.val < second.val :=
        positions.strictMono (by change (0 : ℕ) < 1; omega)
      have hst : second.val < third.val :=
        positions.strictMono (by change (1 : ℕ) < 2; omega)
      have hfirst : p.getD first.val 0 = values 1 := by
        rw [List.getD_eq_get]
        simpa [first] using (hp ⟨0, by simp⟩).symm
      have hsecond : p.getD second.val 0 = values 2 := by
        rw [List.getD_eq_get]
        simpa [second] using (hp ⟨1, by simp⟩).symm
      have hthird : p.getD third.val 0 = values 3 := by
        rw [List.getD_eq_get]
        simpa [third] using (hp ⟨2, by simp⟩).symm
      by_cases hleft : second.val < block.length
      · have := hprefixdec first.val second.val hfs hleft
        omega
      · have := hhighdec second.val third.val (by omega) hst third.is_lt
        omega
    · change ArrowWilfDefs.Contains [3, 2, 4, 1] [] 4 p at ho
      obtain ⟨values, hstep, _, hsub, _⟩ := ho
      have h12 : values 1 < values 2 := hstep 1 (by omega) (by omega)
      have h23 : values 2 < values 3 := hstep 2 (by omega) (by omega)
      have h34 : values 3 < values 4 := hstep 3 (by omega) (by omega)
      obtain ⟨positions, hp⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      let first := positions ⟨0, by simp⟩
      let second := positions ⟨1, by simp⟩
      let third := positions ⟨2, by simp⟩
      let fourth := positions ⟨3, by simp⟩
      have hfs : first.val < second.val :=
        positions.strictMono (by change (0 : ℕ) < 1; omega)
      have hst : second.val < third.val :=
        positions.strictMono (by change (1 : ℕ) < 2; omega)
      have htf : third.val < fourth.val :=
        positions.strictMono (by change (2 : ℕ) < 3; omega)
      have hfirst : p.getD first.val 0 = values 3 := by
        rw [List.getD_eq_get]
        simpa [first] using (hp ⟨0, by simp⟩).symm
      have hsecond : p.getD second.val 0 = values 2 := by
        rw [List.getD_eq_get]
        simpa [second] using (hp ⟨1, by simp⟩).symm
      have hthird : p.getD third.val 0 = values 4 := by
        rw [List.getD_eq_get]
        simpa [third] using (hp ⟨2, by simp⟩).symm
      have hfourth : p.getD fourth.val 0 = values 1 := by
        rw [List.getD_eq_get]
        simpa [fourth] using (hp ⟨3, by simp⟩).symm
      by_cases hthirdleft : third.val < block.length
      · have := hprefixdec first.val third.val (by omega) hthirdleft
        omega
      · by_cases hsecondright : block.length ≤ second.val
        · have := hhighdec second.val third.val hsecondright hst third.is_lt
          omega
        · have := hprefixsmall second.val (by omega) (by omega)
          have := hhighlarge fourth.val (by omega) fourth.is_lt
          omega
  refine ⟨hparent, ?_⟩
  apply (classical_active_sites n p hparent (m + 1) (by
    simp only [p, List.length_append, hprefixlen]; omega)).mpr
  right
  constructor
  · have ht : p.take (m + 1) = block := by
      rw [← hprefixlen]
      exact List.take_left
    rw [ht]
    exact hprefixorder
  · intro later hl hb
    have := hprefixsmall 1 (by omega) (by omega)
    have := hhighlarge later (by omega) hb
    omega

end D5.S3.Combinatorics.Fishburn.FishburnTenElevenClassicalConstruction
