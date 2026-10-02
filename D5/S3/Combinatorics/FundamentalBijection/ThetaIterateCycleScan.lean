/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleScan
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaIterateCycleScan
   mirror-E: none(waiver:one-cycle-scan-for-the-forced-family)
   anchors: []
   utility: none
   digest: Avoidance forces a half-size tail bound and a descending low run in a cycle word. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaIterateHighScan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleScan

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.ArcherCyclicDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycle
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateRecords
open D5.S3.Combinatorics.FundamentalBijection.ThetaIterateHighScan

theorem terminal_value_at_least_half (r q : List ℕ) (v : ℕ)
    (hr : r.Perm (List.range' 1 r.length)) (hsize : 4 ≤ r.length)
    (hq : q.Perm (List.range' 1 q.length)) (hlen : q.length = r.length)
    (hcycle : q.getD 0 0 = r.length)
    (hmap : ∀ x, 1 ≤ x → x ≤ r.length → hat q x = image r x)
    (hfirst : r.getD 0 0 = r.length)
    (hsecond : r.getD 1 0 = r.length - 1)
    (hpenult : r.getD (r.length - 2) 0 = 1)
    (hlast : r.getD (r.length - 1) 0 = v) (hv : 2 ≤ v)
    (hravoid : ¬ Contains [1, 3, 2] [] 3 r)
    (hbavoid : ¬ Contains [1, 3, 2] [] 3 (b r))
    (hqavoid : ¬ Contains [1, 3, 2] [] 3 q) : r.length ≤ 2 * v := by
  have contains132_iff_indices (p : List ℕ) :
      Contains [1, 3, 2] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[i.val] < p[k.val] ∧
          p[k.val] < p[j.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩
      change List.Sublist [x 1, x 3, x 2] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 1 := by
        simpa using (hf ⟨0, by simp⟩).symm
      have h1 : p[(f ⟨1, by simp⟩).val] = x 3 := by
        simpa using (hf ⟨1, by simp⟩).symm
      have h2 : p[(f ⟨2, by simp⟩).val] = x 2 := by
        simpa using (hf ⟨2, by simp⟩).symm
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
        f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
      · simpa only [h0, h2] using hlt 1 (by omega) (by omega)
      · simpa only [h2, h1] using hlt 2 (by omega) (by omega)
    · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
      let x : ℕ → ℕ := fun t => if t = 1 then p[i.val] else if t = 2 then p[k.val]
        else p[j.val]
      have hx1 : x 1 = p[i.val] := by simp [x]
      have hx2 : x 2 = p[k.val] := by simp [x]
      have hx3 : x 3 = p[j.val] := by simp [x]
      have hsub : List.Sublist [p[i.val], p[j.val], p[k.val]] p := by
        let f : Fin 3 → Fin p.length := fun t =>
          if t.val = 0 then i else if t.val = 1 then j else k
        have hf : StrictMono f := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all [f]; omega
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
        intro t
        fin_cases t <;> simp [f]
      refine ⟨x, ?_, ?_, ?_, by simp⟩
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 := by omega
        rcases h with rfl | rfl <;> simp [hx1, hx2, hx3, hik, hkj]
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases h with rfl | rfl | rfl <;> simp [hx1, hx2, hx3]
      · simpa [hx1, hx2, hx3] using hsub

  have hat_one_block (word : List ℕ)
      (hmaximum : ∀ value ∈ word, value ≤ word.getD 0 0)
      (value : ℕ) (hvalue : value ∈ word) :
      hat word value = if word.idxOf value + 1 < word.length then
        word.getD (word.idxOf value + 1) 0 else word.getD 0 0 := by
    have hindex : word.idxOf value < word.length :=
      List.idxOf_lt_length_of_mem hvalue
    have hnonrecord (index : ℕ) (hpositive : 0 < index) (hbound : index < word.length) :
        ¬ IsLtrMax word index := by
      intro hrecord
      have hlt := hrecord 0 hpositive
      have hmember : word.getD index 0 ∈ word := by
        rw [List.getD_eq_getElem _ 0 hbound]
        exact List.getElem_mem hbound
      have hle := hmaximum _ hmember
      omega
    have hgreatest : Nat.findGreatest (IsLtrMax word) (word.idxOf value) = 0 := by
      apply Nat.findGreatest_eq_zero_iff.mpr
      intro index hpositive hbound
      exact hnonrecord index hpositive (by omega)
    unfold hat
    by_cases hnext : word.idxOf value + 1 < word.length
    · rw [if_pos ⟨hnext, hnonrecord _ (by omega) hnext⟩, if_pos hnext]
    · rw [if_neg (fun hcase => hnext hcase.1), if_neg hnext, hgreatest]
  by_contra hnot
  let h := r.length
  have hvsmall : 2 * v < h := by omega
  have hrun := high_prefix_descending r v hr hsize hfirst hsecond hpenult hlast
    hv hravoid hbavoid
  have hnd : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
  have hval (i : ℕ) (hi : i < q.length) : 1 ≤ q.getD i 0 ∧ q.getD i 0 ≤ h := by
    have hm : q.getD i 0 ∈ q := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_mem hi
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp hm)
    omega
  have hmax : ∀ x ∈ q, x ≤ q.getD 0 0 := by
    intro x hx
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp hx)
    omega
  have hidx (i : ℕ) (hi : i < q.length) : q.idxOf (q.getD i 0) = i := by
    rw [List.getD_eq_getElem _ 0 hi]
    simpa using List.get_idxOf hnd ⟨i, hi⟩
  have hhmem : h ∈ q := hq.mem_iff.mpr
    (List.mem_range'.mpr ⟨h - 1, by omega, by omega⟩)
  have hhidx : q.idxOf h = 0 := by
    have hi := hidx 0 (by omega)
    rwa [hcycle] at hi
  have hhatmax : hat q h = v := by
    rw [hmap h (by omega) (le_refl _)]
    exact hlast
  have hqsecond : q.getD 1 0 = v := by
    have hedge := hat_one_block q hmax h hhmem
    rw [hhidx, if_pos (by omega)] at hedge
    exact hedge.symm.trans hhatmax
  have hvmem : v ∈ q := hq.mem_iff.mpr
    (List.mem_range'.mpr ⟨v - 1, by omega, by omega⟩)
  have hvidx : q.idxOf v = 1 := by
    have hi := hidx 1 (by omega)
    rwa [hqsecond] at hi
  have hhatv : hat q v = h + 1 - v := by
    rw [hmap v (by omega) (by omega)]
    change r.getD (v - 1) 0 = h + 1 - v
    have heq := hrun (v - 1) (by omega)
    have hsub : h - (v - 1) = h + 1 - v := by omega
    exact heq.trans hsub
  have hqthird : q.getD 2 0 = h + 1 - v := by
    have hedge := hat_one_block q hmax v hvmem
    rw [hvidx, if_pos (by omega)] at hedge
    exact hedge.symm.trans hhatv
  have hmiddlemem : v + 1 ∈ q := hq.mem_iff.mpr
    (List.mem_range'.mpr ⟨v, by omega, by omega⟩)
  let k := q.idxOf (v + 1)
  have hklen : k < q.length := List.idxOf_lt_length_of_mem hmiddlemem
  have hkval : q.getD k 0 = v + 1 := by
    rw [List.getD_eq_getElem _ 0 hklen]
    exact List.getElem_idxOf hklen
  have hkafter : 2 < k := by
    by_contra hnot
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hcases with heq | heq | heq
    · rw [heq, hcycle] at hkval
      omega
    · rw [heq, hqsecond] at hkval
      omega
    · rw [heq, hqthird] at hkval
      omega
  apply hqavoid
  apply (contains132_iff_indices q).mpr
  refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ⟨k, hklen⟩, by simp, hkafter, ?_, ?_⟩
  · have hlt : q.getD 1 0 < q.getD k 0 := by rw [hqsecond, hkval]; omega
    simpa only [← List.getD_eq_getElem _ 0 (by omega : 1 < q.length),
      ← List.getD_eq_getElem _ 0 hklen] using hlt
  · have hlt : q.getD k 0 < q.getD 2 0 := by rw [hkval, hqthird]; omega
    simpa only [← List.getD_eq_getElem _ 0 hklen,
      ← List.getD_eq_getElem _ 0 (by omega : 2 < q.length)] using hlt

theorem low_suffix_descending (r q : List ℕ) (v : ℕ)
    (hr : r.Perm (List.range' 1 r.length)) (hsize : 4 ≤ r.length)
    (hq : q.Perm (List.range' 1 q.length)) (hlen : q.length = r.length)
    (hcycle : q.getD 0 0 = r.length)
    (hmap : ∀ x, 1 ≤ x → x ≤ r.length → hat q x = image r x)
    (hfirst : r.getD 0 0 = r.length)
    (hsecond : r.getD 1 0 = r.length - 1)
    (hpenult : r.getD (r.length - 2) 0 = 1)
    (hlast : r.getD (r.length - 1) 0 = v)
    (hv : 2 ≤ v) (hsmall : v < r.length - 2)
    (hravoid : ¬ Contains [1, 3, 2] [] 3 r)
    (hbavoid : ¬ Contains [1, 3, 2] [] 3 (b r))
    (hqavoid : ¬ Contains [1, 3, 2] [] 3 q) :
    ∀ i, v ≤ i → i < r.length - 2 → r.getD i 0 = r.length - 1 - i := by
  have contains132_iff_indices (p : List ℕ) :
      Contains [1, 3, 2] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[i.val] < p[k.val] ∧
          p[k.val] < p[j.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩
      change List.Sublist [x 1, x 3, x 2] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 1 := by
        simpa using (hf ⟨0, by simp⟩).symm
      have h1 : p[(f ⟨1, by simp⟩).val] = x 3 := by
        simpa using (hf ⟨1, by simp⟩).symm
      have h2 : p[(f ⟨2, by simp⟩).val] = x 2 := by
        simpa using (hf ⟨2, by simp⟩).symm
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
        f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
      · simpa only [h0, h2] using hlt 1 (by omega) (by omega)
      · simpa only [h2, h1] using hlt 2 (by omega) (by omega)
    · rintro ⟨i, j, k, hij, hjk, hik, hkj⟩
      let x : ℕ → ℕ := fun t => if t = 1 then p[i.val] else if t = 2 then p[k.val]
        else p[j.val]
      have hx1 : x 1 = p[i.val] := by simp [x]
      have hx2 : x 2 = p[k.val] := by simp [x]
      have hx3 : x 3 = p[j.val] := by simp [x]
      have hsub : List.Sublist [p[i.val], p[j.val], p[k.val]] p := by
        let f : Fin 3 → Fin p.length := fun t =>
          if t.val = 0 then i else if t.val = 1 then j else k
        have hf : StrictMono f := by
          intro a b hab
          fin_cases a <;> fin_cases b <;> simp_all [f]; omega
        apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
        refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
        intro t
        fin_cases t <;> simp [f]
      refine ⟨x, ?_, ?_, ?_, by simp⟩
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 := by omega
        rcases h with rfl | rfl <;> simp [hx1, hx2, hx3, hik, hkj]
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases h with rfl | rfl | rfl <;> simp [hx1, hx2, hx3]
      · simpa [hx1, hx2, hx3] using hsub

  have hat_one_block (word : List ℕ)
      (hmaximum : ∀ value ∈ word, value ≤ word.getD 0 0)
      (value : ℕ) (hvalue : value ∈ word) :
      hat word value = if word.idxOf value + 1 < word.length then
        word.getD (word.idxOf value + 1) 0 else word.getD 0 0 := by
    have hindex : word.idxOf value < word.length :=
      List.idxOf_lt_length_of_mem hvalue
    have hnonrecord (index : ℕ) (hpositive : 0 < index) (hbound : index < word.length) :
        ¬ IsLtrMax word index := by
      intro hrecord
      have hlt := hrecord 0 hpositive
      have hmember : word.getD index 0 ∈ word := by
        rw [List.getD_eq_getElem _ 0 hbound]
        exact List.getElem_mem hbound
      have hle := hmaximum _ hmember
      omega
    have hgreatest : Nat.findGreatest (IsLtrMax word) (word.idxOf value) = 0 := by
      apply Nat.findGreatest_eq_zero_iff.mpr
      intro index hpositive hbound
      exact hnonrecord index hpositive (by omega)
    unfold hat
    by_cases hnext : word.idxOf value + 1 < word.length
    · rw [if_pos ⟨hnext, hnonrecord _ (by omega) hnext⟩, if_pos hnext]
    · rw [if_neg (fun hcase => hnext hcase.1), if_neg hnext, hgreatest]
  let h := r.length
  let d := h - v
  have hd : 3 ≤ d := by omega
  have hdv : d ≤ v := by
    have hhalf := terminal_value_at_least_half r q v hr hsize hq hlen hcycle
      hmap hfirst hsecond hpenult hlast hv hravoid hbavoid hqavoid
    omega
  have hrun := high_prefix_descending r v hr hsize hfirst hsecond hpenult hlast
    hv hravoid hbavoid
  have hnd : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
  have hmem (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) : x ∈ q := by
    apply hq.mem_iff.mpr
    exact List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩
  have hidx (i : ℕ) (hi : i < q.length) : q.idxOf (q.getD i 0) = i := by
    rw [List.getD_eq_getElem _ 0 hi]
    simpa using List.get_idxOf hnd ⟨i, hi⟩
  have hpos (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) : q.idxOf x < q.length :=
    List.idxOf_lt_length_of_mem (hmem x hx hxh)
  have hget (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h) :
      q.getD (q.idxOf x) 0 = x := by
    rw [List.getD_eq_getElem _ 0 (hpos x hx hxh)]
    exact List.getElem_idxOf (hpos x hx hxh)
  have hmax : ∀ x ∈ q, x ≤ q.getD 0 0 := by
    intro x hx
    obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp hx)
    omega
  have hbad (i j k : ℕ) (hi : i < q.length) (hj : j < q.length)
      (hk : k < q.length) (hij : i < j) (hjk : j < k)
      (hik : q.getD i 0 < q.getD k 0) (hkj : q.getD k 0 < q.getD j 0) :
      False := by
    apply hqavoid
    apply (contains132_iff_indices q).mpr
    refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩, hij, hjk, ?_, ?_⟩
    · simpa only [← List.getD_eq_getElem _ 0 hi,
        ← List.getD_eq_getElem _ 0 hk] using hik
    · simpa only [← List.getD_eq_getElem _ 0 hk,
        ← List.getD_eq_getElem _ 0 hj] using hkj
  have hhidx : q.idxOf h = 0 := by
    have heq := hidx 0 (by omega)
    rwa [hcycle] at heq
  have hqsecond : q.getD 1 0 = v := by
    have hedge := hat_one_block q hmax h (hmem h (by omega) (le_refl _))
    rw [hhidx, if_pos (by omega), hmap h (by omega) (le_refl _)] at hedge
    change r.getD (h - 1) 0 = q.getD 1 0 at hedge
    exact hedge.symm.trans hlast
  have hvidx : q.idxOf v = 1 := by
    have heq := hidx 1 (by omega)
    rwa [hqsecond] at heq
  have hafter (x : ℕ) (hx : v < x) (hxh : x < h) : 1 < q.idxOf x := by
    have hxpos := hpos x (by omega) (by omega)
    have hxget := hget x (by omega) (by omega)
    by_contra hnot
    have hcases : q.idxOf x = 0 ∨ q.idxOf x = 1 := by omega
    rcases hcases with heq | heq
    · rw [heq, hcycle] at hxget
      omega
    · rw [heq, hqsecond] at hxget
      omega
  have hhighorder (x y : ℕ) (hx : v < x) (hxy : x < y) (hy : y < h) :
      q.idxOf x < q.idxOf y := by
    have hpx := hpos x (by omega) (by omega)
    have hpy := hpos y (by omega) (by omega)
    have hgx := hget x (by omega) (by omega)
    have hgy := hget y (by omega) (by omega)
    have hay := hafter y (by omega) hy
    have hne : q.idxOf x ≠ q.idxOf y := by
      intro heq
      rw [heq] at hgx
      omega
    by_contra hnot
    have hyx : q.idxOf y < q.idxOf x := by omega
    exact hbad 1 (q.idxOf y) (q.idxOf x) (by omega) hpy hpx hay hyx
      (by rw [hqsecond, hgx]; omega) (by rw [hgx, hgy]; omega)
  have hedge (x : ℕ) (hx : 1 ≤ x) (hxh : x ≤ h)
      (hnoth : image r x ≠ h) :
      q.idxOf (image r x) = q.idxOf x + 1 := by
    have heq := hat_one_block q hmax x (hmem x hx hxh)
    rw [hmap x hx hxh] at heq
    by_cases hnext : q.idxOf x + 1 < q.length
    · rw [if_pos hnext] at heq
      have hnextidx := hidx (q.idxOf x + 1) hnext
      rwa [← heq] at hnextidx
    · rw [if_neg hnext, hcycle] at heq
      exact (hnoth heq).elim
  have hreflect (x : ℕ) (hx : 1 ≤ x) (hxd : x ≤ d) :
      image r x = h + 1 - x := by
    change r.getD (x - 1) 0 = h + 1 - x
    have heq := hrun (x - 1) (by omega)
    omega
  have hdedge : q.idxOf (v + 1) = q.idxOf d + 1 := by
    have heq := hreflect d (by omega) (le_refl _)
    have hsub : h + 1 - d = v + 1 := by omega
    rw [hsub] at heq
    have hnext := hedge d (by omega) (by omega) (by rw [heq]; omega)
    rwa [heq] at hnext
  have hlowpredecessor (x : ℕ) (hx : 2 ≤ x) (hxd : x < d) :
      image r (h - x) = x := by
    let high := h + 1 - x
    have hhigh : v + 1 < high ∧ high < h := by dsimp [high]; omega
    have hximage : image r x = high := hreflect x (by omega) (by omega)
    have hxedge : q.idxOf high = q.idxOf x + 1 := by
      have heq := hedge x (by omega) (by omega) (by rw [hximage]; omega)
      rwa [hximage] at heq
    have horder := hhighorder (v + 1) high (by omega) hhigh.1 hhigh.2
    have hxget := hget x (by omega) (by omega)
    have hvget := hget (v + 1) (by omega) (by omega)
    have hxne : q.idxOf x ≠ q.idxOf (v + 1) := by
      intro heq
      rw [heq] at hxget
      omega
    have hxafter : q.idxOf (v + 1) < q.idxOf x := by omega
    let before := q.idxOf x - 1
    let a := q.getD before 0
    have hbefore : before < q.length := by
      have := hpos x (by omega) (by omega)
      omega
    have hamem : a ∈ q := by
      change q.getD before 0 ∈ q
      rw [List.getD_eq_getElem _ 0 hbefore]
      exact List.getElem_mem hbefore
    have haval : 1 ≤ a ∧ a ≤ h := by
      obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp hamem)
      omega
    have haidx : q.idxOf a = before := hidx before hbefore
    have hanext : hat q a = x := by
      have heq := hat_one_block q hmax a hamem
      rw [haidx, if_pos (by
        have := hpos x (by omega) (by omega)
        dsimp [before]
        omega), show before + 1 = q.idxOf x by dsimp [before]; omega] at heq
      exact heq.trans hxget
    have haimage : image r a = x := by
      rw [← hmap a haval.1 haval.2]
      exact hanext
    have hagt : v < a := by
      by_contra hnot
      by_cases had : a ≤ d
      · have heq := hreflect a haval.1 had
        rw [haimage] at heq
        omega
      · have hgda := hget d (by omega) (by omega)
        have haget := hget a haval.1 haval.2
        have hane : q.idxOf a ≠ q.idxOf (v + 1) := by
          intro heq
          rw [heq] at haget
          omega
        have hapast : q.idxOf (v + 1) < q.idxOf a := by
          dsimp [before] at haidx
          omega
        exact hbad (q.idxOf d) (q.idxOf (v + 1)) (q.idxOf a)
          (hpos d (by omega) (by omega)) (hpos (v + 1) (by omega) (by omega))
          (hpos a haval.1 haval.2) (by omega) hapast
          (by rw [hgda, haget]; omega) (by rw [haget, hvget]; omega)
    have halt : a < high := by
      by_contra hnot
      have hah : a < h := by
        have hne : a ≠ h := by
          intro heq
          rw [heq, hhidx] at haidx
          dsimp [before] at haidx
          have := hafter (v + 1) (by omega) (by omega)
          omega
        omega
      have hne : a ≠ high := by
        intro heq
        rw [heq] at haidx
        dsimp [before] at haidx
        omega
      have hreverse := hhighorder high a (by omega) (by omega) hah
      dsimp [before] at haidx
      omega
    have haexact : a = high - 1 := by
      by_contra hnot
      have hagap : a < high - 1 := by omega
      have hleft := hhighorder a (high - 1) hagt hagap (by omega)
      have hright := hhighorder (high - 1) high (by omega) (by omega) hhigh.2
      have hzidx : q.idxOf (high - 1) = q.idxOf x := by
        dsimp [before] at haidx
        omega
      have hzget := hget (high - 1) (by omega) (by omega)
      rw [hzidx] at hzget
      omega
    have ha : a = h - x := by dsimp [high] at haexact; omega
    rwa [ha] at haimage
  intro i hvi hih
  let x := h - 1 - i
  have hx : 2 ≤ x ∧ x < d := by dsimp [x, d, h]; omega
  have heq := hlowpredecessor x hx.1 hx.2
  change r.getD (h - x - 1) 0 = x at heq
  have hindex : h - x - 1 = i := by dsimp [x]; omega
  rwa [hindex] at heq

end D5.S3.Combinatorics.FundamentalBijection.ThetaIterateCycleScan
