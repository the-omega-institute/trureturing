/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube231LargePrefix
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube231LargePrefix
   mirror-E: none(waiver:231-large-edge-chain-prefix)
   anchors: []
   utility: none
   digest: The first forced edges of a large 231 cube cycle determine the low prefix. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube231LargePrefix

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open ThetaBasicInverse
open ThetaBasicInverseTail
open D5.S3.Combinatorics.ArrowWilfDefs

set_option maxHeartbeats 4000000 in
theorem forced_low_prefix (p q : List ℕ) (n : ℕ)
    (hp : p.Perm (List.range' 1 n)) (hq : q.Perm (List.range' 1 n))
    (hn : 11 ≤ n) (havoid : ¬ Contains [2, 3, 1] [] 3 p)
    (hqeq : q = B p) (hfixed : B (B q) = p)
    (hp0 : p.getD 0 0 = n) (hp1 : p.getD 1 0 = 1)
    (hp2 : p.getD 2 0 = n - 2) (hp3 : p.getD 3 0 = 2)
    (hplast : p.getD (n - 1) 0 = n - 1)
    (hq0 : q.getD 0 0 = n - 2)
    (hqrecord : q.getD (n - 4) 0 = n - 1)
    (hqmax : q.getD (n - 2) 0 = n)
    (hqlast : q.getD (n - 1) 0 = 1) :
    q.getD 1 0 = 4 ∧ p.getD 4 0 = 4 ∧
      p.getD 5 0 = 3 ∧ q.getD 3 0 = 3 := by
  have hat_one_block (p : List ℕ) (hmax : ∀ y ∈ p, y ≤ p.getD 0 0)
      (x : ℕ) (hx : x ∈ p) :
      hat p x = if p.idxOf x + 1 < p.length then p.getD (p.idxOf x + 1) 0
        else p.getD 0 0 := by
    have hnonrecord (i : ℕ) (hi : 0 < i) (hil : i < p.length) :
        ¬ IsLtrMax p i := by
      intro hrecord
      have hmem : p.getD i 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hil]
        exact List.getElem_mem hil
      exact (not_lt_of_ge (hmax _ hmem)) (hrecord 0 hi)
    have hgreatest (i : ℕ) (hi : i < p.length) :
        Nat.findGreatest (IsLtrMax p) i = 0 := by
      induction i with
      | zero => rfl
      | succ j ih =>
          rw [Nat.findGreatest_succ, if_neg (hnonrecord (j + 1) (by omega) hi)]
          exact ih (by omega)
    have hidx : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
    unfold hat
    dsimp only
    by_cases hnext : p.idxOf x + 1 < p.length
    · rw [if_pos ⟨hnext, hnonrecord _ (by omega) hnext⟩, if_pos hnext]
    · rw [if_neg (fun h => hnext h.1), if_neg hnext, hgreatest _ hidx]
  have last_one_forces_B_first_max (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length)) (hn : 0 < p.length)
      (hlast : p.getD (p.length - 1) 0 = 1) :
      (B p).getD 0 0 = p.length := by
    have hat_record_block_edges (p : List ℕ) (hp : p.Nodup)
        (s e : ℕ) (hse : s < e) (he : e ≤ p.length)
        (hs : IsLtrMax p s)
        (hnon : ∀ j, s < j → j < e → ¬ IsLtrMax p j)
        (hboundary : e = p.length ∨ IsLtrMax p e) :
        (∀ i, s ≤ i → i + 1 < e →
          hat p (p.getD i 0) = p.getD (i + 1) 0) ∧
        hat p (p.getD (e - 1) 0) = p.getD s 0 := by
      have hidx (i : ℕ) (hi : i < p.length) : p.idxOf (p.getD i 0) = i := by
        rw [List.getD_eq_getElem _ 0 hi]
        simpa using (List.get_idxOf hp ⟨i, hi⟩)
      have hstart : s ≤ Nat.findGreatest (IsLtrMax p) (e - 1) :=
        Nat.le_findGreatest (by omega) hs
      have hend : Nat.findGreatest (IsLtrMax p) (e - 1) ≤ e - 1 :=
        Nat.findGreatest_le _
      have hgreatest : Nat.findGreatest (IsLtrMax p) (e - 1) = s := by
        by_contra hne
        have hgt : s < Nat.findGreatest (IsLtrMax p) (e - 1) := by omega
        exact hnon _ hgt (by omega)
          (Nat.findGreatest_spec (Nat.le_sub_one_of_lt hse) hs)
      constructor
      · intro i hsi hie
        have hi : i < p.length := by omega
        have hnext : i + 1 < p.length := by omega
        have hnr : ¬ IsLtrMax p (i + 1) := hnon _ (by omega) hie
        unfold hat
        rw [hidx i hi, if_pos ⟨hnext, hnr⟩]
      · have hlast : e - 1 < p.length := by omega
        have hbranch : ¬ (e - 1 + 1 < p.length ∧ ¬ IsLtrMax p (e - 1 + 1)) := by
          rcases hboundary with h | h
          · intro h'; omega
          · intro h'; exact h'.2 (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ e)] using h)
        unfold hat
        rw [hidx _ hlast, if_neg hbranch, hgreatest]
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have h1mem : 1 ∈ p := hp.mem_iff.mpr
      (List.mem_range'.mpr ⟨0, hn, by omega⟩)
    have hnmem : p.length ∈ p := hp.mem_iff.mpr
      (List.mem_range'.mpr ⟨p.length - 1, by omega, by omega⟩)
    have hidx1 : p.idxOf 1 = p.length - 1 := by
      have hh := hnodup.idxOf_getElem (i := p.length - 1) (by omega)
      have hv : p[p.length - 1] = 1 := by
        rw [← List.getD_eq_getElem _ 0 (by omega), hlast]
      rw [hv] at hh
      exact hh
    have hidxn : p.idxOf p.length < p.length :=
      List.idxOf_lt_length_of_mem hnmem
    have hvaln : p.getD (p.idxOf p.length) 0 = p.length := by
      rw [List.getD_eq_getElem _ 0 hidxn]
      exact List.getElem_idxOf hidxn
    have hbound (j : ℕ) (hj : j < p.length) : p.getD j 0 ≤ p.length := by
      have hm : p.getD j 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 hj]
        exact List.getElem_mem hj
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hm)
      omega
    have hrecn : D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p (p.idxOf p.length) := by
      intro j hj
      have hjlt : j < p.length := by omega
      have hne : p.getD j 0 ≠ p.length := by
        intro he
        have hi : p[j] = p[p.idxOf p.length] := by
          rw [← List.getD_eq_getElem _ 0 hjlt,
            ← List.getD_eq_getElem _ 0 hidxn, he, hvaln]
        exact (by omega : j ≠ p.idxOf p.length)
          ((hnodup.getElem_inj_iff).mp hi)
      rw [hvaln]
      have hle := hbound j hjlt
      omega
    have hnon (j : ℕ) (hj : p.idxOf p.length < j) (hjlt : j < p.length) :
        ¬ D5.S3.Combinatorics.ArrowWilfDefs.IsLtrMax p j := by
      intro hrec
      have hh := hrec (p.idxOf p.length) hj
      rw [hvaln] at hh
      have hle := hbound j hjlt
      omega
    have hclose := (hat_record_block_edges p hnodup
      (p.idxOf p.length) p.length (by omega) (le_refl _) hrecn hnon
      (Or.inl rfl)).2
    rw [show p.length - 1 = p.length - 1 by rfl, hlast, hvaln] at hclose
    have hB : (B p).getD 0 0 =
        D5.S3.Combinatorics.ArrowWilfDefs.hat p 1 := by
      rw [List.getD_eq_getElem _ 0 (by simp; omega)]
      simp
    exact hB.trans hclose
  have hat_record_block_edges (p : List ℕ) (hp : p.Nodup)
      (s e : ℕ) (hse : s < e) (he : e ≤ p.length)
      (hs : IsLtrMax p s)
      (hnon : ∀ j, s < j → j < e → ¬ IsLtrMax p j)
      (hboundary : e = p.length ∨ IsLtrMax p e) :
      (∀ i, s ≤ i → i + 1 < e →
        hat p (p.getD i 0) = p.getD (i + 1) 0) ∧
      hat p (p.getD (e - 1) 0) = p.getD s 0 := by
    have hidx (i : ℕ) (hi : i < p.length) : p.idxOf (p.getD i 0) = i := by
      rw [List.getD_eq_getElem _ 0 hi]
      simpa using (List.get_idxOf hp ⟨i, hi⟩)
    have hstart : s ≤ Nat.findGreatest (IsLtrMax p) (e - 1) :=
      Nat.le_findGreatest (by omega) hs
    have hend : Nat.findGreatest (IsLtrMax p) (e - 1) ≤ e - 1 :=
      Nat.findGreatest_le _
    have hgreatest : Nat.findGreatest (IsLtrMax p) (e - 1) = s := by
      by_contra hne
      have hgt : s < Nat.findGreatest (IsLtrMax p) (e - 1) := by omega
      exact hnon _ hgt (by omega)
        (Nat.findGreatest_spec (Nat.le_sub_one_of_lt hse) hs)
    constructor
    · intro i hsi hie
      have hi : i < p.length := by omega
      have hnext : i + 1 < p.length := by omega
      have hnr : ¬ IsLtrMax p (i + 1) := hnon _ (by omega) hie
      unfold hat
      rw [hidx i hi, if_pos ⟨hnext, hnr⟩]
    · have hlast : e - 1 < p.length := by omega
      have hbranch : ¬ (e - 1 + 1 < p.length ∧ ¬ IsLtrMax p (e - 1 + 1)) := by
        rcases hboundary with h | h
        · intro h'; omega
        · intro h'; exact h'.2 (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ e)] using h)
      unfold hat
      rw [hidx _ hlast, if_neg hbranch, hgreatest]
  have B_perm (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) :
      (B p).Perm (List.range' 1 p.length) := by
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have hmem (x : ℕ) (hx : x ∈ p) : hat p x ∈ p := by
      have hi : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
      unfold hat
      dsimp only
      split_ifs with h
      · rw [List.getD_eq_getElem _ 0 h.1]
        exact List.getElem_mem h.1
      · have hg : Nat.findGreatest (IsLtrMax p) (p.idxOf x) < p.length :=
          lt_of_le_of_lt (Nat.findGreatest_le _) hi
        rw [List.getD_eq_getElem _ 0 hg]
        exact List.getElem_mem hg
    have hmapNodup : (p.map (hat p)).Nodup := hnodup.map_on (hat_inj_on p hnodup)
    have hsubset : (p.map (hat p)).toFinset ⊆ p.toFinset := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact List.mem_toFinset.mpr (hmem a ha)
    have hcard : (p.map (hat p)).toFinset.card = p.toFinset.card := by
      simp [List.card_toFinset, List.dedup_eq_self.mpr hmapNodup,
        List.dedup_eq_self.mpr hnodup]
    have heq : (p.map (hat p)).toFinset = p.toFinset :=
      Finset.eq_of_subset_of_card_le hsubset (by omega)
    have hperm : (p.map (hat p)).Perm p :=
      List.perm_of_nodup_nodup_toFinset_eq hmapNodup hnodup heq
    exact ((hp.symm.map _).trans hperm).trans hp
  have first_block_edges (q : List ℕ) (n : ℕ)
      (hq : q.Perm (List.range' 1 n)) (hn : 5 ≤ n)
      (hfirst : q.getD 0 0 = n - 2)
      (hnextrecord : q.getD (n - 4) 0 = n - 1)
      (hfinalrecord : q.getD (n - 2) 0 = n) :
      (∀ i, i + 1 < n - 4 →
        hat q (q.getD i 0) = q.getD (i + 1) 0) ∧
        hat q (q.getD (n - 5) 0) = n - 2 := by
    have hlen : q.length = n := by simpa using hq.length_eq
    have hnodup : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
    have hgetinj (i j : ℕ) (hi : i < n) (hj : j < n)
        (heq : q.getD i 0 = q.getD j 0) : i = j := by
      have helem : q[i] = q[j] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : i < q.length),
          ← List.getD_eq_getElem _ 0 (by omega : j < q.length), heq]
      exact (hnodup.getElem_inj_iff).mp helem
    have hbound (j : ℕ) (hj : j < n) : q.getD j 0 ≤ n := by
      have hm : q.getD j 0 ∈ q := by
        rw [List.getD_eq_getElem _ 0 (by omega : j < q.length)]
        exact List.getElem_mem (by omega : j < q.length)
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp hm)
      omega
    have hlow (j : ℕ) (hj : j < n - 4) : q.getD j 0 ≤ n - 2 := by
      have hjn : j < n := by omega
      have hle := hbound j hjn
      have hne1 : q.getD j 0 ≠ n - 1 := by
        intro he
        have hh := hgetinj j (n - 4) hjn (by omega) (he.trans hnextrecord.symm)
        omega
      have hnen : q.getD j 0 ≠ n := by
        intro he
        have hh := hgetinj j (n - 2) hjn (by omega) (he.trans hfinalrecord.symm)
        omega
      omega
    have hrec0 : IsLtrMax q 0 := by intro j hj; omega
    have hnon (j : ℕ) (hj : 0 < j) (hjlt : j < n - 4) :
        ¬ IsLtrMax q j := by
      intro hrec
      have hh := hrec 0 hj
      rw [hfirst] at hh
      have hle := hlow j hjlt
      omega
    have hrecnext : IsLtrMax q (n - 4) := by
      intro j hj
      have hjn : j < n := by omega
      have hle := hbound j hjn
      have hne1 : q.getD j 0 ≠ n - 1 := by
        intro he
        have hh := hgetinj j (n - 4) hjn (by omega) (he.trans hnextrecord.symm)
        omega
      have hnen : q.getD j 0 ≠ n := by
        intro he
        have hh := hgetinj j (n - 2) hjn (by omega) (he.trans hfinalrecord.symm)
        omega
      rw [hnextrecord]
      omega
    have hedges := hat_record_block_edges q hnodup 0 (n - 4)
      (by omega) (by omega) hrec0 hnon (Or.inr hrecnext)
    constructor
    · intro i hi
      exact hedges.1 i (by omega) hi
    · simpa only [show n - 4 - 1 = n - 5 by omega, hfirst] using hedges.2
  have one_block_predecessor (p : List ℕ)
      (hp : p.Perm (List.range' 1 p.length))
      (hmax : ∀ y ∈ p, y ≤ p.getD 0 0)
      (x y c : ℕ) (hx : x ∈ p)
      (hc : 0 < c ∧ c < p.length)
      (hy : p.getD c 0 = y)
      (hedge : D5.S3.Combinatorics.ArrowWilfDefs.hat p x = y) :
      p.getD (c - 1) 0 = x := by
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have hix : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
    have hvalx : p.getD (p.idxOf x) 0 = x := by
      rw [List.getD_eq_getElem _ 0 hix]
      exact List.getElem_idxOf hix
    have hh := hat_one_block p hmax x hx
    rw [hedge] at hh
    have hnext : p.idxOf x + 1 < p.length := by
      by_contra hnot
      rw [if_neg (by omega : ¬ p.idxOf x + 1 < p.length)] at hh
      have helem : p[0] = p[c] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : 0 < p.length),
          ← List.getD_eq_getElem _ 0 hc.2]
        exact hh.symm.trans hy.symm
      exact (by omega : 0 ≠ c) ((hnodup.getElem_inj_iff).mp helem)
    rw [if_pos hnext] at hh
    have hidx : p.idxOf x + 1 = c := by
      have helem : p[p.idxOf x + 1] = p[c] := by
        rw [← List.getD_eq_getElem _ 0 hnext,
          ← List.getD_eq_getElem _ 0 hc.2]
        exact hh.symm.trans hy.symm
      exact (hnodup.getElem_inj_iff).mp helem
    have heq : c - 1 = p.idxOf x := by omega
    rw [heq]
    exact hvalx
  have predecessor_of_one (q : List ℕ)
      (hq : q.Perm (List.range' 1 q.length))
      (hmax : ∀ y ∈ q, y ≤ q.getD 0 0)
      (b c : ℕ) (hb : b < q.length) (hc : 0 < c ∧ c < q.length)
      (hqc : q.getD c 0 = 1) (hrb : (B q).getD b 0 = 1) :
      q.getD (c - 1) 0 = b + 1  := by
    have one_block_predecessor (p : List ℕ)
        (hp : p.Perm (List.range' 1 p.length))
        (hmax : ∀ y ∈ p, y ≤ p.getD 0 0)
        (x y c : ℕ) (hx : x ∈ p)
        (hc : 0 < c ∧ c < p.length)
        (hy : p.getD c 0 = y)
        (hedge : D5.S3.Combinatorics.ArrowWilfDefs.hat p x = y) :
        p.getD (c - 1) 0 = x := by
      have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
      have hix : p.idxOf x < p.length := List.idxOf_lt_length_of_mem hx
      have hvalx : p.getD (p.idxOf x) 0 = x := by
        rw [List.getD_eq_getElem _ 0 hix]
        exact List.getElem_idxOf hix
      have hh := hat_one_block p hmax x hx
      rw [hedge] at hh
      have hnext : p.idxOf x + 1 < p.length := by
        by_contra hnot
        rw [if_neg (by omega : ¬ p.idxOf x + 1 < p.length)] at hh
        have helem : p[0] = p[c] := by
          rw [← List.getD_eq_getElem _ 0 (by omega : 0 < p.length),
            ← List.getD_eq_getElem _ 0 hc.2]
          exact hh.symm.trans hy.symm
        exact (by omega : 0 ≠ c) ((hnodup.getElem_inj_iff).mp helem)
      rw [if_pos hnext] at hh
      have hidx : p.idxOf x + 1 = c := by
        have helem : p[p.idxOf x + 1] = p[c] := by
          rw [← List.getD_eq_getElem _ 0 hnext,
            ← List.getD_eq_getElem _ 0 hc.2]
          exact hh.symm.trans hy.symm
        exact (hnodup.getElem_inj_iff).mp helem
      have heq : c - 1 = p.idxOf x := by omega
      rw [heq]
      exact hvalx
    have hx : b + 1 ∈ q := hq.mem_iff.mpr
      (List.mem_range'.mpr ⟨b, hb, by omega⟩)
    have hedge : D5.S3.Combinatorics.ArrowWilfDefs.hat q (b + 1) = 1 := by
      rw [List.getD_eq_getElem _ 0 (by simpa using hb)] at hrb
      simpa [Nat.add_comm] using hrb
    exact one_block_predecessor q hq hmax (b + 1) 1 c hx hc hqc hedge
  have hcontains231 (p : List ℕ) :
      D5.S3.Combinatorics.ArrowWilfDefs.Contains [2, 3, 1] [] 3 p ↔
        ∃ i j k : Fin p.length, i < j ∧ j < k ∧ p[j.val] > p[i.val] ∧
        p[i.val] > p[k.val] := by
    constructor
    · rintro ⟨x, hlt, _, hsub, _⟩
      change List.Sublist [x 2, x 3, x 1] p at hsub
      obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
      have h0 : p[(f ⟨0, by simp⟩).val] = x 2 := by
        simpa using (hf ⟨0, by simp⟩).symm
      have h1 : p[(f ⟨1, by simp⟩).val] = x 3 := by
        simpa using (hf ⟨1, by simp⟩).symm
      have h2 : p[(f ⟨2, by simp⟩).val] = x 1 := by
        simpa using (hf ⟨2, by simp⟩).symm
      refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f ⟨2, by simp⟩,
        f.strictMono (by simp), f.strictMono (by simp), ?_, ?_⟩
      · simpa only [← h1, ← h0] using hlt 2 (by omega) (by omega)
      · simpa only [← h0, ← h2] using hlt 1 (by omega) (by omega)
    · rintro ⟨i, j, k, hij, hjk, hji, hik⟩
      let x : ℕ → ℕ := fun t => if t = 1 then p[k.val] else if t = 2 then p[i.val]
        else p[j.val]
      have hx1 : x 1 = p[k.val] := by simp [x]
      have hx2 : x 2 = p[i.val] := by simp [x]
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
        rcases h with rfl | rfl <;> simp [hx1, hx2, hx3, hik, hji]
      · intro t ht ht3
        have h : t = 1 ∨ t = 2 ∨ t = 3 := by omega
        rcases h with rfl | rfl | rfl <;> simp [hx1, hx2, hx3]
      · simpa [hx1, hx2, hx3] using hsub
  let r := B q
  have hplen : p.length = n := by simpa using hp.length_eq
  have hqlen : q.length = n := by simpa using hq.length_eq
  have hpnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hrperm : r.Perm (List.range' 1 n) := by
    dsimp [r]
    have hq' : q.Perm (List.range' 1 q.length) := by rw [hqlen]; exact hq
    simpa [hqlen] using B_perm q hq'
  have hrlen : r.length = n := by simp [r, hqlen]
  have hrperm' : r.Perm (List.range' 1 r.length) := by rw [hrlen]; exact hrperm
  have hpr : B r = p := by simpa [r] using hfixed
  have hB_at (w : List ℕ) (x : ℕ) (hx : 0 < x) (hle : x ≤ w.length) :
      (B w).getD (x - 1) 0 = hat w x := by
    rw [List.getD_eq_getElem _ 0 (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range'_1]
    congr 1
    omega
  have hrfirst : r.getD 0 0 = n := by
    have hq' : q.Perm (List.range' 1 q.length) := by rw [hqlen]; exact hq
    have hh := last_one_forces_B_first_max q hq' (by rw [hqlen]; omega)
      (by simpa [hqlen] using hqlast)
    simpa [r, hqlen] using hh
  have hrlast : r.getD (n - 1) 0 = 1 := by
    have hBrfirst : (B r).getD 0 0 = r.length := by rw [hpr, hrlen]; exact hp0
    have hh := B_first_max_forces_last_one r hrperm' (by rw [hrlen]; omega)
      hBrfirst
    simpa [hrlen] using hh
  have hmaxr : ∀ y ∈ r, y ≤ r.getD 0 0 := by
    intro y hy
    rw [hrfirst]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hrperm.mem_iff.mp hy)
    omega
  have hrpen : r.getD (n - 2) 0 = 2 := by
    have hh := predecessor_of_one r hrperm' hmaxr 1 (n - 1)
      (by rw [hrlen]; omega) (by rw [hrlen]; omega)
      (by simpa [hrlen] using hrlast)
      (by rw [hpr]; exact hp1)
    simpa only [show n - 1 - 1 = n - 2 by omega] using hh
  have h4memr : 4 ∈ r := hrperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨3, by omega, by omega⟩)
  have hrhatfour : hat r 4 = 2 := by
    have hh := hB_at r 4 (by omega) (by omega)
    rw [show 4 - 1 = 3 by omega, hpr, hp3] at hh
    exact hh.symm
  have hrprev : r.getD (n - 3) 0 = 4 := by
    have hh := one_block_predecessor r hrperm' hmaxr 4 2 (n - 2)
      h4memr (by rw [hrlen]; omega) hrpen hrhatfour
    simpa only [show n - 2 - 1 = n - 3 by omega] using hh
  have hqblock := first_block_edges q n hq (by omega) hq0 hqrecord hqmax
  have hqone : q.getD 1 0 = 4 := by
    have hh := hqblock.1 0 (by omega)
    rw [hq0] at hh
    have hb := hB_at q (n - 2) (by omega) (by omega)
    rw [show n - 2 - 1 = n - 3 by omega] at hb
    change r.getD (n - 3) 0 = hat q (n - 2) at hb
    rw [hrprev] at hb
    simpa only [show 0 + 1 = 1 by omega] using hh.symm.trans hb.symm
  have hmaxp : ∀ y ∈ p, y ≤ p.getD 0 0 := by
    intro y hy
    rw [hp0]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hy)
    omega
  have h2memp : 2 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨1, by omega, by omega⟩)
  have hidx2 : p.idxOf 2 = 3 := by
    have hi := hpnodup.idxOf_getElem (i := 3) (by omega : 3 < p.length)
    have hv : p[3] = 2 := by
      rw [← List.getD_eq_getElem _ 0 (by omega : 3 < p.length), hp3]
    rw [hv] at hi
    exact hi
  have hpfour : p.getD 4 0 = 4 := by
    have hh := hB_at p 2 (by omega) (by omega)
    rw [show 2 - 1 = 1 by omega, ← hqeq, hqone] at hh
    rw [hat_one_block p hmaxp 2 h2memp, hidx2] at hh
    rw [if_pos (by omega : 3 + 1 < p.length)] at hh
    simpa only [show 3 + 1 = 4 by omega] using hh.symm
  have h3memp : 3 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨2, by omega, by omega⟩)
  have hidx3 : p.idxOf 3 < n := by
    simpa [hplen] using List.idxOf_lt_length_of_mem h3memp
  have h3val : p.getD (p.idxOf 3) 0 = 3 := by
    rw [List.getD_eq_getElem _ 0 (by omega : p.idxOf 3 < p.length)]
    exact List.getElem_idxOf (by omega : p.idxOf 3 < p.length)
  have h3after : 4 < p.idxOf 3 := by
    have hne (j : ℕ) (hj : j < n) (hv : p.getD j 0 ≠ 3) : j ≠ p.idxOf 3 := by
      intro he
      rw [he, h3val] at hv
      exact hv rfl
    have h0 := hne 0 (by omega) (by rw [hp0]; omega)
    have h1 := hne 1 (by omega) (by rw [hp1]; omega)
    have h2 := hne 2 (by omega) (by rw [hp2]; omega)
    have h3 := hne 3 (by omega) (by rw [hp3]; omega)
    have h4 := hne 4 (by omega) (by rw [hpfour]; omega)
    omega
  have hpfive : p.getD 5 0 = 3 := by
    by_contra hnot
    have hidxgt : 5 < p.idxOf 3 := by
      have hne : p.idxOf 3 ≠ 5 := by
        intro he
        rw [he] at h3val
        exact hnot h3val
      omega
    let z := p.getD 5 0
    have hzmem : z ∈ p := by
      dsimp [z]
      rw [List.getD_eq_getElem _ 0 (by omega : 5 < p.length)]
      exact List.getElem_mem (by omega : 5 < p.length)
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hzmem)
    have hzne (j : ℕ) (hj : j < n) (hje : j ≠ 5)
        (hv : p.getD j 0 = z) : False := by
      have helem : p[j] = p[5] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : j < p.length),
          ← List.getD_eq_getElem _ 0 (by omega : 5 < p.length), hv]
      exact hje ((hpnodup.getElem_inj_iff).mp helem)
    have hzgt : 4 < z := by
      have hz1 : z ≠ 1 := by
        intro he; apply hzne 1 (by omega) (by omega); rw [hp1]; exact he.symm
      have hz2 : z ≠ 2 := by
        intro he; apply hzne 3 (by omega) (by omega); rw [hp3]; exact he.symm
      have hz3 : z ≠ 3 := by
        intro he; apply hzne (p.idxOf 3) hidx3 (by omega)
        rw [h3val]; exact he.symm
      have hz4 : z ≠ 4 := by
        intro he; apply hzne 4 (by omega) (by omega); rw [hpfour]; exact he.symm
      omega
    apply havoid
    apply (hcontains231 p).mpr
    refine ⟨⟨4, by omega⟩, ⟨5, by omega⟩,
      ⟨p.idxOf 3, by omega⟩, (by change 4 < 5; omega),
      (by change 5 < p.idxOf 3; exact hidxgt), ?_, ?_⟩
    · rw [← List.getD_eq_getElem _ 0 (by omega : 4 < p.length),
        ← List.getD_eq_getElem _ 0 (by omega : 5 < p.length), hpfour]
      exact hzgt
    · rw [← List.getD_eq_getElem _ 0 (by omega : 4 < p.length),
        ← List.getD_eq_getElem _ 0 (by omega : p.idxOf 3 < p.length),
        hpfour, h3val]
      omega
  have h4memp : 4 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨3, by omega, by omega⟩)
  have hidx4 : p.idxOf 4 = 4 := by
    have hi := hpnodup.idxOf_getElem (i := 4) (by omega : 4 < p.length)
    have hv : p[4] = 4 := by
      rw [← List.getD_eq_getElem _ 0 (by omega : 4 < p.length), hpfour]
    rw [hv] at hi
    exact hi
  have hqthree : q.getD 3 0 = 3 := by
    have hh := hB_at p 4 (by omega) (by omega)
    rw [show 4 - 1 = 3 by omega, ← hqeq] at hh
    rw [hat_one_block p hmaxp 4 h4memp, hidx4] at hh
    rw [if_pos (by omega : 4 + 1 < p.length)] at hh
    simpa only [show 4 + 1 = 5 by omega, hpfive] using hh
  exact ⟨hqone, hpfour, hpfive, hqthree⟩

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube231LargePrefix
