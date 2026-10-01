/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube231LargeFinish
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube231LargeFinish
   mirror-E: none(waiver:231-large-edge-chain-collision)
   anchors: []
   utility: none
   digest: The large 231 inverse edge chain assigns six to two distinct positions. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseTail
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Boundary
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Return
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Shape
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231SecondReturn
import D5.S3.Combinatorics.FundamentalBijection.ThetaCube231LargePrefix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube231LargeFinish

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open ThetaBasicInverse
open ThetaBasicInverseTail ThetaBasicSumIndecomp
open ThetaCube231Boundary ThetaCube231Return ThetaCube231Shape
open ThetaCube231SecondReturn ThetaCube231LargePrefix
open D5.S3.Combinatorics.ArrowWilfDefs

set_option maxHeartbeats 1000000 in
theorem large_edge_collision (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 11 ≤ p.length)
    (hindecomp : ∀ k, 0 < k → k < p.length → ∃ x ∈ p.take k, k < x)
    (havoid : ¬ Contains [2, 3, 1] [] 3 p)
    (hfixed : B (B (B p)) = p) : False := by
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
  have collision (p q : List ℕ) (n : ℕ)
      (hp : p.Perm (List.range' 1 n)) (hq : q.Perm (List.range' 1 n))
      (hn : 11 ≤ n) (hqeq : q = B p) (hfixed : B (B q) = p)
      (hp0 : p.getD 0 0 = n) (hp4 : p.getD 4 0 = 4)
      (hp5 : p.getD 5 0 = 3)
      (hpp : p.getD (n - 2) 0 = n - 3)
      (hplast : p.getD (n - 1) 0 = n - 1)
      (hq0 : q.getD 0 0 = n - 2)
      (hq1 : q.getD 1 0 = 4)
      (hq3 : q.getD 3 0 = 3)
      (hqrecord : q.getD (n - 4) 0 = n - 1)
      (hqmax : q.getD (n - 2) 0 = n)
      (hqlast : q.getD (n - 1) 0 = 1) : False := by
    let r := B q
    have hplen : p.length = n := by simpa using hp.length_eq
    have hqlen : q.length = n := by simpa using hq.length_eq
    have hpnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have hqnodup : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
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
    have hmaxp : ∀ y ∈ p, y ≤ p.getD 0 0 := by
      intro y hy
      rw [hp0]
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hy)
      omega
    have hrfirst : r.getD 0 0 = n := by
      have hq' : q.Perm (List.range' 1 q.length) := by rw [hqlen]; exact hq
      have hh := last_one_forces_B_first_max q hq' (by rw [hqlen]; omega)
        (by simpa [hqlen] using hqlast)
      simpa [r, hqlen] using hh
    have hmaxr : ∀ y ∈ r, y ≤ r.getD 0 0 := by
      intro y hy
      rw [hrfirst]
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hrperm.mem_iff.mp hy)
      omega
    have hqblock := first_block_edges q n hq (by omega) hq0 hqrecord hqmax
    have hrprevfour : r.getD (n - 3) 0 = 4 := by
      have hh := hqblock.1 0 (by omega)
      rw [hq0, show 0 + 1 = 1 by omega, hq1] at hh
      have hb := hB_at q (n - 2) (by omega) (by omega)
      rw [show n - 2 - 1 = n - 3 by omega] at hb
      change r.getD (n - 3) 0 = hat q (n - 2) at hb
      exact hb.trans hh
    have hrnmem : n ∈ r := hrperm.mem_iff.mpr
      (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
    have hrnodup : r.Nodup := hrperm.nodup_iff.mpr List.nodup_range'
    have hridxn : r.idxOf n = 0 := by
      have hi := hrnodup.idxOf_getElem (i := 0) (by omega : 0 < r.length)
      have hv : r[0] = n := by
        rw [← List.getD_eq_getElem _ 0 (by omega : 0 < r.length), hrfirst]
      rw [hv] at hi
      exact hi
    have hrtwo : r.getD 1 0 = n - 1 := by
      have hh := hB_at r n (by omega) (by omega)
      rw [hpr, hplast] at hh
      rw [hat_one_block r hmaxr n hrnmem, hridxn] at hh
      rw [if_pos (by omega : 0 + 1 < r.length)] at hh
      simpa only [show 0 + 1 = 1 by omega] using hh.symm
    have hnm1memr : n - 1 ∈ r := hrperm.mem_iff.mpr
      (List.mem_range'.mpr ⟨n - 2, by omega, by omega⟩)
    have hridxnm1 : r.idxOf (n - 1) = 1 := by
      have hi := hrnodup.idxOf_getElem (i := 1) (by omega : 1 < r.length)
      have hv : r[1] = n - 1 := by
        rw [← List.getD_eq_getElem _ 0 (by omega : 1 < r.length), hrtwo]
      rw [hv] at hi
      exact hi
    have hrthree : r.getD 2 0 = n - 3 := by
      have hh := hB_at r (n - 1) (by omega) (by omega)
      rw [show n - 1 - 1 = n - 2 by omega, hpr, hpp] at hh
      rw [hat_one_block r hmaxr (n - 1) hnm1memr, hridxnm1] at hh
      rw [if_pos (by omega : 1 + 1 < r.length)] at hh
      simpa only [show 1 + 1 = 2 by omega] using hh.symm
    have h3memq : 3 ∈ q := hq.mem_iff.mpr
      (List.mem_range'.mpr ⟨2, by omega, by omega⟩)
    have hidx3q : q.idxOf 3 = 3 := by
      have hi := hqnodup.idxOf_getElem (i := 3) (by omega : 3 < q.length)
      have hv : q[3] = 3 := by
        rw [← List.getD_eq_getElem _ 0 (by omega : 3 < q.length), hq3]
      rw [hv] at hi
      exact hi
    have hqfour : q.getD 4 0 = n - 3 := by
      have hh := hqblock.1 3 (by omega)
      rw [hq3, show 3 + 1 = 4 by omega] at hh
      have hb := hB_at q 3 (by omega) (by omega)
      rw [show 3 - 1 = 2 by omega] at hb
      change r.getD 2 0 = hat q 3 at hb
      rw [hrthree] at hb
      exact hh.symm.trans hb.symm
    have hnm3memp : n - 3 ∈ p := hp.mem_iff.mpr
      (List.mem_range'.mpr ⟨n - 4, by omega, by omega⟩)
    have h5memp : 5 ∈ p := hp.mem_iff.mpr
      (List.mem_range'.mpr ⟨4, by omega, by omega⟩)
    have hpprevfive : p.getD (n - 3) 0 = 5 := by
      have hh := hB_at p 5 (by omega) (by omega)
      rw [show 5 - 1 = 4 by omega, ← hqeq, hqfour] at hh
      have hp' : p.Perm (List.range' 1 p.length) := by rw [hplen]; exact hp
      have hmaxp' : ∀ y ∈ p, y ≤ p.getD 0 0 := hmaxp
      have h := one_block_predecessor p hp' hmaxp' 5 (n - 3) (n - 2)
        h5memp (by rw [hplen]; omega) hpp hh.symm
      simpa only [show n - 2 - 1 = n - 3 by omega] using h
    have h5memr : 5 ∈ r := hrperm.mem_iff.mpr
      (List.mem_range'.mpr ⟨4, by omega, by omega⟩)
    have hrprevfive : r.getD (n - 4) 0 = 5 := by
      have hh := hB_at r 5 (by omega) (by omega)
      rw [show 5 - 1 = 4 by omega, hpr, hp4] at hh
      have h := one_block_predecessor r hrperm' hmaxr 5 4 (n - 3)
        h5memr (by rw [hrlen]; omega) hrprevfour hh.symm
      simpa only [show n - 3 - 1 = n - 4 by omega] using h
    have hqfive : q.getD 5 0 = 5 := by
      have hh := hqblock.1 4 (by omega)
      rw [hqfour, show 4 + 1 = 5 by omega] at hh
      have hb := hB_at q (n - 3) (by omega) (by omega)
      rw [show n - 3 - 1 = n - 4 by omega] at hb
      change r.getD (n - 4) 0 = hat q (n - 3) at hb
      rw [hrprevfive] at hb
      exact hh.symm.trans hb.symm
    have h6memp : 6 ∈ p := hp.mem_iff.mpr
      (List.mem_range'.mpr ⟨5, by omega, by omega⟩)
    have hpprevsix : p.getD (n - 4) 0 = 6 := by
      have hh := hB_at p 6 (by omega) (by omega)
      rw [show 6 - 1 = 5 by omega, ← hqeq, hqfive] at hh
      have hp' : p.Perm (List.range' 1 p.length) := by rw [hplen]; exact hp
      have h := one_block_predecessor p hp' hmaxp 6 5 (n - 3)
        h6memp (by rw [hplen]; omega) hpprevfive hh.symm
      simpa only [show n - 3 - 1 = n - 4 by omega] using h
    have hnm3memr : n - 3 ∈ r := hrperm.mem_iff.mpr
      (List.mem_range'.mpr ⟨n - 4, by omega, by omega⟩)
    have hridxnm3 : r.idxOf (n - 3) = 2 := by
      have hi := hrnodup.idxOf_getElem (i := 2) (by omega : 2 < r.length)
      have hv : r[2] = n - 3 := by
        rw [← List.getD_eq_getElem _ 0 (by omega : 2 < r.length), hrthree]
      rw [hv] at hi
      exact hi
    have hrfour : r.getD 3 0 = 6 := by
      have hh := hB_at r (n - 3) (by omega) (by omega)
      rw [show n - 3 - 1 = n - 4 by omega, hpr, hpprevsix] at hh
      rw [hat_one_block r hmaxr (n - 3) hnm3memr, hridxnm3] at hh
      rw [if_pos (by omega : 2 + 1 < r.length)] at hh
      simpa only [show 2 + 1 = 3 by omega] using hh.symm
    have h4memq : 4 ∈ q := hq.mem_iff.mpr
      (List.mem_range'.mpr ⟨3, by omega, by omega⟩)
    have hidx4q : q.idxOf 4 = 1 := by
      have hi := hqnodup.idxOf_getElem (i := 1) (by omega : 1 < q.length)
      have hv : q[1] = 4 := by
        rw [← List.getD_eq_getElem _ 0 (by omega : 1 < q.length), hq1]
      rw [hv] at hi
      exact hi
    have hqtwo : q.getD 2 0 = 6 := by
      have hh := hqblock.1 1 (by omega)
      rw [hq1, show 1 + 1 = 2 by omega] at hh
      have hb := hB_at q 4 (by omega) (by omega)
      rw [show 4 - 1 = 3 by omega] at hb
      change r.getD 3 0 = hat q 4 at hb
      rw [hrfour] at hb
      exact hh.symm.trans hb.symm
    have h3memp : 3 ∈ p := hp.mem_iff.mpr
      (List.mem_range'.mpr ⟨2, by omega, by omega⟩)
    have hidx3p : p.idxOf 3 = 5 := by
      have hi := hpnodup.idxOf_getElem (i := 5) (by omega : 5 < p.length)
      have hv : p[5] = 3 := by
        rw [← List.getD_eq_getElem _ 0 (by omega : 5 < p.length), hp5]
      rw [hv] at hi
      exact hi
    have hpsix : p.getD 6 0 = 6 := by
      have hh := hB_at p 3 (by omega) (by omega)
      rw [show 3 - 1 = 2 by omega, ← hqeq, hqtwo] at hh
      rw [hat_one_block p hmaxp 3 h3memp, hidx3p] at hh
      rw [if_pos (by omega : 5 + 1 < p.length)] at hh
      simpa only [show 5 + 1 = 6 by omega] using hh.symm
    have helem : p[6] = p[n - 4] := by
      rw [← List.getD_eq_getElem _ 0 (by omega : 6 < p.length),
        ← List.getD_eq_getElem _ 0 (by omega : n - 4 < p.length),
        hpsix, hpprevsix]
    have hpos := (hpnodup.getElem_inj_iff).mp helem
    omega
  let n := p.length; let q := B p; have hfirst : p.getD 0 0 = n :=
    (avoid231_indecomp_iff_first_max p hp (by omega) havoid).mp hindecomp
  have hboundary := terminal_value_next_to_max p hp (by omega) hindecomp havoid hfixed
  have hlast : p.getD (n - 1) 0 = n - 1 := hboundary.1
  have hsecond : p.getD 1 0 = 1 := hboundary.2
  have hreturn := penultimate_block_ends_two p hp (by omega) hfirst hsecond hlast hfixed
  have hshape := return_edge_forces_initial_pair p hp (by omega)
    havoid hfirst hsecond hlast hreturn
  have hpen := penultimate_value p hp (by omega) hfirst hsecond hlast hreturn hfixed
  have hqperm : q.Perm (List.range' 1 n) := by
    dsimp [q, n]; exact B_perm p hp
  have hpnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hmaxp : ∀ y ∈ p, y ≤ p.getD 0 0 := by
    intro y hy; rw [hfirst]; obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hy); omega
  have hB_at (x : ℕ) (hx : 0 < x) (hle : x ≤ n) : q.getD (x - 1) 0 = hat p x := by
    rw [List.getD_eq_getElem _ 0 (by simp [q, n]; omega)]
    simp only [q, List.getElem_map, List.getElem_range'_1]; congr 1; omega
  have hidx1 : p.idxOf 1 = 1 := by
    have hi := hpnodup.idxOf_getElem (i := 1) (by omega : 1 < p.length)
    have hv : p[1] = 1 := (by rw [← List.getD_eq_getElem _ 0 (by omega : 1 < p.length), hsecond])
    rw [hv] at hi; exact hi
  have h1mem : 1 ∈ p := hp.mem_iff.mpr (List.mem_range'.mpr ⟨0, by omega, by omega⟩)
  have hqfirst : q.getD 0 0 = n - 2 := by
    have hh := hB_at 1 (by omega) (by omega); rw [hat_one_block p hmaxp 1 h1mem, hidx1] at hh
    rw [if_pos (by omega : 1 + 1 < p.length)] at hh
    simpa only [show 1 + 1 = 2 by omega, hshape.1] using hh
  have hnm3mem : n - 3 ∈ p := hp.mem_iff.mpr (List.mem_range'.mpr ⟨n - 4, by omega, by omega⟩)
  have hidxnm3 : p.idxOf (n - 3) = n - 2 := by
    have hi := hpnodup.idxOf_getElem (i := n - 2) (by omega : n - 2 < p.length)
    have hv : p[n - 2] = n - 3 := by
      rw [← List.getD_eq_getElem _ 0 (by omega : n - 2 < p.length), hpen]
    rw [hv] at hi; exact hi
  have hqrecord : q.getD (n - 4) 0 = n - 1 := by
    have hh := hB_at (n - 3) (by omega) (by omega); rw [show n - 3 - 1 = n - 4 by omega] at hh
    rw [hat_one_block p hmaxp (n - 3) hnm3mem, hidxnm3] at hh
    rw [if_pos (by omega : n - 2 + 1 < p.length)] at hh
    simpa only [show n - 2 + 1 = n - 1 by omega, hlast] using hh
  have hnm1mem : n - 1 ∈ p := hp.mem_iff.mpr (List.mem_range'.mpr ⟨n - 2, by omega, by omega⟩)
  have hidxnm1 : p.idxOf (n - 1) = n - 1 := by
    have hi := hpnodup.idxOf_getElem (i := n - 1) (by omega : n - 1 < p.length)
    have hv : p[n - 1] = n - 1 := by
      rw [← List.getD_eq_getElem _ 0 (by omega : n - 1 < p.length), hlast]
    rw [hv] at hi; exact hi
  have hqmax : q.getD (n - 2) 0 = n := by
    have hh := hB_at (n - 1) (by omega) (by omega); rw [show n - 1 - 1 = n - 2 by omega] at hh
    rw [hat_one_block p hmaxp (n - 1) hnm1mem, hidxnm1] at hh
    rw [if_neg (by omega : ¬ n - 1 + 1 < p.length), hfirst] at hh; exact hh
  have hnmem : n ∈ p := hp.mem_iff.mpr (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
  have hidxn : p.idxOf n = 0 := by
    have hi := hpnodup.idxOf_getElem (i := 0) (by omega : 0 < p.length)
    have hv : p[0] = n := (by rw [← List.getD_eq_getElem _ 0 (by omega : 0 < p.length), hfirst])
    rw [hv] at hi; exact hi
  have hqlast : q.getD (n - 1) 0 = 1 := by
    have hh := hB_at n (by omega) (by omega); rw [hat_one_block p hmaxp n hnmem, hidxn] at hh
    rw [if_pos (by omega : 0 + 1 < p.length)] at hh
    simpa only [show 0 + 1 = 1 by omega, hsecond] using hh
  have hlow := forced_low_prefix p q n (by simpa [n] using hp) hqperm hn
    havoid rfl (by simpa [q] using hfixed) hfirst hsecond hshape.1
    hshape.2 hlast hqfirst hqrecord hqmax hqlast
  exact collision p q n (by simpa [n] using hp) hqperm hn
    rfl (by simpa [q] using hfixed) hfirst hlow.2.1 hlow.2.2.1 hpen
    hlast hqfirst hlow.1 hlow.2.2.2 hqrecord hqmax hqlast

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube231LargeFinish
