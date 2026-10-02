/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube231SecondReturn
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube231SecondReturn
   mirror-E: none(waiver:231-second-return-edge)
   anchors: []
   utility: none
   digest: The second inverse return edge fixes the penultimate value in the 231 chase. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube231SecondReturn

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open ThetaBasicInverse
open ThetaBasicInverseTail
open D5.S3.Combinatorics.ArrowWilfDefs

theorem penultimate_value (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 5 ≤ p.length)
    (hfirst : p.getD 0 0 = p.length)
    (hsecond : p.getD 1 0 = 1)
    (hlast : p.getD (p.length - 1) 0 = p.length - 1)
    (hreturn : (B p).getD (p.length - 3) 0 = 2)
    (hfixed : B (B (B p)) = p) :
    p.getD (p.length - 2) 0 = p.length - 3 := by
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
  let n := p.length
  let q := B p
  let r := B q
  have hqperm : q.Perm (List.range' 1 n) := by
    dsimp [q, n]
    exact B_perm p hp
  have hqlen : q.length = n := by simp [q, n]
  have hqperm' : q.Perm (List.range' 1 q.length) := by rw [hqlen]; exact hqperm
  have hrperm : r.Perm (List.range' 1 n) := by
    dsimp [r]
    simpa [hqlen] using B_perm q hqperm'
  have hrlen : r.length = n := by simp [r, hqlen]
  have hrperm' : r.Perm (List.range' 1 r.length) := by rw [hrlen]; exact hrperm
  have hpr : B r = p := by simpa [r, q] using hfixed
  have hqnodup : q.Nodup := hqperm.nodup_iff.mpr List.nodup_range'
  have hpnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hB_at (w : List ℕ) (x : ℕ) (hx : 0 < x) (hle : x ≤ w.length) :
      (B w).getD (x - 1) 0 = hat w x := by
    rw [List.getD_eq_getElem _ 0 (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range'_1]
    congr 1
    omega
  have hmaxp : ∀ y ∈ p, y ≤ p.getD 0 0 := by
    intro y hy
    rw [hfirst]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hy)
    omega
  have hnmem : n ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
  have hidxn : p.idxOf n = 0 := by
    have hi := hpnodup.idxOf_getElem (i := 0) (by omega : 0 < p.length)
    have hv : p[0] = n := by
      rw [← List.getD_eq_getElem _ 0 (by omega : 0 < p.length), hfirst]
    rw [hv] at hi
    exact hi
  have hqlast : q.getD (n - 1) 0 = 1 := by
    have hh := hB_at p n (by omega) (by omega)
    change q.getD (n - 1) 0 = hat p n at hh
    rw [hat_one_block p hmaxp n hnmem, hidxn] at hh
    rw [if_pos (by omega : 0 + 1 < p.length)] at hh
    simpa only [show 0 + 1 = 1 by omega, hsecond] using hh
  have hrfirst : r.getD 0 0 = n := by
    have hh := last_one_forces_B_first_max q hqperm' (by rw [hqlen]; omega)
      (by simpa [hqlen] using hqlast)
    simpa [r, hqlen] using hh
  have hrlast : r.getD (n - 1) 0 = 1 := by
    have hBrfirst : (B r).getD 0 0 = r.length := by
      rw [hpr, hrlen]
      exact hfirst
    have hh := B_first_max_forces_last_one r hrperm' (by rw [hrlen]; omega)
      hBrfirst
    simpa [hrlen] using hh
  have hmaxr : ∀ y ∈ r, y ≤ r.getD 0 0 := by
    intro y hy
    rw [hrfirst]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hrperm.mem_iff.mp hy)
    omega
  have hrBtwo : (B r).getD 1 0 = 1 := by rw [hpr]; exact hsecond
  have hrpen : r.getD (n - 2) 0 = 2 := by
    have hh := predecessor_of_one r hrperm' hmaxr 1 (n - 1)
      (by rw [hrlen]; omega) (by rw [hrlen]; omega)
      (by simpa [hrlen] using hrlast) hrBtwo
    simpa only [show n - 1 - 1 = n - 2 by omega] using hh
  have hhatq : hat q (n - 1) = 2 := by
    have hh := hB_at q (n - 1) (by omega) (by omega)
    rw [show n - 1 - 1 = n - 2 by omega] at hh
    change r.getD (n - 2) 0 = hat q (n - 1) at hh
    exact hh.symm.trans hrpen
  have hnm1memq : n - 1 ∈ q := hqperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 2, by omega, by omega⟩)
  let s := q.idxOf (n - 1)
  have hs : s < n := by
    simpa [s, hqlen] using List.idxOf_lt_length_of_mem hnm1memq
  have hsval : q.getD s 0 = n - 1 := by
    rw [List.getD_eq_getElem _ 0 (by omega : s < q.length)]
    exact List.getElem_idxOf (by omega : s < q.length)
  have hqreturn : q.getD (n - 3) 0 = 2 := by simpa [q, n] using hreturn
  have h2memq : 2 ∈ q := hqperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨1, by omega, by omega⟩)
  have hidx2 : q.idxOf 2 = n - 3 := by
    have hi := hqnodup.idxOf_getElem (i := n - 3) (by omega : n - 3 < q.length)
    have hv : q[n - 3] = 2 := by
      rw [← List.getD_eq_getElem _ 0 (by omega : n - 3 < q.length), hqreturn]
    rw [hv] at hi
    exact hi
  have hbranch : s + 1 < q.length ∧ ¬ IsLtrMax q (s + 1) := by
    by_contra hnot
    have hh := hhatq
    unfold hat at hh
    dsimp only at hh
    rw [if_neg hnot] at hh
    have hb := last_record_bounds_prefix q s (by omega : s < q.length) s (le_refl _)
    rw [hsval, hh] at hb
    omega
  have hqnext : q.getD (s + 1) 0 = 2 := by
    have hh := hhatq
    unfold hat at hh
    dsimp only at hh
    rw [if_pos hbranch] at hh
    exact hh
  have hsnext : s + 1 = n - 3 := by
    have hi : s + 1 < q.length := hbranch.1
    have hj : n - 3 < q.length := by omega
    have helem : q[s + 1] = q[n - 3] := by
      rw [← List.getD_eq_getElem _ 0 hi,
        ← List.getD_eq_getElem _ 0 hj, hqnext, hqreturn]
    exact (hqnodup.getElem_inj_iff).mp helem
  have hspos : s = n - 4 := by omega
  have hqsecondreturn : q.getD (n - 4) 0 = n - 1 := by
    rw [← hspos]
    exact hsval
  have hm3mem : n - 3 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 4, by omega, by omega⟩)
  have hhatp : hat p (n - 3) = n - 1 := by
    have hh := hB_at p (n - 3) (by omega) (by omega)
    rw [show n - 3 - 1 = n - 4 by omega] at hh
    change q.getD (n - 4) 0 = hat p (n - 3) at hh
    exact hh.symm.trans hqsecondreturn
  let u := p.idxOf (n - 3)
  have hu : u < n := List.idxOf_lt_length_of_mem hm3mem
  have hnextu : u + 1 < p.length := by
    by_contra hnot
    have hh := hat_one_block p hmaxp (n - 3) hm3mem
    rw [show p.idxOf (n - 3) = u by rfl,
      if_neg (by omega : ¬ u + 1 < p.length), hfirst] at hh
    rw [hhatp] at hh
    omega
  have hnextval : p.getD (u + 1) 0 = n - 1 := by
    have hh := hat_one_block p hmaxp (n - 3) hm3mem
    rw [show p.idxOf (n - 3) = u by rfl, if_pos hnextu] at hh
    exact hh.symm.trans hhatp
  have hnextpos : u + 1 = n - 1 := by
    have hi : u + 1 < p.length := hnextu
    have hj : n - 1 < p.length := by omega
    have helem : p[u + 1] = p[n - 1] := by
      rw [← List.getD_eq_getElem _ 0 hi,
        ← List.getD_eq_getElem _ 0 hj, hnextval, hlast]
    exact (hpnodup.getElem_inj_iff).mp helem
  have hupos : u = n - 2 := by omega
  rw [← hupos, List.getD_eq_getElem _ 0 (by omega : u < p.length)]
  exact List.getElem_idxOf (by omega : u < p.length)

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube231SecondReturn
