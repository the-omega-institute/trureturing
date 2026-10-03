/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Return
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube231Return
   mirror-E: none(waiver:231-forced-return-edge)
   anchors: []
   utility: none
   digest: The penultimate inverse record block in the 231 chase ends at two. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Return

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open ThetaBasicInverse
open D5.S3.Combinatorics.ArrowWilfDefs

theorem penultimate_block_ends_two (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 3 < p.length)
    (hfirst : p.getD 0 0 = p.length)
    (hsecond : p.getD 1 0 = 1)
    (hlast : p.getD (p.length - 1) 0 = p.length - 1)
    (hfixed : B (B (B p)) = p) :
    (B p).getD (p.length - 3) 0 = 2 := by
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
  let n := p.length
  let q := B p
  let r := B q
  have hpnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hqperm : q.Perm (List.range' 1 n) := by
    dsimp [q, n]
    exact B_perm p hp
  have hqlen : q.length = n := by simp [q, n]
  have hqperm' : q.Perm (List.range' 1 q.length) := by
    rw [hqlen]
    exact hqperm
  have hqnodup : q.Nodup := hqperm.nodup_iff.mpr List.nodup_range'
  have hrperm : r.Perm (List.range' 1 n) := by
    dsimp [r]
    simpa [hqlen] using B_perm q hqperm'
  have hrlen : r.length = n := by simp [r, hqlen]
  have hpr : B r = p := by simpa [r, q] using hfixed
  have hmaxp : ∀ y ∈ p, y ≤ p.getD 0 0 := by
    intro y hy
    rw [hfirst]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hy)
    omega
  have hB_at (w : List ℕ) (x : ℕ) (hx : 0 < x) (hle : x ≤ w.length) :
      (B w).getD (x - 1) 0 = hat w x := by
    rw [List.getD_eq_getElem _ 0 (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range'_1]
    congr 1
    omega
  have hnm1mem : n - 1 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 2, by omega, by omega⟩)
  have hnmem : n ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
  have hidxnm1 : p.idxOf (n - 1) = n - 1 := by
    have hi := hpnodup.idxOf_getElem (i := n - 1) (by omega : n - 1 < p.length)
    have hv : p[n - 1] = n - 1 := by
      rw [← List.getD_eq_getElem _ 0 (by omega : n - 1 < p.length), hlast]
    rw [hv] at hi
    exact hi
  have hidxn : p.idxOf n = 0 := by
    have hi := hpnodup.idxOf_getElem (i := 0) (by omega : 0 < p.length)
    have hv : p[0] = n := by
      rw [← List.getD_eq_getElem _ 0 (by omega : 0 < p.length), hfirst]
    rw [hv] at hi
    exact hi
  have hqpen : q.getD (n - 2) 0 = n := by
    have hh := hB_at p (n - 1) (by omega) (by omega)
    rw [show n - 1 - 1 = n - 2 by omega] at hh
    change q.getD (n - 2) 0 = hat p (n - 1) at hh
    rw [hat_one_block p hmaxp (n - 1) hnm1mem, hidxnm1] at hh
    rw [if_neg (by omega : ¬ n - 1 + 1 < p.length), hfirst] at hh
    exact hh
  have hqlast : q.getD (n - 1) 0 = 1 := by
    have hh := hB_at p n (by omega) (by omega)
    change q.getD (n - 1) 0 = hat p n at hh
    rw [hat_one_block p hmaxp n hnmem, hidxn] at hh
    rw [if_pos (by omega : 0 + 1 < p.length)] at hh
    simpa only [show 0 + 1 = 1 by omega, hsecond] using hh
  have hqrecn : IsLtrMax q (n - 2) := by
    intro j hj
    have hjlt : j < n := by omega
    have hm : q.getD j 0 ∈ q := by
      rw [List.getD_eq_getElem _ 0 (by omega : j < q.length)]
      exact List.getElem_mem (by omega : j < q.length)
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hqperm.mem_iff.mp hm)
    have hne : q.getD j 0 ≠ n := by
      intro he
      have helem : q[j] = q[n - 2] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : j < q.length),
          ← List.getD_eq_getElem _ 0 (by omega : n - 2 < q.length),
          he, hqpen]
      exact (by omega : j ≠ n - 2) ((hqnodup.getElem_inj_iff).mp helem)
    rw [hqpen]
    omega
  have hqnonlast : ¬ IsLtrMax q (n - 1) := by
    intro hrec
    have hh := hrec (n - 2) (by omega)
    rw [hqpen, hqlast] at hh
    omega
  have hqedges := hat_record_block_edges q hqnodup (n - 2) n
    (by omega) (by omega) hqrecn (by
      intro j hj hjlt
      have heq : j = n - 1 := by omega
      simpa [heq] using hqnonlast) (Or.inl (by omega))
  have hrfirst : r.getD 0 0 = n := by
    have hh := hqedges.2
    rw [show n - 1 = n - 1 by rfl, hqlast, hqpen] at hh
    have hb := hB_at q 1 (by omega) (by omega)
    change r.getD 0 0 = hat q 1 at hb
    exact hb.trans hh
  have hrlast : r.getD (n - 1) 0 = 1 := by
    have hh := hqedges.1 (n - 2) (le_refl _) (by omega)
    rw [hqpen, show n - 2 + 1 = n - 1 by omega, hqlast] at hh
    have hb := hB_at q n (by omega) (by omega)
    change r.getD (n - 1) 0 = hat q n at hb
    exact hb.trans hh
  have hmaxr : ∀ y ∈ r, y ≤ r.getD 0 0 := by
    intro y hy
    rw [hrfirst]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hrperm.mem_iff.mp hy)
    omega
  have hrnmem : n ∈ r := hrperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 1, by omega, by omega⟩)
  have hrnodup : r.Nodup := hrperm.nodup_iff.mpr List.nodup_range'
  have hridxn : r.idxOf n = 0 := by
    have hi := hrnodup.idxOf_getElem (i := 0) (by omega : 0 < r.length)
    have hv : r[0] = n := by
      rw [← List.getD_eq_getElem _ 0 (by omega : 0 < r.length), hrfirst]
    rw [hv] at hi
    exact hi
  have hrsecond : r.getD 1 0 = n - 1 := by
    have hh := hB_at r n (by omega) (by omega)
    rw [hpr, hlast] at hh
    rw [hat_one_block r hmaxr n hrnmem, hridxn] at hh
    rw [if_pos (by omega : 0 + 1 < r.length)] at hh
    simpa only [show 0 + 1 = 1 by omega] using hh.symm
  have hqtwo : hat q 2 = n - 1 := by
    have hh := hB_at q 2 (by omega) (by omega)
    change r.getD 1 0 = hat q 2 at hh
    exact hh.symm.trans hrsecond
  have hnm1memq : n - 1 ∈ q := hqperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 2, by omega, by omega⟩)
  have hs : q.idxOf (n - 1) < n - 2 := by
    have hi := List.idxOf_lt_length_of_mem hnm1memq
    have hil : q.idxOf (n - 1) < n := by simpa [hqlen] using hi
    by_contra hnot
    have hcases : q.idxOf (n - 1) = n - 2 ∨ q.idxOf (n - 1) = n - 1 := by omega
    have hval : q.getD (q.idxOf (n - 1)) 0 = n - 1 := by
      rw [List.getD_eq_getElem _ 0 hi]
      exact List.getElem_idxOf hi
    rcases hcases with he | he
    · rw [he, hqpen] at hval; omega
    · rw [he, hqlast] at hval; omega
  have hqbound (j : ℕ) (hj : j < n) : q.getD j 0 ≤ n := by
    have hm : q.getD j 0 ∈ q := by
      rw [List.getD_eq_getElem _ 0 (by omega : j < q.length)]
      exact List.getElem_mem (by omega : j < q.length)
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hqperm.mem_iff.mp hm)
    omega
  have hqvalnm1 : q.getD (q.idxOf (n - 1)) 0 = n - 1 := by
    rw [List.getD_eq_getElem _ 0 (by rw [hqlen]; omega)]
    exact List.getElem_idxOf (by rw [hqlen]; omega)
  have hqrecnm1 : IsLtrMax q (q.idxOf (n - 1)) := by
    intro j hj
    have hjlt : j < n := by omega
    have hne1 : q.getD j 0 ≠ n - 1 := by
      intro he
      have helem : q[j] = q[q.idxOf (n - 1)] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : j < q.length),
          ← List.getD_eq_getElem _ 0 (by omega : q.idxOf (n - 1) < q.length),
          he, hqvalnm1]
      exact (by omega : j ≠ q.idxOf (n - 1))
        ((hqnodup.getElem_inj_iff).mp helem)
    have hnen : q.getD j 0 ≠ n := by
      intro he
      have helem : q[j] = q[n - 2] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : j < q.length),
          ← List.getD_eq_getElem _ 0 (by omega : n - 2 < q.length),
          he, hqpen]
      exact (by omega : j ≠ n - 2) ((hqnodup.getElem_inj_iff).mp helem)
    have hle := hqbound j hjlt
    rw [hqvalnm1]
    omega
  have hqnon (j : ℕ) (hj : q.idxOf (n - 1) < j) (hjlt : j < n - 2) :
      ¬ IsLtrMax q j := by
    intro hrec
    have hh := hrec (q.idxOf (n - 1)) hj
    rw [hqvalnm1] at hh
    have hle := hqbound j (by omega)
    have hne : q.getD j 0 ≠ n := by
      intro he
      have helem : q[j] = q[n - 2] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : j < q.length),
          ← List.getD_eq_getElem _ 0 (by omega : n - 2 < q.length),
          he, hqpen]
      exact (by omega : j ≠ n - 2) ((hqnodup.getElem_inj_iff).mp helem)
    omega
  have hqblock := hat_record_block_edges q hqnodup (q.idxOf (n - 1))
    (n - 2) hs (by omega) hqrecnm1 hqnon (Or.inr hqrecn)
  have hqclose := hqblock.2
  have hlastval : q.getD (n - 3) 0 ∈ q := by
    rw [List.getD_eq_getElem _ 0 (by omega : n - 3 < q.length)]
    exact List.getElem_mem (by omega : n - 3 < q.length)
  have hqclose' : hat q (q.getD (n - 3) 0) = n - 1 := by
    simpa only [show n - 2 - 1 = n - 3 by omega, hqvalnm1] using hqclose
  have h2mem : 2 ∈ q := hqperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨1, by omega, by omega⟩)
  simpa [q, n] using
    (hat_inj_on q hqnodup (q.getD (n - 3) 0) hlastval 2 h2mem
      (hqclose'.trans hqtwo.symm))

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Return
