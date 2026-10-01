/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube312Final
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube312Final
   mirror-E: none(waiver:312-terminal-cycle-conflict)
   anchors: []
   utility: none
   digest: The forced 312 suffix makes a fixed inverse edge collide with the cycle word. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Suffix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Final

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open D5.S3.Combinatorics.ArrowWilfDefs
open ThetaBasicInverse
open ThetaCube312Suffix

/-- The fixed high edge collides with the edge forced by the two cycle words. -/
theorem terminal_collision (p : List ℕ) (n : ℕ)
    (hp : p.Perm (List.range' 1 n)) (hn : 7 ≤ n)
    (hpair : p.getD (n - 5) 0 = n - 2)
    (hpen : p.getD (n - 4) 0 = n - 1)
    (htwo : p.getD (n - 3) 0 = 2)
    (hmax : p.getD (n - 2) 0 = n)
    (hqfirst : (B p).getD 0 0 = n)
    (hqthird : (B p).getD 2 0 = n - 3)
    (hqpenult : (B p).getD (n - 2) 0 = 2)
    (hrfirst : (B (B p)).getD 0 0 = n)
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
  have terminal_high_fixed (p : List ℕ) (n : ℕ)
      (hp : p.Perm (List.range' 1 n)) (hn : 7 ≤ n)
      (hpair : p.getD (n - 5) 0 = n - 2)
      (hpen : p.getD (n - 4) 0 = n - 1)
      (hmax : p.getD (n - 2) 0 = n) :
      (B p).getD (n - 3) 0 = n - 2 := by
    have hlen : p.length = n := by simpa using hp.length_eq
    have hnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
    have hinj (i j : ℕ) (hi : i < n) (hj : j < n)
        (heq : p.getD i 0 = p.getD j 0) : i = j := by
      have helem : p[i] = p[j] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : i < p.length),
          ← List.getD_eq_getElem _ 0 (by omega : j < p.length), heq]
      exact (hnodup.getElem_inj_iff).mp helem
    have hbound (j : ℕ) (hj : j < n) : p.getD j 0 ≤ n := by
      have hm : p.getD j 0 ∈ p := by
        rw [List.getD_eq_getElem _ 0 (by omega : j < p.length)]
        exact List.getElem_mem (by omega : j < p.length)
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hm)
      omega
    have hnot (j t v : ℕ) (hj : j < n) (ht : t < n)
        (hjt : j ≠ t) (htv : p.getD t 0 = v) : p.getD j 0 ≠ v := by
      intro he
      exact hjt (hinj j t hj ht (he.trans htv.symm))
    have hrecpair : IsLtrMax p (n - 5) := by
      intro j hj
      have hjn : j < n := by omega
      have hle := hbound j hjn
      have hne2 := hnot j (n - 5) (n - 2) hjn (by omega) (by omega) hpair
      have hne1 := hnot j (n - 4) (n - 1) hjn (by omega) (by omega) hpen
      have hnen := hnot j (n - 2) n hjn (by omega) (by omega) hmax
      rw [hpair]
      omega
    have hrecnext : IsLtrMax p (n - 4) := by
      intro j hj
      have hjn : j < n := by omega
      have hle := hbound j hjn
      have hne1 := hnot j (n - 4) (n - 1) hjn (by omega) (by omega) hpen
      have hnen := hnot j (n - 2) n hjn (by omega) (by omega) hmax
      rw [hpen]
      omega
    have hedge := (hat_record_block_edges p hnodup (n - 5) (n - 4)
      (by omega) (by omega) hrecpair (by intro j hj hj'; omega)
      (Or.inr hrecnext)).2
    have hB : (B p).getD (n - 3) 0 = hat p (n - 2) := by
      rw [List.getD_eq_getElem _ 0 (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range'_1]
      congr 1
      omega
    rw [show n - 4 - 1 = n - 5 by omega, hpair] at hedge
    exact hB.trans hedge
  let q := B p
  let r := B q
  have hlen : p.length = n := by simpa using hp.length_eq
  have hp' : p.Perm (List.range' 1 p.length) := by rw [hlen]; exact hp
  have hqperm : q.Perm (List.range' 1 n) := by
    simpa [q, hlen] using B_perm p hp'
  have hqlen : q.length = n := by simp [q, hlen]
  have hqperm' : q.Perm (List.range' 1 q.length) := by
    rw [hqlen]
    exact hqperm
  have hrperm : r.Perm (List.range' 1 n) := by
    simpa [r, hqlen] using B_perm q hqperm'
  have hrlen : r.length = n := by simp [r, hqlen]
  have hrperm' : r.Perm (List.range' 1 r.length) := by
    rw [hrlen]
    exact hrperm
  have hqnodup : q.Nodup := hqperm.nodup_iff.mpr List.nodup_range'
  have hrnodup : r.Nodup := hrperm.nodup_iff.mpr List.nodup_range'
  have hqmax : ∀ y ∈ q, y ≤ q.getD 0 0 := by
    intro y hy
    rw [show q.getD 0 0 = n by exact hqfirst]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hqperm.mem_iff.mp hy)
    omega
  have hrmax : ∀ y ∈ r, y ≤ r.getD 0 0 := by
    intro y hy
    rw [show r.getD 0 0 = n by exact hrfirst]
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hrperm.mem_iff.mp hy)
    omega
  have hB_at (w : List ℕ) (x : ℕ) (hx : 0 < x) (hle : x ≤ w.length) :
      (B w).getD (x - 1) 0 = hat w x := by
    rw [List.getD_eq_getElem _ 0 (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range'_1]
    congr 1
    omega
  have hqfixed : q.getD (n - 3) 0 = n - 2 := by
    dsimp [q]
    exact terminal_high_fixed p n hp hn hpair hpen hmax
  have hm2memq : n - 2 ∈ q := hqperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 3, by omega, by omega⟩)
  have hqidxm2 : q.idxOf (n - 2) = n - 3 := by
    have hi : n - 3 < q.length := by omega
    have hh := hqnodup.idxOf_getElem (i := n - 3) hi
    have hv : q[n - 3] = n - 2 := by
      rw [← List.getD_eq_getElem _ 0 hi, hqfixed]
    rw [hv] at hh
    exact hh
  have hr_two : r.getD (n - 3) 0 = 2 := by
    have hh := hB_at q (n - 2) (by omega) (by omega)
    have hsub : n - 2 - 1 = n - 3 := by omega
    rw [hsub] at hh
    change r.getD (n - 3) 0 = hat q (n - 2) at hh
    rw [hat_one_block q hqmax (n - 2) hm2memq, hqidxm2] at hh
    have hnext : n - 3 + 1 = n - 2 := by omega
    rw [hnext, if_pos (by omega : n - 2 < q.length)] at hh
    exact hh.trans hqpenult
  have hr_two_mem : 2 ∈ r := hrperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨1, by omega, by omega⟩)
  have hridx_two : r.idxOf 2 = n - 3 := by
    have hi : n - 3 < r.length := by omega
    have hh := hrnodup.idxOf_getElem (i := n - 3) hi
    have hv : r[n - 3] = 2 := by
      rw [← List.getD_eq_getElem _ 0 hi, hr_two]
    rw [hv] at hh
    exact hh
  have hr_m2_mem : n - 2 ∈ r := hrperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 3, by omega, by omega⟩)
  have hr_edge : hat r (n - 2) = 2 := by
    have hh := hB_at r (n - 2) (by omega) (by omega)
    have hsub : n - 2 - 1 = n - 3 := by omega
    rw [hsub] at hh
    change (B (B (B p))).getD (n - 3) 0 = hat r (n - 2) at hh
    rw [hfixed, htwo] at hh
    exact hh.symm
  have hridx_m2 : r.idxOf (n - 2) = n - 4 := by
    have hh := hat_one_block r hrmax (n - 2) hr_m2_mem
    rw [hr_edge] at hh
    have hinside : r.idxOf (n - 2) + 1 < r.length := by
      by_contra hnot
      rw [if_neg (by omega : ¬ r.idxOf (n - 2) + 1 < r.length)] at hh
      rw [hrfirst] at hh
      omega
    rw [if_pos hinside] at hh
    have hidx : r.idxOf (n - 2) + 1 = r.idxOf 2 := by
      have hi : r.idxOf (n - 2) + 1 < r.length := hinside
      have hj : r.idxOf 2 < r.length := by omega
      have helem : r[r.idxOf (n - 2) + 1] = r[r.idxOf 2] := by
        rw [← List.getD_eq_getElem _ 0 hi,
          ← List.getD_eq_getElem _ 0 hj, ← hh]
        rw [List.getD_eq_getElem _ 0 hj]
        exact (List.getElem_idxOf hj).symm
      exact (hrnodup.getElem_inj_iff).mp helem
    rw [hridx_two] at hidx
    omega
  have hr_fixed : r.getD (n - 4) 0 = n - 2 := by
    rw [← hridx_m2, List.getD_eq_getElem _ 0 (by omega : r.idxOf (n - 2) < r.length)]
    exact List.getElem_idxOf (by omega : r.idxOf (n - 2) < r.length)
  have hm3memq : n - 3 ∈ q := hqperm.mem_iff.mpr
    (List.mem_range'.mpr ⟨n - 4, by omega, by omega⟩)
  have hqidxm3 : q.idxOf (n - 3) = 2 := by
    have hi : 2 < q.length := by omega
    have hh := hqnodup.idxOf_getElem (i := 2) hi
    have hv : q[2] = n - 3 := by
      rw [← List.getD_eq_getElem _ 0 hi, hqthird]
    rw [hv] at hh
    exact hh
  have hqfour : q.getD 3 0 = n - 2 := by
    have hh := hB_at q (n - 3) (by omega) (by omega)
    have hsub : n - 3 - 1 = n - 4 := by omega
    rw [hsub] at hh
    change r.getD (n - 4) 0 = hat q (n - 3) at hh
    rw [hat_one_block q hqmax (n - 3) hm3memq, hqidxm3] at hh
    rw [if_pos (by omega : 2 + 1 < q.length)] at hh
    simpa only [show 2 + 1 = 3 by omega] using hh.symm.trans hr_fixed
  have hpos : 3 = n - 3 := by
    have hi : 3 < q.length := by omega
    have hj : n - 3 < q.length := by omega
    have helem : q[3] = q[n - 3] := by
      rw [← List.getD_eq_getElem _ 0 hi,
        ← List.getD_eq_getElem _ 0 hj, hqfour, hqfixed]
    exact (hqnodup.getElem_inj_iff).mp helem
  omega

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube312Final
