/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Middle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube231Middle
   mirror-E: none(waiver:231-middle-final-block-conflict)
   anchors: []
   utility: none
   digest: A forced final inverse record block excludes the middle terminal values. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Middle

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open ThetaBasicInverse
open D5.S3.Combinatorics.ArrowWilfDefs

/-- The final record block `(n,1,...,n-1)` of the first inverse word
forces the next inverse word to end in `n,1`, contrary to `c ≥ 2`. -/
theorem middle_cycle_conflict (p q : List ℕ) (n c : ℕ)
    (hq : q.Perm (List.range' 1 n)) (hn : 4 ≤ n)
    (hc : 2 ≤ c) (hclt : c < n - 1)
    (hqn : q.getD (c - 1) 0 = n)
    (hqc : q.getD c 0 = 1)
    (hqlast : q.getD (n - 1) 0 = n - 1)
    (hpr : B (B q) = p)
    (hplast : p.getD (n - 1) 0 = c) : False := by
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
  have hqlen : q.length = n := by simpa using hq.length_eq
  have hqnodup : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
  have hqbound (j : ℕ) (hj : j < n) : q.getD j 0 ≤ n := by
    have hm : q.getD j 0 ∈ q := by
      rw [List.getD_eq_getElem _ 0 (by omega : j < q.length)]
      exact List.getElem_mem (by omega : j < q.length)
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp hm)
    omega
  have hqrec : IsLtrMax q (c - 1) := by
    intro j hj
    have hjn : j < n := by omega
    have hne : q.getD j 0 ≠ n := by
      intro he
      have helem : q[j] = q[c - 1] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : j < q.length),
          ← List.getD_eq_getElem _ 0 (by omega : c - 1 < q.length),
          he, hqn]
      exact (by omega : j ≠ c - 1) ((hqnodup.getElem_inj_iff).mp helem)
    rw [hqn]
    have hle := hqbound j hjn
    omega
  have hqnon (j : ℕ) (hj : c - 1 < j) (hjlt : j < n) :
      ¬ IsLtrMax q j := by
    intro hrec
    have hh := hrec (c - 1) hj
    rw [hqn] at hh
    have hle := hqbound j hjlt
    omega
  have hqedges := hat_record_block_edges q hqnodup (c - 1) n
    (by omega) (by omega) hqrec hqnon (Or.inl (by omega))
  have hhatn : hat q n = 1 := by
    have hh := hqedges.1 (c - 1) (le_refl _) (by omega)
    rw [hqn, show c - 1 + 1 = c by omega, hqc] at hh
    exact hh
  have hhatpen : hat q (n - 1) = n := by
    have hh := hqedges.2
    rw [show n - 1 = n - 1 by rfl, hqlast, hqn] at hh
    exact hh
  let r := B q
  have hrperm : r.Perm (List.range' 1 n) := by
    dsimp [r]
    have hq' : q.Perm (List.range' 1 q.length) := by rw [hqlen]; exact hq
    simpa [hqlen] using B_perm q hq'
  have hrlen : r.length = n := by simp [r, hqlen]
  have hrnodup : r.Nodup := hrperm.nodup_iff.mpr List.nodup_range'
  have hrpen : r.getD (n - 2) 0 = n := by
    rw [List.getD_eq_getElem _ 0 (by omega : n - 2 < r.length)]
    simp only [r, List.getElem_map, List.getElem_range'_1]
    simpa only [show 1 + (n - 2) = n - 1 by omega] using hhatpen
  have hrlast : r.getD (n - 1) 0 = 1 := by
    rw [List.getD_eq_getElem _ 0 (by omega : n - 1 < r.length)]
    simp only [r, List.getElem_map, List.getElem_range'_1]
    simpa only [show 1 + (n - 1) = n by omega] using hhatn
  have hrrec : IsLtrMax r (n - 2) := by
    intro j hj
    have hjn : j < n := by omega
    have hm : r.getD j 0 ∈ r := by
      rw [List.getD_eq_getElem _ 0 (by omega : j < r.length)]
      exact List.getElem_mem (by omega : j < r.length)
    obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hrperm.mem_iff.mp hm)
    have hne : r.getD j 0 ≠ n := by
      intro he
      have helem : r[j] = r[n - 2] := by
        rw [← List.getD_eq_getElem _ 0 (by omega : j < r.length),
          ← List.getD_eq_getElem _ 0 (by omega : n - 2 < r.length),
          he, hrpen]
      exact (by omega : j ≠ n - 2) ((hrnodup.getElem_inj_iff).mp helem)
    rw [hrpen]
    omega
  have hrnon (j : ℕ) (hj : n - 2 < j) (hjlt : j < n) :
      ¬ IsLtrMax r j := by
    have hjeq : j = n - 1 := by omega
    subst j
    intro hrec
    have hh := hrec (n - 2) (by omega)
    rw [hrpen, hrlast] at hh
    omega
  have hredges := hat_record_block_edges r hrnodup (n - 2) n
    (by omega) (by omega) hrrec hrnon (Or.inl (by omega))
  have hhatr : hat r n = 1 := by
    have hh := hredges.1 (n - 2) (le_refl _) (by omega)
    rw [hrpen, show n - 2 + 1 = n - 1 by omega, hrlast] at hh
    exact hh
  have hBrlast : (B r).getD (n - 1) 0 = 1 := by
    rw [List.getD_eq_getElem _ 0 (by simp [hrlen]; omega)]
    simp only [List.getElem_map, List.getElem_range'_1]
    simpa only [show 1 + (n - 1) = n by omega] using hhatr
  have hpr' : B r = p := by simpa [r] using hpr
  rw [hpr', hplast] at hBrlast
  omega

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Middle
