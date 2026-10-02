/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaCube231Pair
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaCube231Pair
   mirror-E: none(waiver:terminal-cycle-edge-forces-adjacent-pair)
   anchors: []
   utility: none
   digest: A terminal inverse edge forces the adjacent pair before the last letter. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Pair

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open ThetaBasicInverse
open D5.S3.Combinatorics.ArrowWilfDefs

/-- If `p` begins with the maximum and `B (B p)` sends that maximum to
`1`, the letter before the last one forces an adjacent `c+1,1` pair. -/
theorem terminal_inverse_edge_forces_pair (p : List ℕ)
    (hp : p.Perm (List.range' 1 p.length)) (hn : 1 < p.length)
    (hfirst : p.getD 0 0 = p.length)
    (c : ℕ) (hlast : p.getD (p.length - 1) 0 = c)
    (hr : (B (B p)).getD (p.length - 1) 0 = 1) :
    c < p.length ∧
      ∃ t, t + 1 < p.length ∧ p.getD t 0 = c + 1 ∧ p.getD (t + 1) 0 = 1 := by
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
  have hq : q.Perm (List.range' 1 n) := by
    dsimp [q, n]
    exact B_perm p hp
  have hqlen : q.length = n := by simp [q, n]
  have hqnodup : q.Nodup := hq.nodup_iff.mpr List.nodup_range'
  have hpnodup : p.Nodup := hp.nodup_iff.mpr List.nodup_range'
  have hclast : n - 1 < p.length := by dsimp [n]; omega
  have hcmem : c ∈ p := by
    rw [← hlast, List.getD_eq_getElem _ 0 hclast]
    exact List.getElem_mem hclast
  obtain ⟨j, hj, hjc⟩ := List.mem_range'.mp (hp.mem_iff.mp hcmem)
  have hcpos : 0 < c := by omega
  have hcle : c ≤ n := by omega
  have hmax : ∀ y ∈ p, y ≤ p.getD 0 0 := by
    intro y hy
    rw [hfirst]
    obtain ⟨i, hi, heq⟩ := List.mem_range'.mp (hp.mem_iff.mp hy)
    omega
  have hidxc : p.idxOf c = n - 1 := by
    rw [← hlast, List.getD_eq_getElem _ 0 hclast]
    exact hpnodup.idxOf_getElem (i := n - 1) hclast
  have hhatc : hat p c = n := by
    rw [hat_one_block p hmax c hcmem, hidxc]
    have hno : ¬ n - 1 + 1 < p.length := by dsimp [n]; omega
    rw [if_neg hno, hfirst]
  have hqc : q.getD (c - 1) 0 = n := by
    have hci : c - 1 < q.length := by rw [hqlen]; omega
    rw [List.getD_eq_getElem _ 0 hci]
    simp only [q, List.getElem_map, List.getElem_range'_1]
    simpa [show 1 + (c - 1) = c by omega] using hhatc
  have hqidx : q.idxOf n = c - 1 := by
    have hci : c - 1 < q.length := by rw [hqlen]; omega
    rw [← hqc, List.getD_eq_getElem _ 0 hci]
    exact hqnodup.idxOf_getElem (i := c - 1) hci
  have hrhat : hat q n = 1 := by
    have hni : n - 1 < (B q).length := by simp [hqlen]; omega
    have hr' : (B q).getD (n - 1) 0 = 1 := by simpa [q, n] using hr
    rw [List.getD_eq_getElem _ 0 hni] at hr'
    simp only [List.getElem_map, List.getElem_range'_1] at hr'
    simpa [show 1 + (n - 1) = n by omega] using hr'
  have hresult : c < n := by
    by_contra hnot
    have hcEq : c = n := by omega
    have hi : q.idxOf n = q.length - 1 := by rw [hqidx, hqlen, hcEq]
    have hrec : IsLtrMax q (q.idxOf n) := by
      intro i hii
      have himem : q.getD i 0 ∈ q := by
        rw [List.getD_eq_getElem _ 0 (by omega : i < q.length)]
        exact List.getElem_mem (by omega : i < q.length)
      obtain ⟨j, hj, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp himem)
      have hne : q.getD i 0 ≠ n := by
        intro he
        have hix : i < q.length := by omega
        have hval : q.getD (q.idxOf n) 0 = n := by
          rw [List.getD_eq_getElem _ 0 (by omega : q.idxOf n < q.length)]
          exact List.getElem_idxOf (by omega : q.idxOf n < q.length)
        have helem : q[i] = q[q.idxOf n] := by
          rw [← List.getD_eq_getElem _ 0 hix,
            ← List.getD_eq_getElem _ 0 (by omega : q.idxOf n < q.length), he, hval]
        have := (hqnodup.getElem_inj_iff).mp helem
        omega
      have hval : q.getD (q.idxOf n) 0 = n := by
        rw [List.getD_eq_getElem _ 0 (by omega : q.idxOf n < q.length)]
        exact List.getElem_idxOf (by omega : q.idxOf n < q.length)
      rw [hval]
      omega
    have hg : Nat.findGreatest (IsLtrMax q) (q.idxOf n) = q.idxOf n := by
      apply Nat.le_antisymm (Nat.findGreatest_le _)
      exact Nat.le_findGreatest (le_refl _) hrec
    have hh : hat q n = n := by
      unfold hat
      rw [if_neg (by rw [hi]; omega :
        ¬ (q.idxOf n + 1 < q.length ∧ ¬ IsLtrMax q (q.idxOf n + 1))), hg]
      rw [List.getD_eq_getElem _ 0 (by omega : q.idxOf n < q.length)]
      exact List.getElem_idxOf (by omega : q.idxOf n < q.length)
    omega
  have hnrecnext : ¬ IsLtrMax q c := by
    intro hrec
    have hidxlt : q.idxOf n < c := by rw [hqidx]; omega
    have hqval : q.getD (q.idxOf n) 0 = n := by
      rw [List.getD_eq_getElem _ 0 (by rw [hqlen]; omega)]
      exact List.getElem_idxOf (by rw [hqlen]; omega)
    have hcval : q.getD c 0 ≤ n := by
      have hcm : q.getD c 0 ∈ q := by
        rw [List.getD_eq_getElem _ 0 (by rw [hqlen]; omega)]
        exact List.getElem_mem (by rw [hqlen]; omega)
      obtain ⟨i, hi, heq⟩ := List.mem_range'.mp (hq.mem_iff.mp hcm)
      omega
    have hlarge := hrec (q.idxOf n) hidxlt
    rw [hqval] at hlarge
    omega
  have hqnext : q.getD c 0 = 1 := by
    have hnext : q.idxOf n + 1 < q.length := by rw [hqidx, hqlen]; omega
    unfold hat at hrhat
    rw [if_pos ⟨hnext, by simpa only [hqidx, show c - 1 + 1 = c by omega]
      using hnrecnext⟩] at hrhat
    simpa only [hqidx, show c - 1 + 1 = c by omega] using hrhat
  have hcp1mem : c + 1 ∈ p := hp.mem_iff.mpr
    (List.mem_range'.mpr ⟨c, by omega, by omega⟩)
  have hhat : hat p (c + 1) = 1 := by
    have hci : c < q.length := by rw [hqlen]; omega
    have hqval : q.getD c 0 = hat p (c + 1) := by
      rw [List.getD_eq_getElem _ 0 hci]
      simp only [q, List.getElem_map, List.getElem_range'_1]
      rw [Nat.add_comm]
    exact hqval.symm.trans hqnext
  let t := p.idxOf (c + 1)
  have ht : t < p.length := List.idxOf_lt_length_of_mem hcp1mem
  have htval : p.getD t 0 = c + 1 := by
    rw [List.getD_eq_getElem _ 0 ht]
    exact List.getElem_idxOf ht
  have htnext : t + 1 < p.length := by
    by_contra hnot
    have hnone : ¬ t + 1 < p.length := by omega
    have hh := hat_one_block p hmax (c + 1) hcp1mem
    rw [show p.idxOf (c + 1) = t by rfl, if_neg hnone, hfirst] at hh
    rw [hhat] at hh
    omega
  refine ⟨hresult, t, htnext, htval, ?_⟩
  have hh := hat_one_block p hmax (c + 1) hcp1mem
  rw [show p.idxOf (c + 1) = t by rfl, if_pos htnext] at hh
  rw [hhat] at hh
  exact hh.symm

end D5.S3.Combinatorics.FundamentalBijection.ThetaCube231Pair
