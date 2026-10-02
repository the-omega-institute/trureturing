/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaBasicSumFactors
   mirror-E: none(waiver:unique-permutation-sum-factorization)
   anchors: []
   utility: none
   digest: Permutations decompose into normalized sum-indecomposable factors. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumIndecomp
import D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumFactors

open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSum
open D5.S3.Combinatorics.Nonnesting.NonnestingBasicSum (sumIndecomposable)

/-- Concatenate normalized factors, shifting each suffix past its preceding factor. -/
def sumFactors : List (List ℕ) → List ℕ
  | [] => []
  | u :: fs => u ++ (sumFactors fs).map (fun x => x + u.length)

/-- The least positive value cut can be iterated until every factor has no
internal cut. -/
theorem exists_sum_factorization (w : List ℕ)
    (hw : w.Perm (List.range' 1 w.length)) :
    ∃ fs : List (List ℕ), sumFactors fs = w ∧ ∀ u ∈ fs,
      0 < u.length ∧ u.Perm (List.range' 1 u.length) ∧ sumIndecomposable u := by
  let Factor (u : List ℕ) : Prop :=
    0 < u.length ∧ u.Perm (List.range' 1 u.length) ∧ sumIndecomposable u
  have indecomp_iff (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) :
      sumIndecomposable p ↔
        ∀ k, 0 < k → k < p.length → ∃ x ∈ p.take k, k < x := by
    classical
    constructor
    · intro hind k hk hkl
      by_contra hnone
      have hsmall : ∀ x ∈ p.take k, x ≤ k := by
        intro x hx
        by_contra hgt
        exact hnone ⟨x, hx, by omega⟩
      have hnodup := hp.nodup_iff.mpr List.nodup_range'
      have hsubset : (p.take k).toFinset ⊆ (List.range' 1 k).toFinset := by
        intro x hx
        have hxt := List.mem_toFinset.mp hx
        obtain ⟨a, ha, heq⟩ := List.mem_range'.mp
          (hp.mem_iff.mp (List.mem_of_mem_take hxt))
        exact List.mem_toFinset.mpr
          (List.mem_range'.mpr ⟨x - 1, by have := hsmall x hxt; omega, by omega⟩)
      have hcard : (p.take k).toFinset.card = (List.range' 1 k).toFinset.card := by
        simp [List.card_toFinset, List.dedup_eq_self.mpr hnodup.take,
          List.dedup_eq_self.mpr List.nodup_range', Nat.min_eq_left (by omega : k ≤ p.length)]
      have hset := Finset.eq_of_subset_of_card_le hsubset (by omega)
      obtain ⟨i, j, hji⟩ := hind ⟨k, hkl⟩ hk
      have hx := List.get_mem (p.take k) i
      have hy := List.get_mem (p.drop k) j
      have hybound : (p.drop k).get j ≤ k := le_trans hji (hsmall _ hx)
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp
        (hp.mem_iff.mp (List.mem_of_mem_drop hy))
      have hyfirst : (p.drop k).get j ∈ p.take k := by
        apply List.mem_toFinset.mp
        rw [hset]
        exact List.mem_toFinset.mpr
          (List.mem_range'.mpr ⟨(p.drop k).get j - 1, by omega, by omega⟩)
      exact List.disjoint_left.mp (List.disjoint_take_drop hnodup (le_refl k)) hyfirst hy
    · intro hind k hk
      by_contra hnone
      have hsep : ∀ x ∈ p.take k.val, ∀ y ∈ p.drop k.val, x < y := by
        intro x hx y hy
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
        obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hy
        by_contra hnot
        exact hnone ⟨i, j, by omega⟩
      obtain ⟨x, hx, hgt⟩ := hind k.val hk k.isLt
      exact (not_le_of_gt hgt) (separated_prefix_cut p hp k.val (by omega) hsep x hx)
  have prefix_cut_iff_sum (w : List ℕ)
      (hw : w.Perm (List.range' 1 w.length)) (k : ℕ) (hk : k ≤ w.length) :
      (∀ x ∈ w.take k, x ≤ k) ↔
        ∃ v : List ℕ,
          w = w.take k ++ v.map (fun x => x + k) ∧
          (w.take k).Perm (List.range' 1 k) ∧
          v.Perm (List.range' 1 (w.length - k)) := by
    constructor
    · intro hsmall
      let u := w.take k
      let tail := w.drop k
      have hnodup : w.Nodup := hw.nodup_iff.mpr List.nodup_range'
      have hUlen : u.length = k := by simp [u, hk]
      have hUnodup : u.Nodup := hnodup.take
      have hsubset : u.toFinset ⊆ (List.range' 1 k).toFinset := by
        intro x hx
        have hxu : x ∈ u := List.mem_toFinset.mp hx
        have hxw : x ∈ w := List.mem_of_mem_take hxu
        have hxr : x ∈ List.range' 1 w.length := hw.mem_iff.mp hxw
        obtain ⟨j, hj, hval⟩ := List.mem_range'.mp hxr
        have hx1 : 1 ≤ x := by omega
        have hxk : x ≤ k := hsmall x hxu
        exact List.mem_toFinset.mpr (List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩)
      have hcard : u.toFinset.card = (List.range' 1 k).toFinset.card := by
        simp [List.card_toFinset, List.dedup_eq_self.mpr hUnodup,
          List.dedup_eq_self.mpr List.nodup_range', hUlen]
      have hset : u.toFinset = (List.range' 1 k).toFinset :=
        Finset.eq_of_subset_of_card_le hsubset (by omega)
      have hu : u.Perm (List.range' 1 k) :=
        List.perm_of_nodup_nodup_toFinset_eq hUnodup List.nodup_range' hset
      have hrange : List.range' 1 w.length =
          List.range' 1 k ++ List.range' (k + 1) (w.length - k) := by
        have h := List.range'_append_1 (s := 1) (m := k) (n := w.length - k)
        simpa [Nat.add_sub_of_le hk, Nat.add_comm] using h.symm
      have hwhole : (u ++ tail).Perm (List.range' 1 k ++
          List.range' (k + 1) (w.length - k)) := by
        simpa only [u, tail, List.take_append_drop, hrange] using hw
      have htail : tail.Perm (List.range' (k + 1) (w.length - k)) := by
        have h := (hu.symm.append (List.Perm.refl tail)).trans hwhole
        exact (List.perm_append_left_iff (List.range' 1 k)).mp h
      let v := tail.map (fun x => x - k)
      have htail_shift : tail = v.map (fun x => x + k) := by
        change tail = (tail.map (fun x => x - k)).map (fun x => x + k)
        rw [List.map_map]
        calc
          tail = tail.map (fun x => x) := by simp
          _ = tail.map ((fun x => x + k) ∘ fun x => x - k) := by
            apply List.map_congr_left
            intro x hx
            have hxr : x ∈ List.range' (k + 1) (w.length - k) := htail.mem_iff.mp hx
            obtain ⟨j, _, hxj⟩ := List.mem_range'.mp hxr
            dsimp
            omega
      have hv : v.Perm (List.range' 1 (w.length - k)) := by
        have hmap := htail.map (fun x => x - k)
        have hr : (List.range' (k + 1) (w.length - k)).map (fun x => x - k) =
            List.range' 1 (w.length - k) := by
          have h := List.Ico.map_sub (k + 1) (w.length + 1) k (by omega)
          simpa [List.Ico, Nat.add_sub_of_le hk, Nat.add_comm,
            show w.length + 1 - k - 1 = w.length - k by omega] using h
        simpa only [v, hr] using hmap
      refine ⟨v, ?_, ?_, hv⟩
      · calc
          w = u ++ tail := (List.take_append_drop k w).symm
          _ = w.take k ++ v.map (fun x => x + k) := by rw [htail_shift]
      · exact hu
    · rintro ⟨v, _, hu, _⟩ x hx
      have hxr : x ∈ List.range' 1 k := hu.mem_iff.mp hx
      obtain ⟨j, hj, hval⟩ := List.mem_range'.mp hxr
      omega
  have first_indecomp_factor (w : List ℕ)
      (hw : w.Perm (List.range' 1 w.length)) (hn : 0 < w.length) :
      ∃ (k : ℕ) (v : List ℕ), 0 < k ∧ k ≤ w.length ∧
        w = w.take k ++ v.map (fun x => x + k) ∧
        (w.take k).Perm (List.range' 1 k) ∧
        v.Perm (List.range' 1 (w.length - k)) ∧
        (∀ j, 0 < j → j < k → ∃ x ∈ (w.take k).take j, j < x) := by
    classical
    let P : ℕ → Prop := fun k =>
      0 < k ∧ k ≤ w.length ∧ ∀ x ∈ w.take k, x ≤ k
    have hex : ∃ k, P k := by
      refine ⟨w.length, hn, le_refl _, ?_⟩
      intro x hx
      have hxw : x ∈ w := by simpa using hx
      obtain ⟨i, hi, hval⟩ := List.mem_range'.mp (hw.mem_iff.mp hxw)
      omega
    let k := Nat.find hex
    have hk : P k := Nat.find_spec hex
    obtain ⟨v, heq, hu, hv⟩ := (prefix_cut_iff_sum w hw k hk.2.1).mp hk.2.2
    refine ⟨k, v, hk.1, hk.2.1, heq, hu, hv, ?_⟩
    intro j hj hjk
    have hnot : ¬ ∀ x ∈ w.take j, x ≤ j := by
      intro hjcut
      have hPj : P j := ⟨hj, by omega, hjcut⟩
      have hmin : k ≤ j := Nat.find_min' hex hPj
      omega
    push Not at hnot
    obtain ⟨x, hx, hgt⟩ := hnot
    refine ⟨x, ?_, hgt⟩
    simpa [List.take_take, Nat.min_eq_left (by omega : j ≤ k)] using hx
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hn : w = []
    · subst w
      exact ⟨[], rfl, by simp⟩
    · have hpos : 0 < w.length := List.length_pos_iff_ne_nil.mpr hn
      obtain ⟨k, v, hkpos, hkle, heq, hu, hv, hindec⟩ :=
        first_indecomp_factor w hw hpos
      have hvlen : v.length = w.length - k := by
        simpa using hv.length_eq
      have hvlt : v.length < n := by omega
      have hvvalid : v.Perm (List.range' 1 v.length) := by
        simpa [hvlen] using hv
      obtain ⟨fs, hfs, hgood⟩ := ih v.length hvlt v hvvalid rfl
      refine ⟨w.take k :: fs, ?_, ?_⟩
      · simp only [sumFactors]
        rw [hfs]
        simpa [List.length_take, Nat.min_eq_left hkle] using heq.symm
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | htail
        · have hlenU : (w.take k).length = k := by simp [hkle]
          refine ⟨by omega, ?_, ?_⟩
          · simpa [hlenU] using hu
          · apply (indecomp_iff (w.take k) (by simpa [hlenU] using hu)).mpr
            intro j hj hjk
            exact hindec j hj (by simpa [hlenU] using hjk)
        · exact hgood a htail

/-- A permutation's normalized sequence of indecomposable sum factors is unique. -/
theorem sum_factorization_unique (w : List ℕ) (fs gs : List (List ℕ))
    (hfs : sumFactors fs = w) (hgs : sumFactors gs = w)
    (hgoodfs : ∀ u ∈ fs, 0 < u.length ∧
      u.Perm (List.range' 1 u.length) ∧ sumIndecomposable u)
    (hgoodgs : ∀ u ∈ gs, 0 < u.length ∧
      u.Perm (List.range' 1 u.length) ∧ sumIndecomposable u) : fs = gs := by
  let Factor (u : List ℕ) : Prop :=
    0 < u.length ∧ u.Perm (List.range' 1 u.length) ∧ sumIndecomposable u
  have indecomp_iff (p : List ℕ) (hp : p.Perm (List.range' 1 p.length)) :
      sumIndecomposable p ↔
        ∀ k, 0 < k → k < p.length → ∃ x ∈ p.take k, k < x := by
    classical
    constructor
    · intro hind k hk hkl
      by_contra hnone
      have hsmall : ∀ x ∈ p.take k, x ≤ k := by
        intro x hx
        by_contra hgt
        exact hnone ⟨x, hx, by omega⟩
      have hnodup := hp.nodup_iff.mpr List.nodup_range'
      have hsubset : (p.take k).toFinset ⊆ (List.range' 1 k).toFinset := by
        intro x hx
        have hxt := List.mem_toFinset.mp hx
        obtain ⟨a, ha, heq⟩ := List.mem_range'.mp
          (hp.mem_iff.mp (List.mem_of_mem_take hxt))
        exact List.mem_toFinset.mpr
          (List.mem_range'.mpr ⟨x - 1, by have := hsmall x hxt; omega, by omega⟩)
      have hcard : (p.take k).toFinset.card = (List.range' 1 k).toFinset.card := by
        simp [List.card_toFinset, List.dedup_eq_self.mpr hnodup.take,
          List.dedup_eq_self.mpr List.nodup_range', Nat.min_eq_left (by omega : k ≤ p.length)]
      have hset := Finset.eq_of_subset_of_card_le hsubset (by omega)
      obtain ⟨i, j, hji⟩ := hind ⟨k, hkl⟩ hk
      have hx := List.get_mem (p.take k) i
      have hy := List.get_mem (p.drop k) j
      have hybound : (p.drop k).get j ≤ k := le_trans hji (hsmall _ hx)
      obtain ⟨a, ha, heq⟩ := List.mem_range'.mp
        (hp.mem_iff.mp (List.mem_of_mem_drop hy))
      have hyfirst : (p.drop k).get j ∈ p.take k := by
        apply List.mem_toFinset.mp
        rw [hset]
        exact List.mem_toFinset.mpr
          (List.mem_range'.mpr ⟨(p.drop k).get j - 1, by omega, by omega⟩)
      exact List.disjoint_left.mp (List.disjoint_take_drop hnodup (le_refl k)) hyfirst hy
    · intro hind k hk
      by_contra hnone
      have hsep : ∀ x ∈ p.take k.val, ∀ y ∈ p.drop k.val, x < y := by
        intro x hx y hy
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
        obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hy
        by_contra hnot
        exact hnone ⟨i, j, by omega⟩
      obtain ⟨x, hx, hgt⟩ := hind k.val hk k.isLt
      exact (not_le_of_gt hgt) (separated_prefix_cut p hp k.val (by omega) hsep x hx)
  have first_cut_unique (w : List ℕ) (k j : ℕ)
      (hk : ∀ x ∈ w.take k, x ≤ k)
      (hj : ∀ x ∈ w.take j, x ≤ j)
      (hik : ∀ t, 0 < t → t < k → ∃ x ∈ (w.take k).take t, t < x)
      (hij : ∀ t, 0 < t → t < j → ∃ x ∈ (w.take j).take t, t < x)
      (hkpos : 0 < k) (hjpos : 0 < j) : k = j := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hkj | hjk
    · obtain ⟨x, hx, hgt⟩ := hij k hkpos hkj
      have hxk : x ∈ w.take k := by
        simpa [List.take_take, Nat.min_eq_left (by omega : k ≤ j)] using hx
      exact (not_le_of_gt hgt) (hk x hxk)
    · obtain ⟨x, hx, hgt⟩ := hik j hjpos hjk
      have hxj : x ∈ w.take j := by
        simpa [List.take_take, Nat.min_eq_left (by omega : j ≤ k)] using hx
      exact (not_le_of_gt hgt) (hj x hxj)
  induction hlen : w.length using Nat.strong_induction_on generalizing w fs gs with
  | h n ih =>
    cases fs with
    | nil =>
        cases gs with
        | nil => rfl
        | cons v vs =>
            have hv : Factor v := hgoodgs v (by simp)
            have hzero : w = [] := by simpa [sumFactors] using hfs.symm
            have hsumNil : v ++ (sumFactors vs).map (fun x => x + v.length) = [] := by
              simpa [sumFactors] using hgs.trans hzero
            have hvnil : v = [] := (List.append_eq_nil_iff.mp hsumNil).1
            exact ((List.length_pos_iff_ne_nil.mp hv.1) hvnil).elim
    | cons u us =>
        have hu : Factor u := hgoodfs u (by simp)
        cases gs with
        | nil =>
            have hzero : w = [] := by simpa [sumFactors] using hgs.symm
            have hsumNil : u ++ (sumFactors us).map (fun x => x + u.length) = [] := by
              simpa [sumFactors] using hfs.trans hzero
            have hunil : u = [] := (List.append_eq_nil_iff.mp hsumNil).1
            exact ((List.length_pos_iff_ne_nil.mp hu.1) hunil).elim
        | cons v vs =>
            have hv : Factor v := hgoodgs v (by simp)
            have htakeU : w.take u.length = u := by
              rw [← hfs]
              simp [sumFactors]
            have htakeV : w.take v.length = v := by
              rw [← hgs]
              simp [sumFactors]
            have hcutU : ∀ x ∈ w.take u.length, x ≤ u.length := by
              intro x hx
              rw [htakeU] at hx
              obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hu.2.1.mem_iff.mp hx)
              omega
            have hcutV : ∀ x ∈ w.take v.length, x ≤ v.length := by
              intro x hx
              rw [htakeV] at hx
              obtain ⟨a, ha, heq⟩ := List.mem_range'.mp (hv.2.1.mem_iff.mp hx)
              omega
            have hindecompU : ∀ t, 0 < t → t < u.length →
                ∃ x ∈ (w.take u.length).take t, t < x := by
              intro t ht htu
              rw [htakeU]
              exact (indecomp_iff u hu.2.1).mp hu.2.2 t ht htu
            have hindecompV : ∀ t, 0 < t → t < v.length →
                ∃ x ∈ (w.take v.length).take t, t < x := by
              intro t ht htv
              rw [htakeV]
              exact (indecomp_iff v hv.2.1).mp hv.2.2 t ht htv
            have hlenEq : u.length = v.length :=
              first_cut_unique w u.length v.length hcutU hcutV
                hindecompU hindecompV hu.1 hv.1
            have huv : u = v := by
              calc
                u = w.take u.length := htakeU.symm
                _ = w.take v.length := by rw [hlenEq]
                _ = v := htakeV
            subst v
            have htail : sumFactors us = sumFactors vs := by
              have heq : u ++ (sumFactors us).map (fun x => x + u.length) =
                  u ++ (sumFactors vs).map (fun x => x + u.length) :=
                hfs.trans hgs.symm
              have hmap := List.append_cancel_left heq
              exact (List.map_inj_right (fun x y h => by omega)).mp hmap
            have hlt : (sumFactors us).length < n := by
              have hlength := congrArg List.length hfs
              simp [sumFactors] at hlength
              have hupos : 0 < u.length := hu.1
              omega
            have hus : ∀ a ∈ us, Factor a := by
              intro a ha
              exact hgoodfs a (by simp [ha])
            have hvs : ∀ a ∈ vs, Factor a := by
              intro a ha
              exact hgoodgs a (by simp [ha])
            have hrest := ih (sumFactors us).length hlt (sumFactors us) us vs
              rfl htail.symm hus hvs rfl
            rw [hrest]

end D5.S3.Combinatorics.FundamentalBijection.ThetaBasicSumFactors
