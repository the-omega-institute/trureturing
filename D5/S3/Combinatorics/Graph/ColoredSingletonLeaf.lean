/- GID: D5/S3/Combinatorics/Graph/ColoredSingletonLeaf
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ColoredSingletonLeaf
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Singleton leaves force sharp reciprocal estimates with exact degree corrections. -/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ColoredSingletonLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A singleton color leaf adjacent to a vertex of degree two gives a reciprocal
bound retaining both the size correction and the other neighbor's exact degree.
No restriction is imposed on isolated vertices or on the other degrees. -/
theorem singleton_leaf_reciprocal_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 3) (proper : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (w l z : V) (hwl : c w ≠ c l) (hwz : c w ≠ c z) (hlz : c l ≠ c z)
    (hl : univ.filter (fun x => c x = c l) = {l})
    (hnl : G.neighborFinset l = {w}) (hnw : G.neighborFinset w = {l, z}) :
    let k := (univ.filter (fun x => c x = c w)).card - 1
    (23 / 12 : ℚ) + k / (2 * ((k : ℚ) + 1) * ((k : ℚ) + 2)) +
        1 / (2 * ((G.degree z : ℚ) + 1)) ≤
      (∑ i : Fin 3, 1 / (((univ.filter (fun x => c x = i)).card : ℚ) + 1)) +
        (1 / 2 : ℚ) * ∑ x, 1 / ((G.degree x : ℚ) + 1) := by
  classical
  let A (i : Fin 3) := univ.filter (fun x => c x = i)
  let U := (A (c w)).erase w
  let Z := A (c z)
  let k := U.card
  let r := Z.card
  let f (x : V) : ℚ := 1 / ((G.degree x : ℚ) + 1)
  have hw : w ∈ A (c w) := by simp [A]
  have hz : z ∈ Z := by simp [Z, A]
  have hk : (A (c w)).card = k + 1 := by
    simpa [k, U] using (card_erase_add_one hw).symm
  have hkn : (univ.filter (fun x => c x = c w)).card - 1 = k := by
    change (A (c w)).card - 1 = k
    omega
  have hr : 1 ≤ r := card_pos.mpr ⟨z, hz⟩
  have hcolors : ({c w, c l, c z} : Finset (Fin 3)) = univ := by
    apply eq_univ_of_card
    simp [hwl, hwz, hlz]
  have colors (x : V) : c x = c w ∨ c x = c l ∨ c x = c z := by
    have hm : c x ∈ ({c w, c l, c z} : Finset (Fin 3)) := hcolors.symm ▸ mem_univ _
    simpa only [mem_insert, mem_singleton] using hm
  have color_sum (g : Fin 3 → ℚ) : ∑ i, g i = g (c w) + g (c l) + g (c z) := by
    rw [← hcolors]
    simp [hwl, hwz, hlz, add_assoc]
  have hl' : A (c l) = {l} := hl
  have hlzv : l ≠ z := fun he => hlz (congrArg c he)
  have dw : G.degree w = 2 := by
    rw [← G.card_neighborFinset_eq_degree, hnw]
    simp [hlzv]
  have dl : G.degree l = 1 := by
    rw [← G.card_neighborFinset_eq_degree, hnl, card_singleton]
  have du (u : V) (hu : u ∈ U) : G.degree u ≤ r := by
    have huw : u ≠ w := (mem_erase.mp hu).1
    have huc : c u = c w := (mem_filter.mp (mem_erase.mp hu).2).2
    apply card_le_card (show G.neighborFinset u ⊆ Z from ?_)
    intro v hv
    have huv : G.Adj u v := (G.mem_neighborFinset u v).mp hv
    have hvc : c v = c z := by
      rcases colors v with hvw | hvl | hvz
      · exact False.elim (proper huv (huc.trans hvw.symm))
      · have hve : v = l := mem_singleton.mp (hl' ▸ (show v ∈ A (c l) by simp [A, hvl]))
        subst v
        have hum : u ∈ G.neighborFinset l := (G.mem_neighborFinset l u).mpr huv.symm
        exact False.elim (huw (mem_singleton.mp (hnl ▸ hum)))
      · exact hvz
    simp [Z, A, hvc]
  have dz (v : V) (hv : v ∈ Z.erase z) : G.degree v ≤ k := by
    have hvz : v ≠ z := (mem_erase.mp hv).1
    have hvc : c v = c z := (mem_filter.mp (mem_erase.mp hv).2).2
    apply card_le_card (show G.neighborFinset v ⊆ U from ?_)
    intro u hu
    have hvu : G.Adj v u := (G.mem_neighborFinset v u).mp hu
    have huc : c u = c w := by
      rcases colors u with huw | hul | huz
      · exact huw
      · have hue : u = l := mem_singleton.mp (hl' ▸ (show u ∈ A (c l) by simp [A, hul]))
        subst u
        have hvm : v ∈ G.neighborFinset l := (G.mem_neighborFinset l v).mpr hvu.symm
        have hvw : v = w := mem_singleton.mp (hnl ▸ hvm)
        exact False.elim (hwz (hvw ▸ hvc))
      · exact False.elim (proper hvu (hvc.trans huz.symm))
    have huw : u ≠ w := by
      intro hue
      subst u
      have hvm : v ∈ G.neighborFinset w := (G.mem_neighborFinset w v).mpr hvu.symm
      rcases mem_insert.mp (hnw ▸ hvm) with hvl | hvz'
      · exact hlz (hvl ▸ hvc)
      · exact hvz (mem_singleton.mp hvz')
    exact mem_erase.mpr ⟨huw, by simp [A, huc]⟩
  have su : (k : ℚ) / (r + 1) ≤ ∑ u ∈ U, f u := by
    calc
      (k : ℚ) / (r + 1) = ∑ _u ∈ U, (1 / ((r : ℚ) + 1)) := by simp [k, div_eq_mul_inv]
      _ ≤ ∑ u ∈ U, f u := by
        apply sum_le_sum
        intro u hu
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right (du u hu) 1
  have sz : ((r : ℚ) - 1) / (k + 1) ≤ ∑ v ∈ Z.erase z, f v := by
    calc
      ((r : ℚ) - 1) / (k + 1) = ∑ _v ∈ Z.erase z, (1 / ((k : ℚ) + 1)) := by
        simp [card_erase_of_mem hz, Nat.cast_sub hr, r, div_eq_mul_inv]
      _ ≤ ∑ v ∈ Z.erase z, f v := by
        apply sum_le_sum
        intro v hv
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right (dz v hv) 1
  have partition : (∑ x, f x) = (∑ u ∈ U, f u) + (∑ v ∈ Z.erase z, f v) +
      (1 / 3 : ℚ) + 1 / 2 + f z := by
    have hp := (sum_fiberwise univ c f).symm
    change (∑ x, f x) = ∑ i, ∑ x ∈ A i, f x at hp
    rw [color_sum, hl', sum_singleton] at hp
    have hsu := sum_erase_add (A (c w)) f hw
    have hsz := sum_erase_add Z f hz
    change (∑ u ∈ U, f u) + f w = ∑ u ∈ A (c w), f u at hsu
    change (∑ v ∈ Z.erase z, f v) + f z = ∑ v ∈ A (c z), f v at hsz
    have hfw : f w = 1 / 3 := by norm_num [f, dw]
    have hfl : f l = 1 / 2 := by norm_num [f, dl]
    linarith
  have sc : (∑ i : Fin 3, 1 / (((A i).card : ℚ) + 1)) =
      1 / ((k : ℚ) + 2) + 1 / 2 + 1 / ((r : ℚ) + 1) := by
    rw [color_sum, hl', hk]
    norm_num [r, Z, Nat.cast_add, Nat.cast_one, add_assoc]
  have hgap : 0 ≤ ((r : ℚ) - k) * ((r : ℚ) - k - 1) := by
    rcases le_or_gt r k with hrk | hkr
    · have hrk' : (r : ℚ) ≤ k := by exact_mod_cast hrk
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have hkr' : (k : ℚ) + 1 ≤ r := by exact_mod_cast hkr
      exact mul_nonneg (by linarith) (by linarith)
  have phi : (1 : ℚ) ≤ ((k : ℚ) + 2) / (2 * (r + 1)) + r / (2 * (k + 1)) := by
    have he : (((k : ℚ) + 2) / (2 * (r + 1)) + r / (2 * (k + 1))) - 1 =
        (((r : ℚ) - k) * ((r : ℚ) - k - 1)) / (2 * ((k : ℚ) + 1) * (r + 1)) := by
      field_simp
      ring
    apply sub_nonneg.mp
    rw [he]
    exact div_nonneg hgap (by positivity)
  rw [hkn]
  change (23 / 12 : ℚ) + k / (2 * ((k : ℚ) + 1) * ((k : ℚ) + 2)) +
      1 / (2 * ((G.degree z : ℚ) + 1)) ≤
    (∑ i : Fin 3, 1 / (((A i).card : ℚ) + 1)) + (1 / 2 : ℚ) * ∑ x, f x
  rw [sc, partition]
  have rearrange : (11 / 12 : ℚ) + 1 / ((k : ℚ) + 2) +
      ((k : ℚ) + 2) / (2 * (r + 1)) + ((r : ℚ) - 1) / (2 * (k + 1)) =
      11 / 12 + (((k : ℚ) + 2) / (2 * (r + 1)) + r / (2 * (k + 1))) +
        k / (2 * ((k : ℚ) + 1) * ((k : ℚ) + 2)) := by
    field_simp
    ring
  have hfz : f z / 2 = 1 / (2 * ((G.degree z : ℚ) + 1)) := by dsimp [f]; field_simp
  have lower : (11 / 12 : ℚ) + 1 / ((k : ℚ) + 2) +
      ((k : ℚ) + 2) / (2 * (r + 1)) + ((r : ℚ) - 1) / (2 * (k + 1)) + f z / 2 ≤
      1 / ((k : ℚ) + 2) + 1 / 2 + 1 / ((r : ℚ) + 1) +
        1 / 2 * ((∑ u ∈ U, f u) + (∑ v ∈ Z.erase z, f v) + 1 / 3 + 1 / 2 + f z) := by
    have he : ((k : ℚ) + 2) / (2 * (r + 1)) = (k / (r + 1)) / 2 + 1 / (r + 1) := by
      field_simp
    rw [he]
    have he' : ((r : ℚ) - 1) / (2 * (k + 1)) = (((r : ℚ) - 1) / (k + 1)) / 2 := by
      field_simp
    rw [he']
    linarith
  rw [rearrange, hfz] at lower
  linarith

/-- When both remaining color classes are singleton leaves at the same center,
every other vertex is isolated. The exact reciprocal identity includes those
isolates and implies the sharp internal payment of `13/6`. -/
theorem two_singleton_leaves_internal_payment (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 3) (proper : ∀ ⦃x y⦄, G.Adj x y → c x ≠ c y)
    (w l z : V) (hwl : c w ≠ c l) (hwz : c w ≠ c z) (hlz : c l ≠ c z)
    (hl : univ.filter (fun x => c x = c l) = {l})
    (hz : univ.filter (fun x => c x = c z) = {z})
    (hnl : G.neighborFinset l = {w}) (hnz : G.neighborFinset z = {w})
    (hnw : G.neighborFinset w = {l, z}) :
    let d := (univ.filter (fun x => c x = c w)).card + 1
    ((∑ i : Fin 3, 1 / (((univ.filter (fun x => c x = i)).card : ℚ) + 1)) +
        (1 / 2 : ℚ) * ∑ x, 1 / ((G.degree x : ℚ) + 1) =
      (d : ℚ) / 2 + 2 / 3 + 1 / d) ∧
    (13 / 6 : ℚ) ≤
      (∑ i : Fin 3, 1 / (((univ.filter (fun x => c x = i)).card : ℚ) + 1)) +
        (1 / 2 : ℚ) * ∑ x, 1 / ((G.degree x : ℚ) + 1) := by
  classical
  let A (i : Fin 3) := univ.filter (fun x => c x = i)
  let U := (A (c w)).erase w
  let k := U.card
  let f (x : V) : ℚ := 1 / ((G.degree x : ℚ) + 1)
  have hw : w ∈ A (c w) := by simp [A]
  have hk : (A (c w)).card = k + 1 := by
    simpa [k, U] using (card_erase_add_one hw).symm
  have hcolors : ({c w, c l, c z} : Finset (Fin 3)) = univ := by
    apply eq_univ_of_card
    simp [hwl, hwz, hlz]
  have colors (x : V) : c x = c w ∨ c x = c l ∨ c x = c z := by
    have hm : c x ∈ ({c w, c l, c z} : Finset (Fin 3)) := hcolors.symm ▸ mem_univ _
    simpa only [mem_insert, mem_singleton] using hm
  have color_sum (g : Fin 3 → ℚ) : ∑ i, g i = g (c w) + g (c l) + g (c z) := by
    rw [← hcolors]
    simp [hwl, hwz, hlz, add_assoc]
  have hl' : A (c l) = {l} := hl
  have hz' : A (c z) = {z} := hz
  have hlzv : l ≠ z := fun he => hlz (congrArg c he)
  have dw : G.degree w = 2 := by
    rw [← G.card_neighborFinset_eq_degree, hnw]
    simp [hlzv]
  have dl : G.degree l = 1 := by
    rw [← G.card_neighborFinset_eq_degree, hnl, card_singleton]
  have dz : G.degree z = 1 := by
    rw [← G.card_neighborFinset_eq_degree, hnz, card_singleton]
  have isolated (u : V) (hu : u ∈ U) : G.degree u = 0 := by
    have huw : u ≠ w := (mem_erase.mp hu).1
    have huc : c u = c w := (mem_filter.mp (mem_erase.mp hu).2).2
    rw [← G.card_neighborFinset_eq_degree, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    have huv : G.Adj u v := (G.mem_neighborFinset u v).mp hv
    rcases colors v with hvw | hvl | hvz
    · exact proper huv (huc.trans hvw.symm)
    · have hve : v = l := mem_singleton.mp (hl' ▸ (show v ∈ A (c l) by simp [A, hvl]))
      subst v
      have hum : u ∈ G.neighborFinset l := (G.mem_neighborFinset l u).mpr huv.symm
      exact huw (mem_singleton.mp (hnl ▸ hum))
    · have hve : v = z := mem_singleton.mp (hz' ▸ (show v ∈ A (c z) by simp [A, hvz]))
      subst v
      have hum : u ∈ G.neighborFinset z := (G.mem_neighborFinset z u).mpr huv.symm
      exact huw (mem_singleton.mp (hnz ▸ hum))
  have su : (∑ u ∈ U, f u) = k := by
    calc
      (∑ u ∈ U, f u) = ∑ _u ∈ U, (1 : ℚ) := by
        apply sum_congr rfl
        intro u hu
        simp [f, isolated u hu]
      _ = k := by simp [k]
  have partition : (∑ x, f x) = k + (4 / 3 : ℚ) := by
    have hp := (sum_fiberwise univ c f).symm
    change (∑ x, f x) = ∑ i, ∑ x ∈ A i, f x at hp
    rw [color_sum, hl', hz', sum_singleton, sum_singleton] at hp
    have hsu := sum_erase_add (A (c w)) f hw
    change (∑ u ∈ U, f u) + f w = ∑ u ∈ A (c w), f u at hsu
    have hfw : f w = 1 / 3 := by norm_num [f, dw]
    have hfl : f l = 1 / 2 := by norm_num [f, dl]
    have hfz : f z = 1 / 2 := by norm_num [f, dz]
    linarith
  have sc : (∑ i : Fin 3, 1 / (((A i).card : ℚ) + 1)) =
      1 / ((k : ℚ) + 2) + 1 := by
    rw [color_sum, hl', hz', hk]
    simp [Nat.cast_add, Nat.cast_one, add_assoc]
    ring
  change ((∑ i : Fin 3, 1 / (((A i).card : ℚ) + 1)) + (1 / 2 : ℚ) * ∑ x, f x =
      ((A (c w)).card + 1 : ℕ) / (2 : ℚ) + 2 / 3 + 1 / ((A (c w)).card + 1 : ℕ)) ∧ _
  change _ ∧ (13 / 6 : ℚ) ≤
    (∑ i : Fin 3, 1 / (((A i).card : ℚ) + 1)) + (1 / 2 : ℚ) * ∑ x, f x
  rw [sc, partition, hk]
  push_cast
  constructor
  · ring
  · have excess : (1 / ((k : ℚ) + 2) + 1 + 1 / 2 * (k + 4 / 3)) - 13 / 6 =
        (k * ((k : ℚ) + 1)) / (2 * ((k : ℚ) + 2)) := by
      field_simp
      ring
    apply sub_nonneg.mp
    rw [excess]
    positivity

end D5.S3.Combinatorics.Graph.ColoredSingletonLeaf
