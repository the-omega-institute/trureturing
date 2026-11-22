/- GID: D5/S3/Combinatorics/Graph/Hypercube/BinaryKernelMinimum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Hypercube/BinaryKernelMinimum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Minimum binary adjacency-kernel supports of even cubes are neighbor shells. -/

module

public import D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCrossing
import all D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelCrossing
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Classification of the minimum supports in even cube dimensions at least six. -/

public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum

open Finset BinaryKernelCrossing
open scoped BigOperators symmDiff

variable {n : ℕ}

private theorem toggle_of_notMem {x : Finset (Fin n)} {i : Fin n} (hi : i ∉ x) :
    x ∆ {i} = insert i x := by
  rw [symmDiff_comm, Finset.symmDiff_eq_union (disjoint_singleton_left.mpr hi), singleton_union]

private theorem toggle_of_mem {x : Finset (Fin n)} {i : Fin n} (hi : i ∈ x) :
    x ∆ {i} = x.erase i := by
  have h := toggle_of_notMem (notMem_erase i x)
  rw [insert_erase hi] at h
  calc
    x ∆ {i} = (x.erase i ∆ {i}) ∆ {i} := congrArg (fun t => t ∆ {i}) h.symm
    _ = x.erase i := symmDiff_symmDiff_cancel_right _ _

private theorem toggle_injective (x : Finset (Fin n)) :
    Function.Injective (fun i : Fin n => x ∆ ({i} : Finset (Fin n))) := by
  intro i j h
  simpa using congrArg (fun t : Finset (Fin n) => x ∆ t) h

private theorem mem_directions {S : Finset (Finset (Fin n))} {x : Finset (Fin n)} {i : Fin n} :
    i ∈ neighborDirections S x ↔ x ∆ {i} ∈ S := by
  simp [neighborDirections]

private def translate (x : Finset (Fin n)) : Finset (Fin n) ≃ Finset (Fin n) where
  toFun y := x ∆ y
  invFun y := x ∆ y
  left_inv := symmDiff_symmDiff_cancel_left x
  right_inv := symmDiff_symmDiff_cancel_left x

private theorem directions_translate (S : Finset (Finset (Fin n))) (x y : Finset (Fin n)) :
    neighborDirections (S.map (translate x).toEmbedding) y = neighborDirections S (x ∆ y) := by
  ext i
  simp only [mem_directions, mem_map_equiv]
  change x ∆ (y ∆ {i}) ∈ S ↔ (x ∆ y) ∆ {i} ∈ S
  rw [symmDiff_assoc]

private theorem degree_eq_two_or_dimension {S : Finset (Finset (Fin n))}
    (hS : S.card = n) (hrows : ∀ x, Even (neighborDirections S x).card)
    {x : Finset (Fin n)} (hx : (neighborDirections S x).Nonempty) :
    (neighborDirections S x).card = 2 ∨ (neighborDirections S x).card = n := by
  let d := (neighborDirections S x).card
  change d = 2 ∨ d = n
  have hd₂ : 2 ≤ d := by
    have hpos := card_pos.mpr hx
    obtain ⟨k, hk⟩ := hrows x
    change d = k + k at hk
    change 0 < d at hpos
    omega
  have hdₙ : d ≤ n := by simpa [d] using card_le_univ (neighborDirections S x)
  have hbound : 2 * d + d * (n - d) ≤ 2 * n := by
    simpa only [hS] using (crossing_pair_bounds S x fun y _ => hrows y).2
  have hmul := congrArg (fun k : ℕ => k * (n - d)) (Nat.sub_add_cancel hd₂)
  change (d - 2 + 2) * (n - d) = d * (n - d) at hmul
  rw [Nat.add_mul] at hmul
  have hsum : 2 * (n - d) + 2 * d = 2 * n := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hdₙ]
  have hidentity : 2 * d + d * (n - d) = 2 * n + (d - 2) * (n - d) := by omega
  have hzero : (d - 2) * (n - d) = 0 := by omega
  rcases Nat.mul_eq_zero.mp hzero with h | h <;> omega

private theorem directions_eq_pair {S : Finset (Finset (Fin n))}
    {x : Finset (Fin n)} {i j : Fin n} (hij : i ≠ j)
    (hi : i ∈ neighborDirections S x) (hj : j ∈ neighborDirections S x)
    (hcap : (neighborDirections S x).card ≤ 2) :
    neighborDirections S x = {i, j} := by
  symm
  apply eq_of_subset_of_card_le
  · simp [insert_subset_iff, hi, hj]
  · simpa [card_pair hij] using hcap

private theorem toggle_pair_left {i j : Fin n} (hij : i ≠ j) :
    ({i, j} : Finset (Fin n)) ∆ {i} = {j} := by
  rw [toggle_of_mem (x := ({i, j} : Finset (Fin n))) (mem_insert_self i {j})]
  simp [hij]

private theorem toggle_pair_right {i j : Fin n} (hij : i ≠ j) :
    ({i, j} : Finset (Fin n)) ∆ {j} = {i} := by
  rw [pair_comm, toggle_pair_left hij.symm]

private theorem triple_of_pair {i j : Fin n} {t : Finset (Fin n)}
    (hij : i ≠ j) (ht : t.card = 3) (hi : i ∈ t) (hj : j ∈ t) :
    ∃ k ∈ t, k ∉ ({i, j} : Finset (Fin n)) ∧ insert k {i, j} = t := by
  have hpair := card_pair hij
  obtain ⟨k, hkt, hk⟩ := exists_mem_notMem_of_card_lt_card
    (show ({i, j} : Finset (Fin n)).card < t.card by omega)
  refine ⟨k, hkt, hk, eq_of_subset_of_card_le ?_ ?_⟩
  · simp [insert_subset_iff, hkt, hi, hj]
  · rw [card_insert_of_notMem hk, hpair, ht]

private theorem crossing_triple {S : Finset (Finset (Fin n))}
    (hrows : ∀ x, Even (neighborDirections S x).card)
    (hcap : ∀ x, (neighborDirections S x).card ≤ 2)
    {i j : Fin n} (hi : ({i} : Finset (Fin n)) ∈ S) (hj : ({j} : Finset (Fin n)) ∉ S) :
    ∃ t ∈ S, t.card = 3 ∧ i ∈ t ∧ j ∈ t ∧
      ∀ u ∈ S, u.card = 3 → i ∈ u → j ∈ u → u = t := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  let p : Finset (Fin n) := {i, j}
  have hp : p.card = 2 := card_pair hij
  have hjp : j ∈ neighborDirections S p := by
    rwa [mem_directions, toggle_pair_right hij]
  have hip : i ∉ neighborDirections S p := by
    rwa [mem_directions, toggle_pair_left hij]
  obtain ⟨r, hr⟩ := hrows p
  have hpos := card_pos.mpr ⟨j, hjp⟩
  have hnonempty : ((neighborDirections S p).erase j).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hjp]
    omega
  obtain ⟨k, hk⟩ := hnonempty
  obtain ⟨hkj, hkp⟩ := mem_erase.mp hk
  have hki : k ≠ i := fun h => hip (h ▸ hkp)
  have hkn : k ∉ p := by simp [p, hki, hkj]
  have ht : insert k p ∈ S := by
    simpa only [toggle_of_notMem hkn] using mem_directions.mp hkp
  refine ⟨insert k p, ht, by rw [card_insert_of_notMem hkn, hp], ?_, ?_, ?_⟩
  · simp [p]
  · simp [p]
  intro u hu huc hui huj
  obtain ⟨l, _, hlp, hl⟩ := triple_of_pair hij huc hui huj
  have hlrow : l ∈ neighborDirections S p := by
    rw [mem_directions, toggle_of_notMem hlp, hl]
    exact hu
  rw [directions_eq_pair hkj hkp hjp (hcap p), mem_insert, mem_singleton] at hlrow
  rcases hlrow with rfl | rfl
  · exact hl.symm
  · exact (hlp (by simp)).elim

private theorem triple_crossing_card_le_two (I t : Finset (Fin n)) (ht : t.card = 3) :
    ((t ∩ I) ×ˢ (t \ I)).card ≤ 2 := by
  rw [card_product]
  have h := card_inter_add_card_sdiff t I
  have hc : (t ∩ I).card = 0 ∨ (t ∩ I).card = 1 ∨ (t ∩ I).card = 2 ∨
      (t \ I).card = 0 := by omega
  rcases hc with h₀ | h₁ | h₂ | h₃ <;> simp [*] <;> omega

private theorem degree_two_impossible {S : Finset (Finset (Fin n))}
    (hn : 6 ≤ n) (hS : S.card = n) (hrows : ∀ x, Even (neighborDirections S x).card)
    (hcap : ∀ x, (neighborDirections S x).card ≤ 2)
    (hzero : (neighborDirections S ∅).card = 2) : False := by
  let I := neighborDirections S ∅
  let T := S.filter fun t => t.card = 3
  let L := I.image fun i => ({i} : Finset (Fin n))
  let P := I ×ˢ (univ \ I)
  let r (p : Fin n × Fin n) (t : Finset (Fin n)) := p.1 ∈ t ∧ p.2 ∈ t
  have hunit (i : Fin n) : i ∈ I ↔ ({i} : Finset (Fin n)) ∈ S := by
    simp only [I, mem_directions]
    change (⊥ : Finset (Fin n)) ∆ {i} ∈ S ↔ _
    rw [bot_symmDiff]
  have hL : L.card = 2 := by
    rw [card_image_of_injective]
    · exact hzero
    · intro i j hij
      simpa using hij
  have hLT : L ∪ T ⊆ S := by
    apply union_subset
    · intro t ht
      obtain ⟨i, hi, rfl⟩ := mem_image.mp ht
      exact (hunit i).mp hi
    · exact filter_subset _ _
  have hdisj : Disjoint L T := disjoint_left.mpr fun t ht ht' => by
    obtain ⟨i, _, rfl⟩ := mem_image.mp ht
    simpa using (mem_filter.mp ht').2
  have hP : P.card = 2 * (n - 2) := by
    rw [card_product, card_sdiff_of_subset (subset_univ I), card_univ, Fintype.card_fin, hzero]
  -- Each crossing pair has exactly one selected triple above it.
  have habove : ∀ p ∈ P, (T.bipartiteAbove r p).card = 1 := by
    rintro ⟨i, j⟩ hp
    obtain ⟨hi, hj⟩ := mem_product.mp hp
    have hj' : j ∉ I := (mem_sdiff.mp hj).2
    obtain ⟨t, ht, ht₃, hit, hjt, hu⟩ :=
      crossing_triple hrows hcap ((hunit i).mp hi) (mt (hunit j).mpr hj')
    apply card_eq_one.mpr
    refine ⟨t, ?_⟩
    ext u
    simp only [mem_bipartiteAbove, T, mem_filter, r, mem_singleton]
    constructor
    · rintro ⟨⟨hus, hu₃⟩, hui, huj⟩
      exact hu u hus hu₃ hui huj
    · rintro rfl
      exact ⟨⟨ht, ht₃⟩, hit, hjt⟩
  have hbelow (t : Finset (Fin n)) : P.bipartiteBelow r t = (t ∩ I) ×ˢ (t \ I) := by
    ext p
    simp only [mem_bipartiteBelow, P, mem_product, mem_sdiff, mem_univ, true_and, r, mem_inter]
    exact ⟨fun ⟨⟨hi, hj⟩, hit, hjt⟩ => ⟨⟨hit, hi⟩, hjt, hj⟩,
      fun ⟨⟨hit, hi⟩, hjt, hj⟩ => ⟨⟨hi, hj⟩, hit, hjt⟩⟩
  have hcount : P.card = ∑ t ∈ T, (P.bipartiteBelow r t).card := calc
    P.card = ∑ p ∈ P, (T.bipartiteAbove r p).card := by
      rw [sum_congr rfl habove]
      simp
    _ = _ := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow r
  have hlocal : ∀ t ∈ T, (P.bipartiteBelow r t).card ≤ 2 := by
    intro t ht
    rw [hbelow]
    exact triple_crossing_card_le_two I t (mem_filter.mp ht).2
  have hmax : (∑ t ∈ T, (P.bipartiteBelow r t).card) ≤ 2 * T.card := by
    simpa only [sum_const, Nat.nsmul_eq_mul, Nat.mul_comm T.card] using (sum_le_sum hlocal)
  have hLTcard := card_le_card hLT
  rw [card_union_of_disjoint hdisj, hL, hS] at hLTcard
  -- The incidence bound is tight, and the unit and triple layers exhaust the support.
  have hTcard : 2 * T.card = P.card := by omega
  have hST : L ∪ T = S := by
    apply eq_of_subset_of_card_le hLT
    rw [card_union_of_disjoint hdisj, hL, hS]
    omega
  have hcross (t : Finset (Fin n)) (ht : t ∈ S) (ht₃ : t.card = 3) :
      (t ∩ I).Nonempty := by
    have htT : t ∈ T := mem_filter.mpr ⟨ht, ht₃⟩
    by_contra h
    have hnil : t ∩ I = ∅ := not_nonempty_iff_eq_empty.mp h
    have hlt : (P.bipartiteBelow r t).card < 2 := by simp [hbelow, hnil]
    have hsum := sum_lt_sum hlocal ⟨t, htT, hlt⟩
    simp only [sum_const, Nat.nsmul_eq_mul, Nat.mul_comm T.card] at hsum
    omega
  have hlayers (t : Finset (Fin n)) (ht : t ∈ S) : t.card = 1 ∨ t.card = 3 := by
    rw [← hST, mem_union] at ht
    rcases ht with ht | ht
    · obtain ⟨i, _, rfl⟩ := mem_image.mp ht
      exact Or.inl (card_singleton i)
    · exact Or.inr (mem_filter.mp ht).2
  obtain ⟨a, b, hab, hI⟩ := card_eq_two.mp (show I.card = 2 from hzero)
  have ha : a ∈ I := by simp [hI]
  have hb : b ∈ I := by simp [hI]
  have hno_both (t : Finset (Fin n)) (ht : t ∈ S) (ht₃ : t.card = 3)
      (hat : a ∈ t) (hbt : b ∈ t) : False := by
    let p : Finset (Fin n) := {a, b}
    obtain ⟨c, _, hcp, hc⟩ := triple_of_pair hab ht₃ hat hbt
    have harow : a ∈ neighborDirections S p := by
      rw [mem_directions, toggle_pair_left hab]
      exact (hunit b).mp hb
    have hbrow : b ∈ neighborDirections S p := by
      rw [mem_directions, toggle_pair_right hab]
      exact (hunit a).mp ha
    have hcrow : c ∈ neighborDirections S p := by
      rwa [mem_directions, toggle_of_notMem hcp, hc]
    rw [directions_eq_pair hab harow hbrow (hcap p)] at hcrow
    exact hcp hcrow
  obtain ⟨j, _, hj⟩ := exists_mem_notMem_of_card_lt_card
    (show I.card < (univ : Finset (Fin n)).card by rw [card_univ, Fintype.card_fin, hzero]; omega)
  obtain ⟨t, ht, ht₃, hat, hjt, hu⟩ :=
    crossing_triple hrows hcap ((hunit a).mp ha) (mt (hunit j).mpr hj)
  have hbt : b ∉ t := fun h => hno_both t ht ht₃ hat h
  have haj : a ≠ j := fun h => hj (h ▸ ha)
  obtain ⟨k, hkt, hkp, _⟩ := triple_of_pair haj ht₃ hat hjt
  have hkj : k ≠ j := fun h => hkp (by simp [h])
  have hk : k ∉ I := by
    rw [hI, mem_insert, mem_singleton]
    rintro (rfl | rfl)
    · exact hkp (by simp)
    · exact hbt hkt
  obtain ⟨v, _, _, _, _, hv_unique⟩ :=
    crossing_triple hrows hcap ((hunit a).mp ha) (mt (hunit k).mpr hk)
  have htv : t = v := hv_unique t ht ht₃ hat hkt
  obtain ⟨l, _, hl⟩ := exists_mem_notMem_of_card_lt_card
    (show (insert b t).card < (univ : Finset (Fin n)).card by
      rw [card_insert_of_notMem hbt, ht₃, card_univ, Fintype.card_fin]
      omega)
  have hlt : l ∉ t := fun h => hl (mem_insert_of_mem h)
  let x := insert l t
  have hx : x.card = 4 := by rw [card_insert_of_notMem hlt, ht₃]
  have hbx : b ∉ x := by
    have hbl : b ≠ l := by
      rintro rfl
      exact hl (mem_insert_self b t)
    simp [x, hbl, hbt]
  -- A selected neighbor of the four-set must retain a and one of j or k.
  have hrow : neighborDirections S x = {l} := by
    ext i
    rw [mem_directions, mem_singleton]
    refine ⟨?_, ?_⟩
    · intro hi
      have hix : i ∈ x := by
        by_contra h
        have hcases := hlayers _ hi
        rw [toggle_of_notMem h, card_insert_of_notMem h, hx] at hcases
        omega
      let u := x.erase i
      have huS : u ∈ S := by simpa only [toggle_of_mem hix] using hi
      have huc : u.card = 3 := by rw [card_erase_of_mem hix, hx]
      have hau : a ∈ u := by
        obtain ⟨z, hz⟩ := hcross u huS huc
        have hzI := (mem_inter.mp hz).2
        rcases (show z = a ∨ z = b by simpa [hI] using hzI) with rfl | rfl
        · exact (mem_inter.mp hz).1
        · exact (hbx (mem_of_mem_erase (mem_inter.mp hz).1)).elim
      have hju : j ∈ u ∨ k ∈ u := by
        by_cases hji : j = i
        · exact Or.inr (mem_erase.mpr ⟨(fun h => hkj (h.trans hji.symm)), mem_insert_of_mem hkt⟩)
        · exact Or.inl (mem_erase.mpr ⟨hji, mem_insert_of_mem hjt⟩)
      have hut : u = t := hju.elim (hu u huS huc hau) fun h =>
        (hv_unique u huS huc hau h).trans htv.symm
      by_contra hil
      have hit : i ∈ t := (mem_insert.mp hix).resolve_left hil
      have hiu : i ∈ u := hut.symm ▸ hit
      exact (notMem_erase i x) hiu
    · intro hil
      subst i
      have hlx : l ∈ x := mem_insert_self l t
      rw [toggle_of_mem hlx, show x.erase l = t by simp [x, hlt]]
      exact ht
  have he := hrows x
  rw [hrow, card_singleton] at he
  obtain ⟨k, hk⟩ := he
  omega

private theorem singleton_symmDiff {a b : Fin n} (hab : a ≠ b) :
    ({a} : Finset (Fin n)) ∆ {b} = {a, b} := by
  rw [Finset.symmDiff_eq_union (disjoint_singleton.mpr hab), singleton_union]

private theorem shell_rows (he : Even n) (x y : Finset (Fin n)) :
    Even (neighborDirections (univ.image fun i : Fin n => x ∆ ({i} : Finset (Fin n))) y).card := by
  let z := x ∆ y
  have hmem (i : Fin n) :
      i ∈ neighborDirections (univ.image fun j : Fin n => x ∆ ({j} : Finset (Fin n))) y ↔
      ∃ j : Fin n, z = ({i} : Finset (Fin n)) ∆ {j} := by
    rw [mem_directions, mem_image]
    simp only [mem_univ, true_and]
    constructor
    · rintro ⟨j, hj⟩
      have h := congrArg (fun t : Finset (Fin n) => x ∆ t) hj
      change x ∆ (x ∆ {j}) = x ∆ (y ∆ {i}) at h
      rw [symmDiff_symmDiff_cancel_left, ← symmDiff_assoc] at h
      change ({j} : Finset (Fin n)) = z ∆ {i} at h
      refine ⟨j, ?_⟩
      calc
        z = (z ∆ {i}) ∆ {i} := (symmDiff_symmDiff_cancel_right _ _).symm
        _ = {j} ∆ {i} := by rw [← h]
        _ = {i} ∆ {j} := symmDiff_comm _ _
    · rintro ⟨j, hj⟩
      refine ⟨j, ?_⟩
      have hy : x ∆ z = y := symmDiff_symmDiff_cancel_left _ _
      rw [← hy, symmDiff_assoc, hj, symmDiff_symmDiff_self']
  by_cases hz : z = ∅
  · have h : neighborDirections
        (univ.image fun i : Fin n => x ∆ ({i} : Finset (Fin n))) y = univ := by
      ext i
      rw [hmem]
      exact iff_of_true ⟨i, by simpa using hz⟩ (mem_univ _)
    simpa [h] using he
  by_cases h₂ : z.card = 2
  · obtain ⟨a, b, hab, hzab⟩ := card_eq_two.mp h₂
    have hab' := singleton_symmDiff hab
    have hpair : neighborDirections
        (univ.image fun i : Fin n => x ∆ ({i} : Finset (Fin n))) y = {a, b} := by
      ext i
      rw [hmem, mem_insert, mem_singleton]
      constructor
      · rintro ⟨j, hj⟩
        have hij : j ≠ i := by
          rintro rfl
          exact hz (by simpa using hj)
        have hip : i ∈ z := by simp [hj, singleton_symmDiff hij.symm]
        simpa [hzab] using hip
      · rintro (rfl | rfl)
        · exact ⟨b, hzab.trans hab'.symm⟩
        · exact ⟨a, hzab.trans (by rw [symmDiff_comm, hab'])⟩
    rw [hpair, card_pair hab]
    exact ⟨1, rfl⟩
  have hnil : neighborDirections
      (univ.image fun i : Fin n => x ∆ ({i} : Finset (Fin n))) y = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨j, hj⟩ := (hmem i).mp hi
    have hij : j ≠ i := by
      rintro rfl
      exact hz (by simpa using hj)
    apply h₂
    rw [hj, singleton_symmDiff hij.symm, card_pair hij.symm]
  simp [hnil]

/-- In even dimensions at least six, the weight-n binary adjacency-kernel supports
are exactly the sets of all one-coordinate flips of a center. -/
theorem minimum_support_iff (hn : 6 ≤ n) (he : Even n) (S : Finset (Finset (Fin n))) :
    (S.card = n ∧ ∀ x, Even (neighborDirections S x).card) ↔
      ∃ x : Finset (Fin n), S = univ.image fun i : Fin n => x ∆ {i} := by
  constructor
  · rintro ⟨hS, hrows⟩
    by_cases hfull : ∃ x, (neighborDirections S x).card = n
    · obtain ⟨x, hx⟩ := hfull
      have hall : neighborDirections S x = univ := by
        apply eq_of_subset_of_card_le (subset_univ _)
        rw [hx, card_univ, Fintype.card_fin]
      refine ⟨x, (eq_of_subset_of_card_le ?_ ?_).symm⟩
      · intro t ht
        obtain ⟨i, _, rfl⟩ := mem_image.mp ht
        exact mem_directions.mp (show i ∈ neighborDirections S x by simp [hall])
      · rw [card_image_of_injective _ (toggle_injective x), card_univ, Fintype.card_fin, hS]
    · exfalso
      have hcap (x) : (neighborDirections S x).card ≤ 2 := by
        by_cases hx : (neighborDirections S x).Nonempty
        · rcases degree_eq_two_or_dimension hS hrows hx with h | h
          · omega
          · exact (hfull ⟨x, h⟩).elim
        · simp [not_nonempty_iff_eq_empty.mp hx]
      obtain ⟨t, ht⟩ : S.Nonempty := card_pos.mp (by omega)
      let i : Fin n := ⟨0, by omega⟩
      let x := t ∆ ({i} : Finset (Fin n))
      have hi : i ∈ neighborDirections S x := by
        simpa [mem_directions, x] using ht
      have hx : (neighborDirections S x).card = 2 :=
        (degree_eq_two_or_dimension hS hrows ⟨i, hi⟩).resolve_right fun h => hfull ⟨x, h⟩
      apply degree_two_impossible (S := S.map (translate x).toEmbedding) hn
      · simpa using hS
      · intro y
        rw [directions_translate]
        exact hrows _
      · intro y
        rw [directions_translate]
        exact hcap _
      · rw [directions_translate]
        change (neighborDirections S (x ∆ (⊥ : Finset (Fin n)))).card = 2
        rwa [symmDiff_bot]
  · rintro ⟨x, rfl⟩
    exact ⟨by rw [card_image_of_injective _ (toggle_injective x), card_univ, Fintype.card_fin],
      shell_rows he x⟩

end D5.S3.Combinatorics.Graph.Hypercube.BinaryKernelMinimum
