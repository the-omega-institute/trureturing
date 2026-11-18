/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointGeometry
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Actual coordinate differences for the twenty-point 11/9 theta obstruction.
 -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta

/-! Differences are taken from an actual selected root in the original cube. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry

open SimpleGraph GirthSliceCounting
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced flip)
open private diff diff_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private SideHigh compressed selected_three_hamming nine_side_three_step_cover from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private eleven_nine_theta from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointTheta

attribute [local instance] Classical.propDecidable

open Classical in
private theorem diff_self {n : Nat} (x : Q n) : diff x x = ∅ := by
  classical
  ext i
  simp [diff]

open Classical in
private theorem diff_symm {n : Nat} (x y : Q n) : diff x y = diff y x := by
  classical
  ext i
  simp [diff, ne_comm]

open Classical in
private theorem diff_empty_iff {n : Nat} (x y : Q n) : diff x y = ∅ ↔ x = y := by
  classical
  constructor
  · intro h
    funext i
    by_contra hi
    have : i ∈ diff x y := by simp [diff, hi]
    rw [h] at this
    simp at this
  · rintro rfl
    exact diff_self x

open Classical in
private theorem diff_triangle {n : Nat} (x y z : Q n) :
    diff x y = (diff x z \ diff y z) ∪ (diff y z \ diff x z) := by
  classical
  ext i
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
    simp [diff, hx, hy, hz]

open Classical in
private theorem diff_triangle_card {n : Nat} (x y z : Q n) :
    (diff x y).card + 2 * (diff x z ∩ diff y z).card =
      (diff x z).card + (diff y z).card := by
  classical
  have hd : Disjoint (diff x z \ diff y z) (diff y z \ diff x z) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hA := Finset.card_sdiff_add_card_inter (diff x z) (diff y z)
  have hB := Finset.card_sdiff_add_card_inter (diff y z) (diff x z)
  rw [Finset.inter_comm (diff y z) (diff x z)] at hB
  rw [diff_triangle x y z, Finset.card_union_of_disjoint hd]
  omega

private theorem diff_injective {n : ℕ} (o : Q n) : Function.Injective (fun x => diff x o) := by
  intro x y hxy
  change diff x o = diff y o at hxy
  funext i
  have hi : i ∈ diff x o ↔ i ∈ diff y o := by rw [hxy]
  simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  clear hxy
  cases hx : x i <;> cases hy : y i <;> cases ho : o i <;>
    simp_all [diff]

private theorem adjacent_diff_extension {n : ℕ} (o : Q n) {x y : Q n}
    (hxy : (hypercube n).Adj x y)
    (hc : (diff y o).card = (diff x o).card + 1) :
    ∃ i, i ∉ diff x o ∧ diff y o = insert i (diff x o) := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip hxy
  change y = flip x i at hi
  subst y
  by_cases hm : i ∈ diff x o
  · rw [diff_flip, if_pos hm, Finset.card_erase_of_mem hm] at hc
    omega
  · exact ⟨i, hm, by rw [diff_flip, if_neg hm]⟩

private theorem inter_card {n : ℕ} {o x y : Q n} {a b d : ℕ}
    (hx : (diff x o).card = a) (hy : (diff y o).card = b)
    (hxy : hammingDist x y = d) :
    d + 2 * (diff x o ∩ diff y o).card = a + b := by
  have h := diff_triangle_card x y o
  change hammingDist x y + 2 * (diff x o ∩ diff y o).card =
    (diff x o).card + (diff y o).card at h
  simpa only [hx, hy, hxy] using h

private theorem triple_one_overlap
    {α : Type*} [DecidableEq α] {T : Finset α} {a b t r s : α}
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (hra : r ≠ a) (hrb : r ≠ b) (hrt : r ≠ t)
    (hsa : s ≠ a) (hsb : s ≠ b) (hst : s ≠ t) (hrs : r ≠ s)
    (hT : T.card = 3)
    (hU : (T ∩ {a, t}).card = 1) (hW : (T ∩ {b, t}).card = 1)
    (hA : (T ∩ {a, t, r}).card = 2) (hC : (T ∩ {b, t, s}).card = 2) :
    T = {t, r, s} := by
  have hf (x y z : α) (hzx : z ≠ x) (hzy : z ≠ y) :
      T ∩ {x, y, z} = insert z (T ∩ {x, y}) ∧ z ∈ T ∨
        T ∩ {x, y, z} = T ∩ {x, y} ∧ z ∉ T := by
    by_cases hz : z ∈ T
    · left
      refine ⟨?_, hz⟩
      ext i
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      aesop
    · right
      refine ⟨?_, hz⟩
      ext i
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      aesop
  have hr : r ∈ T := by
    rcases hf a t r hra hrt with ⟨_, hr⟩ | ⟨he, _⟩
    · exact hr
    · rw [he, hU] at hA; omega
  have hs : s ∈ T := by
    rcases hf b t s hsb hst with ⟨_, hs⟩ | ⟨he, _⟩
    · exact hs
    · rw [he, hW] at hC; omega
  have ht : t ∈ T := by
    by_contra hnt
    have hUa : T ∩ {a, t} = if a ∈ T then {a} else ∅ := by
      ext i; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      split_ifs with ha <;> simp_all <;> aesop
    have hWb : T ∩ {b, t} = if b ∈ T then {b} else ∅ := by
      ext i; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      split_ifs with hb <;> simp_all <;> aesop
    have ha : a ∈ T := by by_contra ha; simp [hUa, ha] at hU
    have hb : b ∈ T := by by_contra hb; simp [hWb, hb] at hW
    have hfour : ({a, b, r, s} : Finset α) ⊆ T := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨ha, hb, hr, hs⟩
    have hc := Finset.card_le_card hfour
    have he : ({a, b, r, s} : Finset α).card = 4 := by
      simp [hab, hra.symm, hsa.symm, hrb.symm, hsb.symm, hrs]
    rw [he, hT] at hc
    omega
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨ht, hr, hs⟩
  · simp [hT, hrt.symm, hst.symm, hrs]

private theorem two_step_distance {n : ℕ} {x m y : Q n}
    (hxm : (hypercube n).Adj x m) (hmy : (hypercube n).Adj m y) (hxy : x ≠ y) :
    hammingDist x y = 2 := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip hxm
  obtain ⟨j, hj⟩ := adjacent_exists_flip hmy
  change m = flip x i at hi
  change y = flip m j at hj
  have hij : i ≠ j := by
    intro he
    apply hxy
    rw [hj, hi, ← he, BalancedCriticalSpectrum.flip_flip]
  rw [hammingDist_comm]
  change (diff y x).card = 2
  rw [hj, hi, diff_flip, diff_flip, diff_self]
  simp [hij.symm]

private theorem compressed_distance {n : ℕ} {S : Finset (Q n)}
    {R : Finset (S : Set (Q n))}
    {x y : SideHigh ((hypercube n).induce (S : Set (Q n))) R}
    (hxy : (compressed ((hypercube n).induce (S : Set (Q n))) R).Adj x y) :
    hammingDist x.val.val y.val.val = 2 := by
  obtain ⟨hxy, m, _, hxm, hym⟩ := hxy
  exact two_step_distance hxm hym.symm (fun he => hxy (Subtype.ext (Subtype.ext he)))

private theorem subset_of_inter_card {α : Type*} [DecidableEq α]
    {T U : Finset α} (hc : (T ∩ U).card = T.card) : T ⊆ U := by
  have he : T ∩ U = T := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hc.ge
  exact Finset.inter_eq_left.mp he

private theorem common_middle_diff {n : ℕ} {o x y m : Q n}
    (hx : (diff x o).card = 3) (hy : (diff y o).card = 3)
    (hxy : hammingDist x y = 2)
    (hxm : (hypercube n).Adj x m) (hym : (hypercube n).Adj y m) :
    diff m o = diff x o ∩ diff y o ∨ diff m o = diff x o ∪ diff y o := by
  have hi := inter_card hx hy hxy
  have hI : (diff x o ∩ diff y o).card = 2 := by omega
  have hU : (diff x o ∪ diff y o).card = 4 := by
    have h := Finset.card_union_add_card_inter (diff x o) (diff y o)
    omega
  obtain ⟨i, hm⟩ := adjacent_exists_flip hxm
  change m = flip x i at hm
  have hmcard : (diff m o).card = 2 ∨ (diff m o).card = 4 := by
    rw [hm, diff_flip]
    split_ifs with hi
    · left; rw [Finset.card_erase_of_mem hi, hx]
    · right; rw [Finset.card_insert_of_notMem hi, hx]
  have h1 : hammingDist m x = 1 := hxm.symm
  have h2 : hammingDist m y = 1 := hym.symm
  rcases hmcard with hm2 | hm4
  · left
    have hmx := inter_card hm2 hx h1
    have hmy := inter_card hm2 hy h2
    have hmxsub : diff m o ⊆ diff x o := subset_of_inter_card (by omega)
    have hmysub : diff m o ⊆ diff y o := subset_of_inter_card (by omega)
    exact Finset.eq_of_subset_of_card_le (Finset.subset_inter hmxsub hmysub) (by omega)
  · right
    have hmx := inter_card hx hm4 (show hammingDist x m = 1 from hxm)
    have hmy := inter_card hy hm4 (show hammingDist y m = 1 from hym)
    have hxmSub : diff x o ⊆ diff m o := subset_of_inter_card (by omega)
    have hymSub : diff y o ⊆ diff m o := subset_of_inter_card (by omega)
    exact (Finset.eq_of_subset_of_card_le (Finset.union_subset hxmSub hymSub) (by omega)).symm

private theorem adj_of_diff_pair_single {n : ℕ} {o x y : Q n} {a b : Fin n}
    (hab : a ≠ b) (hx : diff x o = {a, b}) (hy : diff y o = {a}) :
    (hypercube n).Adj x y := by
  change (diff x y).card = 1
  rw [diff_triangle x y o, hx, hy]
  have he : ({a, b} \ {a}) ∪ ({a} \ ({a, b} : Finset (Fin n))) = {b} := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [he, Finset.card_singleton]

private theorem adj_of_diff_subset_card {n : ℕ} {o x y : Q n}
    (hsub : diff x o ⊆ diff y o)
    (hc : (diff y o).card = (diff x o).card + 1) : (hypercube n).Adj x y := by
  have h := diff_triangle_card x y o
  rw [Finset.inter_eq_left.mpr hsub, hc] at h
  change hammingDist x y = 1
  change hammingDist x y + 2 * (diff x o).card =
    (diff x o).card + ((diff x o).card + 1) at h
  omega

private theorem low_not_three {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {m x y z : V} (hm2 : G.degree m = 2)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hmx : G.Adj m x) (hmy : G.Adj m y) (hmz : G.Adj m z) : False := by
  have hs : ({x, y, z} : Finset V) ⊆ G.neighborFinset m := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
      SimpleGraph.mem_neighborFinset]
    exact ⟨hmx, hmy, hmz⟩
  have hc := Finset.card_le_card hs
  rw [SimpleGraph.card_neighborFinset_eq_degree, hm2] at hc
  have he : ({x, y, z} : Finset V).card = 3 := by simp [hxy, hxz, hyz]
  rw [he] at hc
  omega

private theorem diff_single_adj_of_mem {n : ℕ} {o m a : Q n} {i : Fin n}
    (hm : (diff m o).card = 2) (ha : diff a o = {i}) (hi : i ∈ diff m o) :
    (hypercube n).Adj m a := by
  have h := diff_triangle_card m a o
  rw [ha, Finset.inter_singleton_of_mem hi, Finset.card_singleton, hm] at h
  change hammingDist m a = 1
  change hammingDist m a + 2 * 1 = 2 + 1 at h
  omega

private theorem unequal_root_obstruction
    {n : ℕ} {S : Finset (Q n)} {o : Q n}
    {a A B C D m k : (S : Set (Q n))}
    (hlow : ∀ {v w}, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False)
    {U W : Finset (Fin n)} {r s t h i : Fin n}
    (hU : U.card = 2) (hW : W.card = 2) (hUW : Disjoint U W)
    (hr : r ∈ W) (hs : s ∈ W) (ht : t ∈ U) (hh : h ∈ U) (hth : t ≠ h)
    (hi : i ∈ U) (ha : diff a.val o = {i})
    (hA : diff A.val o = insert r U) (hD : diff D.val o = insert s U)
    (hB : diff B.val o = insert t W) (hC : diff C.val o = insert h W)
    (hAB : A ≠ B) (hAD : A ≠ D) (hBD : B ≠ D)
    (hDC : D ≠ C) (hAC : A ≠ C)
    (ha2 : ((hypercube n).induce (S : Set (Q n))).degree a = 2)
    (hm2 : ((hypercube n).induce (S : Set (Q n))).degree m = 2)
    (hk2 : ((hypercube n).induce (S : Set (Q n))).degree k = 2)
    (hAm : ((hypercube n).induce (S : Set (Q n))).Adj A m)
    (hBm : ((hypercube n).induce (S : Set (Q n))).Adj B m)
    (hDk : ((hypercube n).induce (S : Set (Q n))).Adj D k)
    (hCk : ((hypercube n).induce (S : Set (Q n))).Adj C k) : False := by
  have hrU : r ∉ U := fun hx => Finset.disjoint_left.mp hUW hx hr
  have hsU : s ∉ U := fun hx => Finset.disjoint_left.mp hUW hx hs
  have htW : t ∉ W := fun hx => Finset.disjoint_left.mp hUW ht hx
  have hhW : h ∉ W := fun hx => Finset.disjoint_left.mp hUW hh hx
  have hA3 : (diff A.val o).card = 3 := by rw [hA, Finset.card_insert_of_notMem hrU, hU]
  have hD3 : (diff D.val o).card = 3 := by rw [hD, Finset.card_insert_of_notMem hsU, hU]
  have hB3 : (diff B.val o).card = 3 := by rw [hB, Finset.card_insert_of_notMem htW, hW]
  have hC3 : (diff C.val o).card = 3 := by rw [hC, Finset.card_insert_of_notMem hhW, hW]
  have hfull (x y : Fin n) (hx : x ∈ W) (hy : y ∈ U) :
      insert x U ∪ insert y W = U ∪ W := by
    ext j
    simp only [Finset.mem_union, Finset.mem_insert]
    aesop
  have hfour : (U ∪ W).card = 4 := by rw [Finset.card_union_of_disjoint hUW, hU, hW]
  have hm : diff m.val o = diff A.val o ∩ diff B.val o := by
    rcases common_middle_diff (x := A.val) (y := B.val) (m := m.val) hA3 hB3
        (two_step_distance hAm hBm.symm (fun he => hAB (Subtype.ext he))) hAm hBm with hm | hm
    · exact hm
    · have hmf : diff m.val o = U ∪ W := by rw [hm, hA, hB, hfull r t hr ht]
      have hdsub : diff D.val o ⊆ diff m.val o := by
        rw [hD, hmf]
        exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hs, Finset.subset_union_left⟩
      have hDm : ((hypercube n).induce (S : Set (Q n))).Adj D m :=
        adj_of_diff_subset_card (x := D.val) (y := m.val) hdsub (by rw [hmf, hfour, hD3])
      exact (low_not_three hm2 hAB hAD hBD hAm.symm hBm.symm hDm.symm).elim
  have hk : diff k.val o = diff D.val o ∩ diff C.val o := by
    rcases common_middle_diff (x := D.val) (y := C.val) (m := k.val) hD3 hC3
        (two_step_distance hDk hCk.symm (fun he => hDC (Subtype.ext he))) hDk hCk with hk | hk
    · exact hk
    · have hkf : diff k.val o = U ∪ W := by rw [hk, hD, hC, hfull s h hs hh]
      have hasub : diff A.val o ⊆ diff k.val o := by
        rw [hA, hkf]
        exact Finset.insert_subset_iff.mpr ⟨Finset.mem_union_right _ hr, Finset.subset_union_left⟩
      have hAk : ((hypercube n).induce (S : Set (Q n))).Adj A k :=
        adj_of_diff_subset_card (x := A.val) (y := k.val) hasub (by rw [hkf, hfour, hA3])
      exact (low_not_three hk2 hDC hAD.symm hAC.symm hDk.symm hCk.symm hAk.symm).elim
  have hUt : U = {t, h} := (Finset.eq_of_subset_of_card_le
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨ht, hh⟩)
    (by rw [hU, Finset.card_pair hth])).symm
  have him : i ∈ diff m.val o ∨ i ∈ diff k.val o := by
    rw [hUt] at hi
    rcases Finset.mem_insert.mp hi with hit | hih
    · left
      rw [hm, hA, hB]
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (hit ▸ ht),
        Finset.mem_insert.mpr (Or.inl hit)⟩
    · right
      have hih := Finset.mem_singleton.mp hih
      rw [hk, hD, hC]
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem (hih ▸ hh),
        Finset.mem_insert.mpr (Or.inl hih)⟩
  have hmcard : (diff m.val o).card = 2 := by
    have hc := inter_card hA3 hB3
      (two_step_distance hAm hBm.symm (fun he => hAB (Subtype.ext he)))
    rw [hm]; omega
  have hkcard : (diff k.val o).card = 2 := by
    have hc := inter_card hD3 hC3
      (two_step_distance hDk hCk.symm (fun he => hDC (Subtype.ext he)))
    rw [hk]; omega
  rcases him with him | hik
  · exact hlow (diff_single_adj_of_mem hmcard ha him) hm2 ha2
  · exact hlow (diff_single_adj_of_mem hkcard ha hik) hk2 ha2

private theorem same_root_new_coordinate
    {α : Type*} [DecidableEq α] {a b t r q : α}
    (hra : r ≠ a) (hrb : r ≠ b) (hrt : r ≠ t)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqt : q ≠ t)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (hc : (insert r ({a, t} : Finset α) ∩ insert q {b, t}).card = 2) : r = q := by
  by_contra hrq
  have he : insert r ({a, t} : Finset α) ∩ insert q {b, t} = {t} := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [he, Finset.card_singleton] at hc
  omega

private theorem not_mem_of_inter_pair_one
    {α : Type*} [DecidableEq α] {T : Finset α} {b t : α}
    (hbt : b ≠ t) (ht : t ∈ T) (hc : (T ∩ {b, t}).card = 1) : b ∉ T := by
  intro hb
  have hsub : ({b, t} : Finset α) ⊆ T := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hb, ht⟩
  rw [Finset.inter_eq_right.mpr hsub, Finset.card_pair hbt] at hc
  omega

private theorem inserted_mem_of_disjoint_inter_one
    {α : Type*} [DecidableEq α] {U W : Finset α} {r : α}
    (hUW : Disjoint U W) (hc : (insert r U ∩ W).card = 1) : r ∈ W := by
  by_contra hr
  have he : insert r U ∩ W = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hiU, hiW⟩ := Finset.mem_inter.mp hi
    rcases Finset.mem_insert.mp hiU with hir | hiU
    · exact hr (hir ▸ hiW)
    · exact Finset.disjoint_left.mp hUW hiU hiW
  rw [he, Finset.card_empty] at hc
  omega

private theorem eleven_nine_nonembedding
    {n : ℕ} {S : Finset (Q n)} {L R : Finset (S : Set (Q n))}
    (hpart : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith (L : Set _) (R : Set _))
    (hdeg : ∀ v, ((hypercube n).induce (S : Set (Q n))).degree v = 2 ∨
      ((hypercube n).induce (S : Set (Q n))).degree v = 3)
    (hlow : ∀ {v w}, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False)
    (hbal : IsBalanced S)
    (hL3 : (degreeThree ((hypercube n).induce (S : Set (Q n))) L).card = 3)
    (hR2 : (degreeTwo ((hypercube n).induce (S : Set (Q n))) R).card = 2)
    (hR3 : (degreeThree ((hypercube n).induce (S : Set (Q n))) R).card = 7)
    (hR : R.card = 9) : False := by
  let G := (hypercube n).induce (S : Set (Q n))
  have hg := BalancedCubeGirth.eight_le_egirth S hbal
  obtain ⟨u, v, w, a, b, Z, P, Q, A, B, C, D, huv, huw, hvw, hab,
    hhi, hlo, hNa, hNb, hNu, hNv, hNw, hnd, hNZ, hNP, hNQ, hAB, hDC, hzero⟩ :=
    eleven_nine_theta hpart hdeg hlow hg hL3 hR2 hR3 hR
  change degreeThree G L = {u, v, w} at hhi
  change degreeTwo G R = {a, b} at hlo
  change G.neighborFinset a = {u, v} at hNa
  change G.neighborFinset b = {v, w} at hNb
  change degreeThree G (G.neighborFinset u) = {A.val, D.val} at hNu
  change degreeThree G (G.neighborFinset v) = {Z.val} at hNv
  change degreeThree G (G.neighborFinset w) = {B.val, C.val} at hNw
  change (compressed G R).neighborFinset Z = {P, Q} at hNZ
  change (compressed G R).neighborFinset P = {Z, A, C} at hNP
  change (compressed G R).neighborFinset Q = {Z, B, D} at hNQ
  change (compressed G R).Adj A B at hAB
  change (compressed G R).Adj D C at hDC
  change ∀ x ∈ ({P, Q} : Finset (SideHigh G R)),
    degreeThree G (G.neighborFinset x.val) = ∅ at hzero
  have hZA : Z ≠ A := by intro he; have h := hnd; simp [he] at h
  have hZB : Z ≠ B := by intro he; have h := hnd; simp [he] at h
  have hZC : Z ≠ C := by intro he; have h := hnd; simp [he] at h
  have hZD : Z ≠ D := by intro he; have h := hnd; simp [he] at h
  have hZP : Z ≠ P := by intro he; have h := hnd; simp [he] at h
  have hZQ : Z ≠ Q := by intro he; have h := hnd; simp [he] at h
  have hPQ : P ≠ Q := by intro he; have h := hnd; simp [he] at h
  have hAD : A ≠ D := by intro he; have h := hnd; simp [he] at h
  have hBC : B ≠ C := by intro he; have h := hnd; simp [he] at h
  have hAnB : A ≠ B := by intro he; have h := hnd; simp [he] at h
  have hAnC : A ≠ C := by intro he; have h := hnd; simp [he] at h
  have hDnB : D ≠ B := by intro he; have h := hnd; simp [he] at h
  have hDnC : D ≠ C := by intro he; have h := hnd; simp [he] at h
  have hroots (r : (S : Set (BalancedCriticalSpectrum.Q n))) (hr : r ∈ ({u, v, w} : Finset _)) :
      r ∈ L ∧ G.degree r = 3 := by
    have hm : r ∈ degreeThree G L := by rw [hhi]; exact hr
    exact Finset.mem_filter.mp hm
  have hu := hroots u (by simp)
  have hv := hroots v (by simp)
  have hw := hroots w (by simp)
  have hadj (r : (S : Set (BalancedCriticalSpectrum.Q n))) (x : SideHigh G R)
      (hx : x.val ∈ degreeThree G (G.neighborFinset r)) : G.Adj r x.val :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hx).1
  have hno_pair (r : (S : Set (BalancedCriticalSpectrum.Q n))) (x X Y : SideHigh G R)
      (hN : degreeThree G (G.neighborFinset r) = {X.val, Y.val})
      (hxX : x ≠ X) (hxY : x ≠ Y) : ¬ G.Adj r x.val := by
    intro hrx
    have hm : x.val ∈ degreeThree G (G.neighborFinset r) :=
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hrx,
        (Finset.mem_filter.mp x.property).2⟩
    rw [hN] at hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact hxX (Subtype.ext he)
    · exact hxY (Subtype.ext (Finset.mem_singleton.mp he))
  have hthree (r : (S : Set (BalancedCriticalSpectrum.Q n))) (hr : r ∈ L ∧ G.degree r = 3)
      (x : SideHigh G R) (hn : ¬ G.Adj r x.val) : hammingDist r.val x.val.val = 3 := by
    obtain ⟨s, t, hrs, hst, htx, hrt, hsx⟩ :=
      nine_side_three_step_cover hpart hdeg hlow hg hR hr.1 hr.2
        (Finset.mem_filter.mp x.property).1 hn
    exact selected_three_hamming hbal hrs hst htx hrt hsx
  have hcard3 (x : SideHigh G R) (hx : Z ≠ x) : (diff x.val.val v.val).card = 3 := by
    have hn : ¬ G.Adj v x.val := by
      intro hvx
      have hm : x.val ∈ degreeThree G (G.neighborFinset v) :=
        Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hvx,
          (Finset.mem_filter.mp x.property).2⟩
      rw [hNv, Finset.mem_singleton] at hm
      exact hx (Subtype.ext hm).symm
    change hammingDist x.val.val v.val = 3
    rw [hammingDist_comm]
    exact hthree v hv x hn
  have hneighbor (m r : (S : Set (BalancedCriticalSpectrum.Q n))) (hr : r ∈ G.neighborFinset m) : G.Adj r m :=
    ((G.mem_neighborFinset _ _).mp hr).symm
  have hva : G.Adj v a := hneighbor a v (by rw [hNa]; simp)
  have hua : G.Adj u a := hneighbor a u (by rw [hNa]; simp)
  have hvb : G.Adj v b := hneighbor b v (by rw [hNb]; simp)
  have hwb : G.Adj w b := hneighbor b w (by rw [hNb]; simp)
  obtain ⟨α, ha⟩ := adjacent_exists_flip hva
  obtain ⟨β, hb⟩ := adjacent_exists_flip hvb
  change a.val = flip v.val α at ha
  change b.val = flip v.val β at hb
  have hda : diff a.val v.val = {α} := by rw [ha, diff_flip, diff_self]; simp
  have hdb : diff b.val v.val = {β} := by rw [hb, diff_flip, diff_self]; simp
  have hαβ : α ≠ β := by
    intro he
    apply hab
    apply Subtype.ext
    rw [ha, hb, he]
  have huc : (diff u.val v.val).card = 2 := by
    change hammingDist u.val v.val = 2
    exact two_step_distance (x := u.val) (m := a.val) (y := v.val)
      hua hva.symm (fun he => huv (Subtype.ext he))
  have hwc : (diff w.val v.val).card = 2 := by
    change hammingDist w.val v.val = 2
    exact two_step_distance (x := w.val) (m := b.val) (y := v.val)
      hwb hvb.symm (fun he => hvw (Subtype.ext he).symm)
  obtain ⟨δ, hδa, hdu⟩ := adjacent_diff_extension (x := a.val) (y := u.val)
    v.val hua.symm (by rw [hda, Finset.card_singleton, huc])
  obtain ⟨ε, hεb, hdw⟩ := adjacent_diff_extension (x := b.val) (y := w.val)
    v.val hwb.symm (by rw [hdb, Finset.card_singleton, hwc])
  rw [hda] at hδa hdu
  rw [hdb] at hεb hdw
  have hαδ : α ≠ δ := (show δ ≠ α by simpa only [Finset.mem_singleton] using hδa).symm
  have hβε : β ≠ ε := (show ε ≠ β by simpa only [Finset.mem_singleton] using hεb).symm
  rw [Finset.pair_comm δ α] at hdu
  rw [Finset.pair_comm ε β] at hdw
  have hδβ : δ ≠ β := by
    intro he
    have hub : G.Adj u b := adj_of_diff_pair_single (x := u.val) (y := b.val) hαβ.symm
      (by rw [hdu, he, Finset.pair_comm α β]) hdb
    have hm := (G.mem_neighborFinset _ _).mpr hub.symm
    rw [hNb] at hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact huv he
    · exact huw (Finset.mem_singleton.mp he)
  have hεα : ε ≠ α := by
    intro he
    have hwa : G.Adj w a := adj_of_diff_pair_single (x := w.val) (y := a.val) hαβ
      (by rw [hdw, he, Finset.pair_comm β α]) hda
    have hm := (G.mem_neighborFinset _ _).mpr hwa.symm
    rw [hNa] at hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact huw he.symm
    · exact hvw (Finset.mem_singleton.mp he).symm
  have huA : G.Adj u A.val := hadj u A (by rw [hNu]; simp)
  have huD : G.Adj u D.val := hadj u D (by rw [hNu]; simp)
  have hwB : G.Adj w B.val := hadj w B (by rw [hNw]; simp)
  have hwC : G.Adj w C.val := hadj w C (by rw [hNw]; simp)
  obtain ⟨r, hr, hA⟩ := adjacent_diff_extension (x := u.val) (y := A.val.val)
    v.val huA (by rw [hcard3 A hZA, huc])
  obtain ⟨s, hs, hD⟩ := adjacent_diff_extension (x := u.val) (y := D.val.val)
    v.val huD (by rw [hcard3 D hZD, huc])
  obtain ⟨t, ht, hB⟩ := adjacent_diff_extension (x := w.val) (y := B.val.val)
    v.val hwB (by rw [hcard3 B hZB, hwc])
  obtain ⟨h, hh, hC⟩ := adjacent_diff_extension (x := w.val) (y := C.val.val)
    v.val hwC (by rw [hcard3 C hZC, hwc])
  rw [hdu] at hr hA hs hD
  rw [hdw] at ht hB hh hC
  have hrs : r ≠ s := by
    intro he
    apply hAD
    apply Subtype.ext
    apply Subtype.ext
    apply diff_injective v.val
    change diff A.val.val v.val = diff D.val.val v.val
    rw [hA, hD, he]
  have hth : t ≠ h := by
    intro he
    apply hBC
    apply Subtype.ext
    apply Subtype.ext
    apply diff_injective v.val
    change diff B.val.val v.val = diff C.val.val v.val
    rw [hB, hC, he]
  have hinter (r0 : (S : Set (BalancedCriticalSpectrum.Q n))) (hr0 : r0 ∈ L ∧ G.degree r0 = 3)
      (hr2 : (diff r0.val v.val).card = 2) (x : SideHigh G R) (hx : Z ≠ x)
      (hn : ¬ G.Adj r0 x.val) : (diff x.val.val v.val ∩ diff r0.val v.val).card = 1 := by
    have hh := inter_card hr2 (hcard3 x hx) (hthree r0 hr0 x hn)
    rw [Finset.inter_comm] at hh
    omega
  have hAw := hinter w hw hwc A hZA (hno_pair w A B C hNw hAnB hAnC)
  have hDw := hinter w hw hwc D hZD (hno_pair w D B C hNw hDnB hDnC)
  have hBu := hinter u hu huc B hZB (hno_pair u B A D hNu hAnB.symm hDnB.symm)
  have hCu := hinter u hu huc C hZC (hno_pair u C A D hNu hAnC.symm hDnC.symm)
  have hpnone (x : SideHigh G R) (hx : x ∈ ({P, Q} : Finset _))
      (r0 : (S : Set (BalancedCriticalSpectrum.Q n))) (hr3 : G.degree r0 = 3) : ¬ G.Adj r0 x.val := by
    intro hrx
    have hm : r0 ∈ degreeThree G (G.neighborFinset x.val) :=
      Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hrx.symm, hr3⟩
    rw [hzero x hx] at hm
    exact Finset.notMem_empty _ hm
  have hPu := hinter u hu huc P hZP (hpnone P (by simp) u hu.2)
  have hPw := hinter w hw hwc P hZP (hpnone P (by simp) w hw.2)
  have hQu := hinter u hu huc Q hZQ (hpnone Q (by simp) u hu.2)
  have hQw := hinter w hw hwc Q hZQ (hpnone Q (by simp) w hw.2)
  simp only [hdu, hdw] at hAw hDw hBu hCu hPu hPw hQu hQw
  by_cases hδε : δ = ε
  · subst ε
    have hrα : r ≠ α := by exact (not_or.mp (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hr)).1
    have hrδ : r ≠ δ := by exact (not_or.mp (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hr)).2
    have hsα : s ≠ α := by exact (not_or.mp (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hs)).1
    have hsδ : s ≠ δ := by exact (not_or.mp (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hs)).2
    have htβ : t ≠ β := by exact (not_or.mp (by simpa only [Finset.mem_insert, Finset.mem_singleton] using ht)).1
    have htδ : t ≠ δ := by exact (not_or.mp (by simpa only [Finset.mem_insert, Finset.mem_singleton] using ht)).2
    have hhβ : h ≠ β := by exact (not_or.mp (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hh)).1
    have hhδ : h ≠ δ := by exact (not_or.mp (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hh)).2
    have hrβ : r ≠ β := by
      have hn := not_mem_of_inter_pair_one hδβ.symm
        (show δ ∈ diff A.val.val v.val by rw [hA]; simp) hAw
      intro he
      apply hn
      rw [hA]; simp [he]
    have hsβ : s ≠ β := by
      have hn := not_mem_of_inter_pair_one hδβ.symm
        (show δ ∈ diff D.val.val v.val by rw [hD]; simp) hDw
      intro he
      apply hn
      rw [hD]; simp [he]
    have htα : t ≠ α := by
      have hn := not_mem_of_inter_pair_one hαδ
        (show δ ∈ diff B.val.val v.val by rw [hB]; simp) hBu
      intro he
      apply hn
      rw [hB]; simp [he]
    have hhα : h ≠ α := by
      have hn := not_mem_of_inter_pair_one hαδ
        (show δ ∈ diff C.val.val v.val by rw [hC]; simp) hCu
      intro he
      apply hn
      rw [hC]; simp [he]
    have hrt : r = t := by
      apply same_root_new_coordinate hrα hrβ hrδ htα htβ htδ hαβ hαδ hδβ.symm
      have hc := inter_card (hcard3 A hZA) (hcard3 B hZB) (compressed_distance hAB)
      rw [hA, hB] at hc
      omega
    have hsh : s = h := by
      apply same_root_new_coordinate hsα hsβ hsδ hhα hhβ hhδ hαβ hαδ hδβ.symm
      have hc := inter_card (hcard3 D hZD) (hcard3 C hZC) (compressed_distance hDC)
      rw [hD, hC] at hc
      omega
    subst t
    subst h
    have hPA : (diff P.val.val v.val ∩ {α, δ, r}).card = 2 := by
      have hAP : (compressed G R).Adj P A := ((compressed G R).mem_neighborFinset _ _).mp
        (by rw [hNP]; simp)
      have hc := inter_card (hcard3 P hZP) (hcard3 A hZA) (compressed_distance hAP)
      rw [hA, Finset.insert_comm r α, Finset.pair_comm r δ] at hc
      omega
    have hPC : (diff P.val.val v.val ∩ {β, δ, s}).card = 2 := by
      have hCP : (compressed G R).Adj P C := ((compressed G R).mem_neighborFinset _ _).mp
        (by rw [hNP]; simp)
      have hc := inter_card (hcard3 P hZP) (hcard3 C hZC) (compressed_distance hCP)
      rw [hC, Finset.insert_comm s β, Finset.pair_comm s δ] at hc
      omega
    have hQD : (diff Q.val.val v.val ∩ {α, δ, s}).card = 2 := by
      have hDQ : (compressed G R).Adj Q D := ((compressed G R).mem_neighborFinset _ _).mp
        (by rw [hNQ]; simp)
      have hc := inter_card (hcard3 Q hZQ) (hcard3 D hZD) (compressed_distance hDQ)
      rw [hD, Finset.insert_comm s α, Finset.pair_comm s δ] at hc
      omega
    have hQB : (diff Q.val.val v.val ∩ {β, δ, r}).card = 2 := by
      have hBQ : (compressed G R).Adj Q B := ((compressed G R).mem_neighborFinset _ _).mp
        (by rw [hNQ]; simp)
      have hc := inter_card (hcard3 Q hZQ) (hcard3 B hZB) (compressed_distance hBQ)
      rw [hB, Finset.insert_comm r β, Finset.pair_comm r δ] at hc
      omega
    have hPset := triple_one_overlap hαβ hαδ hδβ.symm
      hrα hrβ hrδ hsα hsβ hsδ hrs (hcard3 P hZP) hPu hPw hPA hPC
    have hQset := triple_one_overlap hαβ hαδ hδβ.symm
      hsα hsβ hsδ hrα hrβ hrδ hrs.symm (hcard3 Q hZQ) hQu hQw hQD hQB
    apply hPQ
    apply Subtype.ext
    apply Subtype.ext
    apply diff_injective v.val
    change diff P.val.val v.val = diff Q.val.val v.val
    rw [hPset, hQset, Finset.pair_comm r s]
  · have hUW : Disjoint ({α, δ} : Finset (Fin n)) {β, ε} := by
      apply Finset.disjoint_left.mpr
      intro i hiU hiW
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiU hiW
      rcases hiU with he | he <;> rcases hiW with he' | he'
      · exact hαβ (he.symm.trans he')
      · exact hεα (he'.symm.trans he)
      · exact hδβ (he.symm.trans he')
      · exact hδε (he.symm.trans he')
    have hrW : r ∈ ({β, ε} : Finset (Fin n)) :=
      inserted_mem_of_disjoint_inter_one hUW (by simpa only [hA] using hAw)
    have hsW : s ∈ ({β, ε} : Finset (Fin n)) :=
      inserted_mem_of_disjoint_inter_one hUW (by simpa only [hD] using hDw)
    have htU : t ∈ ({α, δ} : Finset (Fin n)) :=
      inserted_mem_of_disjoint_inter_one hUW.symm (by simpa only [hB] using hBu)
    have hhU : h ∈ ({α, δ} : Finset (Fin n)) :=
      inserted_mem_of_disjoint_inter_one hUW.symm (by simpa only [hC] using hCu)
    obtain ⟨_, m, hm2, hAm, hBm⟩ := hAB
    obtain ⟨_, k, hk2, hDk, hCk⟩ := hDC
    have ha2 : G.degree a = 2 := (Finset.mem_filter.mp
      (show a ∈ degreeTwo G R by rw [hlo]; simp)).2
    exact unequal_root_obstruction hlow (by simp [hαδ]) (by simp [hβε]) hUW
      hrW hsW htU hhU hth (by simp) hda hA hD hB hC
      (fun he => hAnB (Subtype.ext he)) (fun he => hAD (Subtype.ext he))
      (fun he => hDnB (Subtype.ext he).symm) (fun he => hDnC (Subtype.ext he))
      (fun he => hAnC (Subtype.ext he)) ha2 hm2 hk2 hAm hBm hDk hCk

#print axioms eleven_nine_nonembedding

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
