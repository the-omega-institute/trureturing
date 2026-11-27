/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32LayerCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9Weight32LayerCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9BinaryAxialCompletion]
   utility: none
   digest: Bound the binary axial completion fiber by sixteen settings and eight classes under layer swap. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCodeCoordinateClass
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9Weight32DegreeTwoRows
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9BinaryAxialCompletion
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality
import Mathlib.Tactic.NormNum

/-! Signed square cancellation bounds the number of binary axial completions. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9Weight32LayerCount

open Finset
open scoped BigOperators symmDiff
open EightCubeBits (Vertex Word cube toggle cube_toggle toggle_injective shell_card shell shell_symm
  coeff row row_eq_card IsKernel asFunction asFunction_symmDiff isKernel_iff_adjacency)
open Q9Weight32DegreeTwoRows (rowDegree degreeTwoRows mem_degreeTwoRows eighteen_le_degreeTwoRows)
open BinaryCubeKernelSupport (binarySites four_dvd_binarySites_card)
open BinaryCubeAnalyticWeightTwelve (weight_less_twelve_one_shell weight_twelve_two_shells)
open BinaryCubeSplitReconstruction (delta)
open BalancedCriticalSpectrum (Q flip)
open ComponentBoundary.BinaryCubeHalfKernel (adjacency)
open ComponentBoundary.Q9SignedAxialFold (transverse)
open ComponentBoundary.Q9IsotropicHuang (flipSign)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel (adjacency_add)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.EightCubeBits (shell_asFunction toggle_twice)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeKernelSupport (cubeFinsetEquiv cubeFinsetEquiv_flip)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedGeometricObstruction (bitRow bitRow_sum flipSign_unit transverse_square)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9BinaryAxialCompletion (sign_flip)

private theorem binary_cases (z : ZMod 2) : z = 0 ∨ z = 1 :=
  (show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) z

private theorem sum_shell {R : Type*} [AddCommMonoid R] (x : Vertex) (f : Vertex → R) :
    (∑ y ∈ shell x, f y) = ∑ i : Fin 8, f (toggle x i) := by
  unfold shell
  rw [sum_image]
  intro i _ j _ hij
  exact toggle_injective x hij

private theorem sum_shell_inter {R : Type*} [AddCommMonoid R] (x : Vertex) (T : Word)
    (f : Vertex → R) (hf : ∀ y ∉ T, f y = 0) :
    (∑ y ∈ shell x ∩ T, f y) = ∑ y ∈ shell x, f y := by
  apply sum_subset inter_subset_left
  intro y hy hy'
  exact hf y (fun h => hy' (mem_inter.mpr ⟨hy, h⟩))

private theorem pair_sum {α R : Type*} [DecidableEq α] [AddCommMonoid R]
    (f : α → R) {a b : α} (hab : a ≠ b) :
    (∑ y ∈ ({a, b} : Finset α), f y) = f a + f b := by
  simp [hab]

private theorem common_shell_card_le_two {x y : Vertex} (hxy : x ≠ y) :
    (shell x ∩ shell y).card ≤ 2 := by
  let g : Vertex ≃ Finset (Fin 8) := cube.trans (cubeFinsetEquiv 8)
  have hs (z : Vertex) : (shell z).map g.toEmbedding =
      ComponentBoundary.HuangThreeColumnIntegrality.neighbors (g z) := by
    rw [shell, map_eq_image, image_image,
      ComponentBoundary.HuangThreeColumnIntegrality.neighbors]
    congr 1
    funext i
    change cubeFinsetEquiv 8 (cube (toggle z i)) = cubeFinsetEquiv 8 (cube z) ∆ {i}
    rw [cube_toggle, cubeFinsetEquiv_flip]
  rw [← card_map (f := g.toEmbedding) (s := shell x ∩ shell y), map_inter, hs x, hs y]
  exact ComponentBoundary.HuangThreeColumnIntegrality.common_neighbors_card_le_two
    (fun h => hxy (g.injective h))

private def signedEntry (x y : Vertex) : ℤ :=
  bitRow (fun z => if z = y then 1 else 0) x

private theorem signedEntry_toggle (x : Vertex) (i : Fin 8) :
    signedEntry x (toggle x i) = flipSign i (cube x) := by
  unfold signedEntry
  rw [bitRow_sum, sum_eq_single i]
  · simp
  · intro j _ hji
    have h : toggle x j ≠ toggle x i := fun he => hji (toggle_injective x he)
    simp [h]
  · simp

private theorem signedEntry_zero {x y : Vertex} (hy : y ∉ shell x) :
    signedEntry x y = 0 := by
  unfold signedEntry
  rw [bitRow_sum]
  apply sum_eq_zero
  intro i _
  have h : toggle x i ≠ y := fun he =>
    hy (mem_image.mpr ⟨i, mem_univ _, he⟩)
  simp [h]

private theorem signedEntry_unit {x y : Vertex} (hy : y ∈ shell x) :
    signedEntry x y = 1 ∨ signedEntry x y = -1 := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hy
  rw [signedEntry_toggle]
  exact flipSign_unit i (cube x)

private theorem signedEntry_symm (x y : Vertex) : signedEntry x y = signedEntry y x := by
  by_cases hy : y ∈ shell x
  · obtain ⟨i, _, rfl⟩ := mem_image.mp hy
    calc
      signedEntry x (toggle x i) = flipSign i (cube x) := signedEntry_toggle x i
      _ = flipSign i (cube (toggle x i)) := by rw [cube_toggle, sign_flip]
      _ = signedEntry (toggle x i) x := by
        simpa only [toggle_twice] using (signedEntry_toggle (toggle x i) i).symm
  · rw [signedEntry_zero hy, signedEntry_zero (fun h => hy (shell_symm.mp h))]

private theorem bitRow_eq_sum (v : Vertex → ℤ) (x : Vertex) :
    bitRow v x = ∑ y ∈ shell x, signedEntry x y * v y := by
  rw [sum_shell, bitRow_sum]
  exact sum_congr rfl (fun i _ => by rw [signedEntry_toggle])

private theorem square_pair_sign {p q x y : Vertex} (hpq : p ≠ q) (hxy : x ≠ y)
    (hx : x ∈ shell p ∩ shell q) (hy : y ∈ shell p ∩ shell q) :
    signedEntry x p * signedEntry x q + signedEntry y p * signedEntry y q = 0 := by
  have hsub : ({x, y} : Word) ⊆ shell p ∩ shell q := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact hx
    · simpa only [mem_singleton.mp hz] using hy
  have hcommon : ({x, y} : Word) = shell p ∩ shell q :=
    eq_of_subset_of_card_le hsub (by simpa [hxy] using common_shell_card_le_two hpq)
  have hpair : (∑ z ∈ shell p, signedEntry p z * signedEntry z q) =
      signedEntry p x * signedEntry x q + signedEntry p y * signedEntry y q := by
    rw [← sum_shell_inter p (shell q) (fun z => signedEntry p z * signedEntry z q) (fun z hz => by
      rw [signedEntry_zero (fun h => hz (shell_symm.mp h)), mul_zero])]
    rw [← hcommon, pair_sum _ hxy]
  have hdelta :
      bitRow (fun z => signedEntry z q) p = 0 := by
    let d : Vertex → ℤ := fun z => if z = q then 1 else 0
    change bitRow (bitRow d) p = 0
    have hcomp : bitRow d ∘ cube.symm = transverse (d ∘ cube.symm) := by
      funext z
      simp [Function.comp_apply, bitRow]
    unfold bitRow
    change transverse (bitRow d ∘ cube.symm) (cube p) = 0
    rw [hcomp, transverse_square]
    simp [Function.comp_apply, d, hpq]
  rw [bitRow_eq_sum, hpair, signedEntry_symm p x, signedEntry_symm p y] at hdelta
  exact hdelta

/-- A signed Huang row divisible by four cannot duplicate the neighbor pair of
another degree-two row on the same signed support. -/
theorem degreeTwoRows_injOn_neighborPair {T : Word} {v : Vertex → ℤ} {e : Q 8 → ℤ}
    (hv : ∀ t ∈ T, v t = 1 ∨ v t = -1) (hv0 : ∀ t ∉ T, v t = 0)
    (hAv : ∀ x, transverse (v ∘ cube.symm) x = -4 * e x) :
    Set.InjOn (fun x : Vertex => shell x ∩ T) (degreeTwoRows T : Set Vertex) := by
  intro x hx y _hy heq
  by_contra hxy
  have hxcard : (shell x ∩ T).card = 2 := mem_degreeTwoRows.mp hx
  obtain ⟨p, q, hpq, hpair⟩ := card_eq_two.mp hxcard
  have hpair' : shell y ∩ T = ({p, q} : Word) := heq.symm.trans hpair
  have hprod (z : Vertex) (hz : shell z ∩ T = ({p, q} : Word)) :
      signedEntry z p * signedEntry z q = -(v p * v q) := by
    have hp : p ∈ shell z ∩ T := by rw [hz]; simp
    have hq : q ∈ shell z ∩ T := by rw [hz]; simp
    have hsum := hAv (cube z)
    change bitRow v z = -4 * e (cube z) at hsum
    rw [bitRow_eq_sum,
      ← sum_shell_inter z T (fun t => signedEntry z t * v t) (fun t ht => by
        rw [hv0 t ht, mul_zero]), hz, pair_sum _ hpq] at hsum
    rcases hv p (mem_inter.mp hp).2 with hpv | hpv <;>
      rcases hv q (mem_inter.mp hq).2 with hqv | hqv <;>
      rcases signedEntry_unit (mem_inter.mp hp).1 with hps | hps <;>
      rcases signedEntry_unit (mem_inter.mp hq).1 with hqs | hqs <;>
      norm_num [hpv, hqv, hps, hqs] at hsum ⊢ <;> omega
  have hxcommon : x ∈ shell p ∩ shell q := by
    have hp : p ∈ shell x ∩ T := by rw [hpair]; simp
    have hq : q ∈ shell x ∩ T := by rw [hpair]; simp
    exact mem_inter.mpr ⟨shell_symm.mp (mem_inter.mp hp).1, shell_symm.mp (mem_inter.mp hq).1⟩
  have hycommon : y ∈ shell p ∩ shell q := by
    have hp : p ∈ shell y ∩ T := by rw [hpair']; simp
    have hq : q ∈ shell y ∩ T := by rw [hpair']; simp
    exact mem_inter.mpr ⟨shell_symm.mp (mem_inter.mp hp).1, shell_symm.mp (mem_inter.mp hq).1⟩
  have hzero := square_pair_sign hpq hxy hxcommon hycommon
  rw [hprod x hpair, hprod y hpair'] at hzero
  have hp : p ∈ shell x ∩ T := by rw [hpair]; simp
  have hq : q ∈ shell x ∩ T := by rw [hpair]; simp
  rcases hv p (mem_inter.mp hp).2 with h | h <;>
    rcases hv q (mem_inter.mp hq).2 with h' | h' <;> norm_num [h, h'] at hzero

private def extend {T : Word} (c : T → ZMod 2) (x : Vertex) : ZMod 2 :=
  if hx : x ∈ T then c ⟨x, hx⟩ else 0

/-- The binary cube neighbor map with columns restricted to the support. -/
def neighborMap (T : Word) : (T → ZMod 2) →+ (Vertex → ZMod 2) where
  toFun c x := ∑ y ∈ shell x, extend c y
  map_zero' := by
    funext x
    change (∑ y ∈ shell x, extend (0 : T → ZMod 2) y) = 0
    apply sum_eq_zero
    intro y _
    by_cases hy : y ∈ T <;> simp [extend, hy]
  map_add' c d := by
    funext x
    change (∑ y ∈ shell x, extend (c + d) y) =
      (∑ y ∈ shell x, extend c y) + ∑ y ∈ shell x, extend d y
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro y _
    by_cases hy : y ∈ T <;> simp [extend, hy]

/-- The kernel of the full binary row system. -/
abbrev neighborKernel (T : Word) := (neighborMap T).ker

private def sites {T : Word} (c : T → ZMod 2) : Word :=
  (univ.filter fun t : T => c t = 1).map (Function.Embedding.subtype _)

private theorem mem_sites {T : Word} (c : T → ZMod 2) (x : Vertex) :
    x ∈ sites c ↔ ∃ hx : x ∈ T, c ⟨x, hx⟩ = 1 := by
  constructor
  · intro hx
    obtain ⟨⟨y, hy⟩, h, rfl⟩ := mem_map.mp hx
    exact ⟨hy, (mem_filter.mp h).2⟩
  · rintro ⟨hx, h⟩
    exact mem_map.mpr ⟨⟨x, hx⟩, mem_filter.mpr ⟨mem_univ _, h⟩, rfl⟩

private theorem extend_eq_coeff {T : Word} (c : T → ZMod 2) (x : Vertex) :
    extend c x = coeff (sites c) x := by
  by_cases hx : x ∈ T
  · rcases binary_cases (c ⟨x, hx⟩) with h | h <;> simp [extend, coeff, mem_sites, hx, h]
  · simp [extend, coeff, mem_sites, hx]

set_option maxHeartbeats 1500000 in
private theorem neighborMap_eq_row {T : Word} (c : T → ZMod 2) (x : Vertex) :
    neighborMap T c x = row (sites c) x := by
  change (∑ y ∈ shell x, extend c y) = _
  simp only [extend_eq_coeff, sum_shell, row]

private theorem sites_subset {T : Word} (c : T → ZMod 2) : sites c ⊆ T :=
  fun x hx => ((mem_sites c x).mp hx).choose

private theorem card_sites {T : Word} (c : T → ZMod 2) :
    (sites c).card = Nat.card {t : T // c t = 1} := by
  unfold sites
  rw [card_map]
  exact (Nat.subtype_card (univ.filter fun t : T => c t = 1) (fun t => by simp)).symm

private theorem sites_one {T : Word} : sites (1 : T → ZMod 2) = T := by
  ext x
  simp [mem_sites]

private theorem one_mem_neighborKernel {T : Word}
    (hdegree : ∀ x, rowDegree T x = 0 ∨ rowDegree T x = 2 ∨ rowDegree T x = 4) :
    (1 : T → ZMod 2) ∈ neighborKernel T := by
  change neighborMap T 1 = 0
  funext x
  rw [neighborMap_eq_row, sites_one, row_eq_card]
  change ((rowDegree T x : ℕ) : ZMod 2) = 0
  rcases hdegree x with h | h | h <;> rw [h] <;> decide

private theorem kernel_sites {T : Word} {c : T → ZMod 2} (hc : c ∈ neighborKernel T) :
    IsKernel (sites c) := by
  intro x
  rw [← neighborMap_eq_row]
  exact congrFun (show neighborMap T c = 0 from hc) x

private theorem weight_ge_sixteen {S : Word} (hS : IsKernel S) (hpos : 0 < S.card)
    (hcap : ∀ x, (shell x ∩ S).card ≤ 4) : 16 ≤ S.card := by
  classical
  let f := asFunction S
  have hf : adjacency f = 0 := (isKernel_iff_adjacency S).mp hS
  have hsites : binarySites f = S.map cube.toEmbedding := by
    ext q
    obtain ⟨x, rfl⟩ := cube.surjective q
    simp only [binarySites, mem_filter, mem_univ, true_and, f, asFunction,
      mem_map_equiv, Equiv.symm_apply_apply]
    by_cases hx : x ∈ S <;> simp [coeff, hx]
  have hcard : (binarySites f).card = S.card := by rw [hsites, card_map]
  have hdiv := four_dvd_binarySites_card (m := 2) (by decide) hf
  rw [hcard] at hdiv
  have hshell (x : Vertex) : asFunction (shell x) = adjacency (delta (cube x)) := by
    rw [shell_asFunction]
    congr 1
    funext q
    obtain ⟨y, rfl⟩ := cube.surjective q
    simp [asFunction, coeff, delta]
  have hinj {U V : Word} (h : asFunction U = asFunction V) : U = V := by
    ext x
    have hx := congrFun h (cube x)
    simp only [asFunction, Equiv.symm_apply_apply, coeff] at hx
    by_cases hu : x ∈ U <;> by_cases hv : x ∈ V <;> simp [hu, hv] at hx ⊢
  by_contra hsmall
  have h12 : S.card ≤ 12 := by omega
  by_cases hw : S.card = 12
  · obtain ⟨p, q, _, h⟩ := weight_twelve_two_shells f hf (hcard.trans hw)
    obtain ⟨x, rfl⟩ := cube.surjective p
    obtain ⟨y, rfl⟩ := cube.surjective q
    have he : S = shell x ∆ shell y := by
      apply hinj
      rw [asFunction_symmDiff, hshell, hshell, ← adjacency_add]
      exact h
    have hdiff : ((shell x ∪ shell y) \ (shell x ∩ shell y)).card = 12 := by
      rw [he] at hw
      simpa only [symmDiff_eq_sup_sdiff_inf, Finset.sup_eq_union, Finset.inf_eq_inter] using hw
    have hunion := card_union_add_card_inter (shell x) (shell y)
    have hparts := card_sdiff_add_card_eq_card
      (inter_subset_union (s := shell x) (t := shell y))
    rw [shell_card, shell_card] at hunion
    rw [hdiff] at hparts
    have hinter : (shell x ∩ shell y).card = 2 := by omega
    have hleft : shell x ∩ S = shell x \ shell y := by
      rw [he]
      ext z
      simp only [mem_inter, mem_symmDiff, mem_sdiff]
      by_cases hx : z ∈ shell x <;> by_cases hy : z ∈ shell y <;> simp [hx, hy]
    have hbad := hcap x
    rw [hleft, card_sdiff, inter_comm, shell_card, hinter] at hbad
    omega
  · obtain ⟨_, p, h⟩ := weight_less_twelve_one_shell f hf (by omega) (by omega)
    obtain ⟨x, rfl⟩ := cube.surjective p
    have he : S = shell x := hinj (h.trans (hshell x).symm)
    have hbad := hcap x
    rw [he, inter_self, shell_card] at hbad
    omega

private theorem sites_complement_card {T : Word} (c : T → ZMod 2) :
    (sites c).card + (sites (c + 1)).card = T.card := by
  have he : sites (c + 1) = T \ sites c := by
    ext x
    by_cases hx : x ∈ T
    · rcases binary_cases (c ⟨x, hx⟩) with h | h
      · simp [mem_sites, hx, h]
      · simp [mem_sites, hx, h, CharTwo.add_self_eq_zero]
    · simp [mem_sites, hx]
  rw [he, add_comm]
  exact card_sdiff_add_card_eq_card (sites_subset c)

private theorem sites_card_pos {T : Word} {c : T → ZMod 2} (hc : c ≠ 0) :
    0 < (sites c).card := by
  by_contra h
  have hempty : sites c = ∅ := card_eq_zero.mp (by omega)
  apply hc
  funext t
  change c t = 0
  rcases binary_cases (c t) with ht | ht
  · exact ht
  · have hmem := (mem_sites c t.val).mpr ⟨t.property, ht⟩
    simp [hempty] at hmem

private theorem kernel_word_weight {T : Word} (hsize : T.card = 32)
    (hcap : ∀ x, rowDegree T x ≤ 4) (hone : (1 : T → ZMod 2) ∈ neighborKernel T)
    (c : T → ZMod 2) (hc : c ∈ neighborKernel T) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    Nat.card {t : T // c t = 1} = 16 := by
  have lower (d : T → ZMod 2) (hd : d ∈ neighborKernel T) (hd0 : d ≠ 0) :
      16 ≤ (sites d).card :=
    weight_ge_sixteen (kernel_sites hd) (sites_card_pos hd0) fun x =>
      (card_le_card (inter_subset_inter_left (s := shell x) (sites_subset d))).trans (hcap x)
  have hc' : c + 1 ≠ 0 := by
    intro h
    apply hc1
    funext t
    have ht := congrFun h t
    change c t + 1 = 0 at ht
    rcases binary_cases (c t) with h0 | h1
    · simp [h0] at ht
    · exact h1
  have h₁ := lower c hc hc0
  have h₂ := lower (c + 1) ((neighborKernel T).add_mem hc hone) hc'
  have hsum := sites_complement_card c
  rw [hsize] at hsum
  rw [← card_sites]
  omega

private theorem overlap_of_degreeTwoRows {T : Word} (hsize : T.card = 32)
    (hrows : 18 ≤ (degreeTwoRows T).card) :
    ∃ x ∈ degreeTwoRows T, ∃ y ∈ degreeTwoRows T, x ≠ y ∧
      ∃ a, a ∈ shell x ∩ T ∧ a ∈ shell y ∩ T := by
  classical
  by_contra h
  let R := degreeTwoRows T
  let P : Vertex → Word := fun x => shell x ∩ T
  have hdisj : (R : Set Vertex).PairwiseDisjoint P := by
    intro x hx y hy hxy
    apply disjoint_left.mpr
    intro a ha hb
    exact h ⟨x, hx, y, hy, hxy, a, ha, hb⟩
  have hcount : (R.biUnion P).card = R.card * 2 := by
    rw [card_biUnion hdisj]
    exact sum_const_nat (fun x hx => mem_degreeTwoRows.mp hx)
  have hsub : R.biUnion P ⊆ T := by
    intro a ha
    obtain ⟨x, _, hx⟩ := mem_biUnion.mp ha
    exact (mem_inter.mp hx).2
  have hle := card_le_card hsub
  rw [hcount, hsize] at hle
  change 18 ≤ R.card at hrows
  omega

private theorem pair_at_vertex {P : Word} {a : Vertex} (ha : a ∈ P) (hP : P.card = 2) :
    ∃ b, a ≠ b ∧ P = {a, b} := by
  have hcard : (P.erase a).card = 1 := by rw [card_erase_of_mem ha, hP]
  obtain ⟨b, hb⟩ := card_eq_one.mp hcard
  have hab : a ≠ b := by
    intro he
    subst b
    exact notMem_erase a P (hb ▸ mem_singleton_self a)
  exact ⟨b, hab, by rw [← insert_erase ha, hb]⟩

private theorem equal_on_pair {T : Word} {a b x : Vertex}
    (hab : a ≠ b) (hp : shell x ∩ T = ({a, b} : Word)) (ha : a ∈ T) (hb : b ∈ T)
    (c : T → ZMod 2) (hc : c ∈ neighborKernel T) :
    c ⟨b, hb⟩ = c ⟨a, ha⟩ := by
  have hrow : neighborMap T c x = (0 : Vertex → ZMod 2) x :=
    congrFun (show neighborMap T c = 0 from hc) x
  have h : (∑ y ∈ shell x, extend c y) = 0 := by
    simpa only [neighborMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] using hrow
  have hv (t : Vertex) (ht : t ∉ T) : extend c t = 0 := by
    simp only [extend, dif_neg ht]
  have hrestricted : (∑ y ∈ ({a, b} : Word), extend c y) = 0 := by
    simpa only [hp] using (sum_shell_inter x T (extend c) hv).trans h
  have habSum : extend c a + extend c b = 0 :=
    (pair_sum (extend c) hab).symm.trans hrestricted
  have hsum : c ⟨a, ha⟩ + c ⟨b, hb⟩ = 0 := by
    simpa only [extend, dif_pos ha, dif_pos hb] using habSum
  have he : ∀ p q : ZMod 2, p + q = 0 → q = p := by decide
  exact he _ _ hsum

private theorem exists_large_coordinateClass {T : Word} (hsize : T.card = 32)
    (hrows : 18 ≤ (degreeTwoRows T).card)
    (hinj : Set.InjOn (fun x : Vertex => shell x ∩ T) (degreeTwoRows T : Set Vertex)) :
    ∃ a : T, 3 ≤ Nat.card {b : T // ∀ c ∈ neighborKernel T, c b = c a} := by
  classical
  obtain ⟨x, hx, y, hy, hxy, a, hax, hay⟩ := overlap_of_degreeTwoRows hsize hrows
  obtain ⟨b, hab, hp⟩ := pair_at_vertex hax (mem_degreeTwoRows.mp hx)
  obtain ⟨d, had, hq⟩ := pair_at_vertex hay (mem_degreeTwoRows.mp hy)
  have hbd : b ≠ d := by
    intro h
    subst d
    exact hxy (hinj hx hy (hp.trans hq.symm))
  have haT : a ∈ T := (mem_inter.mp hax).2
  have hbT : b ∈ T := (mem_inter.mp (show b ∈ shell x ∩ T by rw [hp]; simp)).2
  have hdT : d ∈ T := (mem_inter.mp (show d ∈ shell y ∩ T by rw [hq]; simp)).2
  let aT : T := ⟨a, haT⟩
  let bT : T := ⟨b, hbT⟩
  let dT : T := ⟨d, hdT⟩
  have hab' : aT ≠ bT := fun h => hab (congrArg Subtype.val h)
  have had' : aT ≠ dT := fun h => had (congrArg Subtype.val h)
  have hbd' : bT ≠ dT := fun h => hbd (congrArg Subtype.val h)
  let C : Finset T := univ.filter fun t => ∀ c ∈ neighborKernel T, c t = c aT
  have hC (t : T) : t ∈ C ↔ ∀ c ∈ neighborKernel T, c t = c aT := by simp [C]
  have hsub : ({aT, bT, dT} : Finset T) ⊆ C := by
    intro t ht
    simp only [mem_insert, mem_singleton] at ht
    apply (hC t).mpr
    intro c hc
    rcases ht with rfl | rfl | rfl
    · rfl
    · exact equal_on_pair hab hp haT hbT c hc
    · exact equal_on_pair had hq haT hdT c hc
  refine ⟨aT, ?_⟩
  rw [Nat.subtype_card C hC]
  have h3 : ({aT, bT, dT} : Finset T).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab', had']), card_insert_of_notMem (by simp [hbd']),
      card_singleton]
  simpa only [h3] using card_le_card hsub

/-- The cardinal bound uses the degree-two row injection, independently of the
construction of the signs or of the inhomogeneous layer equation. -/
theorem card_neighborKernel_le_of_injOn {T : Word} (hsize : T.card = 32)
    (hdegree : ∀ x, rowDegree T x = 0 ∨ rowDegree T x = 2 ∨ rowDegree T x = 4)
    (hinj : Set.InjOn (fun x : Vertex => shell x ∩ T) (degreeTwoRows T : Set Vertex)) :
    Nat.card (neighborKernel T) ≤ 16 := by
  have hone := one_mem_neighborKernel hdegree
  have hcap (x : Vertex) : rowDegree T x ≤ 4 := by
    rcases hdegree x with h | h | h <;> omega
  obtain ⟨a, ha⟩ := exists_large_coordinateClass hsize
    (eighteen_le_degreeTwoRows hsize hdegree) hinj
  have hlen : Fintype.card T = 2 * 16 := by simpa only [Fintype.card_coe] using hsize
  have hprod := BinaryCode.card_mul_coordinateClass_card (neighborKernel T) 16 hlen hone
    (kernel_word_weight hsize hcap hone) a
  let k := Nat.card (neighborKernel T)
  let m := Nat.card {b : T // ∀ c ∈ neighborKernel T, c b = c a}
  change k * m = 64 at hprod
  change 3 ≤ m at ha
  change k ≤ 16
  by_contra h
  have hk : 17 ≤ k := by omega
  have hm : m < 4 := by
    by_contra hn
    have hm4 : 4 ≤ m := by omega
    have hmul : 17 * 4 ≤ k * m := Nat.mul_le_mul hk hm4
    omega
  have hm3 : m = 3 := by omega
  rw [hm3] at hprod
  omega

/-- At most sixteen homogeneous layer settings for a signed weight-32 support. -/
theorem card_neighborKernel_le {T : Word} {v : Vertex → ℤ} {e : Q 8 → ℤ}
    (hsize : T.card = 32)
    (hdegree : ∀ x, rowDegree T x = 0 ∨ rowDegree T x = 2 ∨ rowDegree T x = 4)
    (hv : ∀ t ∈ T, v t = 1 ∨ v t = -1) (hv0 : ∀ t ∉ T, v t = 0)
    (hAv : ∀ x, transverse (v ∘ cube.symm) x = -4 * e x) :
    Nat.card (neighborKernel T) ≤ 16 :=
  card_neighborKernel_le_of_injOn hsize hdegree (degreeTwoRows_injOn_neighborPair hv hv0 hAv)

/-- Each setting is a choice on the support only. -/
abbrev LayerSettings (T : Word) (rhs : Vertex → ZMod 2) :=
  {c : T → ZMod 2 // neighborMap T c = rhs}

/-- The quotient identifying a setting with its simultaneous layer complement. -/
def LayerSettingsModComplement (T : Word) (rhs : Vertex → ZMod 2) :=
  Quot (fun c d : LayerSettings T rhs => d.val = c.val + 1)

private theorem layer_add_one {T : Word} {rhs : Vertex → ZMod 2}
    (hone : (1 : T → ZMod 2) ∈ neighborKernel T) (c : LayerSettings T rhs) :
    neighborMap T (c.val + 1) = rhs := by
  rw [map_add, c.property, show neighborMap T 1 = 0 from hone, add_zero]

private theorem layer_add_one_twice {T : Word} (c : T → ZMod 2) :
    c + 1 + 1 = c := by
  funext t
  change (c t + 1) + 1 = c t
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private theorem layer_card_le {T : Word} {rhs : Vertex → ZMod 2}
    (hbound : Nat.card (neighborKernel T) ≤ 16) : Nat.card (LayerSettings T rhs) ≤ 16 := by
  classical
  by_cases hs : Nonempty (LayerSettings T rhs)
  · obtain ⟨c⟩ := hs
    let f : LayerSettings T rhs → neighborKernel T := fun d =>
      ⟨d.val - c.val, by
        change neighborMap T (d.val - c.val) = 0
        rw [map_sub, d.property, c.property, sub_self]⟩
    have hinj : Function.Injective f := by
      intro d g h
      apply Subtype.ext
      have he : d.val - c.val = g.val - c.val := congrArg Subtype.val h
      simpa only [sub_add_cancel] using congrArg (fun w : T → ZMod 2 => w + c.val) he
    exact (Nat.card_le_card_of_injective f hinj).trans hbound
  · letI : IsEmpty (LayerSettings T rhs) := ⟨fun c => hs ⟨c⟩⟩
    simp

private theorem layer_quotient_card_le {T : Word} {rhs : Vertex → ZMod 2} (a : T)
    (hone : (1 : T → ZMod 2) ∈ neighborKernel T)
    (hbound : Nat.card (LayerSettings T rhs) ≤ 16) :
    Nat.card (LayerSettingsModComplement T rhs) ≤ 8 := by
  classical
  let S := LayerSettings T rhs
  let S₀ := {c : S // c.val a = 0}
  let F : S₀ × ZMod 2 → S := fun ⟨c, b⟩ =>
    if b = 0 then c.val else ⟨c.val.val + 1, layer_add_one hone c.val⟩
  have hval (c : S₀) (b : ZMod 2) : (F (c, b)).val a = b := by
    rcases binary_cases b with h | h
    · simpa [F, h] using c.property
    · simp [F, h, c.property]
  have hF : Function.Injective F := by
    rintro ⟨c, b⟩ ⟨d, b'⟩ h
    have he : b = b' := (hval c b).symm.trans
      ((congrArg (fun l : S => l.val a) h).trans (hval d b'))
    subst b'
    have hcd : c = d := by
      apply Subtype.ext
      apply Subtype.ext
      by_cases hb : b = 0
      · exact congrArg Subtype.val (by simpa [F, hb] using h : c.val = d.val)
      · have he' := congrArg Subtype.val h
        change (F (c, b)).val = (F (d, b)).val at he'
        simp only [F, if_neg hb] at he'
        exact add_right_cancel he'
    subst d
    rfl
  have htwo : Nat.card S₀ * 2 ≤ Nat.card S := by
    simpa only [Nat.card_prod, Nat.card_zmod] using Nat.card_le_card_of_injective F hF
  let G : S₀ → LayerSettingsModComplement T rhs := fun c => Quot.mk _ c.val
  have hG : Function.Surjective G := by
    intro q
    refine Quot.inductionOn q ?_
    intro c
    rcases binary_cases (c.val a) with hz | ho
    · exact ⟨⟨c, hz⟩, rfl⟩
    · let d : S := ⟨c.val + 1, layer_add_one hone c⟩
      have hd : d.val a = 0 := by
        change c.val a + 1 = 0
        rw [ho, CharTwo.add_self_eq_zero]
      refine ⟨⟨d, hd⟩, ?_⟩
      change Quot.mk _ d = Quot.mk _ c
      apply Quot.sound
      change c.val = c.val + 1 + 1
      exact (layer_add_one_twice c.val).symm
  have hquot := Nat.card_le_card_of_surjective G hG
  change Nat.card S ≤ 16 at hbound
  omega

/-- For any binary row target, the affine layer settings have cardinality at
most sixteen, and global layer complementation leaves at most eight classes. -/
theorem card_layerSettings_le {T : Word} {v : Vertex → ℤ} {e : Q 8 → ℤ}
    (hsize : T.card = 32)
    (hdegree : ∀ x, rowDegree T x = 0 ∨ rowDegree T x = 2 ∨ rowDegree T x = 4)
    (hv : ∀ t ∈ T, v t = 1 ∨ v t = -1) (hv0 : ∀ t ∉ T, v t = 0)
    (hAv : ∀ x, transverse (v ∘ cube.symm) x = -4 * e x) (rhs : Vertex → ZMod 2) :
    Nat.card (LayerSettings T rhs) ≤ 16 ∧
      Nat.card (LayerSettingsModComplement T rhs) ≤ 8 := by
  have hbound := layer_card_le (rhs := rhs) (card_neighborKernel_le hsize hdegree hv hv0 hAv)
  obtain ⟨a, ha⟩ : T.Nonempty := card_pos.mp (by omega)
  exact ⟨hbound, layer_quotient_card_le ⟨a, ha⟩ (one_mem_neighborKernel hdegree) hbound⟩

/-- The row target in the axial completion criterion is the indicator of the
support of the even word. -/
def axialTarget (e : Q 8 → ℤ) (x : Vertex) : ZMod 2 :=
  if e (cube x) ≠ 0 then 1 else 0

set_option maxHeartbeats 1500000 in
/-- An integer layer word whose residues agree with the setting on the signed
support satisfies the repository binary row criterion exactly when the setting
satisfies this row equation. -/
theorem binaryRow_mod_two_iff {T : Word} {v : Vertex → ℤ} {e l : Q 8 → ℤ}
    (hv : ∀ t ∈ T, v t = 1 ∨ v t = -1) (hv0 : ∀ t ∉ T, v t = 0)
    (c : T → ZMod 2) (hl : ∀ t : T, (l (cube t.val) : ZMod 2) = c t) (x : Vertex) :
    Q9BinaryAxialCompletion.binaryRow (v ∘ cube.symm) l (cube x) % 2 =
      (if e (cube x) ≠ 0 then 1 else 0) ↔ neighborMap T c x = axialTarget e x := by
  let r := Q9BinaryAxialCompletion.binaryRow (v ∘ cube.symm) l (cube x)
  let b : ℤ := if e (cube x) ≠ 0 then 1 else 0
  have hr : (r : ZMod 2) = neighborMap T c x := by
    change ((∑ i : Fin 8, if (v ∘ cube.symm) (flip (cube x) i) ≠ 0 then
      l (flip (cube x) i) else 0 : ℤ) : ZMod 2) = ∑ y ∈ shell x, extend c y
    rw [Int.cast_sum, sum_shell]
    apply sum_congr rfl
    intro i _
    simp only [Function.comp_apply, ← cube_toggle, Equiv.symm_apply_apply]
    by_cases ht : toggle x i ∈ T
    · have hne : v (toggle x i) ≠ 0 := by
        rcases hv _ ht with h | h <;> simp [h]
      simpa only [if_pos hne, extend, dif_pos ht] using hl ⟨toggle x i, ht⟩
    · simp only [hv0 _ ht, ne_self_iff_false, if_false, Int.cast_zero, extend, dif_neg ht]
  have hb : (b : ZMod 2) = axialTarget e x := by
    by_cases h : e (cube x) ≠ 0 <;> simp [b, axialTarget, h]
  have hbmod : b % 2 = b := by
    by_cases h : e (cube x) ≠ 0
    · simp only [b, if_pos h]; decide
    · simp only [b, if_neg h]; decide
  change r % 2 = b ↔ neighborMap T c x = axialTarget e x
  rw [← hr, ← hb, ZMod.intCast_eq_intCast_iff']
  change r % 2 = b ↔ r % 2 = b % 2
  rw [hbmod]

/-- The actual axial row target has at most sixteen settings on the signed
support and at most eight settings up to simultaneous layer swap. -/
theorem card_axialLayerSettings_le {T : Word} {v : Vertex → ℤ} {e : Q 8 → ℤ}
    (hsize : T.card = 32)
    (hdegree : ∀ x, rowDegree T x = 0 ∨ rowDegree T x = 2 ∨ rowDegree T x = 4)
    (hv : ∀ t ∈ T, v t = 1 ∨ v t = -1) (hv0 : ∀ t ∉ T, v t = 0)
    (hAv : ∀ x, transverse (v ∘ cube.symm) x = -4 * e x) :
    Nat.card (LayerSettings T (axialTarget e)) ≤ 16 ∧
      Nat.card (LayerSettingsModComplement T (axialTarget e)) ≤ 8 :=
  card_layerSettings_le hsize hdegree hv hv0 hAv (axialTarget e)

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9Weight32LayerCount
