/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedWeightSixteenSyndrome
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedWeightSixteenSyndrome
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.EightCubeBits]
   utility: none
   digest: Construct a paired weight-sixteen syndrome and separate it from one-exchange orbits. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.EightCubeBits

/-! The paired dimer support has a weight-sixteen syndrome outside
every one-exchange orbit. The distance-two graph supplies the invariant. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedWeightSixteenSyndrome

open Finset
open scoped symmDiff
local notation "flip" => BalancedCriticalSpectrum.flip
open EightCubeBits (Vertex Word cube toggle cube_toggle toggle_injective shell
  coeff row IsKernel oddRows distance relabel asFunction asFunction_symmDiff
  row_symmDiff row_singleton)
open EightCubeBits (relabel_distance)

/-- The twelve-site dimer support in little-endian coordinates. -/
def D : Word := {5, 65, 68, 71, 77, 86, 89, 90, 102, 105, 106, 197}

def pairedSyndrome : Word :=
  {21, 22, 25, 26, 37, 38, 41, 42, 213, 214, 217, 218, 229, 230, 233, 234}

/-- Translate the four paired directions by the vertex with mask 21.
The four bits of `t` select the directions with masks 3, 12, 48, and 192. -/
def pairedVertex (t : Fin 16) : Vertex :=
  (BitVec.ofNat 8 21 ^^^
    BitVec.ofNat 8 (3 * (t.val % 2)) ^^^
    BitVec.ofNat 8 (12 * (t.val / 2 % 2)) ^^^
    BitVec.ofNat 8 (48 * (t.val / 4 % 2)) ^^^
    BitVec.ofNat 8 (192 * (t.val / 8))).toFin

def distanceTwoNeighbors (S : Word) (x : Vertex) : Word :=
  S.filter fun y => distance x y = 2

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem oddRows_D : oddRows D = pairedSyndrome := by
  decide +kernel

theorem pairedSyndrome_affine :
    pairedSyndrome = (univ : Finset (Fin 16)).image pairedVertex := by
  decide +kernel

theorem oddRows_D_card : (oddRows D).card = 16 := by
  rw [oddRows_D, pairedSyndrome_affine]
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem oddRows_D_degree (x : Vertex) (hx : x ∈ oddRows D) :
    (distanceTwoNeighbors (oddRows D) x).card = 4 := by
  rw [oddRows_D] at hx ⊢
  have h : pairedSyndrome.filter (fun y => (distanceTwoNeighbors pairedSyndrome y).card = 4)
      = pairedSyndrome := by
    decide +kernel
  exact filter_eq_self.mp h x hx

private theorem oddRows_kernel_symmDiff {K : Word} (hK : IsKernel K) (W : Word) :
    oddRows (K ∆ W) = oddRows W := by
  ext r
  simp only [oddRows, mem_filter, mem_univ, true_and, row_symmDiff, hK r, zero_add]

private theorem oddRows_singleton (u : Vertex) : oddRows {u} = shell u := by
  ext r
  by_cases hr : r ∈ shell u <;> simp [oddRows, row_singleton, coeff, hr]

/-- Binary adjacency sends an exchange on a kernel word to the XOR of two shells. -/
theorem oddRows_one_exchange {K : Word} (hK : IsKernel K) {u v : Vertex} (huv : u ≠ v) :
    oddRows (K ∆ ({u, v} : Word)) = shell u ∆ shell v := by
  have hpair : ({u, v} : Word) = ({u} : Word) ∆ {v} := by
    ext x
    simp only [mem_symmDiff, mem_insert, mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl ⟨rfl, huv⟩
      · exact Or.inr ⟨rfl, huv.symm⟩
    · rintro (⟨hu, _⟩ | ⟨hv, _⟩)
      · exact Or.inl hu
      · exact Or.inr hv
  rw [oddRows_kernel_symmDiff hK, hpair]
  have hrow (r : Vertex) : row (({u} : Word) ∆ {v}) r = coeff (shell u ∆ shell v) r := by
    simp only [row_symmDiff, row_singleton]
    have h := congrFun (asFunction_symmDiff (shell u) (shell v)) (cube r)
    simpa only [asFunction, Pi.add_apply, Equiv.symm_apply_apply] using h.symm
  ext r
  by_cases hr : r ∈ shell u ∆ shell v <;> simp [oddRows, hrow, coeff, hr]

private theorem shell_card (x : Vertex) : (shell x).card = 8 := by
  rw [shell, card_image_of_injective _ (toggle_injective x), card_univ, Fintype.card_fin]

private theorem distance_two_of_mem_shell {c x y : Vertex} (hx : x ∈ shell c)
    (hy : y ∈ shell c) (hxy : x ≠ y) : distance x y = 2 := by
  obtain ⟨i, _, rfl⟩ := mem_image.mp hx
  obtain ⟨j, _, rfl⟩ := mem_image.mp hy
  have hij : i ≠ j := fun h => hxy (congrArg (toggle c) h)
  have hdiff : (univ.filter (fun a => flip (cube c) i a ≠ flip (cube c) j a)) =
      ({i, j} : Finset (Fin 8)) := by
    ext a
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    by_cases hi : a = i
    · subst a
      cases h : cube c i <;> simp [BalancedCriticalSpectrum.flip, hij, h]
    · by_cases hj : a = j
      · subst a
        cases h : cube c j <;> simp [BalancedCriticalSpectrum.flip, hij.symm, h]
      · simp [BalancedCriticalSpectrum.flip, hi, hj]
  unfold distance hammingDist
  simp only [cube_toggle]
  rw [hdiff, card_insert_of_notMem (by simpa using hij), card_singleton]

private theorem seven_le_degree_of_shell_subset {S : Word} {c x : Vertex}
    (hc : shell c ⊆ S) (hx : x ∈ shell c) :
    7 ≤ (distanceTwoNeighbors S x).card := by
  have hcard : ((shell c).erase x).card = 7 := by
    rw [card_erase_of_mem hx, shell_card]
  rw [← hcard]
  apply card_le_card
  intro y hy
  obtain ⟨hyx, hyc⟩ := mem_erase.mp hy
  exact mem_filter.mpr ⟨hc hyc, distance_two_of_mem_shell hx hyc hyx.symm⟩

/-- Weight sixteen forces disjoint shells. Each point keeps the other seven
points of its own shell as distance-two neighbors. -/
theorem seven_le_degree_of_shell_symmDiff {u v x : Vertex}
    (hcard : (shell u ∆ shell v).card = 16) (hx : x ∈ shell u ∆ shell v) :
    7 ≤ (distanceTwoNeighbors (shell u ∆ shell v) x).card := by
  have hUnion := card_union_add_card_inter (shell u) (shell v)
  have hDiff := card_sdiff_add_card_eq_card
    (inter_subset_union (s := shell u) (t := shell v))
  have hWeight : ((shell u ∪ shell v) \ (shell u ∩ shell v)).card = 16 := by
    simpa only [symmDiff_eq_sup_sdiff_inf, Finset.sup_eq_union, Finset.inf_eq_inter] using hcard
  rw [hWeight] at hDiff
  rw [shell_card, shell_card] at hUnion
  have hDisjoint : Disjoint (shell u) (shell v) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    apply card_eq_zero.mp
    omega
  rw [Finset.symmDiff_eq_union hDisjoint] at hx ⊢
  rcases mem_union.mp hx with hu | hv
  · exact seven_le_degree_of_shell_subset (fun _ h => mem_union_left _ h) hu
  · exact seven_le_degree_of_shell_subset (fun _ h => mem_union_right _ h) hv

private theorem syndrome_ne_one_exchange_of_profile {S : Word} (hcard : S.card = 16)
    (hdegree : ∀ x ∈ S, (distanceTwoNeighbors S x).card = 4)
    {K : Word} (hK : IsKernel K) (u v : Vertex) :
    S ≠ oddRows (K ∆ ({u, v} : Word)) := by
  intro heq
  by_cases huv : u = v
  · subst v
    rw [show ({u, u} : Word) = {u} by simp, oddRows_kernel_symmDiff hK,
      oddRows_singleton] at heq
    rw [heq, shell_card] at hcard
    omega
  · rw [oddRows_one_exchange hK huv] at heq
    obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < S.card)
    have hsize : (shell u ∆ shell v).card = 16 := by rwa [← heq]
    have hx' : x ∈ shell u ∆ shell v := by rwa [← heq]
    have hseven := seven_le_degree_of_shell_symmDiff hsize hx'
    rw [← heq, hdegree x hx] at hseven
    omega

theorem D_ne_one_exchange {K : Word} (hK : IsKernel K) (u v : Vertex) :
    D ≠ K ∆ ({u, v} : Word) := by
  intro heq
  exact syndrome_ne_one_exchange_of_profile oddRows_D_card oddRows_D_degree hK u v
    (congrArg oddRows heq)

/-- Graph-metric invariance transports the degree in the distance-two graph. -/
theorem distanceTwoDegree_map (e : Vertex ≃ Vertex)
    (he : ∀ x y, distance (e x) (e y) = distance x y) (S : Word) (x : Vertex) :
    (distanceTwoNeighbors (S.map e.toEmbedding) (e x)).card =
      (distanceTwoNeighbors S x).card := by
  unfold distanceTwoNeighbors
  rw [filter_map, card_map]
  apply congrArg Finset.card
  apply filter_congr
  intro y _
  change distance (e x) (e y) = 2 ↔ distance x y = 2
  rw [he]

/-- Every cube translate and coordinate permutation of this syndrome rules out
every one-exchange chart. -/
theorem relabeled_syndrome_ne_one_exchange (σ : Equiv.Perm (Fin 8)) (a : Vertex)
    {K : Word} (hK : IsKernel K) (u v : Vertex) :
    (oddRows D).map (relabel σ a).toEmbedding ≠ oddRows (K ∆ ({u, v} : Word)) := by
  refine syndrome_ne_one_exchange_of_profile ?_ ?_ hK u v
  · rw [card_map, oddRows_D_card]
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
    exact (distanceTwoDegree_map (relabel σ a) (relabel_distance σ a) (oddRows D) y).trans
      (oddRows_D_degree y hy)

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairedWeightSixteenSyndrome
