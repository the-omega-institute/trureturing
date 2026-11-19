import D5.S3.Combinatorics.Graph.Hypercube
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import D5.S3.Combinatorics.Graph.HypercubeCritical.GrayPairCutCounting
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe
import Mathlib.Data.Fin.VecNotation

/-! The crossed Gray placement with partitions 012|345|678 and 012|346|578,
and second support translated in coordinates 3 through 8. Bits indicate
the selected coordinates of a point in the block description. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayCrossedPlacement

open Finset
open D5.S3.Combinatorics.Graph.Hypercube

private abbrev Vertex := BitVec 9

private instance : Fintype Vertex :=
  Fintype.ofEquiv (Fin (2 ^ 9)) (BitVec.equivFin (m := 9)).toEquiv.symm

/-- Cube adjacency in little-endian coordinates. -/
def cube : SimpleGraph Vertex :=
  (hypercube 9).comap (cubeBitVec 9)

instance : DecidableRel cube.Adj := fun x y =>
  inferInstanceAs (Decidable (hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 1))

private def blockWeight (mask x : Vertex) : Nat :=
  (univ.filter fun i : Fin 9 => (mask &&& x).getLsbD i.val = true).card

private def gray (a b c x : Vertex) : Bool :=
  let u := blockWeight a x
  let v := blockWeight b x
  let w := blockWeight c x
  decide (u ≤ 1 ∧ v ≤ 1 ∧ w ≤ 1 ∧ 2 ≤ u + v + w)

private def support (x : Vertex) : Bool :=
  gray 7 56 448 x || gray 7 88 416 (x ^^^ 504)

private def flipBit (x : Vertex) (i : Fin 9) : Vertex :=
  x ^^^ BitVec.ofNat 9 (2 ^ i.val)

/-- The union of the two placed 54-vertex Gray supports. -/
def supportUnion : Finset Vertex := univ.filter fun x => support x = true

/-- The region outside the two Gray supports and all their neighbors. -/
def residual : Finset Vertex :=
  univ.filter fun x => support x = false ∧ ∀ i, support (flipBit x i) = false

private def lower : Finset Vertex := residual.filter fun x => x &&& 7 = 0
private def middle : Finset Vertex :=
  residual.filter fun x => x &&& 7 = 3 ∨ x &&& 7 = 5 ∨ x &&& 7 = 6
private def upper : Finset Vertex := univ.filter fun x => x &&& 7 = 7

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem residual_counts :
    lower.card = 14 ∧ middle.card = 102 ∧ upper.card = 64 ∧
      residual ⊆ lower ∪ middle ∪ upper := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem upper_regular :
    ∀ x ∈ upper, (upper.filter (cube.Adj x)).card = 6 := by
  decide +kernel

private abbrev StarIndex := Fin 3 × Fin 4

private def inSlice (i : StarIndex) (y : Nat) : Vertex :=
  BitVec.ofNat 9 ((![3, 5, 6] : Fin 3 → Nat) i.1 + 8 * y)

private def center (i : StarIndex) : Vertex :=
  inSlice i ((![5, 11, 24, 52] : Fin 4 → Nat) i.2)

private def leaves (i : StarIndex) : Finset Vertex :=
  let offsets : Fin 4 → Fin 4 → Nat :=
    ![![7, 13, 21, 37], ![3, 15, 27, 43], ![25, 26, 28, 56], ![48, 53, 54, 60]]
  univ.image fun j => inSlice i (offsets i.2 j)

private def star (i : StarIndex) : Finset Vertex := insert (center i) (leaves i)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
private theorem stars_valid : ∀ i : StarIndex, (leaves i).card = 4 ∧
    (∀ v ∈ leaves i, cube.Adj (center i) v) ∧ star i ⊆ middle := by
  decide +kernel

private theorem stars_disjoint :
    ∀ i j : StarIndex, i ≠ j → Disjoint (star i) (star j) := by
  decide +kernel

/-- The crossed placement leaves room for at most 146 further selected vertices
of induced maximum degree three. Twelve stars each force one omission, and a
cut count bounds the contribution of the top six-cube by forty-two. -/
theorem residual_card_le
    (S : Finset Vertex) (hS : S ⊆ residual)
    (hdeg : ∀ v ∈ S, (S.filter (cube.Adj v)).card ≤ 3) : S.card ≤ 146 := by
  classical
  obtain ⟨hlo, hmid, hup, hcover⟩ := residual_counts
  have hstar (i : StarIndex) : (star i \ S).Nonempty := by
    obtain ⟨hleaves, hadj, _⟩ := stars_valid i
    exact GrayPairCutCounting.star_has_omission cube S (leaves i) (center i)
      hleaves hadj hdeg
  let missing (i : StarIndex) : (middle \ (S ∩ middle) : Finset Vertex) :=
    ⟨(hstar i).choose, by
      have hm := mem_sdiff.mp (hstar i).choose_spec
      exact mem_sdiff.mpr ⟨(stars_valid i).2.2 hm.1, fun hi => hm.2 (mem_inter.mp hi).1⟩⟩
  have hInjective : Function.Injective missing := by
    intro i j hij
    by_contra hne
    have he := congrArg Subtype.val hij
    change (hstar i).choose = (hstar j).choose at he
    have hi := (mem_sdiff.mp (hstar i).choose_spec).1
    have hj := (mem_sdiff.mp (hstar j).choose_spec).1
    exact Finset.disjoint_left.mp (stars_disjoint i j hne) hi (he.symm ▸ hj)
  have homit := Fintype.card_le_of_injective missing hInjective
  have hmiddle : (S ∩ middle).card ≤ 90 := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe,
      card_sdiff_of_subset inter_subset_right, hmid] at homit
    omega
  have hupper : (S ∩ upper).card ≤ 42 := by
    have h := GrayPairCutCounting.selected_card_mul_le cube upper (S ∩ upper)
      inter_subset_right 6 3 upper_regular (fun v hv =>
        (card_le_card (filter_subset_filter _ inter_subset_left)).trans
          (hdeg v (mem_inter.mp hv).1))
    rw [hup] at h
    omega
  have hlower : (S ∩ lower).card ≤ 14 := (card_le_card inter_subset_right).trans (le_of_eq hlo)
  have hsub : S ⊆ (S ∩ lower) ∪ (S ∩ middle) ∪ (S ∩ upper) := by
    intro v hv
    have hh := hcover (hS hv)
    simpa only [mem_union, mem_inter, hv, true_and] using hh
  have htotal := (card_le_card hsub).trans (card_union_le _ _)
  have hu := card_union_le (S ∩ lower) (S ∩ middle)
  omega

#print axioms residual_card_le

set_option maxRecDepth 4096 in
private theorem support_union_card : supportUnion.card = 108 := by
  decide +kernel

/-- Any set of induced maximum degree three containing this pair as a union
of components has at most 254 vertices. -/
theorem candidate_card_le
    (U : Finset Vertex) (hU : supportUnion ⊆ U)
    (hclosed : ∀ x ∈ supportUnion, ∀ y ∈ U, cube.Adj x y → y ∈ supportUnion)
    (hdeg : ∀ v ∈ U, (U.filter (cube.Adj v)).card ≤ 3) : U.card ≤ 254 := by
  have hsub : U \ supportUnion ⊆ residual := by
    intro x hx
    obtain ⟨hxU, hxN⟩ := mem_sdiff.mp hx
    refine mem_filter.mpr ⟨mem_univ _, ?_, ?_⟩
    · cases hs : support x
      · rfl
      · exact (hxN (mem_filter.mpr ⟨mem_univ _, hs⟩)).elim
    · intro i
      cases hs : support (flipBit x i)
      · rfl
      · have hAdj : cube.Adj x (flipBit x i) := by
          change (hypercube 9).Adj (cubeBitVec 9 x) (cubeBitVec 9 (flipBit x i))
          rw [flipBit, cubeBitVec_xor_single]
          exact BalancedCriticalSpectrum.flip_adj _ _
        exact (hxN (hclosed _ (mem_filter.mpr ⟨mem_univ _, hs⟩) _ hxU hAdj.symm)).elim
  have h := residual_card_le (U \ supportUnion) hsub (fun v hv =>
    (card_le_card (filter_subset_filter _ sdiff_subset)).trans
      (hdeg v (mem_sdiff.mp hv).1))
  rw [card_sdiff_of_subset hU, support_union_card] at h
  omega

#print axioms candidate_card_le

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayCrossedPlacement
