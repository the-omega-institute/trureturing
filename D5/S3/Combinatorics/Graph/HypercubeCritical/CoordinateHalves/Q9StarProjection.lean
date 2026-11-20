import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import Batteries.Tactic.OpenPrivate

/-! A three-coordinate star projection forces three thin cuts.

Exterior parity at a two-flip vertex ties the three leaves in each fiber.
A selected center either uses its full cubic degree on these leaves or belongs
to a closed regular subgraph with no edges in the chosen directions. Balance
rules out the latter by the uniform direction count. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9StarProjection

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum
  (Q IsBalanced flip flip_apply_same directionEdges direction_edge_count)
open BalancedCubeComponentBoundary (directions exterior_even regular_directions)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private flip_cancel_middle mem_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private balanced_subset from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

attribute [local instance] Classical.propDecidable

private def AtCenter (axes : Finset (Fin 9)) (b x : Q 9) : Prop :=
  ∀ i ∈ axes, x i = b i

/-- On the chosen axes, each selected point differs from the center in at most one bit. -/
def HasStarProjection (C : Finset (Q 9)) (axes : Finset (Fin 9)) (b : Q 9) : Prop :=
  ∀ x ∈ C, ∀ i j : Fin 9, i ∈ axes → j ∈ axes → i ≠ j → x i ≠ b i → x j = b j

private theorem flip_other (x : Q 9) {i j : Fin 9} (h : j ≠ i) :
    flip x i j = x j := Function.update_of_ne h ..

private theorem center_of_leaf {C : Finset (Q 9)} {axes : Finset (Fin 9)} {b x : Q 9}
    (hstar : HasStarProjection C axes b) {i : Fin 9} (hi : i ∈ axes)
    (hx : x ∈ C) (hd : x i ≠ b i) : AtCenter axes b (flip x i) := by
  intro j hj
  by_cases hji : j = i
  · subst j
    rw [flip_apply_same]
    exact Bool.not_eq_iff.mpr hd
  · exact (flip_other x hji).trans (hstar x hx i j hi hj (Ne.symm hji) hd)

private theorem leaves_together {C : Finset (Q 9)} {axes : Finset (Fin 9)} {b x : Q 9}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hstar : HasStarProjection C axes b)
    (hx : AtCenter axes b x) {i j : Fin 9} (hi : i ∈ axes) (hj : j ∈ axes) :
    flip x i ∈ C ↔ flip x j ∈ C := by
  by_cases hij : i = j
  · subst j
    rfl
  let z := flip (flip x i) j
  have hzi : z i ≠ b i := by
    change flip (flip x i) j i ≠ b i
    rw [flip_other _ hij, flip_apply_same, hx i hi]
    exact Bool.not_ne_self _
  have hzj : z j ≠ b j := by
    change flip (flip x i) j j ≠ b j
    rw [flip_apply_same, flip_other x (Ne.symm hij), hx j hj]
    exact Bool.not_ne_self _
  have excluded {y : Q 9} (hyi : y i ≠ b i) (hyj : y j ≠ b j) : y ∉ C :=
    fun hy => hyj (hstar y hy i j hi hj hij hyi)
  -- Every other flip preserves both discrepancies, so exterior parity applies to two terms.
  have hsub : directions C z ⊆ ({i, j} : Finset (Fin 9)) := by
    intro k hk
    by_contra hn
    have hki : i ≠ k := fun h => hn (by simp [h])
    have hkj : j ≠ k := fun h => hn (by simp [h])
    refine excluded (y := flip z k) ?_ ?_ ((mem_directions C z k).mp hk)
    · simpa only [flip_other z hki] using hzi
    · simpa only [flip_other z hkj] using hzj
  have hpair (hn : (directions C z).Nonempty) : directions C z = {i, j} := by
    have hle := card_le_card hsub
    rw [card_pair_eq_two_iff.mpr hij] at hle
    obtain ⟨m, hm⟩ := exterior_even C hr hb z (excluded hzi hzj)
    have hpos := hn.card_pos
    exact eq_of_subset_of_card_le hsub (by rw [card_pair_eq_two_iff.mpr hij]; omega)
  have hleft : j ∈ directions C z ↔ flip x i ∈ C := by
    rw [mem_directions]
    simp only [z, BalancedCriticalSpectrum.flip_flip]
  have hright : i ∈ directions C z ↔ flip x j ∈ C := by
    rw [mem_directions]
    simp only [z, flip_cancel_middle]
  rw [← hleft, ← hright]
  constructor
  · intro h
    rw [hpair ⟨j, h⟩]
    simp
  · intro h
    rw [hpair ⟨i, h⟩]
    simp

private theorem every_center_is_full {C : Finset (Q 9)} {axes : Finset (Fin 9)} {b : Q 9}
    (haxes : axes.card = 3)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hstar : HasStarProjection C axes b)
    {x : Q 9} (hxC : x ∈ C) (hx : AtCenter axes b x) {a : Fin 9} (ha : a ∈ axes) :
    flip x a ∈ C := by
  classical
  by_contra hmissing
  let E := C.filter fun u => AtCenter axes b u ∧ flip u a ∉ C
  have hsub : E ⊆ C := filter_subset _ _
  -- A center with a missing leaf has no leaf neighbors. A center with all
  -- three leaves uses its entire degree on those leaves.
  have hclosed {u v : Q 9} (hu : u ∈ E) (hv : v ∈ C) (huv : (hypercube 9).Adj u v) :
      v ∈ E := by
    obtain ⟨huC, hu0, hun⟩ := mem_filter.mp hu
    obtain ⟨j, rfl⟩ := adjacent_exists_flip huv
    have hjout : j ∉ axes := fun hj => hun ((leaves_together hr hb hstar hu0 hj ha).mp hv)
    have hv0 : AtCenter axes b (flip u j) := by
      intro k hk
      have hkj : k ≠ j := fun h => hjout (h ▸ hk)
      exact (flip_other u hkj).trans (hu0 k hk)
    have hvn : flip (flip u j) a ∉ C := by
      intro h
      have hall : axes ⊆ directions C (flip u j) := fun k hk =>
        (mem_directions C _ k).mpr ((leaves_together hr hb hstar hv0 hk ha).mpr h)
      have he := eq_of_subset_of_card_le hall (by rw [regular_directions C hr hv, haxes])
      apply hjout
      rw [he, mem_directions, BalancedCriticalSpectrum.flip_flip]
      exact huC
    exact mem_filter.mpr ⟨hv, hv0, hvn⟩
  have hreg : ((hypercube 9).induce (E : Set (Q 9))).IsRegularOfDegree 3 := by
    intro u
    have he : (hypercube 9).neighborFinset u.val ∩ E =
        (hypercube 9).neighborFinset u.val ∩ C := by
      ext v
      simp only [mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨fun ⟨huv, hv⟩ => ⟨huv, hsub hv⟩,
        fun ⟨huv, hv⟩ => ⟨huv, hclosed u.property hv huv⟩⟩
    calc
      _ = ((hypercube 9).neighborFinset u.val ∩ E).card :=
        (selected_neighbor_card (U := E) u.property).symm
      _ = ((hypercube 9).neighborFinset u.val ∩ C).card := congrArg Finset.card he
      _ = _ := (selected_neighbor_card (U := C) (hsub u.property)).trans
        (hr ⟨u.val, hsub u.property⟩)
  have hzero : directionEdges E a = 0 := by
    unfold directionEdges
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨huE, _, hflip⟩ := mem_filter.mp hu
    exact (mem_filter.mp huE).2.2 (hsub hflip)
  have hcount := direction_edge_count (d := 3) E hreg (balanced_subset hb hsub) a
  rw [hzero, Nat.mul_zero] at hcount
  have hpos : 0 < E.card := card_pos.mpr ⟨x, mem_filter.mpr ⟨hxC, hx, hmissing⟩⟩
  omega

/-- In a balanced cubic support of order 72 projecting into a star on three axes,
the side opposite the center on each of those axes has 20 vertices. -/
theorem star_projection_forces_twenty {C : Finset (Q 9)} {axes : Finset (Fin 9)} {b : Q 9}
    (hC : C.card = 72) (haxes : axes.card = 3)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hstar : HasStarProjection C axes b)
    (i : Fin 9) (hi : i ∈ axes) : (C.filter (fun x => x i = !b i)).card = 20 := by
  classical
  let Z := C.filter (AtCenter axes b)
  let L (j : Fin 9) := C.filter (fun x => x j ≠ b j)
  have hZcard (j : Fin 9) (hj : j ∈ axes) : Z.card = directionEdges C j := by
    -- Orient each edge toward the FALSE endpoint used by directionEdges.
    let orient (x : Q 9) := if b j = false then x else flip x j
    have hinv : Function.Involutive orient := by
      intro x
      by_cases h : b j = false <;> simp [orient, h]
    have hbit (x : Q 9) : orient x j = false ↔ x j = b j := by
      cases h : b j <;> cases hx : x j <;> simp [orient, h, hx]
    have hedge (x : Q 9) :
        (orient x ∈ C ∧ flip (orient x) j ∈ C) ↔ (x ∈ C ∧ flip x j ∈ C) := by
      by_cases h : b j = false
      · simp [orient, h]
      · simpa only [orient, ite_eq_right h, BalancedCriticalSpectrum.flip_flip] using
          (and_comm : (flip x j ∈ C ∧ x ∈ C) ↔ (x ∈ C ∧ flip x j ∈ C))
    unfold directionEdges
    apply card_bijective orient hinv.bijective
    intro x
    simp only [Z, mem_filter, hbit]
    constructor
    · rintro ⟨hx, hx0⟩
      obtain ⟨hy, hyflip⟩ := (hedge x).mpr
        ⟨hx, every_center_is_full haxes hr hb hstar hx hx0 hj⟩
      exact ⟨hy, hx0 j hj, hyflip⟩
    · rintro ⟨hy, hbit', hyflip⟩
      obtain ⟨hx, hxflip⟩ := (hedge x).mp ⟨hy, hyflip⟩
      have hd : flip x j j ≠ b j := by
        rw [flip_apply_same, hbit']
        exact Bool.not_ne_self _
      exact ⟨hx, by simpa only [BalancedCriticalSpectrum.flip_flip] using center_of_leaf hstar hj hxflip hd⟩
  have hz : Z.card = 12 := by
    have hd := direction_edge_count (d := 3) C hr hb i
    rw [← hZcard i hi, hC] at hd
    omega
  -- Flipping the leaf axis identifies each leaf class with the same set of base points.
  let M := (univ : Finset (Q 9)).filter (fun x => AtCenter axes b x ∧ flip x i ∈ C)
  have hLcard (j : Fin 9) (hj : j ∈ axes) : (L j).card = M.card := by
    have hinv : Function.Involutive (fun x : Q 9 => flip x j) := fun x => BalancedCriticalSpectrum.flip_flip x j
    apply card_bijective _ hinv.bijective
    intro x
    simp only [L, M, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hx, hd⟩
      have hc := center_of_leaf hstar hj hx hd
      exact ⟨hc, (leaves_together hr hb hstar hc hj hi).mp (by simpa only [BalancedCriticalSpectrum.flip_flip] using hx)⟩
    · rintro ⟨hc, hleaf⟩
      refine ⟨?_, Bool.not_eq_iff.mp ?_⟩
      · simpa only [BalancedCriticalSpectrum.flip_flip] using (leaves_together hr hb hstar hc hj hi).mpr hleaf
      · simpa only [flip_apply_same] using hc j hj
  have hdisj : (axes : Set (Fin 9)).PairwiseDisjoint L := by
    intro j hj k hk hjk
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨hxC, hxj⟩ := mem_filter.mp hx
    exact (mem_filter.mp hy).2 (hstar x hxC j k hj hk hjk hxj)
  have hZdisj : Disjoint Z (axes.biUnion L) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨j, hj, hleaf⟩ := mem_biUnion.mp hy
    exact (mem_filter.mp hleaf).2 ((mem_filter.mp hx).2 j hj)
  have hcover : Z ∪ axes.biUnion L = C := by
    ext x
    simp only [mem_union, Z, L, mem_filter, mem_biUnion]
    constructor
    · rintro (⟨hx, _⟩ | ⟨j, hj, hx, _⟩) <;> exact hx
    · intro hx
      by_cases hc : AtCenter axes b x
      · exact Or.inl ⟨hx, hc⟩
      · right
        by_contra h
        apply hc
        intro j hj
        by_contra hd
        exact h ⟨j, hj, hx, hd⟩
  have htotal : Z.card + axes.card * M.card = C.card := by
    rw [← sum_const_nat hLcard, ← card_biUnion hdisj, ← card_union_of_disjoint hZdisj, hcover]
  rw [hz, haxes, hC] at htotal
  have hcard : (L i).card = 20 := by
    rw [hLcard i hi]
    omega
  have hside : C.filter (fun x => x i = !b i) = L i := by
    ext x
    simp only [L, mem_filter, Bool.eq_not_iff]
  rw [hside, hcard]

#print axioms star_projection_forces_twenty

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9StarProjection
