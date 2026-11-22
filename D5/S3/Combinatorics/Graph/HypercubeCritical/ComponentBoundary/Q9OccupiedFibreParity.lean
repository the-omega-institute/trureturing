/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: An exact parity identity for occupied fibres of a Huang-balanced cubic cube support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedIncidence

/-! Count occupied fibres of a balanced cubic support after deleting one axis.
Transverse edges contribute equally to the two projected parity degree sums. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity

open scoped BigOperators
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEndpoints directionEdges direction_edge_count)
open BalancedCubeComponentBoundary (directions regular_directions)
open Q9FoldedIncidence (restrictCoordinates)

local notation "flip" => BalancedCriticalSpectrum.flip
local notation "dropCoordinate" => fun a : Fin 9 => restrictCoordinates (Fin.succAboveEmb a)
local notation "parity" => fun z : Q 8 => ∑ i, z i

attribute [local instance] Classical.propDecidable

private abbrev liftVertex (a : Fin 9) (t : Bool) (z : Q 8) : Q 9 :=
  Fin.insertNth (α := fun _ => Bool) a t z

private theorem drop_insert (a : Fin 9) (t : Bool) (z : Q 8) :
    dropCoordinate a (liftVertex a t z) = z :=
  Fin.removeNth_insertNth (α := fun _ => Bool) a t z

private theorem insert_drop (a : Fin 9) (x : Q 9) :
    liftVertex a (x a) (dropCoordinate a x) = x :=
  Fin.insertNth_self_removeNth (α := fun _ => Bool) a x

private theorem flip_insert (a : Fin 9) (t : Bool) (z : Q 8) :
    flip (liftVertex a t z) a = liftVertex a (!t) z := by
  simpa only [BalancedCriticalSpectrum.flip, Fin.insertNth_apply_same] using
    Fin.update_insertNth (α := fun _ => Bool) a t (!t) z

private theorem dropCoordinate_flip_drop (a : Fin 9) (x : Q 9) :
    dropCoordinate a (flip x a) = dropCoordinate a x :=
  Fin.removeNth_update (α := fun _ => Bool) a (!x a) x

private theorem dropCoordinate_flip_keep (a : Fin 9) (k : Fin 8) (x : Q 9) :
    dropCoordinate a (flip x (a.succAbove k)) = flip (dropCoordinate a x) k :=
  Fin.removeNth_update_succAbove (α := fun _ => Bool) a k (!x (a.succAbove k)) x

private theorem parity_flip (z : Q 8) (k : Fin 8) :
    parity (flip z k) = !parity z := by
  have hrest : (∑ i ∈ univ.erase k, flip z k i) = ∑ i ∈ univ.erase k, z i := by
    apply sum_congr rfl
    intro i hi
    simp [BalancedCriticalSpectrum.flip, (mem_erase.mp hi).1]
  change (∑ i, flip z k i) = !(∑ i, z i)
  rw [← sum_erase_add univ (flip z k) (mem_univ k), ← sum_erase_add univ z (mem_univ k),
    hrest, BalancedCriticalSpectrum.flip_apply_same]
  cases (∑ i ∈ univ.erase k, z i) <;> cases z k <;> decide

private def projectedVertices (S : Finset (Q 9)) (a : Fin 9) (b : Bool) : Finset (Q 9) :=
  S.filter (fun x => parity (dropCoordinate a x) = b)

/-- Projected fibres of parity `b` with at least one selected endpoint. -/
def occupiedFibres (S : Finset (Q 9)) (a : Fin 9) (b : Bool) : Finset (Q 8) :=
  (S.image (dropCoordinate a)).filter (fun z => parity z = b)

/-- Projected fibres of parity `b` with both endpoints selected. -/
def doubleFibres (S : Finset (Q 9)) (a : Fin 9) (b : Bool) : Finset (Q 8) :=
  (univ.filter fun z => liftVertex a false z ∈ S ∧ liftVertex a true z ∈ S).filter
    (fun z => parity z = b)

private theorem card_layer (S : Finset (Q 9)) (a : Fin 9) (t : Bool)
    (p : Q 8 → Prop) [DecidablePred p] :
    (univ.filter fun z => liftVertex a t z ∈ S ∧ p z).card =
      (S.filter fun x => x a = t ∧ p (dropCoordinate a x)).card := by
  apply card_bij (fun z _ => liftVertex a t z)
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    exact mem_filter.mpr
      ⟨hz.1, Fin.insertNth_apply_same (α := fun _ => Bool) a t z,
        by simpa only [drop_insert] using hz.2⟩
  · intro z _ w _ h
    simpa only [drop_insert] using congrArg (dropCoordinate a) h
  · intro x hx
    obtain ⟨hx, ht, hp⟩ := mem_filter.mp hx
    have he : liftVertex a t (dropCoordinate a x) = x := by simpa only [ht] using insert_drop a x
    exact ⟨dropCoordinate a x, by simp [he, hx, hp], he⟩

private theorem card_projectedVertices (S : Finset (Q 9)) (a : Fin 9) (b : Bool) :
    (projectedVertices S a b).card =
      (occupiedFibres S a b).card + (doubleFibres S a b).card := by
  let layer (t : Bool) := univ.filter
    (fun z => liftVertex a t z ∈ S ∧ parity z = b)
  have hu : layer false ∪ layer true = occupiedFibres S a b := by
    ext z
    simp only [layer, occupiedFibres, mem_union, mem_filter, mem_univ,
      true_and, mem_image]
    constructor
    · rintro (⟨h, hp⟩ | ⟨h, hp⟩)
      · exact ⟨⟨_, h, drop_insert a false z⟩, hp⟩
      · exact ⟨⟨_, h, drop_insert a true z⟩, hp⟩
    · rintro ⟨⟨x, hx, rfl⟩, hp⟩
      have he := insert_drop a x
      cases ht : x a
      · exact Or.inl ⟨by rw [ht] at he; exact he.symm ▸ hx, hp⟩
      · exact Or.inr ⟨by rw [ht] at he; exact he.symm ▸ hx, hp⟩
  have hi : layer false ∩ layer true = doubleFibres S a b := by
    ext z
    simp only [layer, doubleFibres, mem_inter, mem_filter, mem_univ, true_and]
    tauto
  have hc (t : Bool) : (layer t).card =
      ((projectedVertices S a b).filter fun x => x a = t).card := by
    dsimp only [layer]
    rw [card_layer S a t (fun z => parity z = b)]
    congr 1
    ext x
    simp only [projectedVertices, mem_filter]
    tauto
  have hnot : ((projectedVertices S a b).filter fun x => ¬ x a = false) =
      (projectedVertices S a b).filter (fun x => x a = true) := by
    ext x
    cases h : x a <;> simp [h]
  rw [← hu, ← hi, card_union_add_card_inter, hc, hc, ← hnot]
  exact (card_filter_add_card_filter_not _).symm

private theorem card_both_layers (S : Finset (Q 9)) (a : Fin 9) :
    (univ.filter fun z => liftVertex a false z ∈ S ∧ liftVertex a true z ∈ S).card =
      directionEdges S a := by
  rw [card_layer S a false (fun z => liftVertex a true z ∈ S)]
  unfold directionEdges
  congr 1
  ext x
  simp only [mem_filter]
  have he := flip_insert a (x a) (dropCoordinate a x)
  rw [insert_drop] at he
  by_cases ht : x a = false
  · simp [ht, show flip x a = liftVertex a true (dropCoordinate a x) by simpa [ht] using he]
  · simp [ht]

private theorem card_doubleFibres (S : Finset (Q 9)) (a : Fin 9) (b : Bool) :
    (doubleFibres S a b).card = directionEdges (projectedVertices S a b) a := by
  let V := projectedVertices S a b
  have hl : doubleFibres S a b = univ.filter
      (fun z => liftVertex a false z ∈ V ∧ liftVertex a true z ∈ V) := by
    ext z
    simp only [doubleFibres, V, projectedVertices, mem_filter, mem_univ,
      true_and, drop_insert]
    tauto
  rw [hl, card_both_layers]

private theorem card_parity_partition {n : ℕ} (A : Finset (Q n)) (p : Q n → Bool) (b : Bool) :
    (A.filter fun x => p x = b).card + (A.filter fun x => p x = !b).card = A.card := by
  have h : (A.filter fun x => p x = !b) = A.filter (fun x => ¬ p x = b) := by
    ext x
    cases b <;> cases hpx : p x <;> simp [hpx]
  rw [h, card_filter_add_card_filter_not]

private theorem doubleFibres_partition (S : Finset (Q 9)) (a : Fin 9) (b : Bool) :
    (doubleFibres S a b).card + (doubleFibres S a (!b)).card = directionEdges S a := by
  unfold doubleFibres
  rw [card_parity_partition, card_both_layers]

private theorem direction_degree_sum {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (V : Finset (Q 9)) (hV : V ⊆ S) :
    (∑ i : Fin 9, (V.filter fun x => flip x i ∈ S).card) = 3 * V.card := by
  calc
    _ = ∑ i : Fin 9, ∑ x ∈ V, if flip x i ∈ S then 1 else 0 := by
      simp
    _ = ∑ x ∈ V, (directions S x).card := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      simp [directions]
    _ = 3 * V.card := by
      rw [sum_congr rfl (fun x hx => regular_directions S hr (hV hx))]
      simp [Nat.mul_comm]

private theorem transverse_count (S : Finset (Q 9)) (a : Fin 9) (b : Bool)
    (j : Fin 9) (hj : j ≠ a) :
    ((projectedVertices S a b).filter fun x => flip x j ∈ S).card =
      ((projectedVertices S a (!b)).filter fun x => flip x j ∈ S).card := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
  let f := fun x : Q 9 => flip x (a.succAbove k)
  have hp (x : Q 9) : parity (dropCoordinate a (f x)) = !parity (dropCoordinate a x) := by
    simp only [f, dropCoordinate_flip_keep, parity_flip]
  have hf (x : Q 9) : f (f x) = x := BalancedCriticalSpectrum.flip_flip _ _
  apply card_bij' (fun x _ => f x) (fun x _ => f x)
  · intro x hx
    simp only [projectedVertices, mem_filter] at hx ⊢
    exact ⟨⟨hx.2, (hp x).trans (congrArg Bool.not hx.1.2)⟩,
      by simpa only [f, BalancedCriticalSpectrum.flip_flip] using hx.1.1⟩
  · intro x hx
    simp only [projectedVertices, mem_filter] at hx ⊢
    exact ⟨⟨hx.2, (hp x).trans (by
      simpa only [Bool.not_not] using congrArg Bool.not hx.1.2)⟩,
      by simpa only [f, BalancedCriticalSpectrum.flip_flip] using hx.1.1⟩
  · intro x _
    exact hf x
  · intro x _
    exact hf x

private theorem endpoint_card_twice {n : ℕ} (S : Finset (Q n)) (a : Fin n) :
    (directionEndpoints S a).card = 2 * directionEdges S a := by
  let E := directionEndpoints S a
  have hpart := card_parity_partition E (fun x => x a) false
  have hflip : (E.filter fun x => x a = true).card =
      (E.filter fun x => x a = false).card := by
    apply card_bij' (fun x _ => flip x a) (fun x _ => flip x a)
    · intro x hx
      simp only [E, directionEndpoints, mem_filter] at hx ⊢
      simp [hx.1.1, hx.1.2, hx.2]
    · intro x hx
      simp only [E, directionEndpoints, mem_filter] at hx ⊢
      simp [hx.1.1, hx.1.2, hx.2]
    · intro x _
      exact BalancedCriticalSpectrum.flip_flip x a
    · intro x _
      exact BalancedCriticalSpectrum.flip_flip x a
  have hfalse : (E.filter fun x => x a = false).card = directionEdges S a := by
    unfold directionEdges
    congr 1
    ext x
    simp only [E, directionEndpoints, mem_filter]
    tauto
  change (E.filter fun x => x a = false).card + (E.filter fun x => x a = true).card =
    (directionEndpoints S a).card at hpart
  rw [hflip, hfalse] at hpart
  exact hpart.symm.trans (two_mul _).symm

private theorem axial_count (S : Finset (Q 9)) (a : Fin 9) (b : Bool) :
    ((projectedVertices S a b).filter fun x => flip x a ∈ S).card =
      2 * (doubleFibres S a b).card := by
  rw [card_doubleFibres, ← endpoint_card_twice]
  congr 1
  ext x
  simp only [directionEndpoints, projectedVertices, mem_filter, dropCoordinate_flip_drop]
  tauto

/-- In a balanced induced cubic support, the occupied count of projected
parity `b` is determined by the total axial edge count and the number of
double fibres of the opposite parity. -/
theorem occupied_fibre_identity {S : Finset (Q 9)}
    (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (a : Fin 9) (b : Bool) :
    3 * (occupiedFibres S a b).card =
      7 * directionEdges S a + (doubleFibres S a (!b)).card := by
  have hdeg (p : Bool) :=
    direction_degree_sum hr (projectedVertices S a p) (filter_subset _ _)
  have hsplit (p : Bool) :=
    sum_erase_add (univ : Finset (Fin 9))
      (fun i => ((projectedVertices S a p).filter fun x => flip x i ∈ S).card)
      (mem_univ a)
  have htrans :
      (∑ i ∈ univ.erase a, ((projectedVertices S a b).filter fun x => flip x i ∈ S).card) =
      (∑ i ∈ univ.erase a, ((projectedVertices S a (!b)).filter fun x => flip x i ∈ S).card) :=
    sum_congr rfl fun i hi => transverse_count S a b i (mem_erase.mp hi).1
  have hax (p : Bool) := axial_count S a p
  have hv (p : Bool) := card_projectedVertices S a p
  have hpart := card_parity_partition S (fun x => parity (dropCoordinate a x)) b
  change (projectedVertices S a b).card + (projectedVertices S a (!b)).card =
    S.card at hpart
  have hm := doubleFibres_partition S a b
  have hsize : 6 * directionEdges S a = S.card := direction_edge_count (d := 3) S hr hb a
  have h₀ := hsplit b
  have h₁ := hsplit (!b)
  rw [hdeg b, hax b, htrans] at h₀
  rw [hdeg (!b), hax (!b)] at h₁
  have hv₀ := hv b
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity
