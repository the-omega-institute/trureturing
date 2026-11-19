import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayRelativeCenters
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayCrossedPlacement

/-! For eighteen Gray pairs, the exterior boundary and at most three
disjoint four-leaf stars suffice to rule out 258 vertices. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayEasyPlacements

open Finset
open Q9GrayRelativeCenters (representativeCenters)
open Q9GrayCrossedPlacement (cube)
open D5.S3.Combinatorics.Graph.Hypercube

private instance : Fintype (BitVec 9) :=
  Fintype.ofEquiv (Fin (2 ^ 9)) (BitVec.equivFin (m := 9)).toEquiv.symm

private def InSupports (k : Fin 5) (t x : BitVec 9) : Prop :=
  Q9GrayPlacementNormalForm.Fits Q9TriplePartitionOrbits.standardLabels
    Q9GrayPlacementNormalForm.origin (cubeBitVec 9 x) ∨
  Q9GrayPlacementNormalForm.Fits (Q9TriplePartitionOrbits.secondLabels k)
    Q9GrayPlacementNormalForm.origin (cubeBitVec 9 (x ^^^ t))

private instance (k : Fin 5) (t x : BitVec 9) : Decidable (InSupports k t x) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The two normalized supports in the bit encoding. -/
def supports (k : Fin 5) (t : BitVec 9) : Finset (BitVec 9) :=
  univ.filter (InSupports k t)

/-- Coordinates outside the closed neighborhoods of both supports. -/
def residual (k : Fin 5) (t : BitVec 9) : Finset (BitVec 9) :=
  univ.filter fun x => ¬ InSupports k t x ∧
    ∀ i : Fin 9, ¬ InSupports k t (x ^^^ BitVec.ofNat 9 (2 ^ i.val))

private abbrev Star := BitVec 9 × List (BitVec 9)

private def stars (k : Fin 5) (t : BitVec 9) : List Star :=
  if k = 0 ∧ t = 127 then
    [(7, [3, 5, 6, 71]), (56, [24, 40, 48, 120]), (135, [143, 151, 167, 199])]
  else if k = 0 ∧ t = 255 then
    [(7, [3, 5, 6, 15]), (56, [24, 40, 48, 57]), (199, [71, 135, 195, 197])]
  else if k = 1 ∧ t = 255 then
    [(7, [3, 5, 6, 15]), (55, [23, 39, 51, 53]), (56, [24, 40, 48, 57])]
  else if k = 3 ∧ t = 255 then [(7, [3, 5, 6, 15])]
  else []

private def points (star : Star) : Finset (BitVec 9) :=
  insert star.1 star.2.toFinset

private def Valid (k : Fin 5) (t : BitVec 9) : Prop :=
  let rows := stars k t
  (residual k t).card ≤ 149 + rows.length ∧
    (∀ i : Fin rows.length, let s := rows.get i
      s.2.toFinset.card = 4 ∧
      (∀ x ∈ s.2.toFinset, cube.Adj s.1 x) ∧ points s ⊆ residual k t) ∧
    ∀ i j : Fin rows.length, i ≠ j → Disjoint (points (rows.get i)) (points (rows.get j))

private instance (k : Fin 5) (t : BitVec 9) : Decidable (Valid k t) := by
  unfold Valid
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 16000000 in
-- The certificate checks the residual size and every star in each of the
-- eighteen placements. The other two placements use separate bounds.
private theorem easy_certificates : ∀ (k : Fin 5) (t : BitVec 9),
    t ∈ representativeCenters k →
    ¬ (k = 0 ∧ t = 63) → ¬ (k = 1 ∧ t = 504) → Valid k t := by
  decide +kernel

/-- At the eighteen listed placements, at most 149 vertices outside the
closed neighborhoods can be selected with induced maximum degree three. -/
theorem residual_card_le (k : Fin 5) (t : BitVec 9)
    (ht : t ∈ representativeCenters k)
    (h0 : ¬ (k = 0 ∧ t = 63)) (h1 : ¬ (k = 1 ∧ t = 504))
    (S : Finset (BitVec 9)) (hS : S ⊆ residual k t)
    (hdeg : ∀ v ∈ S, (S.filter (cube.Adj v)).card ≤ 3) : S.card ≤ 149 := by
  classical
  obtain ⟨hcard, hstars, hdis⟩ := easy_certificates k t ht h0 h1
  let rows := stars k t
  have omitted (i : Fin rows.length) : (points (rows.get i) \ S).Nonempty := by
    obtain ⟨hfour, hadj, _⟩ := hstars i
    exact GrayPairCutCounting.star_has_omission cube S _ _ hfour hadj hdeg
  let chooseOmission (i : Fin rows.length) : (residual k t \ S : Finset (BitVec 9)) :=
    ⟨(omitted i).choose, by
      have hm := mem_sdiff.mp (omitted i).choose_spec
      exact mem_sdiff.mpr ⟨(hstars i).2.2 hm.1, hm.2⟩⟩
  have hinj : Function.Injective chooseOmission := by
    intro i j h
    by_contra hij
    have he := congrArg Subtype.val h
    change (omitted i).choose = (omitted j).choose at he
    exact disjoint_left.mp (hdis i j hij) (mem_sdiff.mp (omitted i).choose_spec).1
      (he.symm ▸ (mem_sdiff.mp (omitted j).choose_spec).1)
  have ho := Fintype.card_le_of_injective chooseOmission hinj
  rw [Fintype.card_fin, Fintype.card_coe, card_sdiff_of_subset hS] at ho
  have hc := card_le_card hS
  change (residual k t).card ≤ 149 + rows.length at hcard
  omega

#print axioms residual_card_le

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Count both supports after taking their literal union at each representative.
private theorem supports_card : ∀ (k : Fin 5) (t : BitVec 9),
    t ∈ representativeCenters k → (supports k t).card = 108 := by
  decide +kernel

/-- A candidate containing both supports as a union of components has size at
most 257 in each of the eighteen boundary-and-stars cases. -/
theorem candidate_card_le (k : Fin 5) (t : BitVec 9)
    (ht : t ∈ representativeCenters k)
    (h0 : ¬ (k = 0 ∧ t = 63)) (h1 : ¬ (k = 1 ∧ t = 504))
    (U : Finset (BitVec 9)) (hU : supports k t ⊆ U)
    (hclosed : ∀ x ∈ supports k t, ∀ y ∈ U, cube.Adj x y → y ∈ supports k t)
    (hdeg : ∀ v ∈ U, (U.filter (cube.Adj v)).card ≤ 3) : U.card ≤ 257 := by
  have hsub : U \ supports k t ⊆ residual k t := by
    intro v hv
    obtain ⟨hvU, hvS⟩ := mem_sdiff.mp hv
    refine mem_filter.mpr ⟨mem_univ _, fun h => hvS (mem_filter.mpr ⟨mem_univ _, h⟩), ?_⟩
    intro i hi
    have hadj : cube.Adj v (v ^^^ BitVec.ofNat 9 (2 ^ i.val)) := by
      change (hypercube 9).Adj (cubeBitVec 9 v) (cubeBitVec 9 (v ^^^ BitVec.ofNat 9 (2 ^ i.val)))
      rw [cubeBitVec_xor_single]
      exact BalancedCriticalSpectrum.flip_adj _ _
    exact hvS (hclosed _ (mem_filter.mpr ⟨mem_univ _, hi⟩) v hvU hadj.symm)
  have h := residual_card_le k t ht h0 h1 (U \ supports k t) hsub (fun v hv =>
    (card_le_card (filter_subset_filter _ sdiff_subset)).trans (hdeg v (mem_sdiff.mp hv).1))
  rw [card_sdiff_of_subset hU, supports_card k t ht] at h
  omega

#print axioms candidate_card_le

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayEasyPlacements
