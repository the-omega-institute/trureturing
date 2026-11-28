import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesReplay
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskRootNormalization

/-! Transport a saturated component pair to its least root-neighborhood representative. -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 50000

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesActual

open Finset
open BalancedCriticalSpectrum (Q IsBalanced)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization (normalize)
open Q9SharedContactCNF (Axis)
open Q9FiveAxisMissingContact (Geometry)
open Q9RootStabilizer (normalize_comp)
open Q9TenMaskSixAxisReplay (Recipe)
open Q9FifteenMaskLargeAxesReplay (Inputs)
open Q9GenericRootAction (Canonical normalize_root_neighborhoods_generic translation)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9TightDistanceTwoCNF (support)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9NormalizedContactTranslations (normalized_contact_translation)
open Q9ExteriorTransport (gain_eq_of_endpoints normalize_gain_consistent)

open Classical in
/-- All actual component pairs can be reframed to a canonical root pair, giving
all the typed hypotheses of their retained six-axis refutation. -/
theorem exists_rooted_inputs (r : Recipe) (hrequired : r.required ⊆ r.family) {C D : Finset (Q 9)}
    (σ : Equiv.Perm Axis) (o : Q 9)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hsC : 60 ≤ C.card) (hsD : 60 ≤ D.card) :
    let e := normalize σ o
    let U := C.map e.toEmbedding
    let V := D.map e.toEmbedding
    Geometry U V → minimumDisplacements U V false 2 = r.family →
      ∃ X Y, Inputs r X Y := by
  let e := normalize σ o
  let U := C.map e.toEmbedding
  let V := D.map e.toEmbedding
  change Geometry U V → minimumDisplacements U V false 2 = r.family →
    ∃ X Y, Inputs r X Y
  intro hgeom hM
  obtain ⟨p, t, _, _, hgeom', hM', hcanon⟩ := normalize_root_neighborhoods_generic hgeom hM
  let τ := p.symm
  let z := translation t
  let ρ := τ.trans σ
  let u := e.symm z
  let K := support C D t
  let L := support C D (!t)
  let X := K.map (normalize ρ u).toEmbedding
  let Y := L.map (normalize ρ u).toEmbedding
  have hcomp : e.trans (normalize τ z) = normalize ρ u := normalize_comp σ τ o z
  have hleft : support U V t = K.map e.toEmbedding := by cases t <;> rfl
  have hright : support U V (!t) = L.map e.toEmbedding := by cases t <;> rfl
  have hX : (support U V t).map (normalize τ z).toEmbedding = X := by
    rw [hleft, Finset.map_map, ← Equiv.trans_toEmbedding, hcomp]
  have hY : (support U V (!t)).map (normalize τ z).toEmbedding = Y := by
    rw [hright, Finset.map_map, ← Equiv.trans_toEmbedding, hcomp]
  change Geometry ((support U V t).map (normalize τ z).toEmbedding)
    ((support U V (!t)).map (normalize τ z).toEmbedding) at hgeom'
  change minimumDisplacements ((support U V t).map (normalize τ z).toEmbedding)
    ((support U V (!t)).map (normalize τ z).toEmbedding) false 2 = r.family at hM'
  change Canonical r.family ((support U V t).map (normalize τ z).toEmbedding)
    ((support U V (!t)).map (normalize τ z).toEmbedding) at hcanon
  rw [hX, hY] at hgeom' hM' hcanon
  have hsepKL : ∀ x ∈ K, ∀ y ∈ L, 2 ≤ hammingDist x y := by
    cases t
    · exact hsep
    · intro x hx y hy
      rw [hammingDist_comm]
      exact hsep y hy x hx
  have hrK : ((hypercube 9).induce (K : Set (Q 9))).IsRegularOfDegree 3 := by
    cases t <;> assumption
  have hrL : ((hypercube 9).induce (L : Set (Q 9))).IsRegularOfDegree 3 := by
    cases t <;> assumption
  have hcK : ((hypercube 9).induce (K : Set (Q 9))).Connected := by cases t <;> assumption
  have hcL : ((hypercube 9).induce (L : Set (Q 9))).Connected := by cases t <;> assumption
  have hbK : IsBalanced K := by cases t <;> assumption
  have hbL : IsBalanced L := by cases t <;> assumption
  have hdetK : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w K false)).det = 0 := by
    cases t <;> assumption
  have hdetL : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w L false)).det = 0 := by
    cases t <;> assumption
  have hsK : 60 ≤ K.card := by cases t <;> assumption
  have hsL : 60 ≤ L.card := by cases t <;> assumption
  refine ⟨X, Y, ⟨⟨hgeom', hM' ▸ Subset.rfl, hM'.symm ▸ hrequired⟩,
    ⟨hgeom', hM' ▸ Subset.rfl,
      normalized_contact_translation ρ u hsepKL hrK hrL hcK hcL hbK hbL hdetK hdetL⟩, hcanon, ?_, ?_⟩⟩
  · intro s
    cases s
    · exact normalize_gain_consistent (C := K) (by
        intro x y g h hx p q
        exact gain_eq_of_endpoints hrK hcK hbK hdetK hx p q) ρ u
    · exact normalize_gain_consistent (C := L) (by
        intro x y g h hx p q
        exact gain_eq_of_endpoints hrL hcL hbL hdetL hx p q) ρ u
  · intro s
    cases s
    · simpa only [X, support, Bool.false_eq_true, ite_false, card_map] using hsK
    · simpa only [Y, support, ite_true, card_map] using hsL

open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

open Classical in
/-- A coordinate labeling of the whole contact family transports the actual
components to the canonical neighborhood orbit used by a recipe. -/
theorem exists_rooted_inputs_of_labeling (r : Recipe) (hrequired : r.required ⊆ r.family)
    {C D : Finset (Q 9)} {b : Bool} (σ : Equiv.Perm Axis)
    (hroot : ({σ 0, σ 1} : Finset Axis) ∈ minimumDisplacements C D b 2)
    (hM : ∀ t ∈ r.family, t.map σ.toEmbedding ∈ minimumDisplacements C D b 2)
    (hcard : r.family.card = (minimumDisplacements C D b 2).card)
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hsC : 60 ≤ C.card) (hsD : 60 ≤ D.card) : ∃ X Y, Inputs r X Y := by
  obtain ⟨o, ho, y, hy, hp, _, hxy⟩ := mem_minimumDisplacements.mp hroot
  obtain ⟨hgeom, hmap⟩ := Q9TenMaskRootNormalization.normalize_root_mapped σ
    ho hy hp hxy hsep hrC hrD hbC hbD
  have hfamily : minimumDisplacements (C.map (normalize σ o).toEmbedding)
      (D.map (normalize σ o).toEmbedding) false 2 = r.family := by
    rw [hmap]
    symm
    apply eq_of_subset_of_card_le
    · intro t ht
      refine mem_map.mpr ⟨t.map σ.toEmbedding, hM t ht, ?_⟩
      ext i
      simp [Finset.mapEmbedding_apply]
    · rw [card_map, hcard]
  exact exists_rooted_inputs r hrequired σ o hsep hrC hrD hcC hcD hbC hbD
    hdetC hdetD hsC hsD hgeom hfamily

#print axioms exists_rooted_inputs
#print axioms exists_rooted_inputs_of_labeling

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesActual
