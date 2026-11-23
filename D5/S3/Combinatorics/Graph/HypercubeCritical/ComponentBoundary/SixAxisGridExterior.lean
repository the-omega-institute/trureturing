/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridExterior
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SixAxisGridExterior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Exterior lifts of a subdivided cubical grid jointly exclude internal directions. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubicalSubdivisionRigidity

/-! Joint direction exclusions for exterior lifts of the six-axis K₃,₃ grid. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior

open BalancedCriticalSpectrum (Q IsBalanced)

local notation "cubeFlip" =>
  _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum.flip
local notation "cubeFlipFlip" =>
  _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum.flip_flip
open BalancedCubeComponentBoundary (directions mem_directions)
open BalancedCubeGirth (flip_comm three_step_first_direction_eq)
open CubicalSubdivisionRigidity (gridHigh gridMiddle gridSupport)

/-- The labels of the selected lifts in the column of `(i,j)` (false labels) and in
its row (true labels), all taken along the same direction `e`. -/
def selectedLiftLabels {n : Nat} (D : Finset (Q n)) (X : Q n)
    (d : Bool × Fin 3 → Fin n) (e : Fin n) (i j : Fin 3) : Finset (Bool × Fin 3) :=
  Finset.univ.filter fun h =>
    cubeFlip (gridMiddle X d (if h.1 then (i, h.2) else (h.2, j))) e ∈ D

private theorem incident_middle {n : Nat} (X : Q n) (d : Bool × Fin 3 → Fin n)
    (s : Bool) (fixed varying : Fin 3) :
    cubeFlip (gridHigh X d (!s, fixed)) (d (s, varying)) =
      gridMiddle X d (if s then (fixed, varying) else (varying, fixed)) := by
  cases s
  · exact flip_comm _ _ _
  · rfl

private theorem saturated_branch {n : Nat} {D : Finset (Q n)} {p : Q n}
    (axes : Fin 3 → Fin n) (hinj : Function.Injective axes)
    (hall : ∀ k, cubeFlip p (axes k) ∈ D) (hdegree : (directions D p).card ≤ 3)
    {e : Fin n} (he : ∀ k, e ≠ axes k) : cubeFlip p e ∉ D := by
  let internal := Finset.univ.image axes
  have hsub : internal ⊆ directions D p := by
    intro a ha
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
    exact (mem_directions _ _ _).mpr (hall k)
  have hcard : internal.card = 3 := by
    rw [Finset.card_image_of_injective _ hinj]
    decide
  have heq : internal = directions D p :=
    Finset.eq_of_subset_of_card_le hsub (by simpa only [hcard] using hdegree)
  intro hlift
  have hemem : e ∈ internal := heq.symm ▸ (mem_directions _ _ _).mpr hlift
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hemem
  exact he k hk.symm

private theorem no_partner_continuation {n : Nat} {D : Finset (Q n)}
    (hb : IsBalanced D) {p : Q n} {a b e : Fin n}
    (hae : a ≠ e) (hbe : b ≠ e) (hab : a ≠ b) (hp : p ∈ D)
    (ha : cubeFlip p a ∈ D) (hb' : cubeFlip p b ∈ D)
    (haeD : cubeFlip (cubeFlip p a) e ∈ D) (hbeD : cubeFlip (cubeFlip p b) e ∈ D) :
    cubeFlip (cubeFlip (cubeFlip p a) e) b ∉ D := by
  intro hz
  have heq : cubeFlip (cubeFlip (cubeFlip p a) e) b = cubeFlip (cubeFlip (cubeFlip p b) e) a := by
    calc
      _ = cubeFlip (cubeFlip (cubeFlip p a) b) e := by rw [flip_comm (cubeFlip p a) e b]
      _ = cubeFlip (cubeFlip (cubeFlip p b) a) e := by rw [flip_comm p a b]
      _ = _ := flip_comm (cubeFlip p b) a e
  exact hab (three_step_first_direction_eq hb hae hbe.symm hbe hae.symm
    hp ha haeD hz hb' hbeD (heq ▸ hz) heq)

/-- At any selected exterior lift, exclude both incident axes and the varying
axis of every other selected lift in the same row or column along that exterior
direction. The count is four minus the number of those other lifts. -/
theorem exterior_lift_direction_exclusion {n : Nat} (D : Finset (Q n)) (X : Q n)
    (d : Bool × Fin 3 → Fin n) (hd : Function.Injective d) (hb : IsBalanced D)
    (hgrid : gridSupport X d ⊆ D)
    (hdegree : ∀ s k, (directions D (gridHigh X d (s, k))).card ≤ 3)
    (e : Fin n) (he : e ∉ Set.range d) (i j : Fin 3)
    (hy : cubeFlip (gridMiddle X d (i, j)) e ∈ D) :
    let labels := selectedLiftLabels D X d e i j
    let next := directions D (cubeFlip (gridMiddle X d (i, j)) e)
    Disjoint (labels.image d) next ∧
      (next ∩ Finset.univ.image d).card ≤ 6 - labels.card := by
  dsimp only
  let labels := selectedLiftLabels D X d e i j
  let next := directions D (cubeFlip (gridMiddle X d (i, j)) e)
  have hdis : Disjoint (labels.image d) next := by
    apply Finset.disjoint_left.mpr
    intro axis haxis
    obtain ⟨⟨s, k⟩, hlabel, rfl⟩ := Finset.mem_image.mp haxis
    let fixed := if s then i else j
    let base := if s then j else i
    let p := gridHigh X d (!s, fixed)
    let axes := fun l : Fin 3 => d (s, l)
    have hmiddle (l : Fin 3) : cubeFlip p (axes l) =
        gridMiddle X d (if s then (i, l) else (l, j)) := by
      cases s <;> exact incident_middle X d _ _ _
    have hbase : cubeFlip p (axes base) = gridMiddle X d (i, j) := by
      cases s <;> exact incident_middle X d _ _ _
    have hp : p ∈ D :=
      hgrid (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩))
    have hm (l : Fin 3) : cubeFlip p (axes l) ∈ D := by
      rw [hmiddle]
      exact hgrid (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩))
    have hne (l : Fin 3) : e ≠ axes l := fun h => he ⟨(s, l), h.symm⟩
    intro hnext
    have hz := (mem_directions _ _ _).mp hnext
    change cubeFlip (cubeFlip (gridMiddle X d (i, j)) e) (axes k) ∈ D at hz
    rw [← hbase] at hy hz
    by_cases hk : k = base
    · subst k
      rw [flip_comm (cubeFlip p (axes base)) e (axes base), cubeFlipFlip] at hz
      exact saturated_branch axes (fun _ _ h => congrArg Prod.snd (hd h)) hm
        (hdegree (!s) fixed) hne hz
    · have hneq : axes base ≠ axes k := fun h => hk (congrArg Prod.snd (hd h)).symm
      have hpartner : cubeFlip (cubeFlip p (axes k)) e ∈ D := by
        rw [hmiddle]
        simpa only [labels, selectedLiftLabels, Finset.mem_filter, Finset.mem_univ, true_and]
          using hlabel
      exact no_partner_continuation hb (hne base).symm (hne k).symm hneq hp
        (hm base) (hm k) hy hpartner hz
  refine ⟨hdis, ?_⟩
  let internal := Finset.univ.image d
  have hsub : labels.image d ⊆ internal := Finset.image_mono d (Finset.subset_univ _)
  have hremain : next ∩ internal ⊆ internal \ labels.image d := by
    intro k hk
    obtain ⟨hnext, hint⟩ := Finset.mem_inter.mp hk
    exact Finset.mem_sdiff.mpr ⟨hint, fun hlabel => Finset.disjoint_left.mp hdis hlabel hnext⟩
  calc
    _ ≤ (internal \ labels.image d).card := Finset.card_le_card hremain
    _ = 6 - labels.card := by
      have hlabels : (Finset.univ : Finset (Bool × Fin 3)).card = 6 := by decide
      simp only [Finset.card_sdiff_of_subset hsub, internal, Finset.card_image_of_injective _ hd,
        hlabels]

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior.exterior_lift_direction_exclusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms exterior_lift_direction_exclusion

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.SixAxisGridExterior
