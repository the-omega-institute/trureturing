/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodCertificates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/StarForming/DissociationCover]
   utility: kind=certified-instance; basis=consumer=D5/S3/Combinatorics/Graph/StarForming/CoverDensity.scalar_cover_bound; instance=D5/S3/Combinatorics/Graph/StarForming/HeawoodCertificates.scalar_parameters
   digest: Original S and J two-lift certificates attain exact canonical maxima. -/

import D5.S3.Combinatorics.Graph.StarForming.FiniteMasks
import D5.S3.Combinatorics.Graph.StarForming.RegularCompensation

/-! Original two-sheet Heawood certificates, unchanged label/sheet/twist and
selection data, from subquorum-colorings revision
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
Only S and J receive finite certificate conclusions here. This module does not
assert switching classification or the all-six-type connected-cover theorem. -/

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodCertificates
open StarFormingDissociationRefutation


open DissociationCover

def label (vertex : Fin 28) : Nat := vertex.val % 14 / 2 + 1

def sheet (vertex : Fin 28) : Nat := vertex.val % 2

def dot (first second : Nat) : Nat :=
  ((first % 2) * (second % 2) + (first / 2 % 2) * (second / 2 % 2) +
    (first / 4) * (second / 4)) % 2

def adjacency (twists : List (Nat × Nat)) (first second : Fin 28) : Prop :=
  (first.val < 14) ≠ (second.val < 14) ∧ dot (label first) (label second) = 0 ∧
    (sheet first + sheet second) % 2 =
      if twists.contains (if first.val < 14 then (label first, label second)
        else (label second, label first)) then 1 else 0

instance (twists : List (Nat × Nat)) : DecidableRel (adjacency twists) :=
  fun first second => inferInstanceAs (Decidable
    ((first.val < 14) ≠ (second.val < 14) ∧ dot (label first) (label second) = 0 ∧
      (sheet first + sheet second) % 2 =
        if twists.contains (if first.val < 14 then (label first, label second)
          else (label second, label first)) then 1 else 0))

def selected (points lines : List Nat) (vertex : Fin 28) : Prop :=
  (if vertex.val < 14 then points else lines).contains
    (10 * label vertex + sheet vertex) = true

instance (points lines : List Nat) : DecidablePred (selected points lines) :=
  fun vertex => inferInstanceAs (Decidable
    ((if vertex.val < 14 then points else lines).contains
      (10 * label vertex + sheet vertex) = true))

def scalarTwists : List (Nat × Nat) := [(3, 3), (1, 2), (2, 1)]

def jordanTwists : List (Nat × Nat) := [(3, 3), (2, 1)]

def scalarPoints : List Nat := [10, 20, 30, 50, 60, 70]

def scalarLines : List Nat := [10, 11, 20, 21, 30, 31, 41, 51, 61, 71]

def jordanPoints : List Nat := [20, 31, 40, 41, 50, 51, 61, 70]

def jordanLines : List Nat := [10, 31, 40, 41, 51, 60, 61, 70]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem scalar_dissociates :
    Dissociates (adjacency scalarTwists) (selected scalarPoints scalarLines) := by
  unfold Dissociates
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
theorem jordan_dissociates :
    Dissociates (adjacency jordanTwists) (selected jordanPoints jordanLines) := by
  unfold Dissociates
  decide

theorem scalar_card :
    ((List.finRange 28).filter (fun vertex =>
      decide (selected scalarPoints scalarLines vertex))).length = 16 := by
  decide

theorem jordan_card :
    ((List.finRange 28).filter (fun vertex =>
      decide (selected jordanPoints jordanLines vertex))).length = 16 := by
  decide


def scalarGraph : SimpleGraph (Fin 28) where
  Adj := adjacency scalarTwists
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

def jordanGraph : SimpleGraph (Fin 28) where
  Adj := adjacency jordanTwists
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel scalarGraph.Adj := inferInstanceAs (DecidableRel (adjacency scalarTwists))
instance : DecidableRel jordanGraph.Adj := inferInstanceAs (DecidableRel (adjacency jordanTwists))

def scalarSet : Finset (Fin 28) := Finset.univ.filter (selected scalarPoints scalarLines)
def jordanSet : Finset (Fin 28) := Finset.univ.filter (selected jordanPoints jordanLines)

/-- The two original lists give actual canonical dissociation sets of size16. -/
theorem scalar_selection : IsKIndependent scalarGraph 2 scalarSet ∧ scalarSet.card = 16 := by
  constructor
  · apply (SubQuorum.DoubleStarGrafting.independent_iff scalarGraph scalarSet).mpr
    intro c hc a ha b hb hca hcb
    exact scalar_dissociates c a b (Finset.mem_filter.mp hc).2
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hca hcb
  · have h := scalar_card
    rw [FiniteMasks.list_count] at h
    exact h

theorem jordan_selection : IsKIndependent jordanGraph 2 jordanSet ∧ jordanSet.card = 16 := by
  constructor
  · apply (SubQuorum.DoubleStarGrafting.independent_iff jordanGraph jordanSet).mpr
    intro c hc a ha b hb hca hcb
    exact jordan_dissociates c a b (Finset.mem_filter.mp hc).2
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hca hcb
  · have h := jordan_card
    rw [FiniteMasks.list_count] at h
    exact h

/-- The original binary two-lifts are cubic and bipartite. -/
theorem scalar_class : scalarGraph.Colorable 2 ∧
    ∀ v, DegreeCapacity.degree scalarGraph v = 3 := by
  constructor
  · refine ⟨SimpleGraph.Coloring.mk (fun v => if v.val < 14 then (0 : Fin 2) else 1) ?_⟩
    change ∀ a b : Fin 28, adjacency scalarTwists a b →
      (if a.val < 14 then (0 : Fin 2) else 1) ≠ (if b.val < 14 then 0 else 1)
    decide +kernel
  · decide +kernel

theorem jordan_class : jordanGraph.Colorable 2 ∧
    ∀ v, DegreeCapacity.degree jordanGraph v = 3 := by
  constructor
  · refine ⟨SimpleGraph.Coloring.mk (fun v => if v.val < 14 then (0 : Fin 2) else 1) ?_⟩
    change ∀ a b : Fin 28, adjacency jordanTwists a b →
      (if a.val < 14 then (0 : Fin 2) else 1) ≠ (if b.val < 14 then 0 else 1)
    decide +kernel
  · decide +kernel

private theorem parameters_of_certificate (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (hr : ∀ v, DegreeCapacity.degree G v = 3) (S : Finset (Fin 28))
    (hS : IsKIndependent G 2 S) (hc : S.card = 16) : beta G 2 = 16 ∧ SF G 2 = 16 := by
  have hlo : S.card ≤ beta G 2 := Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,hS⟩)
  have hcomp := beta_le_sf G
  have hhi := DegreeCapacity.sf_regular_bound G 3 (by decide) hr
  norm_num at hhi
  omega

/-- Both finite maxima equal16 for the actual S two-lift. -/
theorem scalar_parameters : beta scalarGraph 2 = 16 ∧ SF scalarGraph 2 = 16 :=
  parameters_of_certificate scalarGraph scalar_class.2 scalarSet
    scalar_selection.1 scalar_selection.2

/-- Both finite maxima equal16 for the actual J two-lift. -/
theorem jordan_parameters : beta jordanGraph 2 = 16 ∧ SF jordanGraph 2 = 16 :=
  parameters_of_certificate jordanGraph jordan_class.2 jordanSet
    jordan_selection.1 jordan_selection.2

end D5.S3.Combinatorics.Graph.StarForming.HeawoodCertificates
