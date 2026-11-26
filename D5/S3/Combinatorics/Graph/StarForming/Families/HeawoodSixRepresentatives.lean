/- GID: D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodSixRepresentatives
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/Families/HeawoodSixRepresentatives
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Six explicit signings cover every connected binary lift of the Heawood graph. -/

import D5.S1.Eigenstructure.BinaryTraceZeroSimilarity
import D5.S3.Combinatorics.Graph.StarForming.Families.HeawoodMatrixAction

namespace D5.S3.Combinatorics.Graph.StarForming.Families.HeawoodSixRepresentatives

open HeawoodSwitching HeawoodLift
open D5.S1.Eigenstructure

private def negativeFlags (k : Fin 6) : List (Nat × Nat) :=
  ![[(1, 2)],
    [(1, 2), (2, 4)],
    [(3, 3), (1, 2), (2, 1)],
    [(3, 3), (2, 1)],
    [(1, 4), (2, 1), (4, 2)],
    [(1, 4), (2, 1), (4, 2), (2, 4)]] k

/-- Six signings, in the order of the two nilpotent, two repeated-root
and two remaining cubic cases. A flag is named by its nonzero binary
point and line coordinates, encoded as integers from one through seven. -/
def representative (k : Fin 6) : Signing := fun e =>
  if (negativeFlags k).contains ((flags e).1.val + 1, (flags e).2.val + 1) then 1 else 0

private theorem representative_gain (k : Fin 6) :
    phi (representative k) = BinaryTraceZeroSimilarity.representative k := by
  revert k
  decide +kernel

/-- Every connected binary Heawood signing gives a graph isomorphic to at
least one of the six specified signings. -/
theorem exists_representative (s : Signing) (h : (graph s).Preconnected) :
    ∃ k : Fin 6, Nonempty (graph s ≃g graph (representative k)) := by
  obtain ⟨k, g, he⟩ :=
    BinaryTraceZeroSimilarity.exists_conjugate (phi s) ((preconnected_iff s).mp h) (trace_phi s)
  rw [← representative_gain k] at he
  obtain ⟨e⟩ := HeawoodMatrixAction.isomorphic_of_phi_conjugate (representative k) s g he
  exact ⟨k, ⟨e.symm⟩⟩

end D5.S3.Combinatorics.Graph.StarForming.Families.HeawoodSixRepresentatives
