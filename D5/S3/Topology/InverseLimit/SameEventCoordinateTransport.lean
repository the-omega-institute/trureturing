/- GID: D5/S3/Topology/InverseLimit/SameEventCoordinateTransport
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/SameEventCoordinateTransport
   mirror-E: none(waiver:implementation-flight)
   anchors: []
   utility: none
   digest: Original whole Dirac capture and proper-stage finite-image obstruction. -/

/- Private preparation: transport precisely the one local split's full fibres
through its actual SignedSuccessorCoordinates.Result. No split is constructed
or assumed to have happened in a raw history by this local lemma. -/
import D5.S3.Topology.InverseLimit.SignedSuccessorCoordinates

/-! Transport full fibres through the same coordinate insertion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped Ordinal

namespace D5.S3.Topology.InverseLimit.ContinuousFiniteImageCapture

open SignedProperLimit SignedSuccessorCoordinates
open Measures.SignedSplitSuccessor

private theorem same_result_whole_fibre_transport
    {a b : Ordinal.{0}} (H : Prefix (Order.succ a))
    (Y Z : Set (H.Space (SignedSuccessorCoordinates.last a))) (R : Result H Y Z)
    (hba : b ≤ a) (y : ℕ → Cube b) (M : Fin 2 → Set ℕ)
    (C : TopologicalSpace.Clopens (splitCarrier Y Z))
    (h0 : ∀ n ∈ M 0, ∀ x : splitCarrier Y Z,
      restrict hba x.1.1.1 = y n → x ∈ C)
    (h1 : ∀ n ∈ M 1, ∀ x : splitCarrier Y Z,
      restrict hba x.1.1.1 = y n → x ∉ C) :
    ∃ D : TopologicalSpace.Clopens R.carrier,
      (∀ n ∈ M 0, ∀ z : R.carrier,
        restrict (hba.trans (Order.le_succ a)) z.1 = y n → z ∈ D) ∧
      (∀ n ∈ M 1, ∀ z : R.carrier,
        restrict (hba.trans (Order.le_succ a)) z.1 = y n → z ∉ D) := by
  let D : TopologicalSpace.Clopens R.carrier :=
    ⟨R.equiv.symm ⁻¹' (C : Set (splitCarrier Y Z)),
      C.isClopen.preimage R.equiv.symm.continuous⟩
  refine ⟨D, ?_, ?_⟩
  · intro n hn z hz
    apply h0 n hn (R.equiv.symm z)
    rw [← R.restrict_inverse b hba z]
    exact hz
  · intro n hn z hz
    apply h1 n hn (R.equiv.symm z)
    rw [← R.restrict_inverse b hba z]
    exact hz

end D5.S3.Topology.InverseLimit.ContinuousFiniteImageCapture
