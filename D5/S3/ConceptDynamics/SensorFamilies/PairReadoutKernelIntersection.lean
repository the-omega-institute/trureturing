/- GID: D5/S3/ConceptDynamics/SensorFamilies/PairReadoutKernelIntersection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SensorFamilies/PairReadoutKernelIntersection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The kernel of a paired readout is the intersection of its two kernels. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-29):
   * Repository searches found completion-specific kernel intersections and
     finite-quotient joint kernels, but no arbitrary two-function product
     identity.
   * Pinned Mathlib supplies `Setoid.ker`, set intersection, and product
     extensionality. Pair equality projects to both component equalities and is
     reconstructed from them.
   * The statement is valid for empty or infinite carriers and outputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.SensorFamilies.PairReadoutKernelIntersection

universe u v w

/-- Joint observation by two readouts identifies exactly those pairs identified
by each readout separately. -/
theorem pair_readout_kernel_eq_intersection
    {X : Type u} {Y : Type v} {Z : Type w}
    (left : X -> Y) (right : X -> Z) :
    {pair : X × X |
      Setoid.ker (fun x => (left x, right x)) pair.1 pair.2} =
      {pair : X × X | Setoid.ker left pair.1 pair.2} ∩
        {pair : X × X | Setoid.ker right pair.1 pair.2} := by
  ext pair
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Setoid.ker_def]
  constructor
  · intro samePair
    exact ⟨congrArg Prod.fst samePair, congrArg Prod.snd samePair⟩
  · rintro ⟨sameLeft, sameRight⟩
    exact Prod.ext sameLeft sameRight

/-- Satisfiability probe: the Boolean identity paired with a constant readout
has exactly the identity kernel. -/
example :
    {pair : Bool × Bool |
      Setoid.ker (fun x : Bool => (x, ())) pair.1 pair.2} =
      {pair : Bool × Bool | Setoid.ker (fun x : Bool => x) pair.1 pair.2} ∩
        {pair : Bool × Bool |
          Setoid.ker (fun _ : Bool => ()) pair.1 pair.2} := by
  exact pair_readout_kernel_eq_intersection
    (X := Bool) (Y := Bool) (Z := Unit)
    (fun x : Bool => x) (fun _ : Bool => ())

#print axioms pair_readout_kernel_eq_intersection

end D5.S3.ConceptDynamics.SensorFamilies.PairReadoutKernelIntersection
