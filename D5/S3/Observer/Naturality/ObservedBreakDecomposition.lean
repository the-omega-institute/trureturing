/- GID: D5/S3/Observer/Naturality/ObservedBreakDecomposition
   generality: G
   mirror-B: D5/B/S3/Observer/Naturality/ObservedBreakDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Split observed symmetry breaking into observer and intrinsic defects. -/

import Mathlib.Algebra.Group.Hom.Basic

/- Library-search audit trail (2026-09-04):
   * Repository searches for observed/intrinsic breaks, observer commutators,
     naturality defects, and defect decompositions found metric bounds and
     composition chain laws, but no theorem stating this two-term identity.
   * `ProjectionCommutatorIdentity` and
     `ReadoutUpdateCommutatorFactorization` concern operator products rather
     than an additive observation map.
   * Pinned Mathlib supplies `map_sub` and `sub_add_sub_cancel`, which are used
     directly. No packaged theorem states the displayed observer identity.
   * The source writes the readout as an ordinary function, but its equality
     requires preservation of subtraction. The theorem records that necessary
     repair with an `AddMonoidHom`; the integer counterexample shows that the
     unrestricted statement is false. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Naturality.ObservedBreakDecomposition

/-- The part of the observed break caused by failure of the observer to
intertwine the object and observation updates. -/
def observerBreak {X Y : Type*} [Sub Y]
    (JX : X -> X) (JY : Y -> Y) (O : X -> Y) (x : X) : Y :=
  JY (O x) - O (JX x)

/-- The break carried by the object before it is read by the observer. -/
def intrinsicBreak {X : Type*} [Sub X] (JX : X -> X) (x : X) : X :=
  JX x - x

/-- The observed break is exactly the observer's intertwining defect plus the
readout of the object's intrinsic break. -/
theorem observed_break_decomposition
    {X Y : Type*} [AddGroup X] [AddGroup Y]
    (JX : X -> X) (JY : Y -> Y) (O : X →+ Y) (x : X) :
    JY (O x) - O x =
      observerBreak JX JY O x + O (intrinsicBreak JX x) := by
  simp only [observerBreak, intrinsicBreak]
  rw [map_sub]
  exact (sub_add_sub_cancel _ _ _).symm

/-- Without additivity of the observation map, the displayed decomposition
can fail even for integer-valued dynamics. -/
theorem nonadditive_observer_break_counterexample :
    let O : Int -> Int := fun z => z * z
    let JX : Int -> Int := fun z => z + 1
    let JY : Int -> Int := id
    JY (O 1) - O 1 !=
      observerBreak JX JY O 1 + O (intrinsicBreak JX 1) := by
  decide

#print axioms observed_break_decomposition
#print axioms nonadditive_observer_break_counterexample

end D5.S3.Observer.Naturality.ObservedBreakDecomposition
