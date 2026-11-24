/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldNullMomentum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldNullMomentum
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Vanishing of native relative ghost-one cohomology at nonzero null momentum. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLowWeights

/-! The weight-one vanishing applies to the relative quotient on both null rays. -/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeCohomology

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold mode eq_zero_of_weight_one)
open LatticeGeneratingFieldLocality (Charge)

local instance nullMomentumShellAddCommGroup (p : Charge hyperbolicPlane) :
    AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _

local instance nullMomentumCyclesAddCommGroup (p : Charge hyperbolicPlane) :
    AddCommGroup (GradedCycles planeFrame planeBasis p 1) :=
  Submodule.addCommGroup _

set_option maxHeartbeats 1000000 in
-- Inference for the literal orbifold stress eigenspace needs a larger budget.
/-- A nonzero null momentum selects weight one of the actual Leech orbifold. -/
theorem ghostOne_eq_zero_of_nonzero_null (p : Charge hyperbolicPlane) (hp : p ≠ 0)
    (hnull : p (0 : Fin 2) * p (1 : Fin 2) = 0) (x : GradedCohomology planeFrame planeBasis p 1) :
    x = 0 := by
  let equivalence := ghostOneCohomologyEquivNonzero p hp
  let v : OrbifoldWeight p := equivalence x
  have hv : mode 0 (v : Orbifold) = (v : Orbifold) := by
    have h := (Module.End.mem_eigenspace_iff (f := mode 0)).mp v.property
    simpa only [hnull, sub_zero, Int.cast_one, one_smul] using h
  apply equivalence.injective
  exact (Subtype.ext (eq_zero_of_weight_one (v : Orbifold) hv)).trans
    (LinearEquiv.map_zero equivalence).symm

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RelativeCohomology
