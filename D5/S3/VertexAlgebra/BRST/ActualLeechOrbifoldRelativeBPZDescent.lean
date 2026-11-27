/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeBPZDescent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeBPZDescent
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Skewness and descent of the native relative BRST pairing. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldAbsoluteQTranspose
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeC0

/-! The native c0 Ward law descends the explicit BPZ form to relative cohomology. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open LatticeGeneratingFieldLocality (Charge)
open RelativeCohomology (NativeShell NativeCohomology nativeQ)
open RelativeC0 (NativeCycles c0_inserted_Q_skew c0QuotientPairing)

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

local instance (p : Charge hyperbolicPlane) : AddCommGroup (NativeShell p) :=
  Submodule.addCommGroup _

private theorem absolutePairing_b0 (x y : ComplexState) :
    absolutePairing (b0 x) y = absolutePairing x (b0 y) := by
  simpa only [neg_zero] using absolutePairing_ghostB 0 x y

/-- The relative differential is skew for the concrete c0-inserted BPZ form. -/
theorem relativePairing_Q_skew {p q : Charge hyperbolicPlane}
    (x : NativeShell p) (y : NativeShell q) :
    relativePairing (nativeQ p x).val y.val =
      -relativePairing x.val (nativeQ q y).val :=
  c0_inserted_Q_skew absolutePairing absolutePairing_b0 absolutePairing_Q x y

/-- The concrete relative BPZ pairing on the native kernel modulo image. -/
def relativeCohomologyPairing (p q : Charge hyperbolicPlane) :
    NativeCohomology p →ₗ[ℂ] NativeCohomology q →ₗ[ℂ] ℂ :=
  c0QuotientPairing absolutePairing absolutePairing_b0 absolutePairing_Q p q

/-- On native cycle representatives the quotient pairing is the concrete relative form. -/
@[simp]
theorem relativeCohomologyPairing_mk {p q : Charge hyperbolicPlane}
    (x : NativeCycles p) (y : NativeCycles q) :
    relativeCohomologyPairing p q (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      relativePairing x.val.val y.val.val := rfl

#print axioms relativePairing_Q_skew
#print axioms relativeCohomologyPairing
#print axioms relativeCohomologyPairing_mk

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.NativeBPZ
