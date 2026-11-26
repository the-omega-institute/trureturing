/- GID: D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Intrinsic C₂ span of the actual fixed lattice vertex algebra. -/

import D5.S3.VertexAlgebra.LatticeInvolution

/-! The intrinsic fixed C₂ span uses the restricted actual lattice field. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.ActualFixedC2

open LatticeGeneratingFieldLocality LatticeInvolution LatticeSugawaraConformal

noncomputable section

local instance fixedCarrierGroup (D : LatticeData) : AddCommGroup (FixedCarrier D) :=
  (fixedSpace D).addCommGroup

/-- The intrinsic span taken with the restricted actual lattice field. -/
def fixedC2 (D : LatticeData) : Submodule ℂ (FixedCarrier D) :=
  Submodule.span ℂ {z | ∃ a b : FixedCarrier D, z = fixedMode D a (-2) b}

/-- Translation of a fixed state lies in the intrinsic C₂ span. -/
theorem translation_mem_fixedC2 (D : LatticeData) (v : FixedCarrier D) :
    fixedTranslation D v ∈ fixedC2 D := by
  apply Submodule.subset_span
  refine ⟨v, fixedVacuum D, Subtype.ext ?_⟩
  exact LatticeActualVertexAlgebra.translation_as_mode D v.val

end

end D5.S3.VertexAlgebra.Lattice.ActualFixedC2
