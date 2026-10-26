import D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport

set_option autoImplicit false

universe u

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport

open _root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport

abbrev sourceScope_projectedGround_positive_neutral :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_positive_neutral)

theorem source_actual_projectedGround_positive_neutral :
    sourceScope_projectedGround_positive_neutral :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_positive_neutral

abbrev sourceScope_projectedGround_current_ward :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_current_ward)

theorem source_actual_projectedGround_current_ward :
    sourceScope_projectedGround_current_ward :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_current_ward

abbrev sourceScope_ground_finite_right_transport :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M]
    (A A₀ B J : ℤ → Module.End ℂ M) (r d n gamma : ℤ)
    (outer inner : ℕ),
    (∀ z t : ℤ, J z * A t - A t * J z = A₀ (z + t)) →
      groundFiniteLeft A B J r d n gamma outer inner =
        groundFiniteRight A B J r d n gamma outer inner -
          groundFiniteCorrection A₀ B r d n gamma outer inner

theorem source_actual_ground_finite_right_transport :
    sourceScope_ground_finite_right_transport :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.ground_finite_right_transport

abbrev sourceScope_projectedGround_finite_right_transport :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_finite_right_transport)

theorem source_actual_projectedGround_finite_right_transport :
    sourceScope_projectedGround_finite_right_transport :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_finite_right_transport

/- A full four-slot Contract.Registration needs the template-specific
   source-selection and sensitivity witnesses. This faithful source mirror is
   retained for the linked audit issue and does not claim declared_validated. -/

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport
