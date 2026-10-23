import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.NegativeWordExtension

/-! Exact source telescopes for the negative-current first-source extension.
    These are template bridges only; four-slot registration remains unresolved
    under the repository's concrete issue #20510 exception. -/
set_option autoImplicit false
namespace Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.NegativeWordExtension
open _root_.D5.S3.VertexAlgebra
open LatticeHalfFockGroundRightCurrentTransport

abbrev sourceScope_projectedGround_left_current_word :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_left_current_word)

theorem source_actual_projectedGround_left_current_word :
    sourceScope_projectedGround_left_current_word :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_left_current_word

end Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.NegativeWordExtension
