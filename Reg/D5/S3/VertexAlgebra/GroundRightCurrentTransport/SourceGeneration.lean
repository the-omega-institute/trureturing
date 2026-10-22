import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.SourceGeneration

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.SourceGeneration

abbrev sourceScope_sectorSign_not :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.sectorSign_not)

theorem source_actual_sectorSign_not : sourceScope_sectorSign_not :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.sectorSign_not

abbrev sourceScope_sectorSign_square :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.sectorSign_square)

theorem source_actual_sectorSign_square : sourceScope_sectorSign_square :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.sectorSign_square

abbrev sourceScope_wordParity_not :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.wordParity_not)

theorem source_actual_wordParity_not : sourceScope_wordParity_not :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.wordParity_not

abbrev sourceScope_theta_source_expansion :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.theta_source_expansion)

theorem source_actual_theta_source_expansion : sourceScope_theta_source_expansion :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.theta_source_expansion

abbrev sourceScope_sectorProject_eigen :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.sectorProject_eigen)

theorem source_actual_sectorProject_eigen : sourceScope_sectorProject_eigen :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.sectorProject_eigen

abbrev sourceScope_projectedGround_eigen :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_eigen)

theorem source_actual_projectedGround_eigen : sourceScope_projectedGround_eigen :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.projectedGround_eigen

abbrev sourceScope_rightCurrentWord_eigen :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.rightCurrentWord_eigen)

theorem source_actual_rightCurrentWord_eigen : sourceScope_rightCurrentWord_eigen :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockGroundRightCurrentTransport.rightCurrentWord_eigen

/- These exact full-source reconstructions preserve every original fiber.
   A four-slot Contract.Registration additionally requires a lawful enrolled
   dependent readout, exact sourceSelection and complete-family variation,
   sensitivity and observational-dependence evidence. Those obligations are
   unresolved here; these reconstructions assert no declared_validated state. -/


noncomputable section
open scoped BigOperators VertexOperator
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeInvolution
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeHalfFockGroundRightCurrentTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace SignNotAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Bool) (fun _ => ℂ)
def actual : Realization signature := realize signature
  (fun _ _ epsilon => sectorSign epsilon) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ epsilon : Bool, observation.readout () () (!epsilon) = -sectorSign epsilon
theorem source_bridge : (type_of% (@sectorSign_not)) ↔ arena.Law actual := Iff.rfl
end SignNotAttempt

namespace SignSquareAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Bool) (fun _ => ℂ)
def actual : Realization signature := realize signature
  (fun _ _ epsilon => sectorSign epsilon) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ epsilon : Bool, observation.readout () () epsilon *
    observation.readout () () epsilon = 1
theorem source_bridge : (type_of% (@sectorSign_square)) ↔ arena.Law actual := Iff.rfl
end SignSquareAttempt

namespace WordParityAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ D : LatticeData, List (Index D)) (fun _ => Bool) (fun _ => Bool)
def actual : Realization signature := realize signature
  (fun _ p epsilon => wordParity p.2 epsilon) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (w : List (Index D)) (epsilon : Bool),
    observation.readout () ⟨D, w⟩ (!epsilon) = !(wordParity w epsilon)
theorem source_bridge : (type_of% (@wordParity_not)) ↔ arena.Law actual := Iff.rfl
end WordParityAttempt

namespace ExpansionAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (LatticeData × Bool) (fun p => Carrier p.1) (fun p => Carrier p.1)
def actual : Realization signature := realize signature
  (fun _ p b => sectorProject p.1 p.2 b) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (b : Carrier D) (epsilon : Bool),
    observation.readout () (D, epsilon) b =
      ∑ alpha ∈ b.support, ∑ e ∈ (b alpha).support,
        (b alpha).coeff e • rightCurrentWord D (LatticeAllStateField.occurrences D e)
          (projectedGround D alpha (wordParity (LatticeAllStateField.occurrences D e) epsilon))
theorem source_bridge : (type_of% (@theta_source_expansion)) ↔ arena.Law actual := Iff.rfl
end ExpansionAttempt

namespace ProjectionEigenAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (LatticeData × Bool) (fun p => Carrier p.1) (fun p => Carrier p.1)
def actual : Realization signature := realize signature
  (fun _ p b => sectorProject p.1 p.2 b) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (epsilon : Bool) (b : Carrier D),
    theta D (observation.readout () (D, epsilon) b) =
      sectorSign epsilon • sectorProject D epsilon b
theorem source_bridge : (type_of% (@sectorProject_eigen)) ↔ arena.Law actual := Iff.rfl
end ProjectionEigenAttempt

namespace GroundEigenAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (LatticeData × Bool) (fun p => Charge p.1) (fun p => Carrier p.1)
def actual : Realization signature := realize signature
  (fun _ p alpha => projectedGround p.1 alpha p.2) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (alpha : Charge D) (epsilon : Bool),
    theta D (observation.readout () (D, epsilon) alpha) =
      sectorSign epsilon • projectedGround D alpha epsilon
theorem source_bridge : (type_of% (@projectedGround_eigen)) ↔ arena.Law actual := Iff.rfl
end GroundEigenAttempt

namespace WordEigenAttempt
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  (Σ D : LatticeData, List (Index D) × Bool) (fun p => Charge p.1) (fun p => Carrier p.1)
def actual : Realization signature := realize signature
  (fun _ p alpha => rightCurrentWord p.1 p.2.1 (projectedGround p.1 alpha p.2.2)) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (w : List (Index D)) (alpha : Charge D) (epsilon : Bool),
    theta D (observation.readout () ⟨D, w, epsilon⟩ alpha) =
      sectorSign (wordParity w epsilon) • rightCurrentWord D w (projectedGround D alpha epsilon)
theorem source_bridge : (type_of% (@rightCurrentWord_eigen)) ↔ arena.Law actual := Iff.rfl
end WordEigenAttempt

/- The natural dependent readouts and exact bridges above retain all source
   fibers, including zero rank and zero or vanishing sectors. Completing a
   Contract.Registration still requires whole-family variation, sensitivity,
   observational dependence and structural sourceSelection evidence. No
   registered status or evidence for those missing slots is asserted. -/
end

end Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.SourceGeneration
