import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality

/- Exact typed mirror preserves source-type evidence, not a declared_validated
   four-slot registration. -/
abbrev sourceScope_correctedField_physical_locality :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality.correctedField_physical_locality)
theorem source_actual_correctedField_physical_locality : sourceScope_correctedField_physical_locality :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality.correctedField_physical_locality

open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockPhysicalRescaling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open FieldNormalProductLocality
open scoped VertexOperator BigOperators
noncomputable section
abbrev AuditData := { D : LatticeData // IsUnit D.G.det }
/- The actual family and exact source bridge below are partial audit evidence.
   Whole-family variation, sensitivity, observational dependence and exact
   sourceSelection reconstruction remain unfinished at
   https://github.com/the-omega-institute/trureturing/issues/19578.
   No Contract.Registration is asserted without those proofs. -/

open LatticeHalfFockCorrectedField LatticeHalfFockAllStatePhysicalLocality
namespace CorrectedLocalityAttempt
abbrev Parameter := Σ data : AuditData, Carrier data.val × Carrier data.val
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun p => ℤ × ℤ × ActualTensor p.1.val p.1.property)
    (fun p => ActualTensor p.1.val p.1.property)
def actual : Realization signature := realize signature
  (fun _ p input =>
    (correctedField p.1.val p.1.property p.2.1).coeff input.1
      ((correctedField p.1.val p.1.property p.2.2).coeff input.2.1 input.2.2) -
    (correctedField p.1.val p.1.property p.2.2).coeff input.2.1
      ((correctedField p.1.val p.1.property p.2.1).coeff input.1 input.2.2))
  (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (first second : Carrier D),
    ∃ order : ℕ, ∀ firstExponent secondExponent : ℤ, ∀ vector : ActualTensor D hu,
      ∑ offset ∈ Finset.range (order + 1),
        (((-1 : ℂ) ^ offset) * (order.choose offset : ℂ)) •
          readout.readout () ⟨⟨D, hu⟩, first, second⟩
            (firstExponent - 2 * ((order - offset : ℕ) : ℤ),
              secondExponent - 2 * (offset : ℤ), vector) = 0
theorem source_bridge : (type_of% (@correctedField_physical_locality)) ↔ arena.Law actual := Iff.rfl
end CorrectedLocalityAttempt

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockAllStatePhysicalLocality
