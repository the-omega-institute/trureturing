import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality

set_option autoImplicit false

namespace Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality

/- Exact typed mirror preserves source-type evidence, not a declared_validated
   four-slot registration. -/
abbrev sourceScope_physicalWord_locality :=
  type_of% (@_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality.physicalWord_locality)
theorem source_actual_physicalWord_locality : sourceScope_physicalWord_locality :=
  @_root_.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality.physicalWord_locality

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

open LatticeHalfFockPhysicalWordLocality
namespace WordLocalityAttempt
abbrev Parameter := Σ data : AuditData, Charge data.val × Charge data.val ×
  List (Index data.val) × List (Index data.val)
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature
  Parameter (fun _ => ℤ × ℤ × ℤ × ℤ)
    (fun p => Module.End ℂ (ActualTensor p.1.val p.1.property))
def actual : Realization signature := realize signature
  (fun _ p modes => commutator
    (physicalSlice p.1.val p.1.property
      (chargedWordField p.1.val p.1.property p.2.1 p.2.2.2.1) modes.1)
    (physicalSlice p.1.val p.1.property
      (chargedWordField p.1.val p.1.property p.2.2.1 p.2.2.2.2) modes.2.1)
    modes.2.2.1 modes.2.2.2) (fun empty => nomatch empty)
def arena : Arena where
  signature := signature
  Law readout := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (first second : Charge D) (firstWord secondWord : List (Index D)),
    ∃ order : ℕ, ∀ s t : ℤ, delta^[order]
      (fun left right => readout.readout () ⟨⟨D, hu⟩, first, second, firstWord, secondWord⟩
        (s, t, left, right)) = 0
theorem source_bridge : (type_of% (@physicalWord_locality)) ↔ arena.Law actual := Iff.rfl
end WordLocalityAttempt

end

end Reg.D5.S3.VertexAlgebra.LatticeHalfFockPhysicalWordLocality
