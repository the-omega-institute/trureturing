import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration

/-! Full compiled source telescopes and assertion-valued diagnostic attempts.
These records have no source operand-selection certificate. They do not claim
validated escape registration; the native classifier must report its actual
unsupported form. No theorem admission or retention relies on these records. -/
set_option autoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.OriginalFiltrationSourceAttempt
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ _ P => P) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
def arena (P : Prop) : Arena where
  signature := signature
  Law obs := obs.readout () () P
theorem full_source_bridge (P : Prop) : P ↔ (arena P).Law actual := Iff.rfl
def family (P : Prop) (h : P) : Registration (arena P) P where
  actual := actual
  bridge := full_source_bridge P
  variation := ⟨h, rejected, fun hf => hf⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, fun hf => hf⟩
      intro other hne
      exact (hne (show other = role from @Subsingleton.elim Unit inferInstance other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), True, False, ?_⟩
    change True ≠ False
    intro he
    exact Eq.mp he trivial
/-- Expand a closed theorem's diagnostic record without exposing a generic
Contract-valued function to native input discovery. This changes no classifier. -/
macro "original_diagnostic_attempt%" "(" P:term "," h:term "," unitName:term ","
    realizationName:term "," sourceFamily:term ")" : term =>
  `(({ unitName := $unitName
       realizationName := $realizationName
       realizationSource := none
       generated := false
       arena := .source ⟨arena $P⟩
       objectArena := .source ⟨arena $P⟩
       catalog := Lean.Name.anonymous
       localNames := false
       realization := .source (arena $P) ⟨$sourceFamily⟩
       correspondence := { stage := .evidence, objectStage := .evidence }
       bundleNonempty := .absent
       readout := some (realize signature actual.readout actual.anchor)
       variation := .absent
       sensitivity := .absent
       partialSensitivity := none
       escapeFrom := none
       sourceSelection := none
       continuation := .unknown
       familyRecord := none
       options := #[] } : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} $h (Realization signature) Unit Unit))
end Reg.OriginalFiltrationSourceAttempt

universe u v w z
open LeanInformationAudit Reg.OriginalFiltrationSourceAttempt
namespace Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration
namespace weight_plus
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_plus)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_plus))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_plus))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_plus)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_plus)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_plus)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_plus) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_plus)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_plus),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.weight_plus.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.weight_plus.diagnosticFamily, diagnosticFamily)
end weight_plus
namespace weight_minus
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_minus)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_minus))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_minus))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_minus)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_minus)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_minus)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_minus) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_minus)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_minus),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.weight_minus.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.weight_minus.diagnosticFamily, diagnosticFamily)
end weight_minus
namespace weight_transverse
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_transverse)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_transverse))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_transverse))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_transverse)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_transverse)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_transverse)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_transverse) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_transverse)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.weight_transverse),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.weight_transverse.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.weight_transverse.diagnosticFamily, diagnosticFamily)
end weight_transverse
namespace exponentDegree_add
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_add)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_add))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_add))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_add)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_add)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_add)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_add) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_add)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_add),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.exponentDegree_add.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.exponentDegree_add.diagnosticFamily, diagnosticFamily)
end exponentDegree_add
namespace exponentDegree_single
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_single)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_single))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_single))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_single)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_single)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_single)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_single) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_single)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.exponentDegree_single),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.exponentDegree_single.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.exponentDegree_single.diagnosticFamily, diagnosticFamily)
end exponentDegree_single
namespace X_mul_monomial
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.X_mul_monomial)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.X_mul_monomial))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.X_mul_monomial))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.X_mul_monomial)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.X_mul_monomial)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.X_mul_monomial)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.X_mul_monomial) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.X_mul_monomial)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.X_mul_monomial),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.X_mul_monomial.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.X_mul_monomial.diagnosticFamily, diagnosticFamily)
end X_mul_monomial
namespace single_add_sub
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.single_add_sub)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.single_add_sub))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.single_add_sub))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.single_add_sub)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.single_add_sub)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.single_add_sub)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.single_add_sub) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.single_add_sub)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.single_add_sub),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.single_add_sub.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.single_add_sub.diagnosticFamily, diagnosticFamily)
end single_add_sub
namespace derivative_monomial
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_monomial)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_monomial))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_monomial))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_monomial)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_monomial)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_monomial)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_monomial) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_monomial)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_monomial),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.derivative_monomial.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.derivative_monomial.diagnosticFamily, diagnosticFamily)
end derivative_monomial
namespace multiply_coefficient
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_coefficient)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_coefficient))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_coefficient))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_coefficient)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_coefficient)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_coefficient)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_coefficient) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_coefficient)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_coefficient),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.multiply_coefficient.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.multiply_coefficient.diagnosticFamily, diagnosticFamily)
end multiply_coefficient
namespace derivative_coefficient
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_coefficient)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_coefficient))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_coefficient))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_coefficient)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_coefficient)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_coefficient)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_coefficient) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_coefficient)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_coefficient),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.derivative_coefficient.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.derivative_coefficient.diagnosticFamily, diagnosticFamily)
end derivative_coefficient
namespace multiply_support_degree
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_support_degree)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_support_degree))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_support_degree))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_support_degree)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_support_degree)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_support_degree)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_support_degree) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_support_degree)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_support_degree),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.multiply_support_degree.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.multiply_support_degree.diagnosticFamily, diagnosticFamily)
end multiply_support_degree
namespace derivative_support_degree
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_support_degree)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_support_degree))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_support_degree))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_support_degree)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_support_degree)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_support_degree)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_support_degree) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_support_degree)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_support_degree),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.derivative_support_degree.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.derivative_support_degree.diagnosticFamily, diagnosticFamily)
end derivative_support_degree
namespace create_coefficient
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_coefficient)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_coefficient))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_coefficient))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_coefficient)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_coefficient)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_coefficient)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_coefficient) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_coefficient)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_coefficient),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.create_coefficient.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.create_coefficient.diagnosticFamily, diagnosticFamily)
end create_coefficient
namespace annihilate_coefficient
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_coefficient)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_coefficient))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_coefficient))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_coefficient)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_coefficient)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_coefficient)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_coefficient) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_coefficient)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_coefficient),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.annihilate_coefficient.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.annihilate_coefficient.diagnosticFamily, diagnosticFamily)
end annihilate_coefficient
namespace create_support_charge
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_support_charge)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_support_charge))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_support_charge))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_support_charge)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_support_charge)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_support_charge)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_support_charge) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_support_charge)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.create_support_charge),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.create_support_charge.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.create_support_charge.diagnosticFamily, diagnosticFamily)
end create_support_charge
namespace annihilate_support_charge
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_support_charge)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_support_charge))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_support_charge))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_support_charge)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_support_charge)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_support_charge)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_support_charge) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_support_charge)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.annihilate_support_charge),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.annihilate_support_charge.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.annihilate_support_charge.diagnosticFamily, diagnosticFamily)
end annihilate_support_charge
namespace b_support_charge
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_support_charge)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_support_charge))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_support_charge))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_support_charge)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_support_charge)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_support_charge)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_support_charge) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_support_charge)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_support_charge),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.b_support_charge.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.b_support_charge.diagnosticFamily, diagnosticFamily)
end b_support_charge
namespace c_support_charge
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_support_charge)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_support_charge))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_support_charge))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_support_charge)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_support_charge)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_support_charge)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_support_charge) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_support_charge)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_support_charge),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.c_support_charge.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.c_support_charge.diagnosticFamily, diagnosticFamily)
end c_support_charge
namespace basis_expand
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.basis_expand.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.basis_expand.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.basis_expand.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.basis_expand.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.basis_expand.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.basis_expand.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.basis_expand.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.basis_expand.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.basis_expand.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.basis_expand.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.basis_expand.diagnosticFamily, diagnosticFamily)
end basis_expand
namespace shift_zero
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_zero.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_zero.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_zero.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_zero.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_zero.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_zero.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_zero.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_zero.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_zero.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_zero.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_zero.diagnosticFamily, diagnosticFamily)
end shift_zero
namespace shift_one
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_one.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_one.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_one.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_one.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_one.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_one.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_one.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_one.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_one.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_one.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_one.diagnosticFamily, diagnosticFamily)
end shift_one
namespace shift_smul
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_smul.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_smul.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_smul.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_smul.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_smul.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_smul.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_smul.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_smul.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_smul.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_smul.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_smul.diagnosticFamily, diagnosticFamily)
end shift_smul
namespace shift_add
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_add.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_add.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_add.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_add.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_add.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_add.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_add.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_add.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_add.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_add.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_add.diagnosticFamily, diagnosticFamily)
end shift_add
namespace shift_mul
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_mul.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_mul.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_mul.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_mul.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_mul.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_mul.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_mul.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_mul.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_mul.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_mul.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_mul.diagnosticFamily, diagnosticFamily)
end shift_mul
namespace shift_sum
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_sum.{u,v,w})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_sum.{u,v,w}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_sum.{u,v,w}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_sum.{u,v,w})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_sum.{u,v,w})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_sum.{u,v,w})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_sum.{u,v,w}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_sum.{u,v,w})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_sum.{u,v,w}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_sum.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_sum.diagnosticFamily, diagnosticFamily)
end shift_sum
namespace strictRaises_of_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_of_shift.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_of_shift.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_of_shift.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_of_shift.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_of_shift.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_of_shift.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_of_shift.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_of_shift.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_of_shift.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.strictRaises_of_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.strictRaises_of_shift.diagnosticFamily, diagnosticFamily)
end strictRaises_of_shift
namespace strictRaises_smul
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_smul.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_smul.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_smul.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_smul.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_smul.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_smul.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_smul.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_smul.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_smul.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.strictRaises_smul.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.strictRaises_smul.diagnosticFamily, diagnosticFamily)
end strictRaises_smul
namespace strictRaises_add
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_add.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_add.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_add.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_add.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_add.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_add.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_add.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_add.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.strictRaises_add.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.strictRaises_add.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.strictRaises_add.diagnosticFamily, diagnosticFamily)
end strictRaises_add
namespace shift_diagonal
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_diagonal.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_diagonal.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_diagonal.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_diagonal.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_diagonal.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_diagonal.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_diagonal.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_diagonal.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.shift_diagonal.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_diagonal.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.shift_diagonal.diagnosticFamily, diagnosticFamily)
end shift_diagonal
namespace multiply_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.multiply_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.multiply_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.multiply_shift.diagnosticFamily, diagnosticFamily)
end multiply_shift
namespace derivative_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.derivative_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.derivative_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.derivative_shift.diagnosticFamily, diagnosticFamily)
end derivative_shift
namespace b_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.b_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.b_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.b_shift.diagnosticFamily, diagnosticFamily)
end b_shift
namespace c_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.c_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.c_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.c_shift.diagnosticFamily, diagnosticFamily)
end c_shift
namespace cubic_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubic_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubic_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubic_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubic_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubic_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubic_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubic_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubic_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubic_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cubic_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cubic_shift.diagnosticFamily, diagnosticFamily)
end cubic_shift
namespace cubicTerm_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubicTerm_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubicTerm_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubicTerm_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubicTerm_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubicTerm_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubicTerm_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubicTerm_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubicTerm_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cubicTerm_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cubicTerm_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cubicTerm_shift.diagnosticFamily, diagnosticFamily)
end cubicTerm_shift
namespace Qg_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.Qg_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.Qg_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.Qg_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.Qg_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.Qg_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.Qg_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.Qg_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.Qg_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.Qg_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.Qg_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.Qg_shift.diagnosticFamily, diagnosticFamily)
end Qg_shift
namespace cm_plus_negative
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_negative)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_negative))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_negative))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_negative)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_negative)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_negative)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_negative) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_negative)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_negative),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_plus_negative.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_plus_negative.diagnosticFamily, diagnosticFamily)
end cm_plus_negative
namespace cm_minus_negative
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_negative)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_negative))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_negative))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_negative)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_negative)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_negative)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_negative) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_negative)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_negative),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_minus_negative.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_minus_negative.diagnosticFamily, diagnosticFamily)
end cm_minus_negative
namespace cm_plus_positive
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_positive)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_positive))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_positive))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_positive)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_positive)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_positive)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_positive) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_positive)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_positive),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_plus_positive.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_plus_positive.diagnosticFamily, diagnosticFamily)
end cm_plus_positive
namespace cm_minus_positive
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_positive)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_positive))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_positive))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_positive)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_positive)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_positive)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_positive) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_positive)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_positive),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_minus_positive.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_minus_positive.diagnosticFamily, diagnosticFamily)
end cm_minus_positive
namespace cm_plus_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_plus_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_plus_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_plus_shift.diagnosticFamily, diagnosticFamily)
end cm_plus_shift
namespace cm_minus_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_minus_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_minus_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_minus_shift.diagnosticFamily, diagnosticFamily)
end cm_minus_shift
namespace cm_zero_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_zero_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_zero_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_zero_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_zero_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_zero_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_zero_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_zero_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_zero_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_zero_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_zero_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_zero_shift.diagnosticFamily, diagnosticFamily)
end cm_zero_shift
namespace cm_transverse_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_transverse_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_transverse_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_transverse_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_transverse_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_transverse_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_transverse_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_transverse_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_transverse_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.cm_transverse_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_transverse_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.cm_transverse_shift.diagnosticFamily, diagnosticFamily)
end cm_transverse_shift
namespace sector_coefficient
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.sector_coefficient)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.sector_coefficient))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.sector_coefficient))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.sector_coefficient)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.sector_coefficient)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.sector_coefficient)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.sector_coefficient) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.sector_coefficient)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.sector_coefficient),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.sector_coefficient.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.sector_coefficient.diagnosticFamily, diagnosticFamily)
end sector_coefficient
namespace tensor_current_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_current_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_current_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_current_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_current_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_current_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_current_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_current_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_current_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_current_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.tensor_current_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.tensor_current_shift.diagnosticFamily, diagnosticFamily)
end tensor_current_shift
namespace original_plus_c_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_c_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_c_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_c_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_c_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_c_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_c_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_c_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_c_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_c_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_plus_c_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_plus_c_shift.diagnosticFamily, diagnosticFamily)
end original_plus_c_shift
namespace original_minus_c_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_c_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_c_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_c_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_c_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_c_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_c_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_c_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_c_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_c_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_minus_c_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_minus_c_shift.diagnosticFamily, diagnosticFamily)
end original_minus_c_shift
namespace original_plus_b_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_b_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_b_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_b_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_b_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_b_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_b_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_b_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_b_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_b_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_plus_b_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_plus_b_shift.diagnosticFamily, diagnosticFamily)
end original_plus_b_shift
namespace original_transverse_c_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_c_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_c_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_c_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_c_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_c_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_c_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_c_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_c_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_c_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_transverse_c_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_transverse_c_shift.diagnosticFamily, diagnosticFamily)
end original_transverse_c_shift
namespace original_plus_matter_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_matter_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_matter_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_matter_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_matter_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_matter_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_matter_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_matter_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_matter_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_plus_matter_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_plus_matter_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_plus_matter_shift.diagnosticFamily, diagnosticFamily)
end original_plus_matter_shift
namespace original_minus_matter_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_matter_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_matter_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_matter_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_matter_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_matter_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_matter_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_matter_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_matter_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_minus_matter_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_minus_matter_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_minus_matter_shift.diagnosticFamily, diagnosticFamily)
end original_minus_matter_shift
namespace original_transverse_matter_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_matter_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_matter_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_matter_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_matter_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_matter_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_matter_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_matter_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_matter_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_matter_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_transverse_matter_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_transverse_matter_shift.diagnosticFamily, diagnosticFamily)
end original_transverse_matter_shift
namespace tensor_ghost_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_ghost_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_ghost_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_ghost_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_ghost_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_ghost_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_ghost_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_ghost_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_ghost_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.tensor_ghost_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.tensor_ghost_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.tensor_ghost_shift.diagnosticFamily, diagnosticFamily)
end tensor_ghost_shift
namespace original_ghost_cubic_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_ghost_cubic_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_ghost_cubic_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_ghost_cubic_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_ghost_cubic_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_ghost_cubic_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_ghost_cubic_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_ghost_cubic_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_ghost_cubic_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_ghost_cubic_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_ghost_cubic_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_ghost_cubic_shift.diagnosticFamily, diagnosticFamily)
end original_ghost_cubic_shift
namespace original_cross_c_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_cross_c_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_cross_c_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_cross_c_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_cross_c_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_cross_c_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_cross_c_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_cross_c_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_cross_c_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_cross_c_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_cross_c_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_cross_c_shift.diagnosticFamily, diagnosticFamily)
end original_cross_c_shift
namespace original_reverse_cross_c_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_reverse_cross_c_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_reverse_cross_c_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_reverse_cross_c_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_reverse_cross_c_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_reverse_cross_c_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_reverse_cross_c_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_reverse_cross_c_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_reverse_cross_c_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_reverse_cross_c_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_reverse_cross_c_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_reverse_cross_c_shift.diagnosticFamily, diagnosticFamily)
end original_reverse_cross_c_shift
namespace original_transverse_pair_c_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_pair_c_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_pair_c_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_pair_c_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_pair_c_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_pair_c_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_pair_c_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_pair_c_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_pair_c_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.original_transverse_pair_c_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_transverse_pair_c_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.original_transverse_pair_c_shift.diagnosticFamily, diagnosticFamily)
end original_transverse_pair_c_shift
namespace family_total_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.family_total_shift.{u,v})) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.family_total_shift.{u,v}))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.family_total_shift.{u,v}))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.family_total_shift.{u,v})) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.family_total_shift.{u,v})) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.family_total_shift.{u,v})
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.family_total_shift.{u,v}) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.family_total_shift.{u,v})), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.family_total_shift.{u,v}),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.family_total_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.family_total_shift.diagnosticFamily, diagnosticFamily)
end family_total_shift
namespace dTerm_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.dTerm_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.dTerm_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.dTerm_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.dTerm_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.dTerm_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.dTerm_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.dTerm_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.dTerm_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.dTerm_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.dTerm_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.dTerm_shift.diagnosticFamily, diagnosticFamily)
end dTerm_shift
namespace rTerm_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.rTerm_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.rTerm_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.rTerm_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.rTerm_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.rTerm_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.rTerm_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.rTerm_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.rTerm_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.rTerm_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.rTerm_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.rTerm_shift.diagnosticFamily, diagnosticFamily)
end rTerm_shift
namespace d0_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.d0_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.d0_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.d0_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.d0_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.d0_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.d0_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.d0_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.d0_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.d0_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.d0_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.d0_shift.diagnosticFamily, diagnosticFamily)
end d0_shift
namespace R_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.R_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.R_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.R_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.R_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.R_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.R_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.R_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.R_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.R_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.R_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.R_shift.diagnosticFamily, diagnosticFamily)
end R_shift
namespace invM_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.invM_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.invM_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.invM_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.invM_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.invM_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.invM_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.invM_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.invM_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.invM_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.invM_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.invM_shift.diagnosticFamily, diagnosticFamily)
end invM_shift
namespace h_shift
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.h_shift)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.h_shift))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.h_shift))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.h_shift)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.h_shift)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.h_shift)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.h_shift) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.h_shift)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.h_shift),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.h_shift.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.h_shift.diagnosticFamily, diagnosticFamily)
end h_shift
namespace a_add_vectors
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_add_vectors)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_add_vectors))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_add_vectors))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_add_vectors)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_add_vectors)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_add_vectors)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_add_vectors) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_add_vectors)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_add_vectors),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.a_add_vectors.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.a_add_vectors.diagnosticFamily, diagnosticFamily)
end a_add_vectors
namespace a_smul_vector
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_smul_vector)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_smul_vector))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_smul_vector))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_smul_vector)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_smul_vector)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_smul_vector)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_smul_vector) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_smul_vector)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.a_smul_vector),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.a_smul_vector.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.a_smul_vector.diagnosticFamily, diagnosticFamily)
end a_smul_vector
namespace inverse_covector
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverse_covector)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverse_covector))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverse_covector))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverse_covector)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverse_covector)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverse_covector)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverse_covector) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverse_covector)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverse_covector),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.inverse_covector.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.inverse_covector.diagnosticFamily, diagnosticFamily)
end inverse_covector
namespace inverseGramPair_eq
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGramPair_eq)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGramPair_eq))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGramPair_eq))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGramPair_eq)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGramPair_eq)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGramPair_eq)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGramPair_eq) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGramPair_eq)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGramPair_eq),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.inverseGramPair_eq.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.inverseGramPair_eq.diagnosticFamily, diagnosticFamily)
end inverseGramPair_eq
namespace inverseGram_longitudinal_coefficients
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.inverseGram_longitudinal_coefficients.diagnosticFamily, diagnosticFamily)
end inverseGram_longitudinal_coefficients
namespace momentum_current_decomposition
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentum_current_decomposition)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentum_current_decomposition))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentum_current_decomposition))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentum_current_decomposition)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentum_current_decomposition)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentum_current_decomposition)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentum_current_decomposition) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentum_current_decomposition)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentum_current_decomposition),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.momentum_current_decomposition.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.momentum_current_decomposition.diagnosticFamily, diagnosticFamily)
end momentum_current_decomposition
namespace momentumRemainder_formula
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_formula)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_formula))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_formula))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_formula)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_formula)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_formula)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_formula) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_formula)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_formula),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.momentumRemainder_formula.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.momentumRemainder_formula.diagnosticFamily, diagnosticFamily)
end momentumRemainder_formula
namespace momentumRemainder_strictRaises
/-- The whole native theorem telescope, without dropping any hypotheses. -/
theorem source_bridge : (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_strictRaises)) ↔
    (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_strictRaises))).Law actual := full_source_bridge _
def diagnosticFamily : Registration (arena (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_strictRaises))) (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_strictRaises)) := family (type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_strictRaises)) (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_strictRaises)
/-- Diagnostic only: assertion-valued readout and no source-selection certificate.
This is not a faithful operand-family registration and must not be called validated. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_strictRaises) (Realization signature) Unit Unit :=
  original_diagnostic_attempt%((type_of% (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_strictRaises)), (@D5.S3.VertexAlgebra.LatticeBRSTModeFiltration.momentumRemainder_strictRaises),
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.momentumRemainder_strictRaises.unit,
    `Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration.momentumRemainder_strictRaises.diagnosticFamily, diagnosticFamily)
end momentumRemainder_strictRaises
end Reg.D5.S3.VertexAlgebra.Lattice.LatticeBRSTModeFiltration
