import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.VertexAlgebra.Lattice.FixedGradedDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
open LeanInformationAudit
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution FixedGradedDuality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/- These exact source bridges retain the original hypotheses and dependent
carriers. Four-slot registration remains unfinished: whole-family variation,
sensitivity, observational dependence and native source-binding evidence are
not supplied by a source bridge or by successful elaboration. -/
namespace GradeNondegeneracy
structure Params where
  D : LatticeData
  h : ℤ
abbrev signature : Signature where
  Params := Params
  State p := LinearMap.BilinForm ℂ (Carrier p.D)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := LinearMap.BilinForm ℂ (FixedGrade p.D p.h)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p B => fixedGradeForm p.D B p.h) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (hB : B.Nondegenerate)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y)
    (horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
      m ≠ n → B x y = 0)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h : ℤ),
    ∃ hND : (r.readout () ⟨D, h⟩ B).Nondegenerate,
      Nonempty (FixedGrade D h ≃ₗ[ℂ] Module.Dual ℂ (FixedGrade D h))

theorem source_bridge : (type_of% (@fixedGrade_dualEquiv)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual := source_bridge.mp (@fixedGrade_dualEquiv)

/-- Conditional assembly of the actual four-slot contract. The three arguments
are missing evidence, not certificates established by this module. -/
def audit
    (variation : Variation arena actual)
    (sensitivity : Sensitivity arena actual)
    (dependence : ObservationalDependence signature actual) :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@fixedGrade_dualEquiv) (Realization signature) Params Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.FixedGradedDuality.GradeNondegeneracy.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.FixedGradedDuality.GradeNondegeneracy.audit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨{
    actual := actual
    bridge := source_bridge
    variation := variation
    sensitivity := sensitivity
    dependence := dependence }⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.FixedGradedDuality
    definition := none
    coordinates := #[0, 7]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 1,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end GradeNondegeneracy

namespace GlobalEvaluation
structure Params where
  D : LatticeData
  B : LinearMap.BilinForm ℂ (Carrier D)
  hB : B.Nondegenerate
  hgrade : ∀ (n : ℤ) (v : Carrier D),
    theta D (gradeProjection D n v) = gradeProjection D n (theta D v)
  htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y
  horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
    m ≠ n → B x y = 0
  hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))
  x : FixedCarrier D
abbrev signature : Signature where
  Params := Params
  State p := FixedCarrier p.D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p y => fixedRestrictedDualEvaluation p.D p.hgrade
    (fixedRestrictedDualEquiv p.D p.B p.hB p.hgrade p.htheta p.horth p.hD p.x) y)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (hB : B.Nondegenerate)
    (hgrade : ∀ (n : ℤ) (v : Carrier D),
      theta D (gradeProjection D n v) = gradeProjection D n (theta D v))
    (htheta : ∀ (x y : Carrier D), B (theta D x) (theta D y) = B x y)
    (horth : ∀ (m n : ℤ) (x y : Carrier D), x ∈ grade D m → y ∈ grade D n →
      m ≠ n → B x y = 0)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (x y : FixedCarrier D),
    r.readout () ⟨D, B, hB, hgrade, htheta, horth, hD, x⟩ y =
      B (x : Carrier D) (y : Carrier D)

theorem source_bridge :
    (type_of% (@fixedRestrictedDualEquiv_ambient_evaluation)) ↔ arena.Law actual := Iff.rfl

theorem source_actual : arena.Law actual :=
  source_bridge.mp (@fixedRestrictedDualEquiv_ambient_evaluation)

/-- Conditional assembly of the actual four-slot contract. The three arguments
are missing evidence, not certificates established by this module. -/
def audit
    (variation : Variation arena actual)
    (sensitivity : Sensitivity arena actual)
    (dependence : ObservationalDependence signature actual) :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@fixedRestrictedDualEquiv_ambient_evaluation) (Realization signature) Params Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Lattice.FixedGradedDuality.GlobalEvaluation.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Lattice.FixedGradedDuality.GlobalEvaluation.audit
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨{
    actual := actual
    bridge := source_bridge
    variation := variation
    sensitivity := sensitivity
    dependence := dependence }⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.FixedGradedDuality
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 8,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end GlobalEvaluation
end Reg.D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
