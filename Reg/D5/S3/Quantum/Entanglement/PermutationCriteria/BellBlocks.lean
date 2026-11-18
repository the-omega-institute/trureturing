import Reg.Support.PermutationCriteriaBellBlocks
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
import Reg.Support.SingleDependentReadout
import Reg.Support.UniverseSingleReadout

namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance
open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
noncomputable section
universe u_a u_b u_m u_n
namespace TwoIsometries
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_two_isometries.{u_a, u_b, u_m, u_n}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_two_isometries.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.TwoIsometries.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_a, u_b, u_m, u_n}⟩
  objectArena := .source ⟨arena.{u_a, u_b, u_m, u_n}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_a, u_b, u_m, u_n} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end TwoIsometries
namespace Reindex
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_submatrix_equiv.{u_a, u_b, u_m, u_n}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.Reindex.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_a, u_b, u_m, u_n}⟩
  objectArena := .source ⟨arena.{u_a, u_b, u_m, u_n}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_a, u_b, u_m, u_n} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reindex
namespace Transpose
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_transpose.{u_n}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_transpose.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.Transpose.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_n}⟩
  objectArena := .source ⟨arena.{u_n}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_n} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Transpose
namespace Adjoint
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_conjTranspose.{u_n}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_conjTranspose.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.Adjoint.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_n}⟩
  objectArena := .source ⟨arena.{u_n}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_n} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Adjoint
namespace CoordinateEmbedding
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@coordinateEmbedding_isometry.{u_a, u_m}) (Realization matrixSignature.{u_m}) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.coordinateEmbedding_isometry.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.CoordinateEmbedding.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_a, u_m}⟩
  objectArena := .source ⟨arena.{u_a, u_m}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_a, u_m} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature.{u_m} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end CoordinateEmbedding
namespace RectAdjoint
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_conjTranspose_rect.{u_m, u_n}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_conjTranspose_rect.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.RectAdjoint.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_m, u_n}⟩
  objectArena := .source ⟨arena.{u_m, u_n}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_m, u_n} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end RectAdjoint
end
end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance

namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.WitnessNorms
open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
open scoped ComplexOrder MatrixOrder
noncomputable section
universe u_m u_n
namespace ScalarGram
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_of_scalar_gram.{u_m, u_n}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.traceNorm_of_scalar_gram.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.WitnessNorms.ScalarGram.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u_m, u_n}⟩
  objectArena := .source ⟨arena.{u_m, u_n}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u_m, u_n} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ScalarGram
namespace MixedColumn
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_mixedColumn) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.traceNorm_mixedColumn.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.WitnessNorms.MixedColumn.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end MixedColumn
namespace HalfIdentity
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_halfIdentity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.traceNorm_halfIdentity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.WitnessNorms.HalfIdentity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end HalfIdentity
namespace BellColumn
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_bellColumn) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.traceNorm_bellColumn.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.WitnessNorms.BellColumn.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end BellColumn
namespace BellOneCross
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_bellOneCross) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.traceNorm_bellOneCross.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.WitnessNorms.BellOneCross.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end BellOneCross
namespace BellSquare
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@traceNorm_bellSquare) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Entanglement.PermutationCriteria.traceNorm_bellSquare.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.WitnessNorms.BellSquare.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end BellSquare
end
end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.WitnessNorms

namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix
noncomputable section
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks.traceNorm_fourEntries)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def count_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks.bellValue_injective)
      (Realization countSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks.count_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks.count_source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨count_source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace EmbeddedSingle
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks.embedded_single)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks.EmbeddedSingle.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks.EmbeddedSingle.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end EmbeddedSingle
end
end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
