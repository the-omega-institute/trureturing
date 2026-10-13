import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import Reg.Support.DependentFamily
import Reg.Support.FiniteHistoryFamily

noncomputable section
namespace Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
open _root_.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
open _root_.D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v

/-- The statement parameter is checked against the imported ConstantInfo.type.
The bridge is definitional on the complete thirteen-binder law. -/
def registration : Registration arena.{u,v} (FullLaw identityFamily) where
  actual := actual
  bridge := Iff.rfl
  variation := Reg.Support.FiniteHistoryFamily.variation
  sensitivity := Reg.Support.FiniteHistoryFamily.sensitivity
  dependence := Reg.Support.FiniteHistoryFamily.dependence

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.history_law_conditional_expectation.{u_1, u_2}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, u_2, 0} signature.{u_1, u_2} (fun _ _ w => w.2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "DataProcessing") "FiniteHistoryConditionalExpectation") "history_law_conditional_expectation") "Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation/D5.S3.ConceptDynamics.InformationEscape.FiniteHistoryFamily.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, u_2, 0} signature.{u_1, u_2} (fun _ _ w => w.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation, definition := none, coordinates := #[0, 1, 11], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "body", "fn", "arg", "arg", "body", "arg", "arg"], stateBinder := 16, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }

/-- The full thirteen-binder source, including both rigid universes, dependent
history types, implicit parameters, instances and proof premises, reuses the
ordinary registration's actual family. No ordinary obligation is removed. -/
def analysisSource : Analysis.Source
    (@history_law_conditional_expectation.{u,v}) :=
  Analysis.Source.ofRegistration _ registration .exact {
    owner := `D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
    definition := none
    coordinates := #[0, 1, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg", "fn", "arg",
        "body", "body", "body", "fn", "arg", "arg", "body", "arg", "arg"]
      stateBinder := 16, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] }

def analysis : AuricFib.Contract.Application.{max (u+1) (v+1),max u v,0,v,0,0}
    (@history_law_conditional_expectation.{u,v}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()], []] }
    acquisition := .unavailable "Dependent history family: finite fiber unacquired" }


end Reg.D5.S3.Estimation.DataProcessing.FiniteHistoryConditionalExpectation
