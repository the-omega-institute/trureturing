import D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the consumed original twelve-cell floor inequality. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral
open _root_.D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ n q => h854 n q) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law X := ∀ n q : ℕ, 0 < q → 0 ≤ X.readout () n q
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1 (by omega)
  norm_num [rejected, realize] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 12, ?_⟩
  change h854 1 1 ≠ h854 1 12
  norm_num [h854]
def family : Registration arena (type_of% (@h854_nonneg)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨h854_nonneg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@h854_nonneg) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral.h854_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n q => h854 n q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral
