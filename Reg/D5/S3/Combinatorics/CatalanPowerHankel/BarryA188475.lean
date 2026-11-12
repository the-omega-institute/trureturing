import D5.S3.Combinatorics.CatalanPowerHankel.BarryA188475
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The determinant observation in the original all-index identity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Combinatorics.CatalanPowerHankel.BarryA188475
open _root_.BarryA188475
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

abbrev signature := Reg.Support.SingleDependentReadout.signature ℕ
  (fun n => Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ A => A.det) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ,
    r.readout () n (hankel (n + 1)) =
      1 + 2 * ∑ k ∈ Finset.range (n + 1), (k : ℚ) ^ 2 ∧
    (hankel (n + 1)).det =
      (2 * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 2 + n + 3) / 3

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (h 0).1
  norm_num [rejected, realize] at hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  change (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℚ).det ≠
    (1 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℚ).det
  norm_num

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `BarryA188475.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.CatalanPowerHankel.BarryA188475.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ A => A.det) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.CatalanPowerHankel.BarryA188475
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Combinatorics.CatalanPowerHankel.BarryA188475
