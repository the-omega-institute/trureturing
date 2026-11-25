import D5.S3.Arith.FactorialRatio.PathRodriguesGcd
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The exact gcd retains the window dependence of its tail LCM. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.PathRodriguesGcd

open _root_.D5.S3.Arith.FactorialRatio.PathRodriguesGcd
open _root_.D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature ℕ
  (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ r s => tailLCM (r * (s + 1) - 1) (r - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℕ}, 2 ≤ r → ∀ s : ℕ,
    (Finset.range (s + 1)).gcd (B (r - 1) s) = R.readout () r s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (r := 2) (by decide) 0
  change (Finset.range (0 + 1)).gcd (B (2 - 1) 0) = 0 at hbad
  rw [exact_path_rodrigues_gcd (by decide : 2 ≤ 2) 0] at hbad
  exact (by decide : tailLCM (2 * (0 + 1) - 1) (2 - 1) ≠ 0) hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨2, 0, 2, ?_⟩
  change tailLCM (2 * (0 + 1) - 1) (2 - 1) ≠ tailLCM (2 * (2 + 1) - 1) (2 - 1)
  decide

def family : Registration arena (type_of% @exact_path_rodrigues_gcd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_path_rodrigues_gcd, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exact_path_rodrigues_gcd) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.PathRodriguesGcd.exact_path_rodrigues_gcd.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.PathRodriguesGcd.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r s => tailLCM (r * (s + 1) - 1) (r - 1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.PathRodriguesGcd
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.PathRodriguesGcd
