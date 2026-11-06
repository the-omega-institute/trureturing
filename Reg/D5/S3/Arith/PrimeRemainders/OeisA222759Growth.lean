import D5.S3.Arith.PrimeRemainders.OeisA222759Growth
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.PrimeRemainders.OeisA222759Growth

open _root_.D5.S3.Arith.PrimeRemainders.OeisA222759Growth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature := Reg.Support.SingleDependentReadout.signature ℕ
  (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ n q => cubicRemainder n q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ n _ => n) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k n : ℕ) (_hk : 3 ≤ k) (_hn : 1 ≤ n)
    (_hthreshold : P (P k ^ 3) ≤ n),
    ∃ q : Fin k → ℕ, Function.Injective q ∧
      ∀ i : Fin k, 0 < q i ∧ Nat.Prime (q i) ∧ R.readout () n (q i) ≠ n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let n := P (P 3 ^ 3) + 1
  obtain ⟨q, _, hq⟩ := h 3 n (by decide) (by dsimp [n]; omega) (by dsimp [n]; omega)
  have hf := (hq ⟨0, by decide⟩).2.2
  exact hf rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 2, ?_⟩
  change cubicRemainder 1 1 ≠ cubicRemainder 1 2
  decide

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Arith.PrimeRemainders.OeisA222759Growth.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimeRemainders.OeisA222759Growth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n q => cubicRemainder n q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimeRemainders.OeisA222759Growth
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Arith.PrimeRemainders.OeisA222759Growth
