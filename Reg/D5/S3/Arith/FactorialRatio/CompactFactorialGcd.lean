import D5.S3.Arith.FactorialRatio.CompactFactorialGcd
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! For a fixed rank, both divisibilities observe the same gcd as the window varies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FactorialRatio.CompactFactorialGcd

open _root_.D5.S3.Arith.FactorialRatio.CompactFactorialGcd
open _root_.D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Nat

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ r s => selbergGcd r s) (fun e => nomatch e)

/-- Vary only the occurrence selected by `role`, keeping the other gcd readout fixed. -/
def rejected (role : Bool) : Realization signature :=
  realize signature
    (fun i r s => if i = role then (if role then 0 else 1) else selbergGcd r s)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r s : ℕ), 2 ≤ r → s < r ^ 2 →
    tailLCM (r * s + r - 1) (r - 1) ∣ R.readout false r s ∧
      R.readout true r s ∣ tailLCM (r * s + r - 1) (r - 1) * (2 * r ^ 2)!

private theorem rejected_law (role : Bool) : ¬ arena.Law (rejected role) := by
  intro h
  cases role
  · have hbad := (h 2 3 (by decide) (by decide)).1
    change tailLCM 7 1 ∣ 1 at hbad
    exact (by decide : ¬ tailLCM 7 1 ∣ 1) hbad
  · have hbad := (h 2 0 (by decide) (by decide)).2
    change 0 ∣ tailLCM 1 1 * 8 ! at hbad
    exact (by decide : ¬ 0 ∣ tailLCM 1 1 * 8 !) hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨3, 0, 8, ?_⟩
  change selbergGcd 3 0 ≠ selbergGcd 3 8
  decide

def family : Registration arena (type_of% @compact_factorial_gcd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨compact_factorial_gcd, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected role, ?_, rfl, rejected_law role⟩
      intro i hi
      funext r s
      simp [actual, rejected, realize, hi]
    · intro e
      exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@compact_factorial_gcd) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FactorialRatio.CompactFactorialGcd.compact_factorial_gcd.__information_unit
  realizationName := `Reg.D5.S3.Arith.FactorialRatio.CompactFactorialGcd.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r s => selbergGcd r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FactorialRatio.CompactFactorialGcd
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "body", "fn", "arg", "arg"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "body", "arg", "fn", "arg"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FactorialRatio.CompactFactorialGcd
