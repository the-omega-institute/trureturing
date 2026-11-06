import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Congruence.WuA227244C1Equality
import Reg.Support.DependentFamily

set_option maxHeartbeats 200000
namespace Reg.D5.S3.Arith.Congruence.WuA227244C1Equality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

private def observed (n : ℕ) : ℤ :=
  ((2 : ℤ) ^ (2 ^ (20*n+16)) + 1) * 2 ^ (2 ^ (2 ^ (20*n+16))) - 1

def actual : Realization signature := realize signature (fun _ _ n => observed n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, Nat.Prime 101 ∧ (101 : ℤ) ∣ R.readout () () n ∧
    ∀ q : ℕ, Nat.Prime q → (q : ℤ) ∣ observed n → 101 ≤ q

abbrev sourceScope := type_of% (@_root_.D5.S3.Arith.Congruence.WuA227244C1Equality.result)
private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have hh := (h 0).2.1
  change (101 : ℤ) ∣ 1 at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change observed 0 ≠ observed 1
  dsimp [observed]
  apply ne_of_lt
  gcongr <;> norm_num

def family : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp _root_.D5.S3.Arith.Congruence.WuA227244C1Equality.result, rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim j i))
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@_root_.D5.S3.Arith.Congruence.WuA227244C1Equality.result) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Congruence.WuA227244C1Equality.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.Congruence.WuA227244C1Equality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => observed n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ : Type)
  sourceSelection := some {
    owner := `D5.S3.Arith.Congruence.WuA227244C1Equality
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "arg", "fn", "arg", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Congruence.WuA227244C1Equality
