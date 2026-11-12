import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.LocalDold.NormalizedKBonacci

/-! Faithful whole-family source reconstruction for the actual all-order parity block rank. -/

namespace Reg.D5.S3.Arith.LocalDold.NormalizedKBonacci
open LeanInformationAudit Function
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.LocalDold.NormalizedKBonacci
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ}, 2 ≤ k → ∀ n : ℕ,
    (2 ∣ R.readout () k n ↔ k+1 ∣ n)

def actual : Realization signature :=
  realize signature (fun _ k n => blockGcd k n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev sourceScope := type_of% (@block_even_iff)

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := @h 2 (by omega) 0
  norm_num [rejected,realize] at hc

def familyRegistration : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@block_even_iff), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2,0,1,?_⟩
    intro he
    change blockGcd 2 0 = blockGcd 2 1 at he
    have hd : 2 ∣ blockGcd 2 0 := (block_even_iff (by omega) 0).mpr (dvd_zero _)
    rw [he,block_even_iff (by omega)] at hd
    norm_num at hd

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@block_even_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.LocalDold.NormalizedKBonacci.block_even_iff.__information_unit
  realizationName := `Reg.D5.S3.Arith.LocalDold.NormalizedKBonacci.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ k n => blockGcd k n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.LocalDold.NormalizedKBonacci
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Arith.LocalDold.NormalizedKBonacci
