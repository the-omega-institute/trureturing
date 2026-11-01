import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
import Reg.Support.DependentFamily

/-! The observation is the original finite prime sum, with the entire
uniform real-cutoff telescope preserved in the source law. -/

noncomputable section
namespace Reg.D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail

open Finset LeanInformationAudit
open _root_.D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ y z =>
    ∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (epsilon : ℝ), 0 < epsilon →
    ∃ C : ℝ, 1 < C ∧ ∃ Y : ℝ, 1 < Y ∧
      ∀ y z : ℝ, Y ≤ y → C * y ≤ z →
        |y * Real.log y * R.readout () y z - 1| < epsilon

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C, _hC, Y, _hY, hbad⟩ := h (1 / 2) (by norm_num)
  have hbad' := hbad Y (C * Y) le_rfl le_rfl
  norm_num [rejected, realize] at hbad'

def family : Registration arena (type_of% @prime_square_tail_uniform) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_square_tail_uniform, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 1, 2, ?_⟩
    norm_num [actual, realize, sum_Ioc_succ_top, Finset.sum_filter]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prime_square_tail_uniform) (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail.prime_square_tail_uniform.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ y z =>
    ∑ p ∈ (Ioc ⌊y⌋₊ ⌊z⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "body", "arg",
        "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
