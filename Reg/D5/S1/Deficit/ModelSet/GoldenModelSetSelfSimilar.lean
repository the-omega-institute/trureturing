import D5.S1.Deficit.ModelSet.GoldenModelSetSelfSimilar
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! Registration of the raw-digit shift evaluation identity. -/

namespace Reg.D5.S1.Deficit.ModelSet.GoldenModelSetSelfSimilar

open _root_.D5.S0.Carrier
open _root_.D5.S1.Digit
open _root_.D5.S1.Digit.Admissibility.LeastDigitDecomposition
open _root_.D5.S1.Deficit
open _root_.D5.S1.Deficit.GoldenModelSetSelfSimilar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := RawDigits
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := GoldenInt
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ offset r => betaDigits (shiftDigits offset r))
    (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (offset : ℕ) (r : RawDigits),
    obs.readout () offset r = phi ^ offset * betaDigits r

private theorem single_beta_nonzero : betaDigits (Finsupp.single 0 1) ≠ 0 := by
  intro h
  have hb := congrArg GoldenInt.b h
  rw [DoubleFaceLength.betaDigits_b] at hb
  norm_num [rawValue_single, _root_.D5.S0.Conventions.wValue] at hb

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 (Finsupp.single 0 1)
  change 0 = phi ^ 0 * betaDigits (Finsupp.single 0 1) at hh
  apply single_beta_nonzero
  simpa using hh.symm

def evidence : Registration arena
    (∀ (offset : ℕ) (r : RawDigits),
      betaDigits (shiftDigits offset r) = phi ^ offset * betaDigits r) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨beta_digits_shift, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0, 0, Finsupp.single 0 1, ?_⟩
    change betaDigits (shiftDigits 0 0) ≠ betaDigits (shiftDigits 0 (Finsupp.single 0 1))
    rw [beta_digits_shift, beta_digits_shift]
    simpa [betaDigits] using single_beta_nonzero.symm

noncomputable def beta_digits_shift_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S1.Deficit.GoldenModelSetSelfSimilar.beta_digits_shift)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S1.Deficit.ModelSet.GoldenModelSetSelfSimilar.beta_digits_shift_unit
  realizationName := `Reg.D5.S1.Deficit.ModelSet.GoldenModelSetSelfSimilar.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ offset r => betaDigits (shiftDigits offset r)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Deficit.ModelSet.GoldenModelSetSelfSimilar
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S1.Deficit.ModelSet.GoldenModelSetSelfSimilar
