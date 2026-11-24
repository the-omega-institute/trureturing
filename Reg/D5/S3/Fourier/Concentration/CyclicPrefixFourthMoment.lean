import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment

/-! Dependence of the cyclic prefix fourth moment on the fourth power of the norm. -/

namespace Reg.D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CyclicFejerBand (prefixCharacter)
open _root_.D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖ ^ 4) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (q N : ℕ) [NeZero q] (_ : N ≤ q),
    let fourthPower := V.readout () ()
    let m := 2 * N - q - 1
    3 * (∑ k : ZMod q, fourthPower (prefixCharacter q N k)) =
      (q : ℝ) * ((N : ℝ) * (2 * (N : ℝ) ^ 2 + 1) +
        (m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 1 1 (by decide)
  norm_num [rejected, realize] at hz

def evidence : Registration arena (type_of% @sum_prefixCharacter_norm_four) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_prefixCharacter_norm_four, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change ‖(0 : ℂ)‖ ^ 4 ≠ ‖(1 : ℂ)‖ ^ 4
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@sum_prefixCharacter_norm_four) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CyclicPrefixFourthMoment
