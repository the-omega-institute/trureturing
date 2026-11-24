import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.WeightedOccupationDiagonal

/-! Dependence of the coefficient envelope on the scaled coordinate. -/

namespace Reg.D5.S3.Fourier.Concentration.WeightedOccupationDiagonal

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (diagonal monomialWeight)
open _root_.D5.S3.Fourier.Concentration.WeightedOccupationDiagonal
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => diagonalEnvelope x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J] (w : J → ℝ) (p : ℕ)
      {s : ℝ}, 0 ≤ s →
    let envelope := fun x => V.readout () () x
    s ^ p * diagonal w p ≤ (p.factorial : ℝ) ^ 2 * ∏ j, envelope (s * w j ^ 2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  classical
  have h := law (J := ULift.{u} (Fin 1)) (fun _ => 0) 0 (s := 0) (le_refl 0)
  norm_num [rejected, realize, diagonal, monomialWeight, Nat.multinomial] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 2, ?_⟩
  change diagonalEnvelope 0 ≠ diagonalEnvelope 2
  have h : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  unfold diagonalEnvelope
  norm_num
  linarith

def evidence : Registration arena.{u} (type_of% @scaled_diagonal_le_product.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scaled_diagonal_le_product.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@scaled_diagonal_le_product.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.WeightedOccupationDiagonal.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.WeightedOccupationDiagonal.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => diagonalEnvelope x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.WeightedOccupationDiagonal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.WeightedOccupationDiagonal
