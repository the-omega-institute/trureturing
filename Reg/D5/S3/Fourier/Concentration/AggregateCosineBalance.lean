import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.AggregateCosineBalance

/-! Dependence of the signed cosine sum on the squared aggregate readout. -/

namespace Reg.D5.S3.Fourier.Concentration.AggregateCosineBalance

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.AggregateCosineBalance
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (q : ℕ) [NeZero q] (_ : 7 ≤ q),
    let c := fun k : ZMod q => Real.cos (2 * Real.pi * (k.val : ℝ) / q)
    let d := fun k : ZMod q => Real.cos (4 * Real.pi * (k.val : ℝ) / q)
    let square := V.readout () ()
    (∑ k, (c k - d k) * square (c k + d k)) = (q : ℝ) / 4 ∧
      0 < ∑ k, (c k - d k) * max 0 (c k + d k)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law 7 (by decide)).1
  norm_num [rejected, realize] at h

def evidence : Registration arena (type_of% @aggregate_cosine_imbalance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@aggregate_cosine_imbalance, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ^ 2 ≠ (1 : ℝ) ^ 2
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@aggregate_cosine_imbalance) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.AggregateCosineBalance.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.AggregateCosineBalance.evidence
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
    owner := `D5.S3.Fourier.Concentration.AggregateCosineBalance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.AggregateCosineBalance
