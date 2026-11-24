import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.SixResidueMomentOptimum

/-! Dependence of the six-residue optimum on the squared-mass objective. -/

namespace Reg.D5.S3.Fourier.Concentration.SixResidueMomentOptimum

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.SixResidueMomentOptimum
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (a : ℝ) (_ : 0 ≤ a) (_ : a ≤ 1),
    let c := fun k : Fin 6 => Real.cos (Real.pi * (k.val : ℝ) / 3)
    let d := fun k : Fin 6 => Real.cos (2 * Real.pi * (k.val : ℝ) / 3)
    let v : Fin 6 → ℝ := if a ≤ 1 / 2 then
      ![(1 + 4 * a) / 6, 1 / 6, (1 - 2 * a) / 6, 1 / 6, (1 - 2 * a) / 6, 1 / 6]
      else ![a, (1 - a) / 3, 0, (1 - a) / 3, 0, (1 - a) / 3]
    let square := V.readout () ()
    (∀ k, 0 ≤ v k) ∧ (∑ k, v k) = 1 ∧ (∑ k, v k * c k) = a ∧ (∑ k, v k * d k) = a ∧
      (∑ k, square (v k)) = (if a ≤ 1 / 2 then (1 + 4 * a ^ 2) / 6
        else a ^ 2 + (1 - a) ^ 2 / 3) ∧
      (∀ w : Fin 6 → ℝ, (∀ k, 0 ≤ w k) → (∑ k, w k) = 1 →
        2 * a ≤ (∑ k, w k * c k) + ∑ k, w k * d k →
        (∑ k, square (w k - v k)) ≤ (∑ k, square (w k)) - ∑ k, square (v k)) ∧
      (0 < a → a < 1 → ∀ t : ℝ, 0 ≤ t →
        let u := fun k : Fin 6 => max 0 (1 - t * (1 - c k))
        let p := fun k => u k / ∑ j, u j
        (∑ k, p k * c k) = a → (∑ k, p k * d k) < a)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law 0 (by norm_num) (by norm_num)).2.2.2.2.1
  norm_num [rejected, realize] at h

def evidence : Registration arena (type_of% @six_two_mode_optimum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@six_two_mode_optimum, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ^ 2 ≠ (1 : ℝ) ^ 2
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@six_two_mode_optimum) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.SixResidueMomentOptimum.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.SixResidueMomentOptimum.evidence
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
    owner := `D5.S3.Fourier.Concentration.SixResidueMomentOptimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.SixResidueMomentOptimum
