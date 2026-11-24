import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.FirstCosineClipping

/-! Dependence of the clipping estimate on the squared readout. -/

namespace Reg.D5.S3.Fourier.Concentration.FirstCosineClipping

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FirstCosineClipping
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
  Law V := ∀ {q : ℕ} [NeZero q] (_ : 5 ≤ q),
    let c := fun k : ZMod q => mode k 1
    let d := fun k : ZMod q => mode k 2
    let s := fun k => c k + d k
    let square := V.readout () ()
    ∃ m : ℝ, (∃ k, m = s k) ∧ (∀ k, m ≤ s k) ∧
      4 / 9 < -1 / (2 * m) ∧
      -1 / (2 * m) ≤ 4 / 9 + 16 * square Real.pi / (9 * square (q : ℝ)) ∧
      ∀ a : ℝ, 0 ≤ a →
        let v := fun k => (1 + 2 * a * s k) / (q : ℝ)
        let lower := (1 + 4 * square a) / (q : ℝ)
        let feasible := fun w : ZMod q → ℝ =>
          (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
            a ≤ (∑ k, w k * c k) ∧ a ≤ (∑ k, w k * d k)
        (∑ k, v k) = 1 ∧ (∑ k, v k * c k) = a ∧ (∑ k, v k * d k) = a ∧
          (∀ w : ZMod q → ℝ, (∑ k, w k) = 1 →
            (∑ k, square (w k)) - lower =
              (∑ k, square (w k - v k)) +
                (4 * a / (q : ℝ)) * ((∑ k, w k * s k) - 2 * a)) ∧
          (∀ w, feasible w →
            lower + (∑ k, square (max 0 (-v k))) ≤ (∑ k, square (w k)) ∧
              ((∑ k, square (w k)) = lower ↔ w = v)) ∧
          ((∃ w, feasible w ∧ (∑ k, square (w k)) = lower) ↔ a ≤ -1 / (2 * m))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨m, _, _, hlo, hhi, _⟩ := law (q := 5) (by decide)
  norm_num [rejected, realize] at hhi
  linarith

def evidence : Registration arena (type_of% @first_cosine_clipping) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@first_cosine_clipping, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ^ 2 ≠ (1 : ℝ) ^ 2
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@first_cosine_clipping) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FirstCosineClipping.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FirstCosineClipping.evidence
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
    owner := `D5.S3.Fourier.Concentration.FirstCosineClipping
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

end Reg.D5.S3.Fourier.Concentration.FirstCosineClipping
