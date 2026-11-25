import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.DisjointSupportOccupationMass

/-! Dependence of the coefficient envelope on the scaled coordinate. -/

namespace Reg.D5.S3.Fourier.Concentration.DisjointSupportOccupationMass

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight)
open _root_.D5.S3.Fourier.Concentration.DisjointSupportOccupationMass
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 2 * Real.exp x - 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J] (w : J → ℝ) (_hw : ∀ j, 0 ≤ w j) (d : ℕ)
      {s : ℝ}, 0 ≤ s →
    let envelope := fun x => V.readout () () x
    let B := (d.factorial : ℝ) ^ 2 * ∏ j, envelope (s * w j)
    s ^ (2 * d) * disjointMass w d ≤ B ∧
      B ≤ (d.factorial : ℝ) ^ 2 *
        Real.exp (2 * s * (∑ j, w j) - ∑ j, (1 - Real.exp (-(s * w j))) ^ 2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  classical
  have h := law (J := ULift.{u} (Fin 1)) (fun _ => 0) (fun _ => le_rfl) 0 (s := 0) (le_refl 0)
  have hleft := h.1
  have hnonneg : 0 ≤ disjointMass (fun _ : ULift.{u} (Fin 1) => (0 : ℝ)) 0 := by
    have hweight (a : ULift.{u} (Fin 1) → ℕ) :
        0 ≤ monomialWeight (fun _ => 0) a := by
      unfold monomialWeight
      positivity
    exact sum_nonneg fun p _ => mul_nonneg (hweight p.1) (hweight p.2)
  have hle : disjointMass (fun _ : ULift.{u} (Fin 1) => (0 : ℝ)) 0 ≤ -1 := by
    simpa [rejected, realize] using hleft
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change 2 * Real.exp 0 - 1 ≠ 2 * Real.exp 1 - 1
  have h : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  norm_num
  linarith

def evidence : Registration arena.{u} (type_of% @scaled_disjoint_mass.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scaled_disjoint_mass.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@scaled_disjoint_mass.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.DisjointSupportOccupationMass.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.DisjointSupportOccupationMass.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 2 * Real.exp x - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.DisjointSupportOccupationMass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.DisjointSupportOccupationMass
