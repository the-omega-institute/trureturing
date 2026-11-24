import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.SparseCyclicMajorants

/-! Readouts of the selected mode count in the sparse cyclic majorant estimates. -/

namespace Reg.D5.S3.Fourier.Concentration.SparseCyclicMajorants

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.FinitePoisson
open _root_.D5.S3.Fourier.Concentration.SparseCyclicMajorants
open _root_.Reg.Support
open Finset

noncomputable section

abbrev modeSignature :=
  SingleDependentReadout.signature ℕ (fun q => Finset (ZMod q)) (fun _ => ℝ)

def actual : Realization modeSignature :=
  realize modeSignature (fun _ _ S => S.card) (fun e => nomatch e)

def rejected : Realization modeSignature :=
  realize modeSignature (fun _ _ S => (S.card : ℝ) - 1) (fun e => nomatch e)

abbrev gapArena : Arena where
  signature := modeSignature
  Law v := ∀ (q : ℕ) [NeZero q]
    (K : ZMod q → ℝ) (_ : ∀ x, 0 ≤ K x) (S R : Finset (ZMod q))
    (_ : ∀ k ∉ S, ZMod.dft (fun x => (K x : ℂ)) k = 0)
    (_ : ∀ x ∈ R, 1 ≤ K x),
    let modeCount := v.readout () q S
    (∑ k ∈ S, ∑ x ∈ R, (1 - (ZMod.stdAddChar (-(x * k))).re)) ≤
      modeCount * (∑ x, K x) - (q : ℝ) * K 0

abbrev equalityArena : Arena where
  signature := modeSignature
  Law v := ∀ (q : ℕ) [NeZero q]
    (K : ZMod q → ℝ) (_ : ∀ x, 0 ≤ K x) (S : Finset (ZMod q))
    (_ : ∀ k ∉ S, ZMod.dft (fun x => (K x : ℂ)) k = 0)
    (_ : 0 < K 0),
    let modeCount := v.readout () q S
    modeCount * (∑ x, K x) = (q : ℝ) * K 0 ↔
      ∃ H : AddSubgroup (ZMod q),
        (∀ x, K x = @ite ℝ (x ∈ H) (Classical.propDecidable _) (K 0) 0) ∧
          ∀ k, k ∈ S ↔ k ∈ annihilator H

private theorem rejected_count : rejected.readout () 1 (univ : Finset (ZMod 1)) = 0 := by
  change ((univ : Finset (ZMod 1)).card : ℝ) - 1 = 0
  rw [card_univ, ZMod.card]
  norm_num

private theorem gap_rejected : ¬ gapArena.Law rejected := by
  intro law
  have h := law 1 (fun _ => 1) (fun _ => zero_le_one) univ ∅
    (fun k hk => (hk (mem_univ k)).elim) (by simp)
  dsimp only at h
  rw [rejected_count] at h
  norm_num at h

private theorem equality_rejected : ¬ equalityArena.Law rejected := by
  classical
  intro law
  have h := law 1 (fun _ => 1) (fun _ => zero_le_one) univ
    (fun k hk => (hk (mem_univ k)).elim) zero_lt_one
  dsimp only at h
  rw [rejected_count] at h
  have hr : ∃ H : AddSubgroup (ZMod 1),
      (∀ x, (1 : ℝ) = if x ∈ H then 1 else 0) ∧
        ∀ k, k ∈ (univ : Finset (ZMod 1)) ↔ k ∈ annihilator H := by
    refine ⟨⊤, by simp, fun k => ⟨fun _ => ?_, fun _ => mem_univ k⟩⟩
    intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  have heq := h.mpr hr
  norm_num at heq

private theorem mode_dependence : ObservationalDependence modeSignature actual := by
  intro i
  cases i
  refine ⟨1, ∅, {0}, ?_⟩
  change ((∅ : Finset (ZMod 1)).card : ℝ) ≠ ({0} : Finset (ZMod 1)).card
  norm_num

def gapEvidence : Registration gapArena (type_of% @sparse_dft_majorant_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sparse_dft_majorant_gap, rejected, gap_rejected⟩
  sensitivity := SingleDependentReadout.sensitivity gapArena.Law actual rejected gap_rejected
  dependence := mode_dependence

def equalityEvidence : Registration equalityArena (type_of% @sparse_dft_floor_eq_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sparse_dft_floor_eq_iff, rejected, equality_rejected⟩
  sensitivity :=
    SingleDependentReadout.sensitivity equalityArena.Law actual rejected equality_rejected
  dependence := mode_dependence

def gapRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sparse_dft_majorant_gap) (Realization modeSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.SparseCyclicMajorants.gapUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.SparseCyclicMajorants.gapEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨gapArena⟩
  objectArena := .source ⟨gapArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gapArena ⟨gapEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize modeSignature (fun _ _ S => S.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.SparseCyclicMajorants
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def equalityRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sparse_dft_floor_eq_iff) (Realization modeSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.SparseCyclicMajorants.equalityUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.SparseCyclicMajorants.equalityEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨equalityArena⟩
  objectArena := .source ⟨equalityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source equalityArena ⟨equalityEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize modeSignature (fun _ _ S => S.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.SparseCyclicMajorants
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms gapRegistration
#print axioms equalityRegistration

end

end Reg.D5.S3.Fourier.Concentration.SparseCyclicMajorants
