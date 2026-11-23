import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.FourthRootMomentRegion

/-! Source readouts of the attainable upper endpoints. -/

namespace Reg.D5.S3.Fourier.Concentration.FourthRootMomentRegion

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.FourthRootMomentRegion
open _root_.Reg.Support

noncomputable section

abbrev regionSignature :=
  SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def regionActual : Realization regionSignature :=
  realize regionSignature (fun _ _ x => (1 + x) / 2) (fun e => nomatch e)

def regionRejected : Realization regionSignature :=
  realize regionSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev regionArena : Arena where
  signature := regionSignature
  Law V := ∀ (u v : ℝ),
    let cap := V.readout () () v
    (∃ w : ZMod 4 → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
      ‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 4)‖ ^ 2 = u ∧
      ‖ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod 4)‖ ^ 2 = v) ↔
        0 ≤ v ∧ v ≤ 1 ∧ 0 ≤ u ∧ u ≤ cap

private theorem region_rejected : ¬ regionArena.Law regionRejected := by
  intro law
  have h := law (1 / 2) 0
  have hw := (dft_four_squared_region (1 / 2) 0).mpr (by norm_num)
  have hc := (h.mp hw).2.2.2
  change (1 / 2 : ℝ) ≤ 0 at hc
  norm_num at hc

private theorem region_dependence : ObservationalDependence regionSignature regionActual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change (1 + (0 : ℝ)) / 2 ≠ (1 + (1 : ℝ)) / 2
  norm_num

def regionEvidence : Registration regionArena (type_of% @dft_four_squared_region) where
  actual := regionActual
  bridge := Iff.rfl
  variation := ⟨@dft_four_squared_region, regionRejected, region_rejected⟩
  sensitivity :=
    SingleDependentReadout.sensitivity regionArena.Law regionActual regionRejected region_rejected
  dependence := region_dependence

def regionRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@dft_four_squared_region) (Realization regionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FourthRootMomentRegion.regionUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FourthRootMomentRegion.regionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨regionArena⟩
  objectArena := .source ⟨regionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source regionArena ⟨regionEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize regionSignature (fun _ _ x => (1 + x) / 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FourthRootMomentRegion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms regionRegistration

abbrev maximumSignature :=
  SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def maximumActual : Realization maximumSignature :=
  realize maximumSignature (fun _ _ x => (1 / 2 : ℝ) ^ x) (fun e => nomatch e)

def maximumRejected : Realization maximumSignature :=
  realize maximumSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev maximumArena : Arena where
  signature := maximumSignature
  Law V := ∀ (p : ℕ) (_ : 2 ≤ p),
    let cap := V.readout () () p
    IsGreatest
      {A : ℝ | ∃ w : ZMod 4 → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
        (‖ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod 4)‖ ^ 2) ^ p = 0 ∧
        (‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 4)‖ ^ 2) ^ p = A}
      cap ∧
    IsGreatest
      {A : ℝ | 0 ≤ A ∧ ∃ w : ZMod 4 → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
        w 1 = w 3 ∧ ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod 4) = 0 ∧
        ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 4) = (A : ℂ)}
      (1 / 2 : ℝ) ∧ cap < 1 / 2

private theorem maximum_rejected : ¬ maximumArena.Law maximumRejected := by
  intro law
  have h := (law 2 (by decide)).1
  have hw := (four_first_moment_maxima 2 (by decide)).1
  have hf := le_antisymm (h.2 hw.1) (hw.2 h.1)
  change (1 / 2 : ℝ) ^ 2 = 0 at hf
  norm_num at hf

private theorem maximum_dependence : ObservationalDependence maximumSignature maximumActual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change (1 / 2 : ℝ) ^ (0 : ℕ) ≠ (1 / 2 : ℝ) ^ (1 : ℕ)
  norm_num

def maximumEvidence : Registration maximumArena (type_of% @four_first_moment_maxima) where
  actual := maximumActual
  bridge := Iff.rfl
  variation := ⟨@four_first_moment_maxima, maximumRejected, maximum_rejected⟩
  sensitivity :=
    SingleDependentReadout.sensitivity maximumArena.Law maximumActual maximumRejected
      maximum_rejected
  dependence := maximum_dependence

def maximumRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@four_first_moment_maxima) (Realization maximumSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.FourthRootMomentRegion.maximumUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.FourthRootMomentRegion.maximumEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨maximumArena⟩
  objectArena := .source ⟨maximumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source maximumArena ⟨maximumEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize maximumSignature (fun _ _ x => (1 / 2 : ℝ) ^ x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.FourthRootMomentRegion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms maximumRegistration

end

end Reg.D5.S3.Fourier.Concentration.FourthRootMomentRegion
