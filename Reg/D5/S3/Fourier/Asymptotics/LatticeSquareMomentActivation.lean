import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

/-! Dependence of the exact activation statements on the lower square-moment bound. -/

namespace Reg.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => ((n : ℝ) ^ 2 - 1) / 5) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  norm_num [actual, realize]

namespace Interval

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n → ∀ m : ℝ,
    let lowerBound := fun n : ℕ => R.readout () () n
    (lowerBound n ≤ m ∧ m ≤ (n : ℝ) * (n + 2) / 5) ↔
      ∃! a : ℝ × ℝ × (ℤ → ℝ), Activation m n a.1 a.2.1 a.2.2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (exists_lattice_square_moment_minimizer_on_interval 1 (by decide) 0).mp (by
    norm_num)
  have hbad := ((law 1 (by decide) 0).mpr h).1
  change (1 : ℝ) ≤ 0 at hbad
  norm_num at hbad

def evidence :
    Registration arena (type_of% @exists_lattice_square_moment_minimizer_on_interval) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_lattice_square_moment_minimizer_on_interval, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@exists_lattice_square_moment_minimizer_on_interval) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation.Interval.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation.Interval.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Interval

namespace Global

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℝ,
    let lowerBound := fun n : ℕ => R.readout () () n
    0 ≤ m ↔ ∃! a : ℕ × ℝ × ℝ × (ℤ → ℝ), 0 < a.1 ∧
      (lowerBound a.1 ≤ m ∧ m < (a.1 : ℝ) * (a.1 + 2) / 5) ∧
      Activation m a.1 a.2.1 a.2.2.1 a.2.2.2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨⟨n, t, Z, w⟩, ⟨_, h, _⟩, _⟩ := (law 0).mp le_rfl
  have hbad : (1 : ℝ) ≤ 0 := h.1
  norm_num at hbad

def evidence : Registration arena (type_of% @exists_lattice_square_moment_minimizer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_lattice_square_moment_minimizer, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@exists_lattice_square_moment_minimizer) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation.Global.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation.Global.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Global

end

end Reg.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
