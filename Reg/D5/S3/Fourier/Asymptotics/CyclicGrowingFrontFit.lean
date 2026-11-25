import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit

/-! Dependence of the moment estimates and reference solution on the sampled feature matrix. -/

namespace Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit

open Filter Matrix
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open _root_.D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℕ × ℝ)
  (fun _ => Matrix (Fin 2) (Fin 2) ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ state => frontGram state.1 state.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ state => fun _ _ => state.2) (fun e => nomatch e)

private theorem observed_values_differ :
    actual.readout () () (0, 0) ≠ actual.readout () () (1, 0) := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  change frontGram 0 0 0 0 = frontGram 1 0 0 0 at he
  norm_num [frontGram, frontFeatures, card_latticeInterval] at he

namespace Perturbation

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n → ∀ (u : ℝ) (i j : Fin 2),
    let readout := R.readout () ()
    |readout (n, u) i j - readout (n, 0) i j| ≤ 2 * u ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide) (1 / 4) 0 0
  norm_num [rejected, realize] at hh

def evidence : Registration arena (type_of% @frontGram_sub_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@frontGram_sub_le, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨(), (0, 0), (1, 0), observed_values_differ⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@frontGram_sub_le) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit.Perturbation.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit.Perturbation.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
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

end Perturbation

namespace Limit

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {u : ℕ → ℝ}, Tendsto u atTop (𝓝 0) →
    let readout := R.readout () ()
    Tendsto (fun n : ℕ => readout (n, u n)) atTop
      (𝓝 !![(2 : ℝ), 2/3; 2/3, 2/5])

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (u := fun _ => 0) tendsto_const_nhds
  have hentry := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hh (0 : Fin 2)) (0 : Fin 2)
  change Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 2) at hentry
  have he := tendsto_nhds_unique tendsto_const_nhds hentry
  norm_num at he

def evidence : Registration arena (type_of% @frontGram_tendsto) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@frontGram_tendsto, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨(), (0, 0), (1, 0), observed_values_differ⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@frontGram_tendsto) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit.Limit.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit.Limit.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Limit

namespace Reference

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 0 < n →
    let readout := R.readout () ()
    let m := (n : ℝ) * (n + 1) / 5
    let t := (n : ℝ) * (n + 1) - 1 / 2
    let Z := normalizer n t
    readout (n, 0) *ᵥ ![n * t / Z, -(n : ℝ) ^ 3 / Z] = ![1, m / (n : ℝ) ^ 2]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 (by decide)
  have he := congrArg (fun v : Fin 2 → ℝ => v 0) hh
  norm_num [rejected, realize, mulVec, dotProduct] at he

def evidence : Registration arena (type_of% @frontGram_reference_fit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@frontGram_reference_fit, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    exact ⟨(), (0, 0), (1, 0), observed_values_differ⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@frontGram_reference_fit) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit.Reference.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit.Reference.evidence
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
    owner := `D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reference

end

end Reg.D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
