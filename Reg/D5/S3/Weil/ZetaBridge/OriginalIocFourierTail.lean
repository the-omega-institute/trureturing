/- Faithful escape registration attempt. Not claimed declared_validated.
The selected readout is the complete original basis transform, with physical
frequency substitution retained. All four original binders remain in Law. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.OriginalIocFourierTail
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.OriginalIocFourier
open LeanInformationAudit
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Weil.ZetaBridge.OriginalIocFourierTail

abbrev signature : Signature where
  Params := ℝ × ℤ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s ↦ basisPaperFT p.1 p.2 (2 * Real.pi * s / p.1))
    (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {L : ℝ} (_hL : 0 < L) (n : ℤ) (s : ℝ),
    R.readout () (L, n) s = phase n * (Real.sqrt L : ℂ) *
      (Real.sinc (Real.pi * (s + (n : ℝ))) : ℂ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h (L := 1) (by norm_num) 0 0
  norm_num [rejected, realize, phase] at hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨((1 : ℝ), (0 : ℤ)), (0 : ℝ), (1 : ℝ), ?_⟩
  change basisPaperFT 1 0 (2 * Real.pi * 0 / 1) ≠
    basisPaperFT 1 0 (2 * Real.pi * 1 / 1)
  rw [scaled_basis_sinc (by norm_num : (0 : ℝ) < 1),
    scaled_basis_sinc (by norm_num : (0 : ℝ) < 1)]
  norm_num [phase, Real.sinc_of_ne_zero Real.pi_ne_zero]

def family : Registration arena (type_of% (@scaled_basis_sinc)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@scaled_basis_sinc, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@scaled_basis_sinc) (type_of% actual) Type Unit where
  unitName := `D5.S3.Weil.ZetaBridge.OriginalIocFourier.scaled_basis_sinc.audit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.OriginalIocFourierTail.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p s ↦ basisPaperFT p.1 p.2 (2 * Real.pi * s / p.1)) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.OriginalIocFourierTail
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/-- The original function and length are unrestricted parameters, and the real
frequency is the state. Law retains the actual MemLp and low-mode hypotheses. -/
abbrev physicalSignature : Signature where
  Params := ℝ × (ℝ → ℂ)
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def physicalActual : Realization physicalSignature :=
  realize physicalSignature
    (fun _ p t ↦ ‖Zeta23.paperFT (iocZeroExtend p.1 p.2) t‖ ^ 2)
    (fun e ↦ nomatch e)

def physicalRejected : Realization physicalSignature :=
  realize physicalSignature (fun _ _ _ ↦ 1) (fun e ↦ nomatch e)

def physicalArena : Arena where
  signature := physicalSignature
  Law R := ∀ {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (_hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (interval L)))
    {N : ℕ} (_hN : 0 < N)
    (_hlow : ∀ n : ℤ, |n| ≤ (N : ℤ) → signedCoeff L hL f n = 0),
    IntervalIntegrable (R.readout () (L, f)) MeasureTheory.volume
      (-(Real.pi * (N : ℝ) / (2 * L))) (Real.pi * (N : ℝ) / (2 * L)) ∧
    (1 / (2 * Real.pi)) *
      (∫ t in (-(Real.pi * (N : ℝ) / (2 * L)))..(Real.pi * (N : ℝ) / (2 * L)),
        R.readout () (L, f) t) ≤
      (4 / (3 * Real.pi ^ 2)) * (∫ x in (-L / 2)..(L / 2), ‖f x‖ ^ 2)

private theorem physical_rejected_law : ¬ physicalArena.Law physicalRejected := by
  intro h
  have hzero : MeasureTheory.MemLp (fun _ : ℝ ↦ (0 : ℂ)) 2
      (MeasureTheory.volume.restrict (interval 1)) := by simp
  have hlow : ∀ n : ℤ, |n| ≤ (1 : ℤ) →
      signedCoeff 1 (by norm_num) (fun _ ↦ (0 : ℂ)) n = 0 := by
    intro n _
    simp [signedCoeff, fourierCoeffOn, fourierCoeff, AddCircle.liftIoc]
  have hz := (h (L := 1) (by norm_num) hzero (N := 1) (by decide) hlow).2
  have heq : (1 / (2 * Real.pi)) * (Real.pi / 2 - -(Real.pi / 2)) = (1 / 2 : ℝ) := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hz' : (1 / (2 * Real.pi)) * (Real.pi / 2 - -(Real.pi / 2)) ≤ (0 : ℝ) := by
    simpa [physicalRejected, realize] using hz
  rw [heq] at hz'
  norm_num at hz'

private theorem physical_dependence : ObservationalDependence physicalSignature physicalActual := by
  intro i
  cases i
  refine ⟨((1 : ℝ), fun _ : ℝ ↦ (1 : ℂ)), (0 : ℝ), (2 * Real.pi : ℝ), ?_⟩
  have hext : iocZeroExtend 1 (fun _ : ℝ ↦ (1 : ℂ)) = signedBasis 1 0 := by
    funext x
    simp [iocZeroExtend, signedBasis, phase, frequency]
  change ‖Zeta23.paperFT (iocZeroExtend 1 (fun _ ↦ 1)) ((0 : ℝ) : ℂ)‖ ^ 2 ≠
    ‖Zeta23.paperFT (iocZeroExtend 1 (fun _ ↦ 1)) ((2 * Real.pi : ℝ) : ℂ)‖ ^ 2
  rw [hext]
  change ‖basisPaperFT 1 0 0‖ ^ 2 ≠ ‖basisPaperFT 1 0 (2 * Real.pi)‖ ^ 2
  have h0 := scaled_basis_sinc (by norm_num : (0 : ℝ) < 1) 0 0
  have h1 := scaled_basis_sinc (by norm_num : (0 : ℝ) < 1) 0 1
  norm_num [phase, Real.sinc_of_ne_zero Real.pi_ne_zero] at h0 h1
  rw [h0, h1]
  norm_num

def physicalFamily : Registration physicalArena (type_of% (@original_low_frequency_mass)) where
  actual := physicalActual
  bridge := Iff.rfl
  variation := ⟨@original_low_frequency_mass, physicalRejected, physical_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨physicalRejected, ?_, rfl, physical_rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro e
      exact nomatch e
  dependence := physical_dependence

/- The typed family is the actual four-slot mathematical attempt. The source
selector for the two occurrences under IntervalIntegrable and intervalIntegral
must be extracted from the current compiler statement before constructing a
Contract.Registration. No guessed path is presented as accepted evidence. -/

end Reg.D5.S3.Weil.ZetaBridge.OriginalIocFourierTail
