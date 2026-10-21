/- Four-slot source-family attempt for the actual arbitrary-L2 evaluation.
The complete original telescope and HasSum conclusion are retained. Current
compiler extraction and report acceptance are required; neither is claimed. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.OriginalIocFourierTail
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaBridge.OriginalIocFourier
open LeanInformationAudit MeasureTheory
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Weil.ZetaBridge.OriginalIocFourierEvaluation

abbrev signature : Signature where
  Params := ℝ × (ℝ → ℂ)
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t ↦ Zeta23.paperFT (iocZeroExtend p.1 p.2) t)
    (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {L : ℝ} (hL : 0 < L) {f : ℝ → ℂ}
    (_hf : MemLp f 2 (volume.restrict (interval L))) (t : ℝ),
    HasSum (fun n : ℤ ↦ signedCoeff L hL f n * basisPaperFT L n t)
      (R.readout () (L, f) t)

private theorem one_extension : iocZeroExtend 1 (fun _ : ℝ ↦ (1 : ℂ)) = signedBasis 1 0 := by
  funext x
  simp [iocZeroExtend, signedBasis, phase, frequency]

private theorem ft_one_zero :
    Zeta23.paperFT (iocZeroExtend 1 (fun _ : ℝ ↦ (1 : ℂ))) 0 = 1 := by
  rw [one_extension]
  change basisPaperFT 1 0 0 = 1
  simpa [phase] using scaled_basis_sinc (by norm_num : (0 : ℝ) < 1) 0 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : IsFiniteMeasure (volume.restrict (interval 1)) := by
    unfold interval
    infer_instance
  have hf : MemLp (fun _ : ℝ ↦ (1 : ℂ)) 2 (volume.restrict (interval 1)) := by
    exact memLp_const 1
  have hbad := h (L := 1) (by norm_num) hf 0
  have hgood := hasSum_signedCoeff_mul_basisPaperFT (by norm_num : (0 : ℝ) < 1) hf 0
  have heq := hgood.unique hbad
  rw [Complex.ofReal_zero, ft_one_zero] at heq
  norm_num [rejected, realize] at heq

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨((1 : ℝ), fun _ : ℝ ↦ (1 : ℂ)), (0 : ℝ), (2 * Real.pi : ℝ), ?_⟩
  change Zeta23.paperFT (iocZeroExtend 1 (fun _ ↦ 1)) ((0 : ℝ) : ℂ) ≠
    Zeta23.paperFT (iocZeroExtend 1 (fun _ ↦ 1)) ((2 * Real.pi : ℝ) : ℂ)
  rw [one_extension]
  change basisPaperFT 1 0 0 ≠ basisPaperFT 1 0 (2 * Real.pi)
  have h0 := scaled_basis_sinc (by norm_num : (0 : ℝ) < 1) 0 0
  have h1 := scaled_basis_sinc (by norm_num : (0 : ℝ) < 1) 0 1
  norm_num [phase, Real.sinc_of_ne_zero Real.pi_ne_zero] at h0 h1
  rw [h0, h1]
  norm_num

def family : Registration arena (type_of% (@hasSum_signedCoeff_mul_basisPaperFT)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasSum_signedCoeff_mul_basisPaperFT, rejected, rejected_law⟩
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
    (@hasSum_signedCoeff_mul_basisPaperFT) (type_of% actual) Type Unit where
  unitName := `D5.S3.Weil.ZetaBridge.OriginalIocFourier.hasSum_signedCoeff_mul_basisPaperFT.audit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.OriginalIocFourierEvaluation.family
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
    (fun _ p t ↦ Zeta23.paperFT (iocZeroExtend p.1 p.2) t) (fun e ↦ nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.OriginalIocFourierEvaluation
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaBridge.OriginalIocFourierEvaluation
