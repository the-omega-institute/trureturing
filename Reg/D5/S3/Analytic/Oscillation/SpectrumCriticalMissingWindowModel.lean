import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel
import Reg.Support.DependentFamily

/-! The observed weights in the infinite model law are strictly positive. -/

set_option autoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel

open _root_.D5.S3.Analytic.Oscillation.OrdinateCounting (Spectrum)
open _root_.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindow
  (HasLogSquaredMass HasSmallSquareTail)
open _root_.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel
  (exists_infinite_critical_model)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev weightSignature : Signature where
  Params := Σ S : Spectrum, S.index → ℝ
  State p := p.1.index
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def weightActual : Realization weightSignature :=
  realize weightSignature (fun _ p j => p.2 j) (fun e => nomatch e)

private def weightRejected : Realization weightSignature :=
  realize weightSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev weightArena : Arena where
  signature := weightSignature
  Law V := ∃ (S : Spectrum) (w : S.index → ℝ), Infinite S.index ∧
    (∀ j, 0 < V.readout () ⟨S, w⟩ j) ∧ LinearIndependent ℚ S.gamma ∧
    HasLogSquaredMass S w ∧ HasSmallSquareTail S w

private theorem weight_rejected : ¬ weightArena.Law weightRejected := by
  rintro ⟨S, _, hInf, hw, _⟩
  obtain ⟨j⟩ : Nonempty S.index := @Infinite.nonempty _ hInf
  exact (lt_irrefl 0) (hw j)

private abbrev twoOrdinates : Spectrum where
  index := Fin 2
  gamma := fun j => (j.val : ℝ) + 1
  mult := fun _ => 1
  gamma_pos _ := by positivity
  gamma_injective := by
    intro j k h
    apply Fin.ext
    exact_mod_cast (add_right_cancel h)
  mult_pos _ := Nat.one_pos
  finite_le _ := Set.toFinite _

private theorem weight_dependence : ObservationalDependence weightSignature weightActual := by
  rintro ⟨⟩
  refine ⟨⟨twoOrdinates, twoOrdinates.gamma⟩, (0 : Fin 2), 1, ?_⟩
  change ((0 : ℕ) : ℝ) + 1 ≠ ((1 : ℕ) : ℝ) + 1
  norm_num

def weightEvidence : Registration weightArena (type_of% @exists_infinite_critical_model) where
  actual := weightActual
  bridge := Iff.rfl
  variation := ⟨@exists_infinite_critical_model, weightRejected, weight_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨weightRejected, ?_, ?_, weight_rejected⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := weight_dependence

def weightAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_infinite_critical_model) (Realization weightSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel.weightUnit
  realizationName := `Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel.weightEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨weightArena⟩
  objectArena := .source ⟨weightArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source weightArena ⟨weightEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize weightSignature (fun _ p j => p.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms weightAudit

end Reg.D5.S3.Analytic.Oscillation.SpectrumCriticalMissingWindowModel
