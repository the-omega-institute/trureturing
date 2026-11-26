import D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The complete source laws for the canonical curvature Toeplitz readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward
open _root_.D5.S3.Weil.Probability.CanonicalLiCurvatureZeroFree
open _root_.D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open _root_.D5.S3.Zeros.CompletedZeta
open LeanInformationAudit
open scoped ComplexOrder

private abbrev HalfFree := ∀ s : ℂ, (1 : ℝ) / 2 < s.re → xiReading s ≠ 0

abbrev signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℤ → ℂ)
    (fun N => Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

def actual : Realization signature :=
  realize signature (fun _ N c => toeplitzMatrix c N) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, fun _ => 0, fun _ => 1, ?_⟩
  intro h
  exact zero_ne_one (congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => A 0 0) h)

private theorem negative_not_posSemidef (N : ℕ) :
    ¬ (toeplitzMatrix (fun _ => (-1 : ℂ)) N).PosSemidef := by
  intro h
  have hdiag : 0 ≤ (-1 : ℂ) := h.diag_nonneg (i := 0)
  have hre : (0 : ℝ) ≤ -1 := by simpa using (Complex.nonneg_iff.mp hdiag).1
  linarith

namespace Forward

abbrev arena : Arena where
  signature := signature
  Law R := ∀ N : ℕ, N = 0 ∨ HalfFree →
    (R.readout () N canonicalLiCurvature).PosSemidef

def rejected : Realization signature :=
  realize signature (fun _ N _ => toeplitzMatrix (fun _ => -1) N) (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  exact negative_not_posSemidef 0 (h 0 (.inl rfl))

def family : Registration arena (type_of% @canonical_curvature_forward_posSemidef) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@canonical_curvature_forward_posSemidef, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@canonical_curvature_forward_posSemidef) (Realization signature) ℕ Unit where
  unitName := `D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward.canonical_curvature_forward_posSemidef.__information_unit
  realizationName := `Reg.D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward.Forward.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N c => toeplitzMatrix c N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Forward

namespace Criterion

abbrev arena : Arena where
  signature := signature
  Law R := RiemannHypothesis ↔ ∀ N : ℕ, (R.readout () N canonicalLiCurvature).PosSemidef

def rejected : Realization signature := by
  classical
  exact realize signature (fun _ N _ =>
    if RiemannHypothesis then toeplitzMatrix (fun _ => -1) N else 0) (fun e => nomatch e)

private theorem rejectedLaw : ¬ arena.Law rejected := by
  classical
  intro h
  by_cases hRH : RiemannHypothesis
  · have hzero := h.mp hRH 0
    exact negative_not_posSemidef 0 (by simpa [rejected, realize, hRH] using hzero)
  · apply hRH (h.mpr (fun N => ?_))
    simp [rejected, realize, hRH, Matrix.PosSemidef.zero]

def family : Registration arena (type_of% @rh_iff_canonical_curvature_posSemidef) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rh_iff_canonical_curvature_posSemidef, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rh_iff_canonical_curvature_posSemidef) (Realization signature) ℕ Unit where
  unitName := `D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward.rh_iff_canonical_curvature_posSemidef.__information_unit
  realizationName := `Reg.D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward.Criterion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N c => toeplitzMatrix c N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Criterion

end Reg.D5.S3.Weil.Probability.ActualCanonicalLiCurvatureForward
