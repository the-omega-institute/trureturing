import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.OriginalHalfBinomialNome
import Reg.Support.SingleDependentReadout

/-! Typed observation families for the complete native continuation statements. -/

noncomputable section
open scoped Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped Topology

namespace Reg.D5.S3.Analytic.OriginalHalfBinomialNome
open _root_.D5.S3.Analytic.OriginalHalfBinomialPeriod (period)
open _root_.D5.S3.Analytic.OriginalHalfBinomialWronskian (tau)
open _root_.D5.S3.Analytic.OriginalHalfBinomialDiskCorrection
open _root_.D5.S3.Analytic.OriginalHalfBinomialContinuation
open _root_.D5.S3.Analytic.OriginalHalfBinomialNome

namespace DiskNome
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Unit) (fun _ => ℂ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ z => decide (z = 1 / 16)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law M :=
    DifferentiableOn ℂ Q0 disk ∧
    (∀ r ∈ disk, HasDerivAt Q0
      (Complex.exp (Complex.I * (Real.pi : ℂ) * H r) /
        (16 * (1 - r) * period r ^ 2)) r) ∧
    (∀ r ∈ disk, deriv Q0 r ≠ 0) ∧
    (∀ r : ℂ, Q0 r = 0 ↔ r = 0) ∧
    M.readout () () (deriv Q0 0) = true ∧
    HasDerivAt (deriv Q0) (1 / 16) 0 ∧
    deriv (deriv Q0) 0 / (Nat.factorial 2 : ℂ) = 1 / 32

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa [rejected, realize] using h.2.2.2.2.1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1 / 16, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @actual_nome_disk) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @actual_nome_disk,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_nome_disk) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialNome.DiskNome.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialNome.DiskNome.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => decide (z = 1 / 16)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialNome
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end DiskNome

namespace SourceNome
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ) (fun _ => ℂ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ r z => decide (z = Complex.exp (Complex.I * (Real.pi : ℂ) * tau r))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law M :=
    (∀ r ∈ lens, M.readout () r (Q0 r) = true) ∧
    (∀ r : ℝ, 0 < r → r < 1 → Q0 (r : ℂ) =
      (r : ℂ) * Complex.exp (2 *
        D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans.sourceConstant
          (Real.sqrt r : ℂ)) / 16)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h.1 (1 / 2) (by norm_num [lens, Metric.mem_ball, dist_eq_norm])
  simpa [rejected, realize] using hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, Complex.exp (Complex.I * (Real.pi : ℂ) * tau 0), ?_⟩
  simp [actual, realize, Ne.symm (Complex.exp_ne_zero _)]

def family : Registration arena (type_of% @actual_nome_source) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using @actual_nome_source,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_nome_source) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.OriginalHalfBinomialNome.SourceNome.unit
  realizationName := `Reg.D5.S3.Analytic.OriginalHalfBinomialNome.SourceNome.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r z => decide (z = Complex.exp (Complex.I * (Real.pi : ℂ) * tau r))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.OriginalHalfBinomialNome
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["fn", "arg", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end SourceNome

end Reg.D5.S3.Analytic.OriginalHalfBinomialNome
