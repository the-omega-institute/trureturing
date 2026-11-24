import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchor

namespace Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchor

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Omega.CovarianceToAnchor
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- The seven moment coordinates in the cubic inequality. -/
private abbrev Moments := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Moments (fun _ => ℝ) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ p t =>
    simpsonCubic p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 t)
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V W H K c d m t : ℝ},
    LocalCovariance V W H K c d m →
    (c + m) ^ 2 + (7 / 4) * d ^ 2 ≤ (3 * V - 2 * H) * (3 * W - 2 * K) →
    0 ≤ t → t ≤ 1 → 0 ≤ R.readout () (V, W, H, K, c, d, m) t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcov : LocalCovariance 0 0 0 0 0 0 0 := by constructor <;> norm_num
  have hbad := h (t := 0) hcov (by norm_num) (by norm_num) (by norm_num)
  exact (by norm_num : ¬ (0 : ℝ) ≤ -1) hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(1, 1, 0, 0, 0, 0, 0), 0, 1, ?_⟩
  change simpsonCubic 1 1 0 0 0 0 0 0 ≠ simpsonCubic 1 1 0 0 0 0 0 1
  norm_num [simpsonCubic]

def family : Registration arena (type_of% @simpson_cubic_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@simpson_cubic_nonneg, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@simpson_cubic_nonneg) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchor.unit
  realizationName := `Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t =>
    simpsonCubic p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2 t)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchor
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.CovarianceToAnchor
