import D5.S3.Quantum.Matrix.AnalyticPickHankel
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Typed source-binding attempts for analytic matrix Pick positivity.
Source-selection binding remains unfinished; mathematical proofs are separate. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.AnalyticPickKernel
open _root_.D5.S3.Quantum.Matrix.AnalyticPickHankel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Complex Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
namespace Reg.D5.S3.Quantum.Matrix.AnalyticPickHankel
noncomputable section
universe u v w

private structure MatrixScope where
  index : Type w
  finiteIndex : Fintype index
attribute [instance] MatrixScope.finiteIndex

private abbrev signature : Signature where
  Params := MatrixScope.{w}
  State s := Matrix s.index s.index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
private def actual : Realization signature :=
  realize signature (fun _ _ M => M.PosSemidef) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature.{w} actual := by
  intro i
  let p : MatrixScope.{w} := ⟨ULift.{w} Unit, inferInstance⟩
  refine ⟨p, 0, -1, ?_⟩
  intro h
  change (0 : Matrix p.index p.index ℂ).PosSemidef =
    (-1 : Matrix p.index p.index ℂ).PosSemidef at h
  have hh := (Eq.mp h Matrix.PosSemidef.zero).diag_nonneg (i := ⟨()⟩)
  norm_num at hh

namespace RealTwoPoint
private abbrev arena : Arena where
  signature := signature.{u}
  Law Rr := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {T : ℂ → Matrix d d ℂ} (hT : DifferentiableOn ℂ T {z | 0 < z.im})
    (hPos : ∀ z : ℂ, 0 < z.im →
      (_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.imaginaryPart (T z)).PosSemidef)
    {x y : ℝ} (hxy : x ≠ y)
    (hx : DifferentiableAt ℂ T (x : ℂ)) (hy : DifferentiableAt ℂ T (y : ℂ))
    (hRx : ∀ᶠ t : ℝ in 𝓝 x, (T (t : ℂ)).IsHermitian)
    (hRy : ∀ᶠ t : ℝ in 𝓝 y, (T (t : ℂ)).IsHermitian),
    Rr.readout () ⟨d ⊕ d, inferInstance⟩
      (fromBlocks (deriv T (x : ℂ))
        (((x : ℂ) - (y : ℂ))⁻¹ • (T (x : ℂ) - T (y : ℂ)))
        (((x : ℂ) - (y : ℂ))⁻¹ • (T (x : ℂ) - T (y : ℂ)))
        (deriv T (y : ℂ)))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (T := fun _ => 0) (differentiableOn_const 0)
    (by intros; simpa [_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.imaginaryPart]
      using (Matrix.PosSemidef.zero (n := ULift.{u} Unit) (R := ℂ)))
    (x := 0) (y := 1) (by norm_num) (differentiableAt_const 0) (differentiableAt_const 0)
    (by filter_upwards [] with t; exact Matrix.isHermitian_zero)
    (by filter_upwards [] with t; exact Matrix.isHermitian_zero)
private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law.{u}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.AnalyticPickHankel.real_two_point_loewner_posSemidef.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.AnalyticPickHankel.real_two_point_loewner_posSemidef.{u}, rejected, rejected_law.{u}⟩
  sensitivity := sensitivity.{u}
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.AnalyticPickHankel.real_two_point_loewner_posSemidef.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.AnalyticPickHankel.RealTwoPoint.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AnalyticPickHankel.RealTwoPoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ M => M.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end RealTwoPoint

namespace NormalizedHankel
private abbrev arena : Arena where
  signature := signature.{u}
  Law Rr := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    {T : ℂ → Matrix d d ℂ} (hT : DifferentiableOn ℂ T {z | 0 < z.im})
    (hPos : ∀ z : ℂ, 0 < z.im →
      (_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.imaginaryPart (T z)).PosSemidef)
    (hA : AnalyticAt ℂ T 0)
    (hReal : ∀ᶠ t : ℝ in 𝓝 0, (T (t : ℂ)).IsHermitian),
    Rr.readout () ⟨d ⊕ d, inferInstance⟩
      (fromBlocks (normalizedCoefficient T 1) (normalizedCoefficient T 2)
        (normalizedCoefficient T 2) (normalizedCoefficient T 3))
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (T := fun _ => 0) (differentiableOn_const 0)
    (by intros; simpa [_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.imaginaryPart]
      using (Matrix.PosSemidef.zero (n := ULift.{u} Unit) (R := ℂ))) analyticAt_const
    (by filter_upwards [] with t; exact Matrix.isHermitian_zero)
private theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law.{u}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Quantum.Matrix.AnalyticPickHankel.normalized_hankel_posSemidef.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.AnalyticPickHankel.normalized_hankel_posSemidef.{u}, rejected, rejected_law.{u}⟩
  sensitivity := sensitivity.{u}
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.AnalyticPickHankel.normalized_hankel_posSemidef.{u}) (Realization signature.{u}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.AnalyticPickHankel.NormalizedHankel.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AnalyticPickHankel.NormalizedHankel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ M => M.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end NormalizedHankel

end
end Reg.D5.S3.Quantum.Matrix.AnalyticPickHankel
