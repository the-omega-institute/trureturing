import D5.S3.Quantum.Matrix.AnalyticPickKernel
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Typed source-binding attempts for analytic matrix Pick positivity.
Source-selection binding remains unfinished; mathematical proofs are separate. -/

set_option autoImplicit false
open _root_.D5.S3.Quantum.Matrix.AnalyticPickKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Complex Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology
namespace Reg.D5.S3.Quantum.Matrix.AnalyticPickKernel
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

namespace FiniteCircle
private abbrev arena : Arena where
  signature := signature.{max u v}
  Law Rr := ∀ {d : Type u} {ι : Type v} [Fintype d] [Fintype ι] [DecidableEq d]
    {R : ℝ} (hR : 0 < R) {G : ℂ → Matrix d d ℂ}
    (hG : DiffContOnCl ℂ G (Metric.ball 0 R))
    (hPos : ∀ η ∈ Metric.sphere 0 R, (G η + (G η)ᴴ).PosSemidef)
    (points : ι → ℂ) (hp : ∀ i, ‖points i‖ < R),
    Rr.readout () ⟨ι × d, inferInstance⟩ (caratheodoryGram R points G)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (ι := ULift.{v} Unit) (R := 1) (by norm_num)
    (G := fun _ => 0) diffContOnCl_const
    (by intros; simpa using (Matrix.PosSemidef.zero (n := ULift.{u} Unit) (R := ℂ)))
    (fun _ => 0) (by simp)
private theorem sensitivity : Sensitivity arena.{u,v} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law.{u,v}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u,v} (type_of% (@_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.finite_circle_caratheodory_posSemidef.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.finite_circle_caratheodory_posSemidef.{u,v}, rejected, rejected_law.{u,v}⟩
  sensitivity := sensitivity.{u,v}
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.finite_circle_caratheodory_posSemidef.{u,v}) (Realization signature.{max u v}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.AnalyticPickKernel.FiniteCircle.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AnalyticPickKernel.FiniteCircle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{max u v} (fun _ _ M => M.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end FiniteCircle

namespace OpenDisk
private abbrev arena : Arena where
  signature := signature.{max u v}
  Law Rr := ∀ {d : Type u} {ι : Type v} [Fintype d] [Fintype ι] [DecidableEq d]
    {G : ℂ → Matrix d d ℂ} (hG : DifferentiableOn ℂ G (Metric.ball 0 1))
    (hPos : ∀ η ∈ Metric.ball 0 1, (G η + (G η)ᴴ).PosSemidef)
    (points : ι → ℂ) (hp : ∀ i, ‖points i‖ < 1),
    Rr.readout () ⟨ι × d, inferInstance⟩ (caratheodoryGram 1 points G)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (ι := ULift.{v} Unit)
    (G := fun _ => 0) (differentiableOn_const 0)
    (by intros; simpa using (Matrix.PosSemidef.zero (n := ULift.{u} Unit) (R := ℂ)))
    (fun _ => 0) (by simp)
private theorem sensitivity : Sensitivity arena.{u,v} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law.{u,v}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u,v} (type_of% (@_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.open_disk_caratheodory_posSemidef.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.open_disk_caratheodory_posSemidef.{u,v}, rejected, rejected_law.{u,v}⟩
  sensitivity := sensitivity.{u,v}
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.open_disk_caratheodory_posSemidef.{u,v}) (Realization signature.{max u v}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.AnalyticPickKernel.OpenDisk.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AnalyticPickKernel.OpenDisk.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{max u v} (fun _ _ M => M.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end OpenDisk

namespace UpperHalfPlane
private abbrev arena : Arena where
  signature := signature.{max u v}
  Law Rr := ∀ {d : Type u} {ι : Type v} [Fintype d] [Fintype ι] [DecidableEq d]
    {T : ℂ → Matrix d d ℂ} (hT : DifferentiableOn ℂ T {z | 0 < z.im})
    (hPos : ∀ z : ℂ, 0 < z.im →
      (_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.imaginaryPart (T z)).PosSemidef)
    (points : ι → ℂ) (hp : ∀ i, 0 < (points i).im),
    Rr.readout () ⟨ι × d, inferInstance⟩ (pickGram points T)
private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (d := ULift.{u} Unit) (ι := ULift.{v} Unit)
    (T := fun _ => 0) (differentiableOn_const 0)
    (by intros; simpa [_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.imaginaryPart] using (Matrix.PosSemidef.zero (n := ULift.{u} Unit) (R := ℂ)))
    (fun _ => I) (by simp)
private theorem sensitivity : Sensitivity arena.{u,v} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law.{u,v}⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

def family : Registration arena.{u,v} (type_of% (@_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.upper_half_plane_pick_posSemidef.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.upper_half_plane_pick_posSemidef.{u,v}, rejected, rejected_law.{u,v}⟩
  sensitivity := sensitivity.{u,v}
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Matrix.AnalyticPickKernel.upper_half_plane_pick_posSemidef.{u,v}) (Realization signature.{max u v}) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.AnalyticPickKernel.UpperHalfPlane.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.AnalyticPickKernel.UpperHalfPlane.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{max u v} (fun _ _ M => M.PosSemidef) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end UpperHalfPlane

end
end Reg.D5.S3.Quantum.Matrix.AnalyticPickKernel
