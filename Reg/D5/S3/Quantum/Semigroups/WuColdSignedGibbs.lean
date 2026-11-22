import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Semigroups.WuColdSignedGibbs

/-! Readouts of the signed map and its pure kernel quartic. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Semigroups.WuColdSignedGibbs
open _root_.WuRankOneEndpointFloor (TwoMode)

namespace Reg.D5.S3.Quantum.Semigroups.WuColdSignedGibbs

private abbrev mapSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => TwoMode) (fun _ => TwoMode)

private def mapActual : Realization mapSignature :=
  realize mapSignature (fun _ s X => signedMap s X) (fun e => nomatch e)

private def mapRejected : Realization mapSignature :=
  realize mapSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem triangleImage_ne_zero : signedMap 0 (triangleMatrix 0 0 1) ≠ 0 := by
  rw [signedMap_triangle (by norm_num)]
  intro he
  have he' := congrArg (fun X : TwoMode => X (0, 0) (1, 1)) he
  change (↑(h 0) : ℂ) * 1 = 0 at he'
  norm_num [h, L, u, w] at he'

private theorem mapDependence : ObservationalDependence mapSignature mapActual := by
  intro role
  refine ⟨(0 : ℝ), triangleMatrix 0 0 1, (0 : TwoMode), ?_⟩
  intro he
  dsimp only [mapActual, realize] at he
  exact triangleImage_ne_zero (he.trans ((signedMap 0).map_zero))

namespace Triangle

private abbrev arena : Arena where
  signature := mapSignature
  Law R := ∀ {s : ℝ} (_hs : 0 ≤ s) (x z : Row) (d : ℂ),
    R.readout () s (triangleMatrix x z d) =
      triangleMatrix (signedX s x z) (signedZ s x z) ((h s : ℂ) * d)

private theorem rejected_law : ¬ arena.Law mapRejected := by
  intro law
  apply triangleImage_ne_zero
  exact (signedMap_triangle (by norm_num) 0 0 1).trans (law (s := 0) (by norm_num) 0 0 1).symm

def family : Registration arena (type_of% @signedMap_triangle) where
  actual := mapActual
  bridge := Iff.rfl
  variation := ⟨@signedMap_triangle, mapRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law mapActual mapRejected rejected_law
  dependence := mapDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signedMap_triangle) (Realization mapSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuColdSignedGibbs.signedMap_triangle.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuColdSignedGibbs.Triangle.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize mapSignature (fun _ s X => signedMap s X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuColdSignedGibbs
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Triangle

namespace Kernel

private abbrev arena : Arena where
  signature := mapSignature
  Law R := ∀ {s : ℝ} (_hs : 0 ≤ s) (z : Row),
    R.readout () s (kernelMatrix (u s) z) = κ s • kernelMatrix (w s) z

private theorem rejected_law : ¬ arena.Law mapRejected := by
  intro law
  have he := law (s := 0) (by norm_num) (1 : Row)
  have he' := congrArg (fun X : TwoMode => X (0, 1) (1, 1)) he
  change (0 : ℂ) = κ 0 * 1 at he'
  norm_num [κ, h, L, u, w] at he'

def family : Registration arena (type_of% @signedMap_kernel) where
  actual := mapActual
  bridge := Iff.rfl
  variation := ⟨@signedMap_kernel, mapRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law mapActual mapRejected rejected_law
  dependence := mapDependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@signedMap_kernel) (Realization mapSignature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuColdSignedGibbs.signedMap_kernel.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuColdSignedGibbs.Kernel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize mapSignature (fun _ s X => signedMap s X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuColdSignedGibbs
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Kernel

namespace Quartic

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => Row) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ s z => 2 * h s ^ 2 * w s * (2 + 3 * w s + 2 * w s ^ 2) * ν z ^ 2)
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℝ} (_hs : 0 ≤ s) (z : Row),
    2 / M s ^ 2 * (gibbsWeight (u s) * kernelMatrix (u s) z ^ 2).trace.re ^ 2 -
        (signedMap s (kernelMatrix (u s) z) ^ 4).trace.re =
      R.readout () s z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have he := law (s := 1) (by norm_num) (1 : Row)
  rw [kernel_pure_quartic (by norm_num)] at he
  norm_num [rejected, realize, h, L, u, w, ν, Complex.normSq_apply] at he

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(1 : ℝ), (fun _ => (0 : ℂ)), (fun _ => (1 : ℂ)), ?_⟩
  norm_num [actual, realize, h, L, u, w, ν, Complex.normSq_zero, Complex.normSq_one]

def family : Registration arena (type_of% @kernel_pure_quartic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernel_pure_quartic, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kernel_pure_quartic) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Semigroups.WuColdSignedGibbs.kernel_pure_quartic.audit
  realizationName := `Reg.D5.S3.Quantum.Semigroups.WuColdSignedGibbs.Quartic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ s z => 2 * h s ^ 2 * w s * (2 + 3 * w s + 2 * w s ^ 2) * ν z ^ 2)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Semigroups.WuColdSignedGibbs
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Quartic

end Reg.D5.S3.Quantum.Semigroups.WuColdSignedGibbs
