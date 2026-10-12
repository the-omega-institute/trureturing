import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Hyperideal.ActualRaysJointAngle
import Reg.Support.DependentFamily

open scoped BigOperators Topology
open Set Filter
open _root_.D5.S3.Geometry.Hyperideal.LengthGramBody
open _root_.D5.S3.Geometry.HyperbolicUpperHalfSpace
open _root_.D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Geometry.Hyperideal.ActualRaysJointAngle
noncomputable section

abbrev signature : Signature where
  Params := ℝ → HyperbolicThreeSpace
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 4 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ g t => lift (g t)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (Y U V : Fin 4 → ℝ)
    (hY : lorentz Y Y = -1) (ht : 0 < Y 3)
    (hU : lorentz U U = 1) (hV : lorentz V V = 1)
    (hYU : lorentz Y U = 0) (hYV : lorentz Y V = 0)
    (hc : lorentz U V ∈ Icc (-1:ℝ) 1),
    ∃ gammaU gammaV : ℝ → HyperbolicThreeSpace,
      Isometry gammaU ∧ Isometry gammaV ∧
      gammaU 0 = project Y hY ht ∧ gammaV 0 = project Y hY ht ∧
      (∀ t, R.readout () gammaU t = Real.cosh t • Y + Real.sinh t • U) ∧
      (∀ t, lift (gammaV t) = Real.cosh t • Y + Real.sinh t • V) ∧
      (∀ s t, Real.cosh (dist (gammaU s) (gammaV t)) =
        Real.cosh s * Real.cosh t - lorentz U V * Real.sinh s * Real.sinh t) ∧
      (∀ s t, 0 ≤ s → 0 ≤ t →
        |s-t| ≤ dist (gammaU s) (gammaV t) ∧ dist (gammaU s) (gammaV t) ≤ s+t) ∧
      Tendsto (fun z : ℝ × ℝ => Real.arccos
        ((z.1^2+z.2^2-dist (gammaU z.1) (gammaV z.2)^2)/(2*z.1*z.2)))
        (𝓝[Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)] ((0:ℝ),(0:ℝ)))
        (𝓝 (Real.arccos (lorentz U V)))

private def Y : Fin 4 → ℝ := ![0,0,0,1]
private def U : Fin 4 → ℝ := ![1,0,0,0]

private theorem hypotheses : lorentz Y Y = -1 ∧ 0 < Y 3 ∧
    lorentz U U = 1 ∧ lorentz Y U = 0 ∧ lorentz U U ∈ Icc (-1:ℝ) 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Y,U,lorentz,Fin.sum_univ_succ]
  · change (0 : ℝ) < 1; norm_num
  · norm_num [Y,U,lorentz,Fin.sum_univ_succ]
  · norm_num [Y,U,lorentz,Fin.sum_univ_succ]
  · norm_num [Y,U,lorentz,Fin.sum_univ_succ]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨gu,gv,_,_,_,_,hl,_⟩ := h Y U U hypotheses.1 hypotheses.2.1
    hypotheses.2.2.1 hypotheses.2.2.1 hypotheses.2.2.2.1 hypotheses.2.2.2.1 hypotheses.2.2.2.2
  have he := congrFun (hl 0) 3
  simp only [Real.cosh_zero, Real.sinh_zero, zero_smul, one_smul, add_zero] at he
  change (0 : ℝ) = 1 at he
  norm_num at he

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Geometry.Hyperideal.ActualRaysJointAngle.actual_rays_joint_angle,
    rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    obtain ⟨gu,gv,hi,_,_,_,_,_,_,_,_⟩ :=
      _root_.D5.S3.Geometry.Hyperideal.ActualRaysJointAngle.actual_rays_joint_angle
        Y U U hypotheses.1 hypotheses.2.1 hypotheses.2.2.1 hypotheses.2.2.1
        hypotheses.2.2.2.1 hypotheses.2.2.2.1 hypotheses.2.2.2.2
    refine ⟨gu,0,1,?_⟩
    intro he
    have h := hi.injective (lift_injective he)
    norm_num at h

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.Hyperideal.ActualRaysJointAngle.actual_rays_joint_angle)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ g t => lift (g t)) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Geometry.Hyperideal.ActualRaysJointAngle.actual_rays_joint_angle.lift_unit,
  realizationName := `Reg.D5.S3.Geometry.Hyperideal.ActualRaysJointAngle.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ g t => lift (g t)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Geometry.Hyperideal.ActualRaysJointAngle, definition := none, coordinates := #[10], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "fn", "arg", "body", "fn", "arg"], stateBinder := 12, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end
end Reg.D5.S3.Geometry.Hyperideal.ActualRaysJointAngle
