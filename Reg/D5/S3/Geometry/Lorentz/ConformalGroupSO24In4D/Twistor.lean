import D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source registrations for the chiral representation. -/

open _root_.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
open _root_.D5.S3.Geometry.Lorentz.DiracCliffordSpinors4D (Mat4 γ gamma5 PL PR)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.OmegaMath.OrthogonalMatrixGenerators (generator)
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open Matrix
open scoped Matrix

namespace Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private theorem dilation_mem : dilatation ∈ so24Subspace := so24_antisym_metric 4 5

private theorem twistor_dilation_ne_zero : twistorRep dilatation ≠ 0 := by
  rw [(twistorRep_conformal_generators 0 0).2.1]
  intro h
  have he := congrArg (fun X : Mat4 => X 0 0) h
  norm_num [D5.S3.Geometry.Lorentz.DiracCliffordSpinors4D.gamma5_explicit] at he

private theorem twistor_translation_ne_zero : twistorRep (translationGen 0) ≠ 0 := by
  intro h
  have hk := twistorRep_lie_hom (specialGen 0) (translationGen 0)
    (Submodule.sub_mem so24Subspace (so24_antisym_metric 0 4) (so24_antisym_metric 0 5))
    (Submodule.add_mem so24Subspace (so24_antisym_metric 0 4) (so24_antisym_metric 0 5))
  change twistorRep (bracket (specialGen 0) (translationGen 0)) = _ at hk
  rw [(conformal_algebra_commutators 0 0 0).2.2.2.2.2.1, h] at hk
  change twistorRep ((2 : ℝ) • (LorentzGen 0 0 - eta24 0 0 • dilatation)) = _ at hk
  have hm : LorentzGen 0 0 = 0 := by simp [LorentzGen, L, generator]
  have hη : eta24 0 0 = 1 := by
    norm_num [eta24, OmegaMath.OrthogonalMatrixGenerators.metric, metricSign24]
  simp only [hm, hη, one_smul, zero_sub, map_smul, map_neg, mul_zero, zero_mul, sub_zero] at hk
  exact twistor_dilation_ne_zero (neg_eq_zero.mp ((smul_eq_zero.mp hk).resolve_left (by norm_num)))


namespace TwistorImage

abbrev sig : Signature := signature (Unit) (fun _ => RMat6) (fun _ => Mat4)

def actual : Realization sig :=
  realize sig (fun _ _ X => twistorRep X) (fun e => nomatch e)

def erased : Realization sig :=
  realize sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := ∀ X : RMat6, IsSU22Lie (R.readout () () X)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  have h0 := (h 0).2
  change (1 : Mat4).trace = 0 at h0
  norm_num [Matrix.trace_one] at h0

def family : Registration arena (type_of% @twistorRep_mem_su22) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨twistorRep_mem_su22, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    rintro ⟨⟩
    refine ⟨(), 0, dilatation, ?_⟩
    change twistorRep 0 ≠ twistorRep dilatation
    rw [map_zero]
    exact Ne.symm twistor_dilation_ne_zero

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@twistorRep_mem_su22) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.twistorRep_mem_su22.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.TwistorImage.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ X => twistorRep X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TwistorImage

namespace TwistorBracket

abbrev sig : Signature := signature (Unit) (fun _ => RMat6) (fun _ => Mat4)

def actual : Realization sig :=
  realize sig (fun _ _ X => twistorRep X) (fun e => nomatch e)

def erased : Realization sig :=
  realize sig (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := ∀ X Y : RMat6, X ∈ so24Subspace → Y ∈ so24Subspace →
    R.readout () () (X * Y - Y * X) =
      twistorRep X * twistorRep Y - twistorRep Y * twistorRep X

private theorem rejected : ¬ arena.Law erased := by
  intro h
  have h0 := h 0 0 so24Subspace.zero_mem so24Subspace.zero_mem
  change (1 : Mat4) = twistorRep 0 * twistorRep 0 - twistorRep 0 * twistorRep 0 at h0
  simp at h0

def family : Registration arena (type_of% @twistorRep_lie_hom) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨twistorRep_lie_hom, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    rintro ⟨⟩
    refine ⟨(), 0, dilatation, ?_⟩
    change twistorRep 0 ≠ twistorRep dilatation
    rw [map_zero]
    exact Ne.symm twistor_dilation_ne_zero

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@twistorRep_lie_hom) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.twistorRep_lie_hom.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.TwistorBracket.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ X => twistorRep X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TwistorBracket

namespace TwistorBijection

abbrev sig : Signature :=
  signature Unit (fun _ => so24Subspace →ₗ[ℝ] su22Subspace)
    (fun _ => so24Subspace → su22Subspace)

def actual : Realization sig :=
  realize sig (fun _ _ f => ⇑f) (fun e => nomatch e)

def erased : Realization sig :=
  realize sig (fun _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := Function.Bijective (R.readout () () twistorRepRestricted)

private theorem nonzero_source : (⟨dilatation, dilation_mem⟩ : so24Subspace) ≠ 0 := by
  intro h
  have he := congrArg (fun Y : so24Subspace => twistorRep Y.val) h
  change twistorRep dilatation = twistorRep 0 at he
  rw [map_zero] at he
  exact twistor_dilation_ne_zero he

private theorem rejected : ¬ arena.Law erased := by
  intro h
  exact nonzero_source (h.1 (a₁ := ⟨dilatation, dilation_mem⟩) (a₂ := 0) rfl)

def family : Registration arena (type_of% @twistorRep_bijective_su22) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨twistorRep_bijective_su22, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    rintro ⟨⟩
    refine ⟨(), twistorRepRestricted, 0, ?_⟩
    intro h
    have he := congrArg (fun f : so24Subspace → su22Subspace => f ⟨dilatation, dilation_mem⟩) h
    have hz := congrArg (fun Y : su22Subspace => Y.val) he
    change twistorRep dilatation = 0 at hz
    exact twistor_dilation_ne_zero hz

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@twistorRep_bijective_su22) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.twistorRep_bijective_su22.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.TwistorBijection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ f => ⇑f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TwistorBijection

namespace TwistorGenerators

abbrev sig : Signature := signature (Unit) (fun _ => RMat6) (fun _ => Mat4)

def actual : Realization sig :=
  realize sig (fun _ _ X => twistorRep X) (fun e => nomatch e)

def erased : Realization sig :=
  realize sig (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := sig
  Law R := ∀ μ ν : Fin 4,
    twistorRep (LorentzGen μ ν) = (1 / 4 : ℂ) • (γ μ * γ ν - γ ν * γ μ) ∧
    twistorRep dilatation = (1 / 2 : ℂ) • gamma5 ∧
    R.readout () () (translationGen μ) = Complex.I • (γ μ * PL) ∧
    twistorRep (specialGen μ) = (-Complex.I) • (γ μ * PR)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  exact twistor_translation_ne_zero
    ((twistorRep_conformal_generators 0 0).2.2.1.trans (h 0 0).2.2.1.symm)

def family : Registration arena (type_of% @twistorRep_conformal_generators) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨twistorRep_conformal_generators, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    rintro ⟨⟩
    refine ⟨(), 0, dilatation, ?_⟩
    change twistorRep 0 ≠ twistorRep dilatation
    rw [map_zero]
    exact Ne.symm twistor_dilation_ne_zero

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@twistorRep_conformal_generators) (Realization sig) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.twistorRep_conformal_generators.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D.TwistorGenerators.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig (fun _ _ X => twistorRep X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TwistorGenerators

end

end Reg.D5.S3.Geometry.Lorentz.ConformalGroupSO24In4D
