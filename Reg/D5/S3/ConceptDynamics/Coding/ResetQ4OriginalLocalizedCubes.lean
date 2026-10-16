import D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Reg.D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes
open _root_.D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes
open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
open _root_.D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open _root_.D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) :=
  AddCommGroup.toIntModule _
private instance : IsDomain (Localization.Away (2 : ℤ)) :=
  Localization.Away.isDomain (by norm_num)

abbrev signature : Signature where
  Params := Unit
  State _ := DyadicMatrix
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := DyadicMatrix
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature :=
  realize signature (fun _ _ m => m^3) (fun e => nomatch e)
abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ h : ResetFullAut 4, ∃ i j : Fin 3, ∃ v : Centralizer,
    rhoD h = T^i.val * (1+T)^j.val * r.readout () ()
      ((v : DyadicMatrixˣ) : DyadicMatrix) ∧
    Commute ((v : DyadicMatrixˣ) : DyadicMatrix) T

private theorem rhoD_one : rhoD (1 : ResetFullAut 4) = 1 := by
  let E := resetNativeEquiv 4 (by decide)
  have hi : (E.symm.trans ((1 : Native 4 ≃ₗ[ℤ] Native 4).trans E)).toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    intro v
    change E (E.symm v) = v
    exact E.apply_symm_apply v
  dsimp only [E] at hi
  simp only [rhoD, map_one, hi, LinearMap.toMatrix_id]

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  obtain ⟨i,j,v,hv,_⟩ := h 1
  have hz : (1 : DyadicMatrix) = 0 := by
    simpa only [rhoD_one, bad, realize, mul_zero] using hv
  exact one_ne_zero hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  simp [actual, realize]

def evidence : Registration arena (type_of% @original_localized_cube_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_localized_cube_factorization, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@original_localized_cube_factorization) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => m^3) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "body", "arg", "body",
        "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end Reg.D5.S3.ConceptDynamics.Coding.ResetQ4OriginalLocalizedCubes
