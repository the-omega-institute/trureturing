import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletCyclicLaplace
import Reg.Support.SingleDependentReadout
/-! Source-equivalent readouts with explicit variation and observational dependence. -/

open _root_.D5.S3.CharacterSums.DirichletCyclicLaplace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set Filter MeasureTheory
open scoped Topology BigOperators
open _root_.D5.S3.CharacterSums.DirichletRampEndpoint
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.CharacterSums.DirichletCyclicLaplace

local instance sourceRealMeasurable : MeasurableSpace ℝ :=
  @MeasureSpace.toMeasurableSpace ℝ Real.measureSpace

namespace Weighted
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℂ, ℝ)
    (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ p z => Complex.exp (-p.1 * p.2) * z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p z => Complex.exp (-p.1 * p.2) * z + 1) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law V := ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) (y : ℝ),
    HasSum (fun n : ℕ => Complex.exp (-s * y) *
      (mangoldtRamp n (Real.exp y) : ℂ) * χ (n : ZMod N))
      (V.readout () ⟨s, y⟩ (characterRamp χ (Real.exp y)))
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := (h (1 : DirichletCharacter ℂ 1) 0 0).unique
    (weighted_character_hasSum (1 : DirichletCharacter ℂ 1) 0 0)
  change _ + 1 = _ at bad
  exact one_ne_zero (add_left_cancel (bad.trans (add_zero _).symm))
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨⟨0, 0⟩, 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @weighted_character_hasSum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_character_hasSum, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_character_hasSum) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletCyclicLaplace.weighted_character_hasSum
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicLaplace.Weighted.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => Complex.exp (-p.1 * p.2) * z)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicLaplace
    definition := none
    coordinates := #[2,3]
    readouts := #[
    { path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Weighted

namespace Character
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ f => (∫ y : ℝ in Ioi 0, f y) + 1) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), fun _ => 0, fun y => Complex.exp ((-1 : ℂ) * y), ?_⟩
  change (∫ _ : ℝ in Ioi 0, (0 : ℂ)) ≠ ∫ y : ℝ in Ioi 0, Complex.exp ((-1 : ℂ) * y)
  rw [integral_zero, integral_exp_mul_complex_Ioi (by norm_num : (-1 : ℂ).re < 0)]
  norm_num
def arena : Arena where
  signature := signature
  Law V := ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ},
    1 < s.re → V.readout () ()
      (fun y : ℝ => Complex.exp (-s * y) * characterRamp χ (Real.exp y)) =
        (-deriv χ.LFunction s / χ.LFunction s) / (s * (s - 1))
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := h (1 : DirichletCharacter ℂ 1) (s := 2) (by norm_num)
  change (∫ y : ℝ in Ioi 0, Complex.exp (-(2 : ℂ) * y) *
    characterRamp (1 : DirichletCharacter ℂ 1) (Real.exp y)) + 1 = _ at bad
  rw [← characterRamp_half_plane_laplace (1 : DirichletCharacter ℂ 1)
    (by norm_num : 1 < (2 : ℂ).re)] at bad
  exact one_ne_zero (add_left_cancel (bad.trans (add_zero _).symm))

def family : Registration arena (type_of% @characterRamp_half_plane_laplace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@characterRamp_half_plane_laplace, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@characterRamp_half_plane_laplace) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletCyclicLaplace.characterRamp_half_plane_laplace
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicLaplace.Character.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicLaplace
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Character

namespace Corrected
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ f => (∫ y : ℝ in Ioi 0, f y) + 1) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), fun _ => 0, fun y => Complex.exp ((-1 : ℂ) * y), ?_⟩
  change (∫ _ : ℝ in Ioi 0, (0 : ℂ)) ≠ ∫ y : ℝ in Ioi 0, Complex.exp ((-1 : ℂ) * y)
  rw [integral_zero, integral_exp_mul_complex_Ioi (by norm_num : (-1 : ℂ).re < 0)]
  norm_num
def arena : Arena where
  signature := signature
  Law V := ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
    ∀ {s : ℂ}, 1 < s.re →
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * gChi χ (Real.exp y)) (Ioi 0) ∧
      V.readout () () (fun y : ℝ => Complex.exp (-s * y) * gChi χ (Real.exp y)) =
        characterTransform χ s
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (show (-1 : ZMod 3) ≠ 1 by decide)
  have hne : χ ≠ 1 := by
    rintro rfl
    exact hχ (MulChar.one_apply_coe (-1 : (ZMod 3)ˣ))
  have bad := (h χ hne (s := 2) (by norm_num)).2
  change (∫ y : ℝ in Ioi 0, Complex.exp (-(2 : ℂ) * y) * gChi χ (Real.exp y)) + 1 = _ at bad
  rw [← (gChi_half_plane_laplace χ hne (by norm_num : 1 < (2 : ℂ).re)).2] at bad
  exact one_ne_zero (add_left_cancel (bad.trans (add_zero _).symm))

def family : Registration arena (type_of% @gChi_half_plane_laplace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gChi_half_plane_laplace, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gChi_half_plane_laplace) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletCyclicLaplace.gChi_half_plane_laplace
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicLaplace.Corrected.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicLaplace
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Corrected

namespace Cyclic
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℂ)
def actual : Realization signature :=
  realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ f => (∫ y : ℝ in Ioi 0, f y) + 1) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), fun _ => 0, fun y => Complex.exp ((-1 : ℂ) * y), ?_⟩
  change (∫ _ : ℝ in Ioi 0, (0 : ℂ)) ≠ ∫ y : ℝ in Ioi 0, Complex.exp ((-1 : ℂ) * y)
  rw [integral_zero, integral_exp_mul_complex_Ioi (by norm_num : (-1 : ℂ).re < 0)]
  norm_num
def arena : Arena where
  signature := signature
  Law V := ∀ {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), r ≤ orderOf χ →
    ∀ {s : ℂ}, 1 < s.re →
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) *
      (gl1CyclicFamily (r := r) χ (Real.exp y) : ℂ)) (Ioi 0) ∧
      V.readout () () (fun y : ℝ => Complex.exp (-s * y) *
        (gl1CyclicFamily (r := r) χ (Real.exp y) : ℂ)) = cyclicTransform (r := r) χ s
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := (h (1 : DirichletCharacter ℂ 1) le_rfl (s := 2) (by norm_num)).2
  change (∫ y : ℝ in Ioi 0, Complex.exp (-(2 : ℂ) * y) *
    (gl1CyclicFamily (r := orderOf (1 : DirichletCharacter ℂ 1))
      (1 : DirichletCharacter ℂ 1) (Real.exp y) : ℂ)) + 1 = _ at bad
  rw [← (gl1CyclicFamily_half_plane_laplace (1 : DirichletCharacter ℂ 1)
    le_rfl (by norm_num : 1 < (2 : ℂ).re)).2] at bad
  exact one_ne_zero (add_left_cancel (bad.trans (add_zero _).symm))

def family : Registration arena (type_of% @gl1CyclicFamily_half_plane_laplace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gl1CyclicFamily_half_plane_laplace, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@gl1CyclicFamily_half_plane_laplace) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletCyclicLaplace.gl1CyclicFamily_half_plane_laplace
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletCyclicLaplace.Cyclic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletCyclicLaplace
    definition := none
    coordinates := #[]
    readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Cyclic

end Reg.D5.S3.CharacterSums.DirichletCyclicLaplace
