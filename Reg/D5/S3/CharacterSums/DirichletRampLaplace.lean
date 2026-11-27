import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletRampLaplace
import Reg.Support.SingleDependentReadout
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! The half-line integral distinguishes exponentially damped inputs.
An output shift breaks each transform identity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set LeanInformationAudit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.CharacterSums.DirichletRampEndpoint
open _root_.D5.S3.CharacterSums.DirichletRampLaplace
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.CharacterSums.DirichletRampLaplace

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ f => integral (volume.restrict (Ioi (0 : ℝ))) f) (fun e => nomatch e)

def shifted : Realization signature :=
  realize signature (fun _ _ f => (∫ y : ℝ in Ioi 0, f y) + 1) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), fun _ => 0, fun y => Complex.exp ((-1 : ℂ) * y), ?_⟩
  change (∫ _ : ℝ in Ioi 0, (0 : ℂ)) ≠ ∫ y : ℝ in Ioi 0, Complex.exp ((-1 : ℂ) * y)
  rw [integral_zero, integral_exp_mul_complex_Ioi (by norm_num : (-1 : ℂ).re < 0)]
  norm_num

private theorem nonprincipal_three : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (show (-1 : ZMod 3) ≠ 1 by decide)
  exact ⟨χ, fun h => hχ (h ▸ MulChar.one_apply_coe (-1 : (ZMod 3)ˣ))⟩

namespace Twisted

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ),
    V.readout () () (fun y : ℝ => Complex.exp (-transformLine t * y) *
      characterRamp χ (Real.exp y)) =
      (-deriv χ.LFunction (transformLine t) / χ.LFunction (transformLine t)) /
        (transformLine t * (transformLine t - 1))

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro h
  have bad := h (1 : DirichletCharacter ℂ 1) 0
  change (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine 0 * y) *
    characterRamp (1 : DirichletCharacter ℂ 1) (Real.exp y)) + 1 = _ at bad
  rw [← characterRamp_line_laplace (1 : DirichletCharacter ℂ 1) 0] at bad
  exact one_ne_zero (add_left_cancel (bad.trans (add_zero _).symm))

def family : Registration arena (type_of% @characterRamp_line_laplace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@characterRamp_line_laplace, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@characterRamp_line_laplace) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletRampLaplace.characterRamp_line_laplace
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletRampLaplace.Twisted.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ f => integral (volume.restrict (Ioi (0 : ℝ))) f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletRampLaplace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Twisted

namespace Centered

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t : ℝ),
    V.readout () () (fun y : ℝ => Complex.exp (-transformLine t * y) * gChi χ (Real.exp y)) =
      (-deriv χ.LFunction (transformLine t) / χ.LFunction (transformLine t)) /
        (transformLine t * (transformLine t - 1)) +
      (deriv χ.LFunction 1 / χ.LFunction 1) / (transformLine t - 1)

private theorem shifted_fails : ¬ arena.Law shifted := by
  intro h
  obtain ⟨χ, hχ⟩ := nonprincipal_three
  have bad := h χ hχ 0
  change (∫ y : ℝ in Ioi 0, Complex.exp (-transformLine 0 * y) * gChi χ (Real.exp y)) + 1 =
    _ at bad
  rw [← gChi_line_laplace χ hχ 0] at bad
  exact one_ne_zero (add_left_cancel (bad.trans (add_zero _).symm))

def family : Registration arena (type_of% @gChi_line_laplace) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gChi_line_laplace, shifted, shifted_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted shifted_fails
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gChi_line_laplace) (Realization signature) Unit Unit where
  unitName := `D5.S3.CharacterSums.DirichletRampLaplace.gChi_line_laplace.__information_unit
  realizationName := `Reg.D5.S3.CharacterSums.DirichletRampLaplace.Centered.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ f => integral (volume.restrict (Ioi (0 : ℝ))) f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletRampLaplace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Centered

namespace Range

abbrev sig : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ → ℂ) (fun _ => ℂ)

def actual : Realization sig :=
  realize sig (fun _ x f => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), f n) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ x f => (∑ n ∈ Finset.range (⌊x⌋₊ + 1), f n) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ),
    characterRamp χ x = V.readout () x (fun n => (mangoldtRamp n x : ℂ) * χ (n : ZMod N))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := h (1 : DirichletCharacter ℂ 1) 0
  change _ = (∑ n ∈ Finset.range (⌊(0 : ℝ)⌋₊ + 1),
    (mangoldtRamp n 0 : ℂ) * (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) + 1 at bad
  rw [← characterRamp_eq_range] at bad
  exact zero_ne_one (add_left_cancel ((add_zero _).trans bad))

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  exact ⟨0, (fun _ => 0), (fun _ => 1), by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @characterRamp_eq_range) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@characterRamp_eq_range, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@characterRamp_eq_range) (Realization sig) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletRampLaplace.characterRamp_eq_range
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.DirichletRampLaplace.Range "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletRampLaplace
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Range

namespace Weighted

abbrev sig : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization sig :=
  realize sig (fun _ p z => Complex.exp (-transformLine p.1 * p.2) * z) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ p z => Complex.exp (-transformLine p.1 * p.2) * z + 1) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (t y : ℝ),
    HasSum (fun n : ℕ => Complex.exp (-transformLine t * y) *
      (mangoldtRamp n (Real.exp y) : ℂ) * χ (n : ZMod N))
      (V.readout () ⟨t, y⟩ (characterRamp χ (Real.exp y)))

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := (h (1 : DirichletCharacter ℂ 1) 0 0).unique
    (weighted_ramps_hasSum (1 : DirichletCharacter ℂ 1) 0 0)
  change _ + 1 = _ at bad
  exact one_ne_zero (add_left_cancel (bad.trans (add_zero _).symm))

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  exact ⟨⟨0, 0⟩, 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @weighted_ramps_hasSum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_ramps_hasSum, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_ramps_hasSum) (Realization sig) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletRampLaplace.weighted_ramps_hasSum
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.DirichletRampLaplace.Weighted "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletRampLaplace
    definition := none
    coordinates := #[2,3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Weighted

end Reg.D5.S3.CharacterSums.DirichletRampLaplace
