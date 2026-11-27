import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletZeroBounds
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex
open _root_.D5.S3.CharacterSums.DirichletZeroBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.CharacterSums.DirichletZeroBounds
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -5) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
    χ.IsPrimitive → χ ≠ 1 → ∀ T t : ℝ, |t| ≤ T →
    (∀ ρ : {z : ℂ // χ.LFunction z = 0}, ρ.1.re < 1) ∧
    Summable (fun ρ : {z : ℂ // χ.LFunction z = 0} =>
      (analyticOrderNatAt χ.LFunction ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) ∧
    (∑' ρ : {z : ℂ // χ.LFunction z = 0},
      (analyticOrderNatAt χ.LFunction ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) <
      Real.log ((q : ℝ) * (|t| + 3)) / 2 + 7 / 4 ∧
    (∑' ρ : {z : ℂ // χ.LFunction z = 0},
      (analyticOrderNatAt χ.LFunction ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) ≤
      V.readout () () ((q : ℝ) * (T + 3)) + 4 ∧
    (∑' ρ : {z : ℂ // χ.LFunction z = 0},
      (analyticOrderNatAt χ.LFunction ρ.1 : ℝ) * ‖(2 + t * I - ρ.1)⁻¹‖ ^ 2) ≤
      completionBudget χ t + 1 / 2
private def sample : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
private theorem sample_ne_one : sample ≠ 1 := by
  intro h
  have hh := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3 : ZMod 4)) h
  have hone : (1 : DirichletCharacter ℂ 4) (3 : ZMod 4) = 1 :=
    MulChar.one_apply (by decide)
  have hs : sample (3 : ZMod 4) = (-1 : ℂ) := by
    norm_num [sample, MulChar.ringHomComp_apply, ZMod.χ₄]
  rw [hs, hone] at hh
  norm_num at hh
private theorem primitive_ne_one : sample.primitiveCharacter ≠ 1 := by
  intro h
  have he := sample.changeLevel_primitiveCharacter
  rw [h, DirichletCharacter.changeLevel_one] at he
  exact sample_ne_one he.symm
private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  letI : NeZero sample.conductor := ⟨sample.conductor_ne_zero⟩
  have hh := (h sample.primitiveCharacter_isPrimitive primitive_ne_one 0 0 (by simp)).2.2.2.1
  have hn : 0 ≤ (∑' ρ : {z : ℂ // sample.primitiveCharacter.LFunction z = 0},
      (analyticOrderNatAt sample.primitiveCharacter.LFunction ρ.1 : ℝ) *
        ‖(2 + (0 : ℝ) * I - ρ.1)⁻¹‖ ^ 2) := tsum_nonneg (fun _ => by positivity)
  change _ ≤ (-5 : ℝ) + 4 at hh
  linarith
private theorem dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 1, Real.exp 1, by simp [actual, realize]⟩
def family : Registration arena (type_of% @zero_square_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@zero_square_bound, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@zero_square_bound) (Realization signature) Type Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletZeroBounds.zero_square_bound "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletZeroBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletZeroBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.CharacterSums.DirichletZeroBounds
