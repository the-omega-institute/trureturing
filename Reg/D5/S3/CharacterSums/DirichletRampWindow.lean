import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DirichletRampWindow
import Reg.Support.SingleDependentReadout
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! Singleton windows detect variations of the endpoint used by each bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Set MeasureTheory Filter Finset
open _root_.D5.S3.Weil.Mertens _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.CharacterSums.DirichletRampEndpoint _root_.D5.S3.CharacterSums.DirichletRampWindow
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.CharacterSums.DirichletRampWindow

private theorem nonprincipal_three : ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 := by
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (show (-1 : ZMod 3) ≠ 1 by decide)
  exact ⟨χ, fun he => hχ (he ▸ MulChar.one_apply_coe (-1 : (ZMod 3)ˣ))⟩

namespace Envelope

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hn : χ ≠ 1)
    {Y Z : ℝ} (hZ : Y ≤ Z) (B : ℝ → ℝ) (hB : ConcaveOn ℝ (Set.Icc Y Z) B),
    (∀ x ∈ Set.Icc Y Z, ‖gChi χ x‖ ≤ B x) ↔
    ‖gChi χ Y‖ ≤ B (V.readout () () Y) ∧ ‖gChi χ Z‖ ≤ B Z ∧
      ∀ n : ℕ, (n:ℝ) ∈ Set.Ioo Y Z → (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n:ZMod N) ≠ 0 →
        ‖gChi χ n‖ ≤ B n

private theorem reject_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨χ,hχ⟩ := nonprincipal_three
  have hi : ConcaveOn ℝ (Set.Icc (0:ℝ) 0) id := concaveOn_id (convex_Icc ..)
  have hg : gChi χ 0 = 0 := by simp [gChi,hχ,characterRamp]
  have ha : ∀ x ∈ Set.Icc (0:ℝ) 0, ‖gChi χ x‖ ≤ id x := by
    intro x hx
    have hx0 := le_antisymm hx.2 hx.1
    simp [hx0,hg]
  have bad := ((h hχ le_rfl id hi).mp ha).1
  change ‖gChi χ 0‖ ≤ -1 at bad
  linarith only [bad,norm_nonneg (gChi χ 0)]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @concave_window_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@concave_window_iff, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@concave_window_iff) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletRampWindow.concave_window_iff
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.DirichletRampWindow.Envelope "family"
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
    (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletRampWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Envelope

namespace Derivative

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature := realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => exp (-1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hn : χ ≠ 1)
    {p A c Y Z : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hA : 0 ≤ A) (hc : 0 ≤ c) (hY : 0 < Y) (hZ : Y ≤ Z),
    (∀ x ∈ Set.Icc Y Z, ‖gChi χ x‖ ≤ A * x ^ p ∧
      ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ c * log x) ↔
    (‖gChi χ Y‖ ≤ A * Y ^ p ∧ ‖gChi χ Z‖ ≤ A * Z ^ p ∧
      ∀ n : ℕ, (n:ℝ) ∈ Set.Ioo Y Z → (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n:ZMod N) ≠ 0 →
        ‖gChi χ n‖ ≤ A * (n : ℝ) ^ p) ∧
        ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ c * log (V.readout () () Y)

private theorem reject_fails : ¬ arena.Law rejected := by
  intro h
  obtain ⟨χ,hχ⟩ := nonprincipal_three
  let D := ‖deriv χ.LFunction 1 / χ.LFunction 1‖
  let y : ℝ := exp 1
  have hy : 0 < y := exp_pos _
  have hlog : log y = 1 := log_exp _
  have hc : 0 ≤ D + 1 := by dsimp [D]; positivity
  have ha : ∀ x ∈ Set.Icc y y, ‖gChi χ x‖ ≤ ‖gChi χ y‖ * x ^ (0:ℝ) ∧
      ‖deriv χ.LFunction 1 / χ.LFunction 1‖ ≤ (D + 1) * log x := by
    intro x hx
    rw [le_antisymm hx.2 hx.1,Real.rpow_zero,mul_one,hlog,mul_one]
    exact ⟨le_rfl,by change D ≤ D+1; linarith⟩
  have bad := ((h hχ (p:=0) le_rfl (by norm_num) (norm_nonneg _) hc hy le_rfl).mp ha).2
  change D ≤ (D+1)*log (exp (-1)) at bad
  rw [log_exp] at bad
  have hd : 0 ≤ D := norm_nonneg _
  linarith only [bad,hd]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @power_log_window_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@power_log_window_iff, rejected, reject_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected reject_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@power_log_window_iff) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletRampWindow.power_log_window_iff
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.DirichletRampWindow.Derivative "family"
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
    (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletRampWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Derivative

end Reg.D5.S3.CharacterSums.DirichletRampWindow
