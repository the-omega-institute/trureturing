import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.NonprincipalCharacterGrowth
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Reg.Support.SingleDependentReadout

/-! The observable is the half-totient growth allowance as the evaluation point varies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open _root_.D5.S3.CharacterSums.NonprincipalCharacterGrowth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.NonprincipalCharacterGrowth

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ q (s : ℂ) => (q.totient:ℝ)/2 * ‖s‖ / s.re) (fun e => nomatch e)

def negative : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (_ : χ ≠ 1)
    {s : ℂ} (_ : 0 < s.re), ‖χ.LFunction s‖ ≤ V.readout () q s

private theorem negative_fails : ¬ arena.Law negative := by
  intro h
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (show (-1 : ZMod 3) ≠ 1 by decide)
  have hne : χ ≠ 1 := by
    rintro rfl
    exact hχ (MulChar.one_apply_coe (-1 : (ZMod 3)ˣ))
  have bad := h χ hne (s := 1) (by norm_num)
  change ‖χ.LFunction 1‖ ≤ -1 at bad
  linarith [norm_nonneg (χ.LFunction 1)]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨3, (⟨1, 0⟩ : ℂ), (⟨1, 1⟩ : ℂ), ?_⟩
  norm_num [actual, realize, Complex.norm_def, Complex.normSq_apply,
    Nat.totient_prime Nat.prime_three ]
  nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]

def family : Registration arena (type_of% @nonprincipal_growth) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonprincipal_growth, negative, negative_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual negative negative_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nonprincipal_growth) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.NonprincipalCharacterGrowth.nonprincipal_growth
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.CharacterSums.NonprincipalCharacterGrowth "family"
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
    (fun _ q (s : ℂ) => (q.totient:ℝ)/2 * ‖s‖ / s.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.NonprincipalCharacterGrowth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.CharacterSums.NonprincipalCharacterGrowth
