import D5.S3.CharacterSums.DirichletTriangleBound
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-faithful conditional families for the finite-height estimates. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Complex
open _root_.D5.S3.CharacterSums.DirichletCompletion
open _root_.D5.S3.CharacterSums.DirichletTrianglePerron
open _root_.D5.S3.CharacterSums.DirichletTriangleExplicit
open _root_.D5.S3.CharacterSums.DirichletTriangleBound
open _root_.D5.S3.Analytic.Resolvent.PoissonKernelTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.DirichletTriangleBound

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected (K : ℝ) : Realization signature :=
  realize signature (fun _ _ _ => K + 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

namespace Quantitative

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (_hχ : χ.IsPrimitive) (_hne : χ ≠ 1) {x T : ℝ} (_hx : 1 ≤ x) (_hT : 32 < T)
    (_hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ T → χ.LFunction s ≠ 0),
    R.readout () () (characterTriangle χ x) ≤
      (2 * Real.sqrt x + 4 + 2 / x) * (logDeriv (completion χ) 2).re +
        (x + 2 + 3 / x) * tailBound q T +
          (1 - 1 / x) * ‖logDeriv χ.LFunction 2‖ + ‖parityCorrection χ x‖

private theorem rejected_law {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {x T : ℝ} (hx : 1 ≤ x) (hT : 32 < T)
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ T → χ.LFunction s ≠ 0) :
    ¬arena.Law (rejected ((2 * Real.sqrt x + 4 + 2 / x) *
      (logDeriv (completion χ) 2).re + (x + 2 + 3 / x) * tailBound q T +
        (1 - 1 / x) * ‖logDeriv χ.LFunction 2‖ + ‖parityCorrection χ x‖)) := by
  intro h
  have he := h hχ hne hx hT hfree
  change _ + 1 ≤ _ at he
  linarith

def family {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {x T : ℝ} (hx : 1 ≤ x) (hT : 32 < T)
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ T → χ.LFunction s ≠ 0) :
    Registration arena (type_of% @characterTriangle_finite_height) where
  actual := actual
  bridge := by simp only [actual, realize]
  variation := ⟨@characterTriangle_finite_height, _, rejected_law hχ hne hx hT hfree⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual _
    (rejected_law hχ hne hx hT hfree)
  dependence := dependence

def audit {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {x T : ℝ} (hx : 1 ≤ x) (hT : 32 < T)
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ T → χ.LFunction s ≠ 0) :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@characterTriangle_finite_height) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletTriangleBound.characterTriangle_finite_height
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTriangleBound.Quantitative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family hχ hne hx hT hfree⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Quantitative

namespace Prime

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (_hne : χ ≠ 1) (_hp : 10000 ≤ p)
    (_hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0),
    R.readout () () (characterTriangle χ p) ≤
      (331411 / 222750 : ℝ) * Real.sqrt p * Real.log p

private theorem rejected_law (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hne : χ ≠ 1) (hp : 10000 ≤ p)
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    ¬arena.Law (rejected ((331411 / 222750 : ℝ) * Real.sqrt p * Real.log p)) := by
  intro h
  have he := h p χ hne hp hfree
  change _ + 1 ≤ _ at he
  linarith

def family (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hne : χ ≠ 1) (hp : 10000 ≤ p)
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    Registration arena (type_of% @characterTriangle_prime_bound) where
  actual := actual
  bridge := by simp only [actual, realize]
  variation := ⟨@characterTriangle_prime_bound, _, rejected_law p χ hne hp hfree⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual _
    (rejected_law p χ hne hp hfree)
  dependence := dependence

def audit (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hne : χ ≠ 1) (hp : 10000 ≤ p)
    (hfree : ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@characterTriangle_prime_bound) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DirichletTriangleBound.characterTriangle_prime_bound
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTriangleBound.Prime.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family p χ hne hp hfree⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Prime
end Reg.D5.S3.CharacterSums.DirichletTriangleBound
