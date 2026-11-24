import D5.S3.CharacterSums.DirichletTrianglePerron
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The actual integrals, pointwise operations, and integer endpoint are observed. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Complex
open _root_.D5.S3.CharacterSums.DirichletTrianglePerron
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.DirichletTrianglePerron

local instance sourceMeasurableSpace : MeasurableSpace ℝ :=
  Real.measureSpace.toMeasurableSpace

namespace LaplaceIntegrable

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℂ) (fun _ => ℂ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => (fun w : ℂ => (z : ℂ) * w)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (fun _ : ℂ => (1 : ℂ))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (_hs : 1 < s.re),
    IntegrableOn (fun y : ℝ => R.readout () () (Complex.exp (-s * y))
      (characterTriangle χ (Real.exp y))) (Ioi 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1 : DirichletCharacter ℂ 1) (s := 2) (by norm_num)
  change IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioi 0) at hh
  simpa [IntegrableOn, integrable_const_iff, isFiniteMeasure_iff] using hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h (1 : ℂ)
  norm_num [actual, realize] at he

def family : Registration arena (type_of% @characterTriangle_laplace_integrable) where
  actual := actual
  bridge := by simp only [actual, realize]
  variation := ⟨by simpa only [arena, actual, realize]
      using @characterTriangle_laplace_integrable,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@characterTriangle_laplace_integrable) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletTrianglePerron.characterTriangle_laplace_integrable
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTrianglePerron.LaplaceIntegrable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ z => (fun w : ℂ => (z : ℂ) * w)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTrianglePerron
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LaplaceIntegrable

namespace Laplace

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ f => (∫ y : ℝ in Ioi 0, f y) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (_hs : 1 < s.re), R.readout () () (fun y : ℝ => Complex.exp (-s * y) *
      characterTriangle χ (Real.exp y)) = -logDeriv χ.LFunction s / (s * (s + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1 : DirichletCharacter ℂ 1) (s := 2) (by norm_num)
  have he := characterTriangle_laplace (1 : DirichletCharacter ℂ 1)
    (s := 2) (by norm_num)
  change _ + 1 = _ at hh
  rw [he] at hh
  have hz : (1 : ℂ) = 0 := by linear_combination hh
  exact one_ne_zero hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun y : ℝ => Complex.exp ((-1 : ℂ) * y)), ?_⟩
  change (∫ y : ℝ in Ioi 0, (0 : ℂ)) ≠
    ∫ y : ℝ in Ioi 0, Complex.exp ((-1 : ℂ) * y)
  rw [integral_zero, integral_exp_mul_complex_Ioi (by norm_num)]
  norm_num

def family : Registration arena (type_of% @characterTriangle_laplace) where
  actual := actual
  bridge := by simp only [actual, realize]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
      using @characterTriangle_laplace,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@characterTriangle_laplace) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.CharacterSums.DirichletTrianglePerron.characterTriangle_laplace.__information_unit
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTrianglePerron.Laplace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
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
    owner := `D5.S3.CharacterSums.DirichletTrianglePerron
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Laplace

namespace PerronIntegrable

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℂ) (fun _ => ℂ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => (fun w : ℂ => (z : ℂ) / w)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (fun _ : ℂ => (1 : ℂ))) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x c : ℝ}
    (_hx : 0 ≤ x) (_hc : 1 < c), Integrable (fun t : ℝ => R.readout () ()
      (-logDeriv χ.LFunction ((c : ℂ) + (t : ℂ) * I) *
        (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
      (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1 : DirichletCharacter ℂ 1) (x := 1) (c := 2)
    (by norm_num) (by norm_num)
  change Integrable (fun _ : ℝ => (1 : ℂ)) at hh
  simpa [integrable_const_iff, isFiniteMeasure_iff] using hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h (1 : ℂ)
  norm_num [actual, realize] at he

def family : Registration arena (type_of% @trianglePerronIntegrand_integrable) where
  actual := actual
  bridge := by simp only [actual, realize]
  variation := ⟨by simpa only [arena, actual, realize]
      using @trianglePerronIntegrand_integrable,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@trianglePerronIntegrand_integrable) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.CharacterSums.DirichletTrianglePerron.trianglePerronIntegrand_integrable
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTrianglePerron.PerronIntegrable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ z => (fun w : ℂ => (z : ℂ) / w)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTrianglePerron
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PerronIntegrable

namespace Perron

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ f => ∫ y : ℝ, f y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ f => (∫ y : ℝ, f y) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x c : ℝ}
    (_hx : 0 ≤ x) (_hc : 1 < c), characterTriangle χ x =
      (2 * (Real.pi : ℂ))⁻¹ * R.readout () () (trianglePerronIntegrand χ x c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (1 : DirichletCharacter ℂ 1) (x := 1) (c := 2) (by norm_num)
    (by norm_num)
  have he := characterTriangle_perron (1 : DirichletCharacter ℂ 1)
    (x := 1) (c := 2) (by norm_num) (by norm_num)
  change _ = (2 * (Real.pi : ℂ))⁻¹ * (_ + 1) at hh
  have hz : (2 * (Real.pi : ℂ))⁻¹ = 0 := by linear_combination he - hh
  exact inv_ne_zero (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (Ioc (0 : ℝ) 1).indicator (fun _ => 1), ?_⟩
  simp [actual, realize, integral_indicator measurableSet_Ioc]

def family : Registration arena (type_of% @characterTriangle_perron) where
  actual := actual
  bridge := by simp only [actual, realize]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
      using @characterTriangle_perron,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@characterTriangle_perron) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.CharacterSums.DirichletTrianglePerron.characterTriangle_perron.__information_unit
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTrianglePerron.Perron.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => ∫ y : ℝ, f y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTrianglePerron
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Perron

namespace Endpoint

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ p : ℕ, DirichletCharacter ℂ p) (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ p x => characterTriangle p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p x => characterTriangle p.2 x + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) (χ : DirichletCharacter ℂ p),
    R.readout () ⟨p, χ⟩ (p : ℝ) =
      _root_.D5.S3.Arith.PrimitiveRoot.CharacterSieve.smoothedCharacterSum p χ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 1
  have he := characterTriangle_nat 1 1
  change _ + 1 = _ at hh
  rw [he] at hh
  have hz : (1 : ℂ) = 0 := by linear_combination hh
  exact one_ne_zero hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 3, ?_⟩
  change characterTriangle (1 : DirichletCharacter ℂ 1) 0 ≠ characterTriangle 1 3
  have hχ (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  have hI : Finset.Icc 1 (3 : ℕ) = {1, 2, 3} := by decide
  have hΛ := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  intro h
  have hr := congrArg Complex.re h
  norm_num [characterTriangle, hI, hχ, hΛ, Complex.log_re] at hr

def family : Registration arena (type_of% @characterTriangle_nat) where
  actual := actual
  bridge := by simp only [actual, realize]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
      using @characterTriangle_nat,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@characterTriangle_nat) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.CharacterSums.DirichletTrianglePerron.characterTriangle_nat.__information_unit
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTrianglePerron.Endpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => characterTriangle p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTrianglePerron
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Endpoint

end Reg.D5.S3.CharacterSums.DirichletTrianglePerron
