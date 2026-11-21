import LeanInformationAuditInterface.Contract.Registration
import D5.S3.CharacterSums.DyadicPrimeClassCount
import Reg.Support.SingleDependentReadout

/-! Dependence on the interval count in the relative Chebotarev estimates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Real
open _root_.D5.S3.CharacterSums.DyadicPrimeClassCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.DyadicPrimeClassCount

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℝ → ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ m a => classCount m a) (fun e => nomatch e)

/-- These prefix counts follow the nonexceptional main term exactly, but every interval
with positive lower endpoint has zero mass. -/
def incompatible : Realization signature :=
  realize signature (fun _ m _ lo hi =>
    if lo = 0 then logarithmicIntegral hi / (m.totient : ℝ) else 0) (fun e => nomatch e)

private theorem integral_nonneg {t : ℝ} (ht : 2 ≤ t) : 0 ≤ logarithmicIntegral t := by
  apply intervalIntegral.integral_nonneg ht
  intro u hu
  exact div_nonneg zero_le_one (log_nonneg (by linarith [hu.1]))

private theorem incompatible_prefix {m a : ℕ} (hm : 0 < m) (t : ℝ) :
    (m.totient : ℝ) * (incompatible.readout () m a 0 t + 0) = mainTerm 0 (1 / 2) t := by
  have ht : (m.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hm).ne'
  change (m.totient : ℝ) * ((if (0 : ℝ) = 0 then logarithmicIntegral t / m.totient else 0) + 0) = _
  simp [mainTerm]
  field_simp

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨4, 3, 1,?_⟩
  change classCount 4 3 ≠ classCount 4 1
  intro he
  have he' := congrFun (congrFun he 0) 3
  norm_num [classCount, classPrimes] at he'
  exact (by decide : ((Finset.Ioc 0 3).filter (fun p : ℕ => p.Prime ∧ p ≡ 3 [MOD 4])).card ≠
    ((Finset.Ioc 0 3).filter (fun p : ℕ => p.Prime ∧ p ≡ 1 [MOD 4])).card) he'

namespace Endpoint
abbrev arena : Arena where
  signature := signature
  Law V := ∀ {m a : ℕ} {θ : ℤ} {β Y Q s offset : ℝ},
    16 ≤ Y → 1 < Q → Q ≤ Y → 0 < s → (θ = -1 ∨ θ = 0 ∨ θ = 1) → 1 / 2 ≤ β → β < 1 →
    (θ = 1 → s / (Q ^ 2 * log Q) ≤ 1 - β) →
    (∀ t ∈ ({Y, 2 * Y} : Finset ℝ),
       |(m.totient : ℝ) * (V.readout () m a 0 t + offset) - mainTerm θ β t| ≤
        mainTerm θ β t / 100) →
    min 1 s / (8 * Q ^ 2) * (Y / log Y) ≤ (m.totient : ℝ) * V.readout () m a Y (2 * Y)

private theorem incompatible_fails : ¬ arena.Law incompatible := by
  intro h
  have hc := @h 3 1 0 (1 / 2) 16 2 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inr (Or.inl rfl)) (by norm_num) (by norm_num) (by norm_num) (by
      intro t ht
      rw [incompatible_prefix (by decide : 0 < 3), sub_self, abs_zero]
      have ht2 : 2 ≤ t := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        rcases ht with rfl | rfl <;> norm_num
      simp only [mainTerm, Int.cast_zero, zero_mul, sub_zero]
      exact div_nonneg (integral_nonneg ht2) (by norm_num))
  change _ ≤ (_ : ℝ) * (if (16 : ℝ) = 0 then _ else 0) at hc
  norm_num at hc
  have hl := log_pos (by norm_num : (1 : ℝ) < 16)
  exact (not_lt_of_ge hc) (by positivity)


def family : Registration arena (type_of% @dyadic_class_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@dyadic_class_count, incompatible, incompatible_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual incompatible incompatible_fails
  dependence := dependence

noncomputable def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@dyadic_class_count) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DyadicPrimeClassCount.dyadic_class_count
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DyadicPrimeClassCount.Endpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m a => classCount m a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DyadicPrimeClassCount
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg", "fn", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Endpoint

namespace Uniform
abbrev arena : Arena where
  signature := signature
  Law V := ∀ {B A c s : ℝ}, 0 < A → 0 < c → 0 < s →
    cyclotomicEstimate (V.readout ()) B A c s →
    ∃ K D₀ : ℝ, 0 < K ∧ 0 < D₀ ∧ ∀ (m a : ℕ), 3 ≤ m → a.Coprime m → ∀ D : ℝ,
      D₀ ≤ D → (4 * (m : ℝ)) ^ K ≤ D →
      min 1 s / (8 * (m : ℝ) ^ 2) * ((D / 2) / log (D / 2)) ≤
        (m.totient : ℝ) * V.readout () m a (D / 2) D

private theorem incompatible_fails : ¬ arena.Law incompatible := by
  intro h
  have hmodel : cyclotomicEstimate (incompatible.readout ()) 1 1 1 1 := by
    intro m a hm _
    refine ⟨2, 0, 1 / 2, 0, by norm_num, by exact_mod_cast (show 2 ≤ m by omega),
      Or.inr (Or.inl rfl), by norm_num, by norm_num, by norm_num,?_⟩
    intro t ht
    rw [incompatible_prefix (by omega : 0 < m), sub_self, abs_zero]
    rw [rpow_one] at ht
    simp only [mainTerm, Int.cast_zero, zero_mul, sub_zero]
    exact mul_nonneg (by unfold relativeError; positivity) (integral_nonneg ht)
  obtain ⟨K, D₀, _, _, hK⟩ := @h 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) hmodel
  let D := max 32 (max D₀ ((4 * (3 : ℝ)) ^ K))
  have hD : 32 ≤ D := le_max_left _ _
  have hcount := hK 3 1 (by decide) (by decide) D
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
  have hY : 1 < D / 2 := by linarith
  have hzero : incompatible.readout () 3 1 (D / 2) D = 0 := by
    change (if D / 2 = 0 then _ else _) = _
    simp [show D / 2 ≠ 0 by linarith]
  rw [hzero, mul_zero] at hcount
  have hl := log_pos hY
  have hy : 0 < D / 2 := by linarith
  exact (not_lt_of_ge hcount) (by positivity)

def family : Registration arena (type_of% @uniform_dyadic_class_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@uniform_dyadic_class_count, incompatible, incompatible_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual incompatible incompatible_fails
  dependence := dependence

noncomputable def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@uniform_dyadic_class_count) (Realization signature) Unit Unit where
  unitName := .str `D5.S3.CharacterSums.DyadicPrimeClassCount.uniform_dyadic_class_count
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DyadicPrimeClassCount.Uniform.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m a => classCount m a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DyadicPrimeClassCount
    definition := none
    coordinates := #[10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg", "fn",
        "fn"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Uniform

end Reg.D5.S3.CharacterSums.DyadicPrimeClassCount
