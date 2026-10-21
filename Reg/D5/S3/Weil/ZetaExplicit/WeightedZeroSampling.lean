import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaExplicit.WeightedZeroSampling
import Reg.Support.DependentFamily

/-! Faithful dependent-family audits of supported reproduction and original sampling. -/

namespace Reg.D5.S3.Weil.ZetaExplicit.WeightedZeroSampling

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Zeta23 Zeta23.WeilEF Zeta23.WeilEF.WeightedZeroSampling LeanInformationAudit MeasureTheory Set
open _root_.D5.S3.Weil.TestFunctions
open scoped FourierTransform ComplexConjugate BigOperators
noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z f => paperFT f ((z.2 : ℂ) + Complex.I * (z.1 : ℂ))) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ z f => paperFT f ((z.2 : ℂ) + Complex.I * (z.1 : ℂ)) + 1) (fun e => nomatch e)

/-- The full support reproduction statement with its actual pointwise readout. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (b : WeilTestFunction) {a : ℝ},
    (∀ x ∈ Ioc (-a) a, b x = 1) →
    ∀ {f : ℝ → ℂ}, MemLp f 2 volume →
    (∀ᵐ x ∂(volume : Measure ℝ), x ∉ Ioc (-a) a → f x = 0) →
    ∀ {β : ℝ}, |β| ≤ 1 / 2 → ∀ t : ℝ,
      (∫ s : ℝ, stripKernel b β (t - s) * paperFT f s) =
        R.readout () ⟨β, t⟩ f

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hplateau : ∀ x ∈ Ioc (-(0 : ℝ)) 0,
      standardTestFunction x = 1 := by simp
  have hbad := h standardTestFunction hplateau
    (f := fun _ => 0) (by simp) (by simp) (β := 0) (by norm_num) 0
  simpa [rejected, realize, paperFT] using hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 0⟩, (fun _ => 0), (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)), ?_⟩
  simp [actual, realize, paperFT, integral_indicator, measurableSet_Ioc]

def sourceRegistration : Registration arena (type_of% (@support_convolution_reproduction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨support_convolution_reproduction, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@support_convolution_reproduction) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaExplicit.WeightedZeroSampling.support_convolution_reproduction
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.WeightedZeroSampling.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ z f => paperFT f ((z.2 : ℂ) + Complex.I * (z.1 : ℂ))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ → ℂ)
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaExplicit.WeightedZeroSampling
    definition := none
    coordinates := #[6, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev samplingSignature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def samplingActual : Realization samplingSignature :=
  realize samplingSignature (fun _ _ f => f) (fun e => nomatch e)

private def compensator : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator
    (fun x => Complex.exp (-Complex.I * gammaOf (0 : ℂ) * (x : ℂ)))

private theorem compensator_transform : paperFT compensator (gammaOf (0 : ℂ)) = 1 := by
  have hfun : (fun x : ℝ => compensator x *
      Complex.exp (Complex.I * gammaOf (0 : ℂ) * (x : ℂ))) =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · simp only [compensator, Set.indicator_of_mem hx]
      rw [← Complex.exp_add]
      have hsum : -Complex.I * gammaOf (0 : ℂ) * (x : ℂ) +
          Complex.I * gammaOf (0 : ℂ) * (x : ℂ) = 0 := by ring
      rw [hsum, Complex.exp_zero]
    · simp [compensator, hx]
  unfold paperFT
  rw [hfun]
  simp [integral_indicator, measurableSet_Ioc]

def samplingRejected : Realization samplingSignature :=
  realize samplingSignature (fun _ _ _ => compensator) (fun e => nomatch e)

/-- Only the exact profile occurrence in the first sample sum is intervened on.
Every original hypothesis and both sample-family conclusions remain in the law. -/
def samplingArena : Arena where
  signature := samplingSignature
  Law R := ∀ (a : ℝ), 0 < a →
    ∃ C_a : ℝ, 0 ≤ C_a ∧ ∀ (Z : Zeta23.ZeroConfig) (A : ℝ), 1 ≤ A →
      (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3)) →
      ∀ f : ℝ → ℂ, MemLp f 2 volume →
      (∀ᵐ x ∂(volume : Measure ℝ), x ∉ Ioc (-a) a → f x = 0) →
      Integrable (fun s : ℝ => Real.log (|s| + 3) *
        Complex.normSq (Zeta23.paperFT f s)) →
      Integrable f ∧
      (Summable (fun ρ : Z.carrier =>
          (Z.mult ρ : ℝ) * Complex.normSq (Zeta23.paperFT f (Zeta23.gammaOf ρ))) ∧
        (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) *
          Complex.normSq (Zeta23.paperFT (R.readout () () f) (Zeta23.gammaOf ρ))) ≤
          C_a * A * Zeta23.WeilEF.totalWeight *
            ∫ s : ℝ, Real.log (|s| + 3) * Complex.normSq (Zeta23.paperFT f s)) ∧
      (Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) *
          Complex.normSq (Zeta23.paperFT f (conj (Zeta23.gammaOf ρ)))) ∧
        (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) *
          Complex.normSq (Zeta23.paperFT f (conj (Zeta23.gammaOf ρ)))) ≤
          C_a * A * Zeta23.WeilEF.totalWeight *
            ∫ s : ℝ, Real.log (|s| + 3) * Complex.normSq (Zeta23.paperFT f s))

private def offLinePair : ZeroConfig where
  carrier := {0, 1}
  mult := fun _ => 1
  one_le_mult := by simp
  strip := by intro ρ hρ; rcases hρ with h | h <;> simp_all
  reflect_mem := by intro ρ hρ; rcases hρ with h | h <;> simp_all [reflect]
  mult_reflect := by simp
  finite_window := fun _ _ => Set.Finite.inter_of_left (Set.toFinite _) _

private theorem offLinePair_local (t : ℝ) :
    (offLinePair.N t (t + 1) : ℝ) ≤ 2 * Real.log (|t| + 3) := by
  have hN : offLinePair.N t (t + 1) ≤ 2 := by
    by_cases ht : t < 0 ∧ 0 ≤ t + 1
    · have hw : offLinePair.window t (t + 1) = {0, 1} := by
        ext z
        simp only [ZeroConfig.window, offLinePair, Set.mem_inter_iff,
          Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, ?_⟩
          rcases h with rfl | rfl <;> simpa using ht
      change (∑ᶠ ρ ∈ offLinePair.window t (t + 1), (1 : ℕ)) ≤ 2
      rw [hw, finsum_mem_insert _ (by simp) (Set.finite_singleton _),
        finsum_mem_singleton]
    · have hw : offLinePair.window t (t + 1) = ∅ := by
        ext z
        simp only [ZeroConfig.window, offLinePair, Set.mem_inter_iff,
          Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h
        rcases h with rfl | rfl <;> simpa using ht
      simp [ZeroConfig.N, hw]
  have hL : 1 ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_d9, abs_nonneg t]
  have hNreal : (offLinePair.N t (t + 1) : ℝ) ≤ (2 : ℝ) := by exact_mod_cast hN
  exact hNreal.trans (by linarith)

private theorem sampling_rejected_law : ¬ samplingArena.Law samplingRejected := by
  classical
  intro h
  obtain ⟨C, _hC, hall⟩ := h 1 (by norm_num)
  have hlog : Integrable (fun s : ℝ => Real.log (|s| + 3) *
      Complex.normSq (paperFT (fun _ => 0) s)) := by simp [paperFT]
  have hout := hall offLinePair 2 (by norm_num) offLinePair_local (fun _ => 0)
    (by simp) (by simp) hlog
  let ρ₀ : offLinePair.carrier := ⟨0, by simp [offLinePair]⟩
  letI : Fintype offLinePair.carrier :=
    (show offLinePair.carrier.Finite by simp [offLinePair]).fintype
  let g : offLinePair.carrier → ℝ := fun ρ =>
    (offLinePair.mult ρ : ℝ) * Complex.normSq (paperFT compensator (gammaOf ρ))
  have hg : Summable g := (hasSum_fintype g).summable
  have hlow := hg.sum_le_tsum ({ρ₀} : Finset offLinePair.carrier)
    (fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
  have hvalue : g ρ₀ = 1 := by
    simp [g, ρ₀, offLinePair, compensator_transform]
  simp only [Finset.sum_singleton, hvalue] at hlow
  have henergy : (∫ s : ℝ, Real.log (|s| + 3) *
      Complex.normSq (paperFT (fun _ => 0) s)) = 0 := by simp [paperFT]
  have hupp := hout.2.1.2
  rw [henergy, mul_zero] at hupp
  change (∑' ρ, g ρ) ≤ 0 at hupp
  linarith

private theorem sampling_actual_dependence : ObservationalDependence samplingSignature samplingActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hzero := congrFun h (0 : ℝ)
  norm_num [samplingActual, realize] at hzero

def samplingSourceRegistration : Registration samplingArena (type_of% (@weighted_zero_sampling_Ioc)) where
  actual := samplingActual
  bridge := Iff.rfl
  variation := ⟨weighted_zero_sampling_Ioc, samplingRejected, sampling_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨samplingRejected, ?_, rfl, sampling_rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro e
      exact nomatch e
  dependence := sampling_actual_dependence

def registration_2 : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@weighted_zero_sampling_Ioc) (type_of% samplingActual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaExplicit.WeightedZeroSampling.weighted_zero_sampling_Ioc
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.WeightedZeroSampling.samplingSourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨samplingArena⟩
  objectArena := .source ⟨samplingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source samplingArena ⟨samplingSourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize samplingSignature (fun _ _ f => f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ → ℂ)
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaExplicit.WeightedZeroSampling
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg", "fn", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms sourceRegistration
#print axioms registration_1
#print axioms registration_2

end
end Reg.D5.S3.Weil.ZetaExplicit.WeightedZeroSampling
