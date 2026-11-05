import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaExplicit.ExponentialStripSampling
import Reg.D5.S3.Weil.ZetaExplicit.WeightedZeroSampling
import Reg.Support.DependentFamily
import Batteries.Tactic.OpenPrivate

/-! Faithful function-readout audit for noncompact exponential sampling. -/

namespace Reg.D5.S3.Weil.ZetaExplicit.ExponentialStripSampling

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Zeta23 Zeta23.WeilEF Zeta23.WeilEF.ExponentialStripSampling
open LeanInformationAudit MeasureTheory Set
open scoped FourierTransform ComplexConjugate BigOperators
noncomputable section

open private compensator compensator_transform offLinePair offLinePair_local from
  Reg.D5.S3.Weil.ZetaExplicit.WeightedZeroSampling

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a h => fun x : ℝ =>
    Complex.exp ((-a * |x| : ℝ) : ℂ) * h x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => compensator) (fun e => nomatch e)

/-- The full two-family theorem is retained. Only the complete profile
function inside the first sum upper bound is intervened on. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ), 1 / 2 < a →
    ∃ C_a : ℝ, 0 ≤ C_a ∧ ∀ (Z : Zeta23.ZeroConfig) (A : ℝ), 1 ≤ A →
      (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3)) →
      ∀ h : ℝ → ℂ, Integrable h →
      Integrable (fun s : ℝ => Real.log (|s| + 3) *
        Complex.normSq (Zeta23.paperFT h s)) →
      (Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) *
          Complex.normSq (Zeta23.paperFT
            (fun x : ℝ => Complex.exp ((-a * |x| : ℝ) : ℂ) * h x) (Zeta23.gammaOf ρ))) ∧
        (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * Complex.normSq (Zeta23.paperFT
          (R.readout () a h) (Zeta23.gammaOf ρ))) ≤
          C_a * A * Zeta23.WeilEF.totalWeight *
            ∫ s : ℝ, Real.log (|s| + 3) * Complex.normSq (Zeta23.paperFT h s)) ∧
      (Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) *
          Complex.normSq (Zeta23.paperFT
            (fun x : ℝ => Complex.exp ((-a * |x| : ℝ) : ℂ) * h x)
              (conj (Zeta23.gammaOf ρ)))) ∧
        (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * Complex.normSq (Zeta23.paperFT
          (fun x : ℝ => Complex.exp ((-a * |x| : ℝ) : ℂ) * h x)
            (conj (Zeta23.gammaOf ρ)))) ≤
          C_a * A * Zeta23.WeilEF.totalWeight *
            ∫ s : ℝ, Real.log (|s| + 3) * Complex.normSq (Zeta23.paperFT h s))

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  obtain ⟨C, _hC, hall⟩ := h 1 (by norm_num)
  have hlog : Integrable (fun s : ℝ => Real.log (|s| + 3) *
      Complex.normSq (paperFT (fun _ => 0) s)) := by simp [paperFT]
  have hout := hall offLinePair 2 (by norm_num) offLinePair_local
    (fun _ => 0) (by simp) hlog
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
  have hupp := hout.1.2
  rw [henergy, mul_zero] at hupp
  change (∑' ρ, g ρ) ≤ 0 at hupp
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hzero := congrFun h (0 : ℝ)
  norm_num [actual, realize] at hzero

def sourceRegistration : Registration arena (type_of% (@weighted_zero_sampling_exponential)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_zero_sampling_exponential, rejected, rejected_law⟩
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
    (@weighted_zero_sampling_exponential) (type_of% actual) Type Unit := {
  unitName :=
    `Reg.D5.S3.Weil.ZetaExplicit.ExponentialStripSampling.weighted_zero_sampling_exponential
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.ExponentialStripSampling.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a h => fun x : ℝ =>
    Complex.exp ((-a * |x| : ℝ) : ℂ) * h x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaExplicit.ExponentialStripSampling
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg",
        "fn", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms sourceRegistration

end

end Reg.D5.S3.Weil.ZetaExplicit.ExponentialStripSampling
