import Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
import D5.S3.Fourier.Concentration.OverlapPerturbationBudget

/-! Pointwise radii in the denominator of the inverse-scale sum. -/

namespace Reg.D5.S3.Fourier.Concentration.OverlapPerturbationBudget

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.OverlapPerturbationBudget
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialWeight diagonal)
open _root_.D5.S3.Fourier.Concentration.FiniteSincCollisionMoment (monomialWeight_nonneg)
open FiniteSpectralPerturbation (frequencySignature actual)
open FiniteSineMissingWindow (sensitivity)
open LeanInformationAudit Finset

noncomputable section

universe u

private def smallRadiusReadout : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ _ _ => 1 / 100) (fun e => nomatch e)

abbrev radiusArena : Arena where
  signature := frequencySignature.{u}
  Law A := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (w radius : J → ℝ) (_ : ∀ j, 0 ≤ w j) {ρ : ℝ} (_ : 0 < ρ)
    (_ : ∀ j, ρ ≤ radius j) (p k : ℕ) (_ : k ≤ p),
    (∑ m ∈ piAntidiag univ p, ∑ n ∈ (piAntidiag univ p).erase m,
      monomialWeight w m * monomialWeight w n /
        Real.sqrt (∑ j, (((m j : ℝ) - n j) * A.readout () ⟨J, radius⟩ j) ^ 2)) ≤
      ((∑ j, w j) ^ (2 * p) - diagonal w p) /
          (ρ * Real.sqrt (2 * ((p - k + 1 : ℕ) : ℝ))) +
        (min ((Nat.choose p k : ℝ) ^ 2 * (∑ j, w j) ^ (2 * (p - k)) * diagonal w k)
          ((∑ j, w j) ^ (2 * p)) - diagonal w p) *
          ((ρ * Real.sqrt 2)⁻¹ - (ρ * Real.sqrt (2 * ((p - k + 1 : ℕ) : ℝ)))⁻¹)

private theorem sum_liftBool {A : Type*} [AddCommMonoid A] (f : ULift.{u} Bool → A) :
    (∑ j, f j) = f (ULift.up false) + f (ULift.up true) := by
  have h : (univ : Finset (ULift.{u} Bool)) = {ULift.up false, ULift.up true} := by
    ext x
    rcases x with ⟨b⟩
    cases b <;> simp
  rw [h, sum_insert (by decide), sum_singleton]

private theorem unit_weight_of_degree_one {J : Type*} [Fintype J] (m : J → ℕ)
    (hm : (∑ j, m j) = 1) : monomialWeight (fun _ => 1) m = 1 := by
  have hfac (j : J) : (m j).factorial = 1 := by
    have hle : m j ≤ 1 := by
      rw [← hm]
      exact single_le_sum (fun i _ => Nat.zero_le (m i)) (mem_univ j)
    interval_cases h : m j <;> norm_num
  have hprod : (∏ j, (m j).factorial) = 1 := by simp [hfac]
  simp [monomialWeight, Nat.multinomial, hm, hprod]

private theorem smallRadius_fails : ¬ radiusArena.{u}.Law smallRadiusReadout := by
  intro law
  let m (j : ULift.{u} Bool) := if j.down then 0 else 1
  let n (j : ULift.{u} Bool) := if j.down then 1 else 0
  let s := piAntidiag (univ : Finset (ULift.{u} Bool)) 1
  let w : ULift.{u} Bool → ℝ := 1
  let term (a b : ULift.{u} Bool → ℕ) :=
    monomialWeight w a * monomialWeight w b /
      Real.sqrt (∑ j, (((a j : ℝ) - b j) * (1 / 100 : ℝ)) ^ 2)
  have hm : (∑ j, m j) = 1 := by rw [sum_liftBool]; rfl
  have hn : (∑ j, n j) = 1 := by rw [sum_liftBool]; rfl
  have hne : n ≠ m := by
    intro heq
    have h := congrFun heq (ULift.up true)
    norm_num [m, n] at h
  have hms : m ∈ s := mem_piAntidiag.mpr ⟨hm, fun _ _ => mem_univ _⟩
  have hns : n ∈ s.erase m :=
    mem_erase.mpr ⟨hne, mem_piAntidiag.mpr ⟨hn, fun _ _ => mem_univ _⟩⟩
  have hterm (a b : ULift.{u} Bool → ℕ) : 0 ≤ term a b :=
    div_nonneg (mul_nonneg (monomialWeight_nonneg w (by intro; exact zero_le_one) a)
      (monomialWeight_nonneg w (by intro; exact zero_le_one) b)) (Real.sqrt_nonneg _)
  have hsel : term m n ≤ ∑ a ∈ s, ∑ b ∈ s.erase a, term a b :=
    (single_le_sum (fun b _ => hterm m b) hns).trans
      (single_le_sum (fun a _ => sum_nonneg (fun b _ => hterm a b)) hms)
  have h := law (J := ULift.{u} Bool) w 1 (fun _ => zero_le_one) (ρ := 1)
    zero_lt_one (fun _ => le_rfl) 1 0 (by simp)
  change (∑ a ∈ s, ∑ b ∈ s.erase a, term a b) ≤ _ at h
  have hbad := hsel.trans h
  have hW : (∑ j, w j) = 2 := by rw [sum_liftBool]; norm_num [w]
  have hD0 : diagonal w 0 = 1 := by simp [diagonal, monomialWeight, Nat.multinomial]
  have hD1 : 0 ≤ diagonal w 1 := sum_nonneg fun _ _ => sq_nonneg _
  rw [hW, hD0] at hbad
  have hwM : monomialWeight w m = 1 := unit_weight_of_degree_one m hm
  have hwN : monomialWeight w n = 1 := unit_weight_of_degree_one n hn
  have hsum : (∑ j, (((m j : ℝ) - n j) * (1 / 100 : ℝ)) ^ 2) = 2 / 100 ^ 2 := by
    rw [sum_liftBool]
    norm_num [m, n]
  dsimp [term] at hbad
  rw [hwM, hwN, hsum, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 100)] at hbad
  norm_num [show (2 * 2 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at hbad
  have hS : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hle : 100 / √2 ≤ (4 - diagonal w 1) / √2 := by
    refine hbad.trans_eq ?_
    change (4 - diagonal w 1) / 2 + (4 - diagonal w 1) * ((√2)⁻¹ - 1 / 2) = _
    ring
  have := (div_le_div_iff_of_pos_right hS).mp hle
  linarith

def radiusEvidence :
    Registration radiusArena.{u} (type_of% @weighted_inverse_scale_le_of_overlap.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_inverse_scale_le_of_overlap.{u}, smallRadiusReadout, smallRadius_fails⟩
  sensitivity := sensitivity radiusArena.Law actual smallRadiusReadout smallRadius_fails
  dependence := (FiniteSpectralPerturbation.frequencyEvidence.{u}).dependence

def radiusRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@weighted_inverse_scale_le_of_overlap.{u})
      (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.OverlapPerturbationBudget.radiusUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.OverlapPerturbationBudget.radiusEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨radiusArena.{u}⟩
  objectArena := .source ⟨radiusArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source radiusArena.{u} ⟨radiusEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.OverlapPerturbationBudget
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "arg", "body", "arg", "body", "arg", "arg",
        "arg", "body", "fn", "arg", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms radiusRegistration

end

end Reg.D5.S3.Fourier.Concentration.OverlapPerturbationBudget
