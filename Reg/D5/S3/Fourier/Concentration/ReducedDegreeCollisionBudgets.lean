import Reg.D5.S3.Fourier.Concentration.FiniteSpectralPerturbation
import D5.S3.Fourier.Concentration.ReducedDegreeCollisionBudgets

/-! Sensitivity of the vanishing budget to changing the spectrum it evaluates. -/

namespace Reg.D5.S3.Fourier.Concentration.ReducedDegreeCollisionBudgets

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.ReducedDegreeCollisionBudgets
open _root_.D5.S3.Fourier.Concentration.LocalizedCollisionBudgets
open _root_.D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
  (pairRadius weightedPairBudget)
open _root_.D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
  (monomialFrequency monomialWeight diagonal)
open FiniteSpectralPerturbation (actual frequencySignature)
open FiniteSineMissingWindow (sensitivity)
open LeanInformationAudit Finset
open scoped ENNReal

noncomputable section

universe u

private def rejected : Realization frequencySignature.{u} :=
  realize frequencySignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev frequencyArena : Arena where
  signature := frequencySignature.{u}
  Law V := ∀ {J : Type u} [Fintype J] [DecidableEq J]
    (g w radius : J → ℝ) (_ : ∀ j, 0 ≤ w j) {ρ η : ℝ} (_ : 0 < ρ)
    (_ : ∀ j, ρ ≤ radius j) (p k : ℕ) (_ : 0 < k)
    (_ : 0 < η → ∀ (d : ℕ) (a b : J → ℕ), 0 < d → d < k → d ≤ p →
      (∑ j, a j) = d → (∑ j, b j) = d → (∀ j, min (a j) (b j) = 0) →
      η + ∑ j, ((a j : ℝ) + b j) * radius j <
        |monomialFrequency g a - monomialFrequency g b|),
    (η ≤ 0 ∨ p < k → localizedExcessBound (V.readout () ⟨J, g⟩) w radius p η = 0) ∧
      localizedExcessBound g w radius p η ≤
        ENNReal.ofReal (((∑ j, w j) ^ (2 * p) - diagonal w p) *
          min (min 1 (η / ρ)) (Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2) * η /
            (ρ * Real.sqrt (2 * (k : ℝ)))))

private theorem rejected_law : ¬ frequencyArena.{u}.Law rejected := by
  intro law
  let i : ULift.{u} Bool := ULift.up false
  let j : ULift.{u} Bool := ULift.up true
  have hij : i ≠ j := by decide
  have huniv : (univ : Finset (ULift.{u} Bool)) = {i, j} := by
    ext x
    rcases x with ⟨b⟩
    cases b <;> simp [i, j]
  have hsum {A : Type} [AddCommMonoid A] (f : ULift.{u} Bool → A) :
      (∑ x, f x) = f i + f j := by rw [huniv, sum_insert (by simpa using hij), sum_singleton]
  let g : ULift.{u} Bool → ℝ := fun x => if x.down then 4 else 0
  let w : ULift.{u} Bool → ℝ := 1
  have hsep (d : ℕ) (a b : ULift.{u} Bool → ℕ) (hd : 0 < d) (hdk : d < 2)
      (_ : d ≤ 1) (ha : (∑ x, a x) = d) (hb : (∑ x, b x) = d)
      (hmin : ∀ x, min (a x) (b x) = 0) :
      (1 : ℝ) + ∑ x, ((a x : ℝ) + b x) * w x <
        |monomialFrequency g a - monomialFrequency g b| := by
    rw [hsum a] at ha
    rw [hsum b] at hb
    have hdj := hmin j
    have hdi := hmin i
    have hvalues : (a i = 1 ∧ a j = 0 ∧ b i = 0 ∧ b j = 1) ∨
        (a i = 0 ∧ a j = 1 ∧ b i = 1 ∧ b j = 0) := by
      rcases le_total (a i) (b i) with h | h
      · rw [min_eq_left h] at hdi
        rw [min_eq_right (show b j ≤ a j by omega)] at hdj
        exact Or.inr ⟨hdi, by omega, by omega, hdj⟩
      · rw [min_eq_right h] at hdi
        rw [min_eq_left (show a j ≤ b j by omega)] at hdj
        exact Or.inl ⟨by omega, hdj, hdi, by omega⟩
    simp only [monomialFrequency, hsum]
    rcases hvalues with ⟨hai, haj, hbi, hbj⟩ | ⟨hai, haj, hbi, hbj⟩ <;>
      norm_num [hai, haj, hbi, hbj, w, g, i, j]
  have hzero : localizedExcessBound (fun _ : ULift.{u} Bool => 0) w w 1 1 = 0 :=
    (law g w w (fun _ => zero_le_one) (ρ := 1) (η := 1) zero_lt_one
      (fun _ => le_rfl) 1 2 (by decide) (fun _ => hsep)).1 (Or.inr (by decide))
  let a : ULift.{u} Bool → ℕ := fun x => if x.down then 0 else 1
  let b : ULift.{u} Bool → ℕ := fun x => if x.down then 1 else 0
  let s := piAntidiag (univ : Finset (ULift.{u} Bool)) 1
  have ha : a ∈ s := mem_piAntidiag.mpr ⟨by rw [hsum a]; rfl, fun x _ => mem_univ x⟩
  have hb : b ∈ s.erase a := mem_erase.mpr ⟨by
    intro eq
    have := congrFun eq j
    norm_num [a, b, j] at this,
    mem_piAntidiag.mpr ⟨by rw [hsum b]; rfl, fun x _ => mem_univ x⟩⟩
  have hw (m : ULift.{u} Bool → ℕ) : 0 < monomialWeight w m := by
    unfold monomialWeight
    rw [show w = fun _ => 1 from rfl]
    simpa using (show (0 : ℝ) < Nat.multinomial univ m by exact_mod_cast Nat.multinomial_pos univ m)
  have hpair : 0 < localizedPairBound (fun _ => 0) w 1 a b := by
    have hR : pairRadius w a b = 1 := by
      unfold pairRadius
      rw [huniv, sup_insert, sup_singleton]
      norm_num [a, b, i, j, w]
    unfold localizedPairBound
    have hS : (∑ x, (((a x : ℝ) - b x) * w x) ^ 2) = 2 := by
      rw [hsum (fun x => (((a x : ℝ) - b x) * w x) ^ 2)]
      norm_num [a, b, i, j, w]
    change 0 < if |monomialFrequency (fun _ => 0) a - monomialFrequency (fun _ => 0) b| ≤
      1 + ∑ x, |(a x : ℝ) - b x| * w x then _ else 0
    have hreach : |monomialFrequency (fun _ => 0) a - monomialFrequency (fun _ => 0) b| ≤
        1 + ∑ x, |(a x : ℝ) - b x| * w x := by
      simp only [monomialFrequency, mul_zero, sum_const_zero, sub_self, abs_zero, w, Pi.one_apply]
      positivity
    rw [ite_eq_left hreach, hR]
    change 0 < min (min 1 (ENNReal.ofReal (1 / 1))) (ENNReal.ofReal
      (Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2) * 1 /
        Real.sqrt (∑ x, (((a x : ℝ) - b x) * w x) ^ 2)))
    rw [hS]
    have hpos : 0 < Real.exp (1 / 2) * Real.sqrt (15 * Real.pi / 2) * 1 /
        Real.sqrt (2 : ℝ) := by positivity
    exact lt_min (lt_min zero_lt_one (ENNReal.ofReal_pos.mpr (by norm_num))) (ENNReal.ofReal_pos.mpr hpos)
  let term (m n : ULift.{u} Bool → ℕ) :=
    ENNReal.ofReal (monomialWeight w m * monomialWeight w n) *
      localizedPairBound (fun _ => 0) w 1 m n
  have hsel : term a b ≤ ∑ m ∈ s, ∑ n ∈ s.erase m, term m n :=
    (single_le_sum (f := term a) (fun _ _ => zero_le) hb).trans
      (single_le_sum (f := fun m => ∑ n ∈ s.erase m, term m n) (fun _ _ => zero_le) ha)
  change (∑ m ∈ s, ∑ n ∈ s.erase m, term m n) = 0 at hzero
  rw [hzero] at hsel
  have hweight := ENNReal.ofReal_pos.mpr (mul_pos (hw a) (hw b))
  exact (mul_ne_zero hweight.ne' hpair.ne') (le_antisymm hsel zero_le)

def frequencyEvidence :
    Registration frequencyArena.{u}
      (type_of% @localized_excess_le_of_reduced_separation.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@localized_excess_le_of_reduced_separation.{u}, rejected, rejected_law⟩
  sensitivity := sensitivity frequencyArena.Law actual rejected rejected_law
  dependence := (FiniteSpectralPerturbation.frequencyEvidence.{u}).dependence

def frequencyRegistration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@localized_excess_le_of_reduced_separation.{u})
      (Realization frequencySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.ReducedDegreeCollisionBudgets.frequencyUnit
  realizationName :=
    `Reg.D5.S3.Fourier.Concentration.ReducedDegreeCollisionBudgets.frequencyEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨frequencyArena.{u}⟩
  objectArena := .source ⟨frequencyArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source frequencyArena.{u} ⟨frequencyEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize frequencySignature (fun _ q j => q.2 j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.ReducedDegreeCollisionBudgets
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "fn", "arg", "fn", "fn", "fn",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms frequencyRegistration

end

end Reg.D5.S3.Fourier.Concentration.ReducedDegreeCollisionBudgets
