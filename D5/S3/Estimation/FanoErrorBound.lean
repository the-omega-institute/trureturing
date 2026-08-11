/- GID: D5/S3/Estimation/FanoErrorBound
   generality: G
   mirror-B: D5/B/S3/Estimation/FanoErrorBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Invert finite Fano inequalities into estimator-error lower bounds. -/

/- Library-search audit trail (2026-08-12):
   * Pinned mathlib searches covered Fano/error-probability lower bounds, mutual information
     next to estimator error, and the order lemmas needed to divide. No Fano inequality or
     information-theoretic estimator-error floor was found. The ordered-field theorem
     `div_le_iff₀` is the direct quotient step used below.
   * The actual working tree under `D5/` was searched for Fano/error lower bounds, mutual
     information next to error, and inverted forms. Only the frozen inequalities in `Fano.lean`
     and `FanoSharp.lean` were found; there was no error-probability inversion.
-/

import D5.S3.Estimation.FanoSharp
import D5.S3.Entropy.EntropyEquality
import D5.S3.Entropy.MutualInformationEntropy

/-!
# Error-probability lower bounds from finite Fano inequalities

For `p : Y × X → ℝ`, the first coordinate is the observation and the second is the
hidden parameter. Hence `conditionalEntropy p` is `H(X | Y)`, while the hidden-parameter
marginal is obtained by swapping the coordinates before applying `marginal`.

The primary theorem keeps the factor `log (card X)` on the error mass, so it applies even to
the singleton case and requires no positivity hypothesis for division. The quotient theorem
adds the genuine condition `2 ≤ card X`. A sharp companion uses `log (card X - 1)` and is
strictly stronger when its numerator is positive and `card X ≥ 3`; it does not uniformly
improve a negative, already-vacuous quotient floor.

Mathematically, this file is a re-parameterisation of the frozen Fano inequalities, not a new
inequality. Its substance is limited to reversing the direction from residual uncertainty to
estimation error, proving the error mass lies in `[0, 1]` so the binary entropy bound applies,
and specializing the hidden marginal to a uniform prior.
-/

namespace D5.S3.Estimation.FanoErrorBound

open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.EntropyEquality
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.MutualInformation
open D5.S3.Entropy.MutualInformationEntropy
open D5.S3.Estimation.Fano
open D5.S3.Estimation.FanoSharp

open Classical in
/-- Primary Fano inversion: every estimator's error mass times `log (card X)` is at least the
hidden-parameter entropy left unexplained by the observation, minus the binary entropy cap. -/
theorem fano_error_product_lower_bound {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1) :
    shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
        mutualInformation p - Real.log 2 ≤
      (∑ z, if g z.1 ≠ z.2 then p z else 0) * Real.log (Fintype.card X) := by
  classical
  let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
  change shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
      mutualInformation p - Real.log 2 ≤ e * Real.log (Fintype.card X)
  have he_nonneg : 0 ≤ e := by
    dsimp only [e]
    exact Finset.sum_nonneg fun z _ => by
      by_cases hz : g z.1 ≠ z.2 <;> simp [hz, hp.1 z]
  have he_le_one : e ≤ 1 := by
    calc
      e ≤ ∑ z, p z := by
        dsimp only [e]
        exact Finset.sum_le_sum fun z _ => by
          by_cases hz : g z.1 ≠ z.2 <;> simp [hz, hp.1 z]
      _ = 1 := hp.2
  have hbinary :
      (∀ b : Bool, 0 ≤ if b then e else 1 - e) ∧
        ∑ b : Bool, (if b then e else 1 - e) = 1 := by
    constructor
    · intro b
      cases b <;> simp [he_nonneg, sub_nonneg.mpr he_le_one]
    · simp
  have hbinary_entropy :
      shannonEntropy (fun b : Bool ↦ if b then e else 1 - e) ≤ Real.log 2 := by
    simpa using entropy_le_log_card (fun b : Bool ↦ if b then e else 1 - e) hbinary
  have hfano :
      conditionalEntropy p ≤
        shannonEntropy (fun b : Bool ↦ if b then e else 1 - e) +
          e * Real.log (Fintype.card X) := by
    simpa only [e] using fano_inequality_weak p g hp
  have hmi_entropy := mutual_information_eq_entropy_sub p hp.1
  have hchain := entropy_chain_rule p hp.1
  have hmi_conditional :
      mutualInformation p =
        shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
          conditionalEntropy p := by
    linarith
  linarith

open Classical in
/-- Quotient form of the primary Fano inversion. The cardinality hypothesis is exactly what
makes `log (card X)` positive. -/
theorem fano_error_probability_lower_bound {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hX : 2 ≤ Fintype.card X) :
    (shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
        mutualInformation p - Real.log 2) / Real.log (Fintype.card X) ≤
      ∑ z, if g z.1 ≠ z.2 then p z else 0 := by
  have hcard_gt_one : 1 < Fintype.card X := by omega
  have hcard_real_gt_one : (1 : ℝ) < Fintype.card X := by exact_mod_cast hcard_gt_one
  have hlog_pos : 0 < Real.log (Fintype.card X) := Real.log_pos hcard_real_gt_one
  exact (div_le_iff₀ hlog_pos).2 (fano_error_product_lower_bound p g hp)

open Classical in
/-- Sharp Fano inversion. In the positive-numerator regime this improves `log (card X)` to
`log (card X - 1)`; at two hypotheses the coefficient is the totalized value `log 1 = 0`. -/
theorem fano_error_product_lower_bound_sharp {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hX : 2 ≤ Fintype.card X) :
    shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
        mutualInformation p - Real.log 2 ≤
      (∑ z, if g z.1 ≠ z.2 then p z else 0) *
        Real.log ((Fintype.card X : ℝ) - 1) := by
  classical
  let e : ℝ := ∑ z, if g z.1 ≠ z.2 then p z else 0
  change shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
      mutualInformation p - Real.log 2 ≤
        e * Real.log ((Fintype.card X : ℝ) - 1)
  have he_nonneg : 0 ≤ e := by
    dsimp only [e]
    exact Finset.sum_nonneg fun z _ => by
      by_cases hz : g z.1 ≠ z.2 <;> simp [hz, hp.1 z]
  have he_le_one : e ≤ 1 := by
    calc
      e ≤ ∑ z, p z := by
        dsimp only [e]
        exact Finset.sum_le_sum fun z _ => by
          by_cases hz : g z.1 ≠ z.2 <;> simp [hz, hp.1 z]
      _ = 1 := hp.2
  have hbinary :
      (∀ b : Bool, 0 ≤ if b then e else 1 - e) ∧
        ∑ b : Bool, (if b then e else 1 - e) = 1 := by
    constructor
    · intro b
      cases b <;> simp [he_nonneg, sub_nonneg.mpr he_le_one]
    · simp
  have hbinary_entropy :
      shannonEntropy (fun b : Bool ↦ if b then e else 1 - e) ≤ Real.log 2 := by
    simpa using entropy_le_log_card (fun b : Bool ↦ if b then e else 1 - e) hbinary
  have hcard_ne_one : Fintype.card X ≠ 1 := by omega
  have hfano :
      conditionalEntropy p ≤
        shannonEntropy (fun b : Bool ↦ if b then e else 1 - e) +
          e * Real.log ((Fintype.card X : ℝ) - 1) := by
    simpa only [e] using fano_inequality_sharp p g hp hcard_ne_one
  have hmi_entropy := mutual_information_eq_entropy_sub p hp.1
  have hchain := entropy_chain_rule p hp.1
  have hmi_conditional :
      mutualInformation p =
        shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
          conditionalEntropy p := by
    linarith
  linarith

open Classical in
/-- Quotient form of the sharp inversion. Three hypotheses are required because
`log (card X - 1)` is zero when `card X = 2`. -/
theorem fano_error_probability_lower_bound_sharp {Y X : Type*}
    [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hX : 3 ≤ Fintype.card X) :
    (shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
        mutualInformation p - Real.log 2) /
          Real.log ((Fintype.card X : ℝ) - 1) ≤
      ∑ z, if g z.1 ≠ z.2 then p z else 0 := by
  have hcard_gt_two : 2 < Fintype.card X := by omega
  have hcard_real_gt_two : (2 : ℝ) < Fintype.card X := by exact_mod_cast hcard_gt_two
  have hdenom_gt_one : (1 : ℝ) < (Fintype.card X : ℝ) - 1 := by linarith
  have hlog_pos : 0 < Real.log ((Fintype.card X : ℝ) - 1) :=
    Real.log_pos hdenom_gt_one
  exact (div_le_iff₀ hlog_pos).2
    (fano_error_product_lower_bound_sharp p g hp (by omega))

open Classical in
/-- Standard uniform-prior Fano bound: identifying one of `card X` equiprobable hypotheses
requires mutual information comparable to `log (card X)` for small error. -/
theorem fano_error_probability_lower_bound_uniform {Y X : Type*}
    [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hX : 2 ≤ Fintype.card X)
    (huniform :
      marginal (fun r : X × Y ↦ p (r.2, r.1)) =
        fun _ ↦ (Fintype.card X : ℝ)⁻¹) :
    1 - (mutualInformation p + Real.log 2) / Real.log (Fintype.card X) ≤
      ∑ z, if g z.1 ≠ z.2 then p z else 0 := by
  letI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hprior_nonneg :
      ∀ x, 0 ≤ marginal (fun r : X × Y ↦ p (r.2, r.1)) x := by
    intro x
    rw [marginal]
    exact Finset.sum_nonneg fun y _ ↦ hp.1 (y, x)
  have hprior_sum :
      ∑ x, marginal (fun r : X × Y ↦ p (r.2, r.1)) x = 1 := by
    simp only [marginal]
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    exact hp.2
  have hprior_entropy :
      shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) =
        Real.log (Fintype.card X) :=
    (entropy_eq_log_card_iff_uniform
      (marginal (fun r : X × Y ↦ p (r.2, r.1)))
      ⟨hprior_nonneg, hprior_sum⟩).2 huniform
  have hgeneral := fano_error_probability_lower_bound p g hp hX
  rw [hprior_entropy] at hgeneral
  have hcard_gt_one : 1 < Fintype.card X := by omega
  have hcard_real_gt_one : (1 : ℝ) < Fintype.card X := by exact_mod_cast hcard_gt_one
  have hlog_ne : Real.log (Fintype.card X) ≠ 0 :=
    (Real.log_pos hcard_real_gt_one).ne'
  calc
    1 - (mutualInformation p + Real.log 2) / Real.log (Fintype.card X) =
        (Real.log (Fintype.card X) - mutualInformation p - Real.log 2) /
          Real.log (Fintype.card X) := by
            field_simp [hlog_ne]
            ring
    _ ≤ ∑ z, if g z.1 ≠ z.2 then p z else 0 := hgeneral

open Classical in
/- Neither reflexivity nor simplification proves the primary product inversion. -/
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1) :
    shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
        mutualInformation p - Real.log 2 ≤
      (∑ z, if g z.1 ≠ z.2 then p z else 0) * Real.log (Fintype.card X) := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact fano_error_product_lower_bound p g hp

open Classical in
/- Neither reflexivity nor simplification proves the primary quotient inversion. -/
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hX : 2 ≤ Fintype.card X) :
    (shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
        mutualInformation p - Real.log 2) / Real.log (Fintype.card X) ≤
      ∑ z, if g z.1 ≠ z.2 then p z else 0 := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact fano_error_probability_lower_bound p g hp hX

open Classical in
/- Neither reflexivity nor simplification proves the sharp product inversion. -/
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hX : 2 ≤ Fintype.card X) :
    shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
        mutualInformation p - Real.log 2 ≤
      (∑ z, if g z.1 ≠ z.2 then p z else 0) *
        Real.log ((Fintype.card X : ℝ) - 1) := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact fano_error_product_lower_bound_sharp p g hp hX

open Classical in
/- Neither reflexivity nor simplification proves the sharp quotient inversion. -/
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hX : 3 ≤ Fintype.card X) :
    (shannonEntropy (marginal (fun r : X × Y ↦ p (r.2, r.1))) -
        mutualInformation p - Real.log 2) /
          Real.log ((Fintype.card X : ℝ) - 1) ≤
      ∑ z, if g z.1 ≠ z.2 then p z else 0 := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact fano_error_probability_lower_bound_sharp p g hp hX

open Classical in
/- Neither reflexivity nor simplification proves the uniform-prior corollary. -/
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hX : 2 ≤ Fintype.card X)
    (huniform :
      marginal (fun r : X × Y ↦ p (r.2, r.1)) =
        fun _ ↦ (Fintype.card X : ℝ)⁻¹) :
    1 - (mutualInformation p + Real.log 2) / Real.log (Fintype.card X) ≤
      ∑ z, if g z.1 ≠ z.2 then p z else 0 := by
  fail_if_success rfl
  fail_if_success (simp; done)
  exact fano_error_probability_lower_bound_uniform p g hp hX huniform

/- At `card X = 4` and zero mutual information, the quoted floor is the informative value
`1/2`: `1 - (0 + log 2) / log 4 = 1 - log 2 / (2 log 2) = 1/2`. -/
example :
    1 - ((0 : ℝ) + Real.log 2) / Real.log 4 = 1 / 2 := by
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog_two_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [hlog_four]
  field_simp [hlog_two_ne]
  ring

/- At `card X = 4` and mutual information `log 4`, the floor is `-1/2`, so it imposes no
constraint beyond the independently proved nonnegativity of the error probability. -/
example :
    1 - (Real.log 4 + Real.log 2) / Real.log 4 = -(1 / 2 : ℝ) := by
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog_two_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [hlog_four]
  field_simp [hlog_two_ne]
  ring

/- At two hypotheses the uniform Fano floor is nonpositive for every admissible mutual
information value, so it cannot contradict a stronger positive total-variation lower bound. -/
example (I : ℝ) (hI : 0 ≤ I) :
    1 - (I + Real.log 2) / Real.log 2 ≤ 0 := by
  apply sub_nonpos.mpr
  exact (one_le_div (Real.log_pos (by norm_num))).2 (by linarith)

#print axioms fano_error_product_lower_bound
#print axioms fano_error_probability_lower_bound
#print axioms fano_error_product_lower_bound_sharp
#print axioms fano_error_probability_lower_bound_sharp
#print axioms fano_error_probability_lower_bound_uniform

end D5.S3.Estimation.FanoErrorBound
