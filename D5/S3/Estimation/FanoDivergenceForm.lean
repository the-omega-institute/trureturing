/- GID: D5/S3/Estimation/FanoDivergenceForm
   generality: G
   mirror-B: D5/B/S3/Estimation/FanoDivergenceForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive arbitrary-reference divergence and hypothesis-counting forms of finite Fano. -/

import D5.S3.Estimation.FanoErrorBound
import D5.S3.Entropy.Feedback.DemonIdentity
import D5.S3.Divergence.GrandmotherTheorem

/-!
# Divergence-reference and hypothesis-counting forms of finite Fano

For `p : Y × X → ℝ`, the first coordinate is the observation and the second is the hidden
hypothesis. The arbitrary reference `u` therefore lives on `Y`, while the other factor in the
product reference is the swapped second-coordinate marginal on `X`.

The any-reference mutual-information bound is deliberately a thin, one-line consequence of the
frozen demon identity once Gibbs nonnegativity is available. Its important point is the tightened
hypothesis: the identity needs only strict positivity of `u`, but discarding
`klDivergence (marginal p) u` needs `u` to be normalized too. Without normalization this finite
real-valued KL can be negative (for example, replacing a positive probability law `v` by `2 * v`
subtracts `log 2`), so the inequality does not follow. Strict positivity supplies nonnegativity and
discrete absolute continuity; normalization supplies the missing distribution hypothesis of
`kl_divergence_nonneg`.

The family is attained by choosing `u = marginal p`. The existential theorem records not just the
equality, which is definitionally the product-of-own-marginals definition of mutual information,
but also admissibility of that witness. Normalization follows from the joint law; strict positivity
must be assumed separately. If the observation marginal has zeros, the equality still holds as an
identity, but this witness lies outside the strictly-positive reference family used by the bound.

The substantive change of direction is the counting form: it bounds `log (card X)` at a prescribed
error level. Its product form has no `ε < 1` side condition and includes the singleton case. Only
the quotient form needs `ε < 1`, exactly to make division by `1 - ε` order-preserving. Thus the
identity-to-inequality step is easy; the hypothesis tightening, the admissible attaining witness,
and the side-condition-free counting orientation are the content of this file.
-/

/- Library-search audit trail (2026-08-12):
   * Pinned mathlib searches covered `mutualInformation`, `mutualInfo`, mutual-information
     variational/reference bounds, divergence variational formulae, and the order lemmas used to
     multiply and divide inequalities. No finite mutual-information definition or any-reference
     theorem bridging to this repository's real-valued finite KL was found. The reusable order
     facts are `mul_le_mul_of_nonneg_right`, `le_div_iff₀`,
     `div_le_div_iff_of_pos_right`, and `Real.log_pos`.
   * The actual working tree under `D5/` was searched for both inequality orientations joining
     `mutualInformation` and `klDivergence`, divergence-form Fano bounds, counting/cardinality
     forms, and hypothesis-resolution language. Only `demon_average_divergence_eq` matched the
     any-reference pattern; no any-reference inequality, divergence Fano form, or counting form
     was found.
-/

namespace D5.S3.Estimation.FanoDivergenceForm

open D5.S3.Divergence.ClassicalDPI
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.Feedback.DemonIdentity
open D5.S3.Entropy.MutualInformation
open D5.S3.Estimation.FanoErrorBound
open D5.S3.Divergence.GrandmotherTheorem

open Classical in
/-- Mutual information is at most joint KL to the product of any strictly positive normalized
observation reference and the hidden marginal. After the frozen demon identity, the inequality is
just Gibbs nonnegativity; normalization is essential for that final step. -/
theorem mutual_information_le_product_reference_divergence
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (u : Y → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hu : ∀ y, 0 < u y) (hu_sum : ∑ y, u y = 1) :
    mutualInformation p ≤
      klDivergence p
        (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) := by
  classical
  have hmarginal_nonneg : ∀ y, 0 ≤ marginal p y := by
    intro y
    rw [marginal]
    exact Finset.sum_nonneg fun x _ => hp.1 (y, x)
  have hmarginal_sum : ∑ y, marginal p y = 1 := by
    simp only [marginal]
    rw [← Fintype.sum_prod_type]
    exact hp.2
  have hmarginal_ac : ∀ y, u y = 0 → marginal p y = 0 := by
    intro y huy
    exact (hu y).ne' huy |>.elim
  have hdiscard : 0 ≤ klDivergence (marginal p) u :=
    kl_divergence_nonneg (marginal p) u
      ⟨hmarginal_nonneg, hmarginal_sum⟩
      ⟨fun y => (hu y).le, hu_sum⟩ hmarginal_ac
  rw [demon_average_divergence_eq p u hp.1 hu]
  exact le_add_of_nonneg_right hdiscard

open Classical in
/-- If the observation marginal is strictly positive, it is an admissible reference attaining the
any-reference upper bound exactly. Without that support condition the equality remains true, but
the witness is not in the positive-reference family. -/
theorem exists_observation_marginal_reference_attaining
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hmarginal_pos : ∀ y, 0 < marginal p y) :
    ∃ u : Y → ℝ,
      (∀ y, 0 < u y) ∧ ∑ y, u y = 1 ∧
        klDivergence p
            (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) =
          mutualInformation p := by
  refine ⟨marginal p, hmarginal_pos, ?_, rfl⟩
  simp only [marginal]
  rw [← Fintype.sum_prod_type]
  exact hp.2

open Classical in
/-- Uniform-prior Fano with mutual information replaced by KL to an arbitrary positive normalized
observation reference. The estimator remains completely arbitrary. -/
theorem fano_error_probability_lower_bound_divergence
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (u : Y → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hu : ∀ y, 0 < u y) (hu_sum : ∑ y, u y = 1)
    (hX : 2 ≤ Fintype.card X)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹) :
    1 - (klDivergence p
          (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) +
        Real.log 2) / Real.log (Fintype.card X) ≤
      ∑ z, if g z.1 ≠ z.2 then p z else 0 := by
  have hmi := mutual_information_le_product_reference_divergence p u hp hu hu_sum
  have hfano := fano_error_probability_lower_bound_uniform p g hp hX huniform
  have hcard_gt_one : 1 < Fintype.card X := by omega
  have hcard_real_gt_one : (1 : ℝ) < Fintype.card X := by exact_mod_cast hcard_gt_one
  have hlog_pos : 0 < Real.log (Fintype.card X) := Real.log_pos hcard_real_gt_one
  have hbudget :
      mutualInformation p + Real.log 2 ≤
        klDivergence p
            (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) +
          Real.log 2 := by
    linarith
  have hquotient :
      (mutualInformation p + Real.log 2) / Real.log (Fintype.card X) ≤
        (klDivergence p
            (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) +
          Real.log 2) / Real.log (Fintype.card X) :=
    (div_le_div_iff_of_pos_right hlog_pos).2 hbudget
  exact (sub_le_sub_left hquotient 1).trans hfano

open Classical in
/-- Side-condition-free counting form of uniform Fano. An arbitrary estimator with error at most
`ε` can resolve only enough hypotheses for `(1 - ε) * log (card X)` to fit in the information
budget. At `ε ≥ 1` the statement remains true but can be vacuous. -/
theorem fano_hypothesis_count_product_bound_uniform
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log (Fintype.card X) ≤ mutualInformation p + Real.log 2 := by
  letI : Nonempty X := by
    by_contra hX
    letI : IsEmpty X := not_nonempty_iff.mp hX
    simpa using hp.2
  by_cases hcard : Fintype.card X = 1
  · have hrhs : 0 ≤ mutualInformation p + Real.log 2 :=
      add_nonneg (mutual_information_nonneg p hp) (Real.log_pos (by norm_num)).le
    simpa [hcard] using hrhs
  · have hX : 2 ≤ Fintype.card X := by
      have hcard_pos : 0 < Fintype.card X := Fintype.card_pos_iff.mpr inferInstance
      omega
    have hfano := fano_error_probability_lower_bound_uniform p g hp hX huniform
    have hfloor :
        1 - (mutualInformation p + Real.log 2) / Real.log (Fintype.card X) ≤ ε :=
      hfano.trans herror
    have hcard_gt_one : 1 < Fintype.card X := by omega
    have hcard_real_gt_one : (1 : ℝ) < Fintype.card X := by exact_mod_cast hcard_gt_one
    have hlog_pos : 0 < Real.log (Fintype.card X) := Real.log_pos hcard_real_gt_one
    have hratio :
        1 - ε ≤ (mutualInformation p + Real.log 2) / Real.log (Fintype.card X) := by
      linarith
    exact (le_div_iff₀ hlog_pos).1 hratio

open Classical in
/-- Quotient counting form. The sole extra condition `ε < 1` makes `1 - ε` positive, so the
side-condition-free product bound may be divided without reversing the order. -/
theorem fano_hypothesis_count_bound_uniform
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε)
    (hε : ε < 1) :
    Real.log (Fintype.card X) ≤
      (mutualInformation p + Real.log 2) / (1 - ε) := by
  apply (le_div_iff₀ (sub_pos.mpr hε)).2
  simpa [mul_comm] using
    fano_hypothesis_count_product_bound_uniform p g ε hp huniform herror

open Classical in
/-- Side-condition-free divergence counting form, obtained by enlarging the information budget to
KL against an arbitrary positive normalized observation reference. -/
theorem fano_hypothesis_count_product_bound_divergence
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (u : Y → ℝ) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hu : ∀ y, 0 < u y) (hu_sum : ∑ y, u y = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log (Fintype.card X) ≤
      klDivergence p
          (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) +
        Real.log 2 := by
  have hmi := mutual_information_le_product_reference_divergence p u hp hu hu_sum
  have hbudget :
      mutualInformation p + Real.log 2 ≤
        klDivergence p
            (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) +
          Real.log 2 := by
    linarith
  exact (fano_hypothesis_count_product_bound_uniform p g ε hp huniform herror).trans hbudget

open Classical in
/-- Quotient divergence counting form for target error `ε < 1`. -/
theorem fano_hypothesis_count_bound_divergence
    {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (u : Y → ℝ) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hu : ∀ y, 0 < u y) (hu_sum : ∑ y, u y = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε)
    (hε : ε < 1) :
    Real.log (Fintype.card X) ≤
      (klDivergence p
          (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) +
        Real.log 2) / (1 - ε) := by
  apply (le_div_iff₀ (sub_pos.mpr hε)).2
  simpa [mul_comm] using
    fano_hypothesis_count_product_bound_divergence
      p g u ε hp hu hu_sum huniform herror

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (u : Y → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hu : ∀ y, 0 < u y) (hu_sum : ∑ y, u y = 1) :
    mutualInformation p ≤
      klDivergence p
        (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact mutual_information_le_product_reference_divergence p u hp hu hu_sum

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hmarginal_pos : ∀ y, 0 < marginal p y) :
    ∃ u : Y → ℝ,
      (∀ y, 0 < u y) ∧ ∑ y, u y = 1 ∧
        klDivergence p
            (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) =
          mutualInformation p := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact exists_observation_marginal_reference_attaining p hp hmarginal_pos

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (u : Y → ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hu : ∀ y, 0 < u y) (hu_sum : ∑ y, u y = 1)
    (hX : 2 ≤ Fintype.card X)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹) :
    1 - (klDivergence p
          (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) +
        Real.log 2) / Real.log (Fintype.card X) ≤
      ∑ z, if g z.1 ≠ z.2 then p z else 0 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_error_probability_lower_bound_divergence
    p g u hp hu hu_sum hX huniform

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log (Fintype.card X) ≤ mutualInformation p + Real.log 2 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_hypothesis_count_product_bound_uniform p g ε hp huniform herror

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε)
    (hε : ε < 1) :
    Real.log (Fintype.card X) ≤
      (mutualInformation p + Real.log 2) / (1 - ε) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_hypothesis_count_bound_uniform p g ε hp huniform herror hε

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (u : Y → ℝ) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hu : ∀ y, 0 < u y) (hu_sum : ∑ y, u y = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε) :
    (1 - ε) * Real.log (Fintype.card X) ≤
      klDivergence p
          (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) +
        Real.log 2 := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_hypothesis_count_product_bound_divergence
    p g u ε hp hu hu_sum huniform herror

open Classical in
example {Y X : Type*} [Fintype Y] [Fintype X]
    (p : Y × X → ℝ) (g : Y → X) (u : Y → ℝ) (ε : ℝ)
    (hp : (∀ z, 0 ≤ p z) ∧ ∑ z, p z = 1)
    (hu : ∀ y, 0 < u y) (hu_sum : ∑ y, u y = 1)
    (huniform :
      marginal (fun r : X × Y => p (r.2, r.1)) =
        fun _ => (Fintype.card X : ℝ)⁻¹)
    (herror : (∑ z, if g z.1 ≠ z.2 then p z else 0) ≤ ε)
    (hε : ε < 1) :
    Real.log (Fintype.card X) ≤
      (klDivergence p
          (fun q => u q.1 * marginal (fun r : X × Y => p (r.2, r.1)) q.2) +
        Real.log 2) / (1 - ε) := by
  fail_if_success rfl
  fail_if_success ((try simp); done)
  exact fano_hypothesis_count_bound_divergence
    p g u ε hp hu hu_sum huniform herror hε

/- Normalization cannot be dropped: on the one-point space the positive reference of total mass
two gives `D(1 ‖ 2) = -log 2 < 0`, so the demon identity's remainder cannot be discarded. -/
example :
    klDivergence (fun _ : Unit => (1 : ℝ)) (fun _ => 2) = -Real.log 2 := by
  simp [klDivergence, Real.log_inv]

/- Informative counting regime: with zero information and target error `ε = 1/2`, Fano gives
`log M ≤ log 4`, hence at most four hypotheses can be resolved. -/
example (M : ℕ) (hM : 1 ≤ M)
    (hcount :
      Real.log (M : ℝ) ≤
        ((0 : ℝ) + Real.log 2) / (1 - (1 / 2 : ℝ))) :
    M ≤ 4 := by
  have hlog_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog_two_ne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hbudget :
      ((0 : ℝ) + Real.log 2) / (1 - (1 / 2 : ℝ)) = Real.log 4 := by
    rw [hlog_four]
    field_simp [hlog_two_ne]
    ring
  have hlog : Real.log (M : ℝ) ≤ Real.log 4 := by
    rwa [hbudget] at hcount
  have hM_pos_nat : 0 < M := by omega
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM_pos_nat
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hM_pos, Real.exp_log (by norm_num : (0 : ℝ) < 4)] at hexp
  exact_mod_cast hexp

/- Vacuous counting regime: at target error `ε = 1`, the product form reduces to a nonnegative
information budget and bounds no cardinality; this holds for every `M`. -/
example (M : ℕ) :
    (1 - (1 : ℝ)) * Real.log M ≤ (0 : ℝ) + Real.log 2 := by
  simpa using (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

#print axioms mutual_information_le_product_reference_divergence
#print axioms exists_observation_marginal_reference_attaining
#print axioms fano_error_probability_lower_bound_divergence
#print axioms fano_hypothesis_count_product_bound_uniform
#print axioms fano_hypothesis_count_bound_uniform
#print axioms fano_hypothesis_count_product_bound_divergence
#print axioms fano_hypothesis_count_bound_divergence

end D5.S3.Estimation.FanoDivergenceForm
