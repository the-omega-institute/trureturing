/- GID: D5/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages
   generality: S
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/AdaptiveAffineMessages
   mirror-E: none(waiver:exact-full-box-message-certificate)
   anchors: []
   digest: Actual adaptive grid types have uniformly contracting positive affine messages up to 2.55. -/

import D5.S3.StatisticalMechanics.HardCore.AffineProductCertificate
import D5.S3.StatisticalMechanics.HardCore.AdaptiveAffineMessageData
import D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace D5.S3.StatisticalMechanics.HardCore.AdaptiveAffineMessages

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.AffineProductCertificate
open D5.S3.StatisticalMechanics.HardCore.AdaptiveAffineMessageData
open D5.S3.StatisticalMechanics.HardCore.AdaptiveRadiusFourCertificates

/-- Coefficients of the actual geometric successor. An absent direction has
zero coefficients, so it contributes no message to the Jacobian row sum. -/
def childCoefficients (i : Fin 881) (d : Fin 3) : ℚ × ℚ :=
  (radiusFourStep i (radiusFourChoice i) d).elim (0, 0) affineCoefficients

private def mode (i : Fin 881) (d : Fin 3) : ℕ := affinePattern i / 3 ^ d.val % 3

/-- Reconstruct a rational clamped witness from its three small pattern digits.
No numerical optimization is evaluated during certificate checking. -/
def rowWitness (i : Fin 881) : Option ClipWitness :=
  if affinePattern i = 27 then none else
    let a := fun d => (childCoefficients i d).1
    let b := fun d => (childCoefficients i d).2
    let C := (∑ d, b d) - (999 / 1000 : ℚ) * (affineCoefficients i).2
    let fixedSum := ∑ d, if mode i d = 0 then a d * (20 / 71 : ℚ)
      else if mode i d = 1 then a d else 0
    let freeCount : ℚ := ∑ d, if mode i d = 2 then 1 else 0
    let t := (C - fixedSum) / (1 + freeCount)
    some ⟨t, fun d => if mode i d = 0 then 20 / 71
      else if mode i d = 1 then 1 else t / a d⟩

-- Split the finite quantifier before deciding: each leaf is checked by the kernel
-- in its own auxiliary theorem, without elaborating 881 simultaneous goals.
local syntax "decide_each" num : tactic
local macro_rules
  | `(tactic| decide_each $n:num) => do
    let k := n.getNat
    if k ≤ 1 then `(tactic| decide +kernel)
    else
      let a := Lean.Syntax.mkNumLit (toString (k / 2))
      let b := Lean.Syntax.mkNumLit (toString (k - k / 2))
      `(tactic| exact (Fin.forall_fin_add (m := $a:num) (n := $b:num) _).mpr
          ⟨by decide_each $a, by decide_each $b⟩)

/-- Every actual geometric row passes an exact rational, whole-box certificate.
Repeated coefficient pairs are storage sharing only: all 881 geometric rows
are checked against their own successors, not an assumed quotient tree. -/
theorem affine_message_certificate :
    ∀ i : Fin 881,
      0 ≤ (affineCoefficients i).1 ∧
      (10577 / 1000000 : ℚ) ≤ (affineCoefficients i).2 - (affineCoefficients i).1 ∧
      CheckedRow (20 / 71) (51 / 20) (999 / 1000) (3 / 1000)
        (affineCoefficients i).1 (affineCoefficients i).2
        (fun d => (childCoefficients i d).1)
        (fun d => (childCoefficients i d).2) (rowWitness i) := by
  decide_each 881

/-- The positive affine message associated with an actual geometric state. -/
noncomputable def affineMessage (i : Fin 881) (x : ℝ) : ℝ :=
  ((affineCoefficients i).2 : ℝ) - ((affineCoefficients i).1 : ℝ) * x

/-- Message of an actual successor, or zero if that direction is absent. -/
noncomputable def childMessage (i : Fin 881) (d : Fin 3) (x : ℝ) : ℝ :=
  ((childCoefficients i d).2 : ℝ) - ((childCoefficients i d).1 : ℝ) * x

/-- Hard-core vacancy recursion, with three ordered nonparent directions. -/
noncomputable def vacancy (lam : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  1 / (1 + lam * ∏ d, x d)

/-- The message has a common positive lower bound on the entire probability
interval. This also makes the real logarithmic message coordinate well-defined. -/
theorem affine_message_positive (i : Fin 881) (x : ℝ) (hx : x ≤ 1) :
    (10577 / 1000000 : ℝ) ≤ affineMessage i x := by
  have ha : (0 : ℝ) ≤ (affineCoefficients i).1 := by
    exact_mod_cast (affine_message_certificate i).1
  have hb : (10577 / 1000000 : ℝ) ≤
      ((affineCoefficients i).2 : ℝ) - ((affineCoefficients i).1 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr (affine_message_certificate i).2.1
    simpa only [Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat] using h
  dsimp [affineMessage]
  nlinarith [mul_le_mul_of_nonneg_left hx ha]

private theorem child_message_nonneg (i : Fin 881) (d : Fin 3) (x : ℝ) (hx : x ≤ 1) :
    0 ≤ childMessage i d x := by
  cases hs : radiusFourStep i (radiusFourChoice i) d with
  | none => simp [childMessage, childCoefficients, hs]
  | some j =>
      have hp := affine_message_positive j x hx
      have he : childMessage i d x = affineMessage j x := by
        simp [childMessage, childCoefficients, hs, affineMessage]
      rw [he]
      linarith

/-- The exact rational certificate gives a margin at every real point, for
every activity from zero through 51/20, without a sampling hypothesis. -/
theorem affine_polynomial_margin (i : Fin 881) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) (x : Fin 3 → ℝ)
    (hx : ∀ d, (20 / 71 : ℝ) ≤ x d ∧ x d ≤ 1) :
    (3 / 1000 : ℝ) ≤
      (999 / 1000 : ℝ) * (((affineCoefficients i).2 : ℝ) - (affineCoefficients i).1) +
      lam * (∏ d, x d) * ((999 / 1000 : ℝ) * (affineCoefficients i).2 -
        (∑ d, ((childCoefficients i d).2 : ℝ)) +
        ∑ d, ((childCoefficients i d).1 : ℝ) * x d) := by
  simpa only [Rat.cast_div, Rat.cast_ofNat] using checked_row_sound (20 / 71) (51 / 20) (999 / 1000) (3 / 1000)
    (affineCoefficients i).1 (affineCoefficients i).2
    (fun d => (childCoefficients i d).1) (fun d => (childCoefficients i d).2)
    (rowWitness i) (by norm_num) (affine_message_certificate i).2.2 lam
    (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hlam) x
    (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hx)

private theorem product_bounds (x : Fin 3 → ℝ)
    (hx : ∀ d, (20 / 71 : ℝ) ≤ x d ∧ x d ≤ 1) :
    0 ≤ (∏ d, x d) ∧ (∏ d, x d) ≤ 1 := by
  refine ⟨Finset.prod_nonneg (fun d _ => by linarith [(hx d).1]), ?_⟩
  have h := Finset.prod_le_prod (fun d (_ : d ∈ (Finset.univ : Finset (Fin 3))) =>
    show 0 ≤ x d by linarith [(hx d).1]) (fun d _ => (hx d).2)
  simpa using h

/-- Vacancy stays in the same compact real interval uniformly in the activity. -/
theorem vacancy_mem (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20)
    (x : Fin 3 → ℝ) (hx : ∀ d, (20 / 71 : ℝ) ≤ x d ∧ x d ≤ 1) :
    (20 / 71 : ℝ) ≤ vacancy lam x ∧ vacancy lam x ≤ 1 := by
  have hp := product_bounds x hx
  have hnon : 0 ≤ lam * ∏ d, x d := mul_nonneg hlam.1 hp.1
  have hupper : lam * (∏ d, x d) ≤ 51 / 20 := by
    exact (mul_le_mul_of_nonneg_left hp.2 hlam.1).trans (by simpa using hlam.2)
  have hd : 0 < 1 + lam * ∏ d, x d := by linarith
  constructor
  · unfold vacancy
    apply (le_div_iff₀ hd).mpr
    nlinarith
  · unfold vacancy
    apply (div_le_iff₀ hd).mpr
    linarith

private theorem message_gap_identity (i : Fin 881) (lam : ℝ) (x : Fin 3 → ℝ)
    (hd : 1 + lam * (∏ d, x d) ≠ 0) :
    ((999 / 1000 : ℝ) * affineMessage i (vacancy lam x) -
      (1 - vacancy lam x) * ∑ d, childMessage i d (x d)) *
        (1 + lam * ∏ d, x d) =
      (999 / 1000 : ℝ) * (((affineCoefficients i).2 : ℝ) - (affineCoefficients i).1) +
        lam * (∏ d, x d) * ((999 / 1000 : ℝ) * (affineCoefficients i).2 -
          (∑ d, ((childCoefficients i d).2 : ℝ)) +
          ∑ d, ((childCoefficients i d).1 : ℝ) * x d) := by
  simp only [affineMessage, childMessage, vacancy, Finset.sum_sub_distrib]
  field_simp [hd] <;> ring

/-- The full transformed-Jacobian row is strictly below the common contraction
constant 999/1000 at every point of the entire box. -/
theorem affine_full_row_contraction (i : Fin 881) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) (x : Fin 3 → ℝ)
    (hx : ∀ d, (20 / 71 : ℝ) ≤ x d ∧ x d ≤ 1) :
    (1 - vacancy lam x) * (∑ d, childMessage i d (x d)) /
      affineMessage i (vacancy lam x) < 999 / 1000 := by
  have hv := vacancy_mem lam hlam x hx
  have hpsi := affine_message_positive i (vacancy lam x) hv.2
  have hpp : 0 < affineMessage i (vacancy lam x) := by linarith
  have hprod := product_bounds x hx
  have hd : 0 < 1 + lam * ∏ d, x d := by
    nlinarith [mul_nonneg hlam.1 hprod.1]
  have hm := affine_polynomial_margin i lam hlam x hx
  rw [← message_gap_identity i lam x (ne_of_gt hd)] at hm
  have hgap : 0 < (999 / 1000 : ℝ) * affineMessage i (vacancy lam x) -
      (1 - vacancy lam x) * (∑ d, childMessage i d (x d)) := by
    by_contra hn
    have hnon := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hd.le
    linarith
  exact (div_lt_iff₀ hpp).mpr (by linarith)

/-- Deleting any subset of children preserves contraction. Missing coordinates
are set to vacancy one; the omitted nonnegative message terms are then dropped.
The result quantifies over every subset, not just the complete branching tree. -/
theorem affine_pruned_row_contraction (i : Fin 881) (s : Finset (Fin 3)) (lam : ℝ)
    (hlam : 0 ≤ lam ∧ lam ≤ 51 / 20) (x : Fin 3 → ℝ)
    (hx : ∀ d, (20 / 71 : ℝ) ≤ x d ∧ x d ≤ 1) :
    let y := vacancy lam (fun d => if d ∈ s then x d else 1)
    (1 - y) * (∑ d ∈ s, childMessage i d (x d)) / affineMessage i y < 999 / 1000 := by
  let z : Fin 3 → ℝ := fun d => if d ∈ s then x d else 1
  have hz (d) : (20 / 71 : ℝ) ≤ z d ∧ z d ≤ 1 := by
    by_cases h : d ∈ s
    · simpa [z, h] using hx d
    · norm_num [z, h]
  have hv := vacancy_mem lam hlam z hz
  have hpsi := affine_message_positive i (vacancy lam z) hv.2
  have hpp : 0 < affineMessage i (vacancy lam z) := by linarith
  have hs : (∑ d ∈ s, childMessage i d (x d)) ≤
      ∑ d, childMessage i d (z d) := by
    calc
      _ = ∑ d ∈ s, childMessage i d (z d) := by
        apply Finset.sum_congr rfl
        intro d hd
        simp [z, hd]
      _ ≤ ∑ d, childMessage i d (z d) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
          (fun d _ _ => child_message_nonneg i d (z d) (hz d).2)
  have hmul := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hv.2)
  have hdiv := div_le_div_of_nonneg_right hmul hpp.le
  exact hdiv.trans_lt (affine_full_row_contraction i lam hlam z hz)

#print axioms affine_message_certificate
#print axioms affine_message_positive
#print axioms affine_polynomial_margin
#print axioms vacancy_mem
#print axioms affine_full_row_contraction
#print axioms affine_pruned_row_contraction

end D5.S3.StatisticalMechanics.HardCore.AdaptiveAffineMessages
