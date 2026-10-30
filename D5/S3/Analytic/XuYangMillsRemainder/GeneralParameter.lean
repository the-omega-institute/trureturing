/- GID: D5/S3/Analytic/XuYangMillsRemainder/GeneralParameter
   generality: G
   mirror-B: D5/B/S3/Analytic/XuYangMillsRemainder/GeneralParameter
   mirror-E: none
   anchors: [D5/S3/Analytic/XuYangMillsRemainder/Result]
   utility: none
   digest: Exact original Theorem 2.1 target with compiled sign and endpoint-limit partial results.

This module is an unfrozen checkpoint for the general-parameter Mills
classification.  It keeps the original normalization from `Result.D` and
records the complete theorem statement verbatim as a proposition.  The
general-parameter coefficient representation, strict adjacent-moment
comparison, and the two endpoint asymptotics are still open here.
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import D5.S3.Analytic.XuYangMillsRemainder.Result

open Set Filter
open scoped Topology
noncomputable section

namespace D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter

open D5.S3.Analytic.XuYangMillsRemainder.Result

/-! The original source normalization. -/

def F (n : ℕ) (a x : ℝ) : ℝ := (-1 : ℝ) ^ n * D n x a

def I (j : ℕ) : ℝ := ∫ v in (0 : ℝ)..1, (1 + v ^ 2) ^ j

def B (j : ℕ) : ℝ := ∫ v in (0 : ℝ)..1, v ^ 2 * (1 + v ^ 2) ^ j

def theta (j : ℕ) : ℝ := (1 - I j / B j) / 2

def globalNonnegative (n : ℕ) (a : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → 0 ≤ F n a x

def globalNonpositive (n : ℕ) (a : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → 0 ≤ -F n a x

def completelyMonotone (n : ℕ) (a : ℝ) : Prop :=
  CompletelyMonotoneOn (F n a)

def theorem21 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ,
    (globalNonnegative n a ↔ completelyMonotone n a ∧ a ≤ theta (n - 2)) ∧
    (globalNonpositive n a ↔
      CompletelyMonotoneOn (fun x => -F n a x) ∧ a ≥ theta (n - 1))

/-! A complete-monotonicity predicate contains the zeroth-order sign. -/

private theorem completelyMonotone_zero_sign {f : ℝ → ℝ}
    (hf : CompletelyMonotoneOn f) : ∀ x : ℝ, 0 < x → 0 ≤ f x := by
  intro x hx
  have h := hf.2 0 x hx
  simpa using h

private theorem cm_sign_projections (n : ℕ) (a : ℝ) :
    completelyMonotone n a → globalNonnegative n a := by
  intro h
  exact completelyMonotone_zero_sign h

private theorem neg_cm_sign_projection (n : ℕ) (a : ℝ) :
    CompletelyMonotoneOn (fun x => -F n a x) → globalNonpositive n a := by
  intro h
  exact completelyMonotone_zero_sign h

/-! Endpoint signs forced by a finite one-sided asymptotic limit. -/

private theorem nonnegative_sign_forces_nonpositive_limit {f : ℝ → ℝ}
    {p : ℕ} {u : ℝ}
    (hlim : Tendsto (fun x : ℝ => x ^ p * f x) (𝓝[>] (0 : ℝ)) (𝓝 (-u)))
    (hpos : ∀ x : ℝ, 0 < x → 0 ≤ f x) :
    u ≤ 0 := by
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ^ p * f x ∈ Ici (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_nonneg (pow_nonneg hx.le p) (hpos x hx)
  have hclosed : -u ∈ Ici (0 : ℝ) := isClosed_Ici.mem_of_tendsto hlim hev
  change 0 ≤ -u at hclosed
  linarith

private theorem nonpositive_sign_forces_nonnegative_limit {f : ℝ → ℝ}
    {p : ℕ} {u : ℝ}
    (hlim : Tendsto (fun x : ℝ => x ^ p * f x) atTop (𝓝 (-u)))
    (hneg : ∀ x : ℝ, 0 < x → 0 ≤ -f x) :
    0 ≤ u := by
  have hev : ∀ᶠ x in atTop, x ^ p * (-f x) ∈ Ici (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_nonneg (pow_nonneg (le_of_lt hx) p) (hneg x hx)
  have hlim' : Tendsto (fun x : ℝ => x ^ p * (-f x)) atTop (𝓝 u) := by
    have h := hlim.neg
    have hfun : (fun x : ℝ => -(x ^ p * f x)) = (fun x => x ^ p * (-f x)) := by
      funext x
      ring
    rw [hfun] at h
    simpa using h
  have hclosed : u ∈ Ici (0 : ℝ) := isClosed_Ici.mem_of_tendsto hlim' hev
  exact hclosed

/-! The exact source clauses are retained as a named checkpoint. -/

private theorem theorem21_contains_required_clauses :
    theorem21 =
      (∀ n : ℕ, 2 ≤ n → ∀ a : ℝ,
        (globalNonnegative n a ↔ completelyMonotone n a ∧ a ≤ theta (n - 2)) ∧
        (globalNonpositive n a ↔
          CompletelyMonotoneOn (fun x => -F n a x) ∧ a ≥ theta (n - 1))) := rfl

end D5.S3.Analytic.XuYangMillsRemainder.GeneralParameter
