/- GID: D5/S0/Asymptotics/EscapeProbability/PoissonDomainLimit
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/PoissonDomainLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.LogBounds]
   digest: A pinned exponential limit gives Poisson-domain escape. -/

/- Library-search audit trail (2026-08-15):
   * Pinned mathlib's `Real.tendsto_one_add_pow_exp_of_tendsto` exactly turns
     `A * g A -> t` into `(1 + g A) ^ A -> exp t`; it is applied below with
     `g A = -k(A) n(A)^(-A)`.
   * `Probability.Distributions.Poisson.PoissonLimitThm` uses that same lemma
     for the binomial-to-Poisson mass limit; no probability approximation or
     total-variation result is needed here.
   * Repository searches found no declaration for the varying-`n`, varying-`k`
     escape expression with a finite nonzero scaling limit.
-/

import D5.S0.Asymptotics.FixedPointFreeEscapeProbability
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

namespace D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit

open Filter
open D5.S0.Asymptotics.FixedPointFreeEscapeProbability
open D5.S0.Diagonal.EscapeCount

/-- For every address cardinality, the frozen uniform escape probability has
the closed form used by the analytic Poisson-domain limit. -/
theorem escape_probability_closed_form {Y : Type*} [Fintype Y] [Nonempty Y]
    (f : Y -> Y) (A : Nat) :
    escapeProbability (A := Fin A) f =
      (1 - (Nat.card {y : Y // f y = y} : Real) /
        (Fintype.card Y : Real) ^ A) ^ A := by
  classical
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · rw [escapeProbability, escaped_listing_card]
    simp [Nat.card_eq_fintype_card]
  rw [escapeProbability, escaped_listing_card]
  have hk : Nat.card {y : Y // f y = y} <= Fintype.card Y := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hkpow : Nat.card {y : Y // f y = y} <= Fintype.card Y ^ A :=
    hk.trans (Nat.le_pow (a := Fintype.card Y) (b := A) (by omega))
  have hksub :
      Fintype.card {y : Y // f y = y} <= Fintype.card Y ^ A := by
    simpa [Nat.card_eq_fintype_card] using hkpow
  have hden : (Fintype.card (Fin A -> Fin A -> Y) : Real) =
      (Fintype.card Y : Real) ^ (A * A) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
    norm_num [Nat.cast_pow, pow_mul]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Nat.cast_pow, Nat.cast_sub hksub, hden]
  have hpow : (Fintype.card Y : Real) ^ A ≠ 0 := by positivity
  have hbase :
      ((Fintype.card Y ^ A - Fintype.card {y : Y // f y = y} : Nat) : Real) /
          (Fintype.card Y : Real) ^ A =
        1 - (Nat.card {y : Y // f y = y} : Real) /
          (Fintype.card Y : Real) ^ A := by
    rw [Nat.cast_sub hksub, Nat.cast_pow, Nat.card_eq_fintype_card]
    field_simp [hpow]
  rw [Nat.cast_pow]
  calc
    ((Fintype.card Y : Real) ^ A -
        Fintype.card {y : Y // f y = y}) ^ A /
        (Fintype.card Y : Real) ^ (A * A) =
      (((Fintype.card Y ^ A -
          Fintype.card {y : Y // f y = y} : Nat) : Real) /
        (Fintype.card Y : Real) ^ A) ^ A := by
          rw [Nat.cast_sub hksub, Nat.cast_pow, div_pow, pow_mul]
    _ = _ := by
      simpa only [Nat.card_eq_fintype_card] using
        congrArg (fun x : Real => x ^ A) hbase

/-- If the scaled capture weight `k(A) * A * n(A)^(-A)` has finite limit
`lambda`, then the closed-form escape expression tends to `exp (-lambda)`.
This analytic statement does not assert that a positive `lambda` is realizable
when `k(A)` is constrained to be the fixed-point count of an `n(A)`-element
type. -/
theorem poisson_domain_escape_limit (n k : Nat -> Nat) (lambda : Real)
    (hscale : Tendsto
      (fun A : Nat =>
        (k A : Real) * (A : Real) * ((n A : Real)⁻¹ ^ A))
      atTop (nhds lambda)) :
    Tendsto
      (fun A : Nat =>
        (1 - (k A : Real) * ((n A : Real)⁻¹ ^ A)) ^ A)
      atTop (nhds (Real.exp (-lambda))) := by
  have hneg : Tendsto
      (fun A : Nat =>
        (A : Real) * (-((k A : Real) * ((n A : Real)⁻¹ ^ A))))
      atTop (nhds (-lambda)) := by
    apply hscale.neg.congr'
    filter_upwards with A
    ring
  simpa [sub_eq_add_neg] using
    Real.tendsto_one_add_pow_exp_of_tendsto hneg

/-- If the scaled fixed-point weight of a frozen finite output system tends to
`lambda`, then its escape probability tends to `exp (-lambda)`. -/
theorem poisson_domain_escape_probability_limit
    {Y : Type*} [Fintype Y] [Nonempty Y] (f : Y -> Y) (lambda : Real)
    (hscale : Tendsto
      (fun A : Nat =>
        (Nat.card {y : Y // f y = y} : Real) * (A : Real) *
          ((Fintype.card Y : Real)⁻¹ ^ A))
      atTop (nhds lambda)) :
    Tendsto (fun A : Nat => escapeProbability (A := Fin A) f)
      atTop (nhds (Real.exp (-lambda))) := by
  apply (poisson_domain_escape_limit
    (fun _ => Fintype.card Y)
    (fun _ => Nat.card {y : Y // f y = y}) lambda hscale).congr'
  filter_upwards with A
  symm
  rw [escape_probability_closed_form f A]
  simp [div_eq_mul_inv]

/-- The scaling hypothesis has a positive-limit witness outside the fixed-point
constraint: `n(A) = A` and `k(A) = A^(A-1)` give scale one for `A >= 1`. -/
example : Tendsto
    (fun A : Nat =>
      ((A ^ (A - 1) : Nat) : Real) * (A : Real) *
        (((A : Nat) : Real)⁻¹ ^ A))
    atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with A hA
  rw [Nat.cast_pow, ← pow_succ, Nat.sub_add_cancel hA, ← mul_pow]
  simp [Nat.cast_ne_zero.mpr (by omega : A ≠ 0)]

#print axioms escape_probability_closed_form
#print axioms poisson_domain_escape_limit
#print axioms poisson_domain_escape_probability_limit

end D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit
