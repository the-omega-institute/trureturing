/- GID: D5/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery
   generality: G
   mirror-B: D5/B/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mobius inversion recovers primitive coefficients from logarithmic histories. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius

-- Library-search audit trail (2026-08-28):
-- * Repository searches found no existing primitive-history Mobius recovery.
-- * Pinned Mathlib exactly provides
--   `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`; the proof below is only
--   the degree scaling that puts the logarithmic-history coefficients into that
--   theorem's standard divisor-sum form.

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Dilation.MonsterPrimitiveMobiusRecovery

open scoped BigOperators

-- Index all primitive root rays by `ι`, and let `H ray n` and `L ray n` be the
-- coefficients at the `n`-fold multiple of `ray` in the primitive heat series and
-- negative logarithmic denominator, respectively. The hypothesis is equation
-- (126.2) coefficientwise, after multiplication by `n`. Mobius inversion
-- recovers every positive-degree primitive coefficient with the factor
-- `mu(k) / k`.
theorem monster_primitive_mobius_recovery
    {ι : Type*}
    (H L : ι → ℕ → ℚ)
    (logExpansion : ∀ ray (n : ℕ), n > 0 →
      ∑ d ∈ n.divisors, (d : ℚ) * H ray d = (n : ℚ) * L ray n) :
    ∀ ray (n : ℕ), n > 0 →
      H ray n = ∑ kr ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius kr.1 : ℚ) / (kr.1 : ℚ) * L ray kr.2 := by
  intro ray
  have inversion :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (R := ℚ)
      (f := fun n => (n : ℚ) * H ray n)
      (g := fun n => (n : ℚ) * L ray n)).mp (logExpansion ray)
  intro n hn
  have hn_ne : (n : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  apply mul_left_cancel₀ hn_ne
  rw [Finset.mul_sum]
  calc
    (n : ℚ) * H ray n =
        ∑ kr ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius kr.1 : ℚ) *
            ((kr.2 : ℚ) * L ray kr.2) := (inversion n hn).symm
    _ = ∑ kr ∈ n.divisorsAntidiagonal,
          (n : ℚ) *
            ((ArithmeticFunction.moebius kr.1 : ℚ) / (kr.1 : ℚ) * L ray kr.2) := by
      apply Finset.sum_congr rfl
      intro kr hkr
      have hproduct : kr.1 * kr.2 = n :=
        (Nat.mem_divisorsAntidiagonal.mp hkr).1
      have hleft : (kr.1 : ℚ) ≠ 0 := by
        exact_mod_cast Nat.left_ne_zero_of_mem_divisorsAntidiagonal hkr
      rw [← hproduct, Nat.cast_mul]
      symm
      calc
        (kr.1 : ℚ) * (kr.2 : ℚ) *
              ((ArithmeticFunction.moebius kr.1 : ℚ) / (kr.1 : ℚ) * L ray kr.2) =
            (kr.2 : ℚ) *
              ((kr.1 : ℚ) *
                ((ArithmeticFunction.moebius kr.1 : ℚ) / (kr.1 : ℚ))) * L ray kr.2 := by
          ac_rfl
        _ = (kr.2 : ℚ) * (ArithmeticFunction.moebius kr.1 : ℚ) * L ray kr.2 := by
          rw [mul_div_cancel₀ _ hleft]
        _ = (ArithmeticFunction.moebius kr.1 : ℚ) *
              ((kr.2 : ℚ) * L ray kr.2) := by
          ac_rfl

-- Reverse probe: the public recovery proposition identifies the primitive
-- coefficient and logarithmic coefficient at degree one.
example {ι : Type*} (ray : ι) (H L : ι → ℕ → ℚ)
    (recovery : ∀ ray (n : ℕ), n > 0 →
      H ray n = ∑ kr ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius kr.1 : ℚ) / (kr.1 : ℚ) * L ray kr.2) :
    H ray 1 = L ray 1 := by
  simpa using recovery ray 1 (by decide)

-- Trivialization probe: setting all logarithmic coefficients to zero forces
-- the degree-one primitive coefficient to vanish, so a nonzero primitive family
-- cannot satisfy the public theorem with the trivial logarithmic family.
example {ι : Type*} (ray : ι) (H : ι → ℕ → ℚ)
    (logExpansion : ∀ ray (n : ℕ), n > 0 →
      ∑ d ∈ n.divisors, (d : ℚ) * H ray d = (n : ℚ) * (0 : ℚ)) :
    H ray 1 = 0 := by
  have recovery :=
    monster_primitive_mobius_recovery H (fun _ _ => 0) logExpansion
  simpa using recovery ray 1 (by decide)

#print axioms monster_primitive_mobius_recovery

end D5.S3.Analytic.Dilation.MonsterPrimitiveMobiusRecovery
