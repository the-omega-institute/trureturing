# Golden Limits for the Complementary Kimberling Sequences

## Abstract

The complementary Kimberling sequences have golden consecutive-ratio limits.

**Theorem 1.1 (Both complementary recurrences converge to the golden ratio).**

$$\lim_{n\to\infty} \frac{a^{-}_{n+1}}{a^{-}_n}=\varphi \land \lim_{n\to\infty} \frac{a^{+}_{n+1}}{a^{+}_n}=\varphi$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/ComplementaryGoldenRatioLimit.kimberling_complementary_golden_limits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OEIS A293317 and A293316, entered by Clark Kimberling on 2017-10-28, label their golden-ratio limits as Conjecture; this theorem proves both Conjecture limits. The minus-labelled sequence is A293317 and the plus-labelled sequence is A293316.

The positive-mex construction yields positive target and complementary terms. Its state lengths and append structure give the exact recurrences, while a finite-set cardinality bound makes the complementary term grow at most linearly.

A two-step growth estimate gives a geometric lower bound for the target term, so each signed recurrence error is negligible relative to the next denominator. The general perturbed Fibonacci ratio theorem then gives both limits. Executable checks reproduce both OEIS sequences through index twelve.

## References

- Truth anchor: `D5/S1/Recurrence/ComplementaryGoldenRatioLimit.kimberling_complementary_golden_limits`
