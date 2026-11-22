# Strict increase for Kimberling's A289916

## Abstract

The integer coefficients of Barker's generating function for OEIS A289916 are strictly increasing.

**Definition 1.1 (The denominator).**

Lean statement: `D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease.den`

*Formalization.* `D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease.den` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bounded-error asymptotics for Bernáth's conjecture: OEIS A400645, revision 21, COMMENTS, and its rounded-norm siblings*. DOI: [10.5281/zenodo.24369110](https://doi.org/10.5281/zenodo.24369110). URL: <https://zenodo.org/records/24369110>.

*Commentary.*

The denominator is (1 − z + z²)Q(z) in the integer formal power series ring, with Q(z) = z⁴ − z³ − z² − z + 1.

**Definition 1.2 (The numerator).**

Lean statement: `D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease.num`

*Formalization.* `D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease.num` (`✓ std3`).

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bounded-error asymptotics for Bernáth's conjecture: OEIS A400645, revision 21, COMMENTS, and its rounded-norm siblings*. DOI: [10.5281/zenodo.24369110](https://doi.org/10.5281/zenodo.24369110). URL: <https://zenodo.org/records/24369110>.

*Commentary.*

The numerator is (1 + z)²(1 − z + z² − z³ + z⁴ − z⁵ + z⁶).

**Theorem 1.3 (Unique coefficients and strict increase).**

Lean statement: `D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease.result`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease.result` (`✓ std3`). ∎

*Citation.* Haobo Ma; Wenlin Zhang (2026). *Bounded-error asymptotics for Bernáth's conjecture: OEIS A400645, revision 21, COMMENTS, and its rounded-norm siblings*. DOI: [10.5281/zenodo.24369110](https://doi.org/10.5281/zenodo.24369110). URL: <https://zenodo.org/records/24369110>.

*Commentary.*

Exactly one integer sequence v satisfies (∑ v_n z^n) times the denominator equals the numerator, and that sequence satisfies v_n < v_{n+1} for every n ≥ 0. Uniqueness holds because the denominator has constant term one. Multiplying by 1 + z rewrites the identity with denominator 1 − z − z² − z⁵ − z⁶ + z⁷ = (1 + z³)Q(z) and numerator (1 + z)²(1 + z⁷). The coefficients h_n of its reciprocal satisfy h_0 = 1 and h_n − h_{n−1} = h_{n−2} + h_{n−5} + h_{n−6} − h_{n−7} for n ≥ 1. Induction shows that h_n is nonnegative and nondecreasing, and strictly increasing from n = 2. The coefficients are v_n = h_n + 2h_{n−1} + h_{n−2} + h_{n−7} + 2h_{n−8} + h_{n−9}, so their differences are nonnegative combinations of differences of h, with v_1 − v_0 = 2 and a positive term in v_{n+1} − v_n for n ≥ 1. This is the strict-increase clause of Corollary 8 of H. Ma and W. Zhang's note (DOI 10.5281/zenodo.24369110). Kimberling's conjecture concerns the sequence defined in the A289916 NAME; Ma and Zhang derive Barker's generating function from that definition, and this derivation is not formalized here. The asymptotic clause v_n = D r^n + O(1) is not formalized here either.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease.den`
- Truth anchor: `D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease.num`
- Truth anchor: `D5/S1/Recurrence/Algebraic/OEISA289916StrictIncrease.result`
