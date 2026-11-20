# Digit caps one below a multiple of the radix

## Abstract

With digit cap a·ell−1 the number of bounded-digit representations of n is the sum of the cap a−1 counts of 0,…,⌊n/ell⌋.

**Theorem 1.1 (The multiple-cap identity).**

Lean statement: `D5/S1/Digit/DigitCapMultipleCount.count_multiple`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitCapMultipleCount.count_multiple` (`✓ std3`). ∎

*Citation.* Jean-Marie Dumont; Nikita Sidorov; Alain Thomas (1999). *Number of representations related to a linear recurrent basis*. DOI: [10.4064/aa-88-4-371-396](https://doi.org/10.4064/aa-88-4-371-396). URL: <https://matwbn.icm.edu.pl/ksiazki/aa/aa88/aa8847.pdf>.

*Commentary.*

For ell≥2, a≥1 and every n, count (a·ell−1) ell n equals the sum of count (a−1) ell t over 0≤t≤⌊n/ell⌋. Each digit d≤a·ell−1 splits uniquely as d=ell·q+r with q≤a−1 and r<ell, so a representation of n splits into a representation of t with digits at most a−1, where ell·t≤n, and a representation of n−ell·t with digits below ell. The latter is the unique ordinary radix expansion: there is at least one, and the quotient-digit bound with q=1 allows at most one. So the representations of n with quotient weight t correspond exactly to the cap a−1 representations of t. This is Proposition 6.8 of Dumont, Sidorov and Thomas (1999).

**Theorem 1.2 (The cap ell²−1).**

Lean statement: `D5/S1/Digit/DigitCapMultipleCount.count_square_sub_one`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitCapMultipleCount.count_square_sub_one` (`✓ std3`). ∎

*Citation.* Jean-Marie Dumont; Nikita Sidorov; Alain Thomas (1999). *Number of representations related to a linear recurrent basis*. DOI: [10.4064/aa-88-4-371-396](https://doi.org/10.4064/aa-88-4-371-396). URL: <https://matwbn.icm.edu.pl/ksiazki/aa/aa88/aa8847.pdf>.

*Commentary.*

For ell≥2, count (ell²−1) ell n=⌊n/ell⌋+1: with a=ell every summand is an ordinary radix expansion count, equal to 1.

**Theorem 1.3 (Monotone and nonconstant growth).**

Lean statement: `D5/S1/Digit/DigitCapMultipleCount.count_multiple_mono`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/DigitCapMultipleCount.count_multiple_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jean-Marie Dumont; Nikita Sidorov; Alain Thomas (1999). *Number of representations related to a linear recurrent basis*. DOI: [10.4064/aa-88-4-371-396](https://doi.org/10.4064/aa-88-4-371-396). URL: <https://matwbn.icm.edu.pl/ksiazki/aa/aa88/aa8847.pdf>.

*Commentary.*

For a≥1 the counts with cap a·ell−1 are nondecreasing in n, because the sum runs over the growing range 0,…,⌊n/ell⌋. For a≥2 the count at ell exceeds the count at 0, since the extra summand counts the representation of 1 by the single digit 1≤a−1. In particular, for ell≥3 the cap 2ell−1<ell²−1 already gives nondecreasing, nonconstant counts.

## References

- Truth anchor: `D5/S1/Digit/DigitCapMultipleCount.count_multiple`
- Truth anchor: `D5/S1/Digit/DigitCapMultipleCount.count_multiple_mono`
- Truth anchor: `D5/S1/Digit/DigitCapMultipleCount.count_square_sub_one`
- Dependency: [D5/S1/Digit/DigitCapQuotientBound](DigitCapQuotientBound.md)
