# Dedekind Sum Foundations and BHK Certificates

## Abstract

Rational Dedekind sums are periodic in the numerator and satisfy two exact finite BHK certificates.

The sawtooth and Dedekind sum are defined over exact rationals. The finite certificates use the frozen alternating walk and verify every displayed continued-fraction, inverse, walk, and correction clause.

**Definition 1.1 (The rational sawtooth).**

$$\forall x \in \mathbb{Q},\ \operatorname{sawtooth}(x) = \operatorname{if}(\operatorname{fract}(x) = 0, 0, \operatorname{fract}(x) - \frac{1}{2})$$

*Formalization.* `D5/S1/Phase/Interference/DedekindBhkCertificates.sawtooth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At an integral rational the value is zero; otherwise it is the fractional part minus one half.

**Theorem 1.2 (The sawtooth vanishes on integers).**

$$\forall z \in \mathbb{Z},\ \operatorname{sawtooth}([z]_{\mathbb{Q}}) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkCertificates.sawtooth_int` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Casting any integer to the rationals gives an integral sawtooth input.

**Theorem 1.3 (Integer translation preserves the sawtooth).**

$$\forall x \in \mathbb{Q},\ \forall z \in \mathbb{Z},\ \operatorname{sawtooth}(x + [z]_{\mathbb{Q}}) = \operatorname{sawtooth}(x)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkCertificates.sawtooth_add_int` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fractional part, and hence the sawtooth, is invariant under an integral translation.

**Definition 1.4 (The rational Dedekind sum).**

$$\forall d, c \in \mathbb{N},\ \operatorname{dedekindSum}(d, c) = \sum_{k=1}^{c-1}\operatorname{sawtooth}(\frac{[k]_{\mathbb{Q}}}{[c]_{\mathbb{Q}}})\operatorname{sawtooth}(\frac{[k\,d]_{\mathbb{Q}}}{[c]_{\mathbb{Q}}})$$

*Formalization.* `D5/S1/Phase/Interference/DedekindBhkCertificates.dedekindSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite interval is exactly the natural range from one through c minus one, and both factors are evaluated in the rationals.

**Theorem 1.5 (The numerator reduces modulo the denominator).**

$$\forall d, c \in \mathbb{N},\ \operatorname{dedekindSum}(d \operatorname{mod} c, c) = \operatorname{dedekindSum}(d, c)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkCertificates.s_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each second sawtooth factor has the same fractional part after reducing d modulo c.

**Theorem 1.6 (The sum at one over two is zero).**

$$\operatorname{dedekindSum}(1, 2) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkCertificates.dedekind_sum_one_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact finite rational normalization evaluates the single summand to zero.

**Theorem 1.7 (The sum at three over four).**

$$\operatorname{dedekindSum}(3, 4) = -\frac{1}{8}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkCertificates.dedekind_sum_three_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three exact rational summands total minus one eighth.

**Theorem 1.8 (The sum at four over nine).**

$$\operatorname{dedekindSum}(4, 9) = -\frac{4}{27}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkCertificates.dedekind_sum_four_nine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eight exact rational summands total minus four twenty-sevenths.

**Theorem 1.9 (An exact BHK certificate at three over four).**

$$\frac{1}{1+\frac{1}{2+\frac{1}{1}}} = \frac{3}{4} \land (3\times3) \operatorname{mod} 4 = 1 \land \operatorname{alternatingWalk}([1, 2, 1]) = 0 \land 12\times\operatorname{dedekindSum}(3, 4) = -3 + \frac{3+3}{4} - \operatorname{alternatingWalk}([1, 2, 1])$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkCertificates.bhk_three_four_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The odd normalized continued fraction [0; 1, 2, 1] equals three fourths, three is its inverse modulo four, the frozen alternating walk is zero, and the displayed BHK correction identity holds exactly.

**Theorem 1.10 (An exact BHK certificate at four over nine).**

$$\frac{1}{2+\frac{1}{3+\frac{1}{1}}} = \frac{4}{9} \land (7\times4) \operatorname{mod} 9 = 1 \land \operatorname{alternatingWalk}([2, 3, 1]) = 0 \land 12\times\operatorname{dedekindSum}(4, 9) = -3 + \frac{7+4}{9} - \operatorname{alternatingWalk}([2, 3, 1])$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindBhkCertificates.bhk_four_nine_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The odd normalized continued fraction [0; 2, 3, 1] equals four ninths, seven is its inverse modulo nine, the frozen alternating walk is zero, and the displayed BHK correction identity holds exactly.

The suggested [0; 2] case does not satisfy the source's displayed minus-sign formula under the standard positive continued-fraction convention. No general BHK theorem or theorem-shaped placeholder is asserted here; resolving that orientation convention and proving the continued-fraction induction remain Phase 2 work.

## References

- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkCertificates.bhk_four_nine_certificate`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkCertificates.bhk_three_four_certificate`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkCertificates.dedekindSum`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkCertificates.dedekind_sum_four_nine`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkCertificates.dedekind_sum_one_two`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkCertificates.dedekind_sum_three_four`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkCertificates.s_mod`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkCertificates.sawtooth`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkCertificates.sawtooth_add_int`
- Truth anchor: `D5/S1/Phase/Interference/DedekindBhkCertificates.sawtooth_int`
- Dependency: [D5/S1/Phase/WalkFormula](../WalkFormula.md)
