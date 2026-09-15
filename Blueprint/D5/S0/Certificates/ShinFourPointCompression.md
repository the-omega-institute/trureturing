# A negative answer to four-point sumset compression

## Abstract

The eleven-fold sumset of {0,7,17,80} has 347 elements, a cardinality absent from every four-element integer set in [0,79].

**Definition 1.1 (The affirmative proposition).**

Lean statement: `D5/S0/Certificates/ShinFourPointCompression.claim`

*Formalization.* `D5/S0/Certificates/ShinFourPointCompression.claim` (`✓ std3`).

*Citation.* Henry Shin (2026). *Iterated-sumset spectra: The complete exponent law and its rank geometry*. DOI: [10.48550/arXiv.2609.01690](https://doi.org/10.48550/arXiv.2609.01690).

*Commentary.*

For every natural h at least two and every four-element finite set A of integers, the proposition asks for a four-element integer set B in the closed interval from zero to D_h, with equal cardinalities of their h-fold sumsets. The bound D_h is choose(h+2,2), plus one when h is odd. Each sum uses exactly h elements, with repetition allowed; the zero-fold sumset is {0}. Scalar multiplication of each individual element would define a different operation.

This is the affirmative answer to the unnumbered question after Corollary 10.5 and equation (193), also restated in Question 12.5 of the related source. It preserves only the number of distinct sums. It imposes no requirement to preserve the complete additive relation type, or to make the set primitive.

**Theorem 1.2 (The cardinality 347 cannot be compressed to diameter 79).**

Lean statement: `D5/S0/Certificates/ShinFourPointCompression.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/ShinFourPointCompression.result` (`✓ std3`). ∎

*Resolves.* `Problems/shin-four-point-sumset-compression` (refuted) by `D5/S0/Certificates/ShinFourPointCompression.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shin-four-point-sumset-compression","declaration_gid":"D5/S0/Certificates/ShinFourPointCompression.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Henry Shin (2026). *Iterated-sumset spectra: The complete exponent law and its rank geometry*. DOI: [10.48550/arXiv.2609.01690](https://doi.org/10.48550/arXiv.2609.01690).

*Acknowledgement.* Enkai Zhang (2026). *Sharp order-preserving integer models for short additive equalities*. DOI: [10.48550/arXiv.2609.08915](https://doi.org/10.48550/arXiv.2609.08915).

*Commentary.*

At h=11 the proposed bound is 79. The set {0,7,17,80} has an eleven-fold sumset of cardinality 347. For {0,a,b,c}, the sums are exactly i*a+j*b+k*c with nonnegative coefficients satisfying i+j+k at most eleven. The unused summands are zeros.

A natural number records a finite set by its binary digits. Starting with the digit for zero, each addition step takes the union with the shifts by a, b and c. Induction identifies these digits with the actual repeated sumset in both directions. All sums are at most 880. Counting one bits in 111 bytes therefore counts every sum. The byte counts agree with binary-digit counts for every byte, and the count excludes 347 for every 0<a<b<c at most 79.

Any four-element B in [0,79] has four increasing elements. Subtract its minimum to obtain {0,a,b,c} in the enumerated range. Repeated addition turns this translation into translation by eleven times the minimum, which preserves cardinality. Thus no such B can have the cardinality 347, contradicting the universal proposition. The argument does not determine the least diameter realizing every eleven-fold cardinality; in particular it does not assert that this diameter equals 80.

## References

- Truth anchor: `D5/S0/Certificates/ShinFourPointCompression.claim`
- Truth anchor: `D5/S0/Certificates/ShinFourPointCompression.result`
