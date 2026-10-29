# Tebni's A350759 prime congruences

## Abstract

Both prime congruences for Tebni's OEIS A350759 sequence.

The formal series have rational coefficients. Natural indices start at zero, and the sequence values are integers. PowerSeries.log over Q is the series for log(1+X); PowerSeries.subst takes the inner series first and the outer series second. Integer congruence is Int.ModEq. The prime p=2 is included.

**Definition 1.1 (The published exponential generating function).**

$$sourceSeries = \operatorname{PowerSeries.subst}\left(-1 + (1 + X) \cdot (1 - \operatorname{PowerSeries.log}\left(\mathbb{Q}\right)), \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.sourceSeries` (`✓ std3`).

*Citation.* Mélika Tebni (2022). *OEIS A350759, COMMENTS prime congruences*. URL: <https://oeis.org/A350759>.

*Commentary.*

OEIS A350759, revision 17, FORMULA (unpaginated): "E.g.f.: exp(-1 + (1 + x)*(1 - log(1 + x)))." The displayed substitution is the formal exponential at exactly this exponent.

**Definition 1.2 (Integer sequences with the source generating function).**

$$\forall a: (\mathbb{N} \to \mathbb{Z}), \operatorname{IsSourceSequence}\left(a\right) = (\operatorname{HannaLogarithmicPowerClosure.egf}\left((fun n: \mathbb{N} \mapsto (a\left(n\right): \mathbb{Q}))\right) = sourceSeries)$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.IsSourceSequence` (`✓ std3`).

*Citation.* Mélika Tebni (2022). *OEIS A350759, COMMENTS prime congruences*. URL: <https://oeis.org/A350759>.

*Commentary.*

OEIS A350759, revision 17, FORMULA (unpaginated): "E.g.f.: exp(-1 + (1 + x)*(1 - log(1 + x)))." For a natural-indexed integer sequence a, the existing HannaLogarithmicPowerClosure.egf has degree-n coefficient (a(n):Q)/n!; its equality with sourceSeries defines IsSourceSequence.

**Definition 1.3 (The two COMMENTS assertions).**

$$claim = ((\exists a: (\mathbb{N} \to \mathbb{Z}), \operatorname{IsSourceSequence}\left(a\right)) \land (\forall a: (\mathbb{N} \to \mathbb{Z}), (\operatorname{IsSourceSequence}\left(a\right)) \Rightarrow (\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \Rightarrow ((\operatorname{Int.ModEq}\left((p: \mathbb{Z}), a\left(p\right) + a\left(p + 1\right) - 2, 0\right)) \land (\operatorname{Int.ModEq}\left(((p + 1) \cdot p: \mathbb{Z}), a\left(p + 1\right), 1\right))))))$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.claim` (`✓ std3`).

*Citation.* Mélika Tebni (2022). *OEIS A350759, COMMENTS prime congruences*. URL: <https://oeis.org/A350759>.

*Commentary.*

OEIS A350759, revision 17, COMMENTS (unpaginated): "Conjectures: For all p prime, (a(p) + a(p+1) - 2) == 0 (mod p)," "a(p+1) == 1 (mod ((p+1)*p))." The second line inherits the prime quantifier. The formula also asserts existence of an integer sequence with the source EGF and covers every sequence with that EGF. Subtraction takes place in Z; the product (p+1)*p is formed in N and then cast to Z.

**Theorem 1.4 (Both prime congruences hold).**

$$(\exists a: (\mathbb{N} \to \mathbb{Z}), \operatorname{IsSourceSequence}\left(a\right)) \land (\forall a: (\mathbb{N} \to \mathbb{Z}), (\operatorname{IsSourceSequence}\left(a\right)) \Rightarrow (\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \Rightarrow ((\operatorname{Int.ModEq}\left((p: \mathbb{Z}), a\left(p\right) + a\left(p + 1\right) - 2, 0\right)) \land (\operatorname{Int.ModEq}\left(((p + 1) \cdot p: \mathbb{Z}), a\left(p + 1\right), 1\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mélika Tebni (2022). *OEIS A350759, COMMENTS prime congruences*. URL: <https://oeis.org/A350759>.

*Commentary.*

The rising-factorial expansion gives an integer factorial-scaled coefficient of the form 1+n*z at every index n. The index-zero expansion term is one; each other term is a multiple of n. The source differential equation gives an EGF convolution. Interior prime binomial coefficients vanish modulo p, and Wilson's theorem settles the endpoint, including a separate p=2 case. Combining the residues modulo p and p+1 proves the product congruence. Hanna's expansion in OEIS A176118 is prior art.

## References

- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.IsSourceSequence`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.claim`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.result`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.sourceSeries`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](../../../S1/Recurrence/Algebraic/DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree](../../../S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.md)
