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

**Definition 1.3 (Filtered polynomial diagonal).**

$$\forall f: \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right), \operatorname{diagonal}\left(f\right) = \operatorname{PowerSeries.eval2}\left(\operatorname{Polynomial.eval2RingHom}\left(\operatorname{PowerSeries.C}\left(\right), 1 + X\right), X, f\right)$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write z for the outer variable and Y for the polynomial coefficient variable. The Q-algebra homomorphism D sends z to X and Y to 1+X. The polynomial coefficient ring has the discrete topology and the power-series ring its coefficientwise topology. Evaluation in outer degree m uses only finitely many indices n<=m. This is the original diagonal used by the A350759 proof and by Bala's A119370 logarithmic specialization.

**Theorem 1.4 (Diagonal evaluation formula).**

$$\forall f: \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right), \operatorname{diagonal}\left(f\right) = \operatorname{PowerSeries.eval2}\left(\operatorname{Polynomial.eval2RingHom}\left(\operatorname{PowerSeries.C}\left(\right), 1 + X\right), X, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal is exactly the formal eval₂ operation with the coefficient homomorphism evaluating Y at 1+X, and with the outer variable sent to X. In these displays eval2 and eval2RingHom denote Mathlib's eval₂ and eval₂RingHom.

**Theorem 1.5 (Coefficientwise continuity).**

$$\operatorname{Continuous}\left(diagonal\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity is for coefficientwise convergence with the discrete topology on Q[Y] and Q. It justifies transporting formal locally finite sums.

**Theorem 1.6 (Constant outer coefficients).**

$$\forall p: \operatorname{Polynomial}\left(\mathbb{Q}\right), \operatorname{diagonal}\left(\operatorname{C}\left(p\right)\right) = \operatorname{Polynomial.eval2RingHom}\left(\operatorname{PowerSeries.C}\left(\right), 1 + X\right)\left(p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_C` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant in the outer variable maps to the polynomial coefficient evaluated at 1+X.

**Theorem 1.7 (The outer variable).**

$$\operatorname{diagonal}\left(X\right) = X$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The outer variable maps to the same target X used by the coefficient evaluation.

**Theorem 1.8 (Admissible substitution transport).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \forall b: \operatorname{PowerSeries}\left(\operatorname{Polynomial}\left(\mathbb{Q}\right)\right), (\operatorname{constantCoeff}\left(b\right) = 0) \Rightarrow ((\operatorname{constantCoeff}\left(\operatorname{diagonal}\left(b\right)\right) = 0) \Rightarrow (\operatorname{diagonal}\left(\operatorname{PowerSeries.subst}\left(b, f\right)\right) = \operatorname{PowerSeries.subst}\left(\operatorname{diagonal}\left(b\right), f\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_subst` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a rational outer series f, a polynomial-coefficient inner series b, and zero constant coefficients of b and D(b), the diagonal commutes with formal substitution. Both zero-constant hypotheses are part of the statement.

**Theorem 1.9 (Rational series are fixed).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{diagonal}\left(\operatorname{PowerSeries.map}\left(\operatorname{algebraMap}\left(\mathbb{Q}, \operatorname{Polynomial}\left(\mathbb{Q}\right)\right), f\right)\right) = f$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping a rational series coefficientwise into Q[Y] and then applying D returns the original series.

**Definition 1.10 (The two COMMENTS assertions).**

$$claim = ((\exists a: (\mathbb{N} \to \mathbb{Z}), \operatorname{IsSourceSequence}\left(a\right)) \land (\forall a: (\mathbb{N} \to \mathbb{Z}), (\operatorname{IsSourceSequence}\left(a\right)) \Rightarrow (\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \Rightarrow ((\operatorname{Int.ModEq}\left((p: \mathbb{Z}), a\left(p\right) + a\left(p + 1\right) - 2, 0\right)) \land (\operatorname{Int.ModEq}\left(((p + 1) \cdot p: \mathbb{Z}), a\left(p + 1\right), 1\right))))))$$

*Formalization.* `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.claim` (`✓ std3`).

*Citation.* Mélika Tebni (2022). *OEIS A350759, COMMENTS prime congruences*. URL: <https://oeis.org/A350759>.

*Commentary.*

OEIS A350759, revision 17, COMMENTS (unpaginated): "Conjectures: For all p prime, (a(p) + a(p+1) - 2) is congruent to 0 (mod p)," "a(p+1) is congruent to 1 (mod ((p+1)*p))." The second line inherits the prime quantifier. The formula also asserts existence of an integer sequence with the source EGF and covers every sequence with that EGF. Subtraction takes place in Z; the product (p+1)*p is formed in N and then cast to Z.

**Theorem 1.11 (Both prime congruences hold).**

$$(\exists a: (\mathbb{N} \to \mathbb{Z}), \operatorname{IsSourceSequence}\left(a\right)) \land (\forall a: (\mathbb{N} \to \mathbb{Z}), (\operatorname{IsSourceSequence}\left(a\right)) \Rightarrow (\forall p: \mathbb{N}, (\operatorname{Nat.Prime}\left(p\right)) \Rightarrow ((\operatorname{Int.ModEq}\left((p: \mathbb{Z}), a\left(p\right) + a\left(p + 1\right) - 2, 0\right)) \land (\operatorname{Int.ModEq}\left(((p + 1) \cdot p: \mathbb{Z}), a\left(p + 1\right), 1\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.result` (`✓ std3`). ∎

*Resolves.* `Problems/tebni350759` (proved) by `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tebni350759","declaration_gid":"D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mélika Tebni (2022). *OEIS A350759, COMMENTS prime congruences*. URL: <https://oeis.org/A350759>.

*Commentary.*

The rising-factorial expansion gives an integer factorial-scaled coefficient of the form 1+n*z at every index n. The index-zero expansion term is one; each other term is a multiple of n. The source differential equation gives an EGF convolution. Interior prime binomial coefficients vanish modulo p, and Wilson's theorem settles the endpoint, including a separate p=2 case. Combining the residues modulo p and p+1 proves the product congruence. Hanna's expansion in OEIS A176118 is prior art.

## References

- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.IsSourceSequence`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.claim`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_C`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_X`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_apply`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_continuous`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_lift`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.diagonal_subst`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.result`
- Truth anchor: `D5/S3/Arith/Congruence/TebniA350759PrimeCongruences.sourceSeries`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](../../../S1/Recurrence/Algebraic/DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure](../../../S1/Recurrence/Algebraic/HannaLogarithmicPowerClosure.md)
- Dependency: [D5/S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree](../../../S1/Recurrence/Parity/ExponentialImplicitParityPeriodThree.md)
