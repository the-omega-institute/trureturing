# Hanna's A158119 parity conjecture

## Abstract

Parity of the original factorial-product OGF, its reversion quotient, and its unsigned even coefficients.

Paul D. Hanna's OEIS A158119 conjecture states: a(m) == 1 (mod 2) iff m is a power of 2 or m=0. The original integer OGF and quotient are taken from A155585 and A157308. The pinned source is oeis/oeisdata commit 5d3c6f683f5e0f2876df39773b7e49710c4f5f80, seq/A158/A158119.seq, seq/A157/A157308.seq and seq/A155/A155585.seq. The source definition and bounded prior-work limits are documented in hanna2009a158119.

Related prior work: Vladimir Reshetnikov's ProveIt article at commit b61f8e7e32b64b32a925c2d3cffab80bc20fb4c6, SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a290569-power-weighted-dyck-moments/article.tex, proves powers-of-two parity for the quartic sequence A338634. The inspected text does not explicitly state the original A158119 result. No priority or new-method claim is made here.

**Definition 1.1 (The original factorial-product summand).**

Lean statement: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.summand`

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA158119Parity.summand` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A158119, parity of the original unsigned reversion bisection*. URL: <https://oeis.org/A158119>.

*Commentary.*

For natural n, summand n is n! times X^n times the product, for k=1,...,n, of the formal unit inverse of 1+2kX. The product at n=0 is 1. Every denominator has constant coefficient 1.

**Definition 1.2 (The original ordinary generating function).**

Lean statement: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.F`

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA158119Parity.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A158119, parity of the original unsigned reversion bisection*. URL: <https://oeis.org/A158119>.

*Commentary.*

The coefficient at degree d is the sum of the original summand coefficients for n=0,...,d. All omitted terms are divisible by X^(d+1). This is the coefficientwise meaning of the infinite ordinary generating series in A155585; factorials multiply the coefficients.

**Definition 1.3 (The compositional inverse).**

Lean statement: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.Q`

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA158119Parity.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A158119, parity of the original unsigned reversion bisection*. URL: <https://oeis.org/A158119>.

*Commentary.*

Q is the unique zero-constant compositional inverse of X*F over the integers. The coefficient of X in X*F is 1, so Mathlib's unit-linear reversion applies.

**Definition 1.4 (The normalized quotient).**

Lean statement: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.B`

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA158119Parity.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A158119, parity of the original unsigned reversion bisection*. URL: <https://oeis.org/A158119>.

*Commentary.*

B is F substituted at Q. Substitution into (X*F)(Q)=X gives B*Q=X. Its constant coefficient is 1. Since Q is nonzero and the integer power series ring is a domain, this uniquely specifies the original quotient X/Q.

**Definition 1.5 (The original unsigned bisection).**

Lean statement: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.a`

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA158119Parity.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A158119, parity of the original unsigned reversion bisection*. URL: <https://oeis.org/A158119>.

*Commentary.*

a(m) is the natural absolute value of the integer coefficient of degree 2m in B, for every natural m including zero.

**Theorem 1.6 (The quotient identity).**

Lean statement: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.quotient_equation`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA158119Parity.quotient_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A158119, parity of the original unsigned reversion bisection*. URL: <https://oeis.org/A158119>.

*Commentary.*

The original compositional inverse equation gives this identity directly. It is used in the parity proof to determine Q after reduction modulo two.

**Theorem 1.7 (The full parity statement).**

$$\forall m: \mathbb{N}, \operatorname{Odd}\left(a\left(m\right)\right) \iff (m = 0 \lor (\exists j: \mathbb{N}, m = 2^{j}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA158119Parity.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a158119-original-parity` (proved) by `D5/S1/Recurrence/Algebraic/HannaA158119Parity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a158119-original-parity","declaration_gid":"D5/S1/Recurrence/Algebraic/HannaA158119Parity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2009). *OEIS A158119, parity of the original unsigned reversion bisection*. URL: <https://oeis.org/A158119>.

*Commentary.*

Modulo two the factors 2k vanish and n! vanishes for n at least two. Thus F reduces to 1+X, B reduces to 1+Q, and Q+Q^2=X. Mathlib's uniqueness of reversion identifies Q with the existing reduced Catalan series. CatalanCompositionSquareParity.binary_catalan supplies its powers-of-two support. Integer absolute value preserves oddness, and restricting the degree to 2m gives precisely the displayed equivalence. The zero index is included explicitly. This is an application of existing reversion and Catalan parity results; no new proof method is claimed.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.B`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.F`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.Q`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.a`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.quotient_equation`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.result`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA158119Parity.summand`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](../Invariants/CatalanCompositionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Residue/NegativePowerDiagonalModPrime](../Residue/NegativePowerDiagonalModPrime.md)
