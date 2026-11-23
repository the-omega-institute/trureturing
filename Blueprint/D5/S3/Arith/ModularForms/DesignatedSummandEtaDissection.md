# Integral reciprocal and square dissections

## Abstract

Parity dissections of the designated-summand generating series and its inverse.

The Jacobi product identities turn the parity dissection into an identity between Euler units. The coefficient map from integers to rationals is injective, so the reciprocal dissection holds integrally. Pairing odd Euler factors at q and −q gives the sign norm used to square F. The factor W reduces modulo four to f6 squared, which is supported on even degrees.

Lemma 2.2 of Yaqubi and Mirzavaziri gives the prime-power Frobenius congruence. The dyadic lift uses the iterated Frobenius over ZMod 2, then raises the integral congruence to the required modulus.

**Definition 1.1 (reduce).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.reduce`

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.reduce` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

Reduce every integer coefficient modulo the given natural modulus.

**Theorem 1.2 (coeff_reduce_eq_zero).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.coeff_reduce_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.coeff_reduce_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

A reduced coefficient vanishes exactly when the modulus divides the original coefficient.

**Theorem 1.3 (map_mod_eq_iff).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.map_mod_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.map_mod_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

Two reductions coincide exactly when the constant series of the modulus divides the difference.

**Theorem 1.4 (reduce_lift).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.reduce_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.reduce_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

For every integral formal series p(q) and natural j and r, the coefficientwise reduction of p(q)^(2^(j+1+r)) modulo 2^(j+1) equals the reduction of p(q^(2^(r+1)))^(2^j) at the same modulus.

**Theorem 1.5 (reduce_lift_mul).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.reduce_lift_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.reduce_lift_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

For every integral formal series p(q) and natural j, r and t, the coefficientwise reduction of p(q)^(2^(j+1+r)·t) modulo 2^(j+1) equals the reduction of p(q^(2^(r+1)))^(2^j·t) at the same modulus.

**Definition 1.6 (H).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H`

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The inverse unit of the generating series F.

**Definition 1.7 (H0).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H0`

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The Euler quotient f1^2 f4^2 f6^4 divided by f2^2 f3^2 f12^2, whose degree doubling is the even part of H over the integers.

**Definition 1.8 (T).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.T`

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The Euler quotient f1^4 f6^2 divided by f2^2 f3^2. Over the integers, the odd part of H is −q T(q⁴).

**Theorem 1.9 (FH).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.FH`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.FH` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The product of F and H is one.

**Theorem 1.10 (H_dissection).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H_dissection`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H_dissection` (`✓ std3`). ∎

*Citation.* James A. Sellers (2023). *New Infinite Families of Congruences Modulo Powers of 2 for 2-Regular Partitions with Designated Summands*. DOI: [10.48550/arXiv.2306.15130](https://doi.org/10.48550/arXiv.2306.15130). URL: <https://arxiv.org/abs/2306.15130v1>.

*Commentary.*

Over the integers, H(q) is H0(q²) minus q T(q⁴).

**Theorem 1.11 (H_support).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The integral coefficient of H in degree 4n+3 vanishes for every natural n.

**Definition 1.12 (E).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.E`

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The integral series such that E(q²) is the even part of F(q) squared.

**Definition 1.13 (W).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.W`

*Formalization.* `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.W` (`✓ std3`).

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

The integral Euler quotient f2^4 f6^4 divided by f1^8 f3^4.

**Theorem 1.14 (F_square).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.F_square`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.F_square` (`✓ std3`). ∎

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

Over the integers, F(q) squared is E(q²) plus 2q W(q²).

**Theorem 1.15 (W_support).**

Lean statement: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.W_support`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.W_support` (`✓ std3`). ∎

*Citation.* Daniel Yaqubi and Madjid Mirzavaziri (2026). *Partitions with designated summands: k-tuples and their congruences*. DOI: [10.48550/arXiv.2611.05623](https://doi.org/10.48550/arXiv.2611.05623). URL: <https://arxiv.org/abs/2611.05623v1>.

*Commentary.*

For every natural n, the coefficient of degree 2n+1 in the integral series W is divisible by four.

## References

- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.E`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.FH`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.F_square`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H0`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H_dissection`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.H_support`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.T`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.W`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.W_support`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.coeff_reduce_eq_zero`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.map_mod_eq_iff`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.reduce`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.reduce_lift`
- Truth anchor: `D5/S3/Arith/ModularForms/DesignatedSummandEtaDissection.reduce_lift_mul`
- Dependency: [D5/S1/Recurrence/Residue/CompositionalSquareDyadicDenominators](../../../S1/Recurrence/Residue/CompositionalSquareDyadicDenominators.md)
- Dependency: [D5/S3/Arith/ModularForms/DesignatedSummandThetaDissection](DesignatedSummandThetaDissection.md)
- Dependency: [D5/S3/Combinatorics/Partitions/DesignatedSummands](../../Combinatorics/Partitions/DesignatedSummands.md)
