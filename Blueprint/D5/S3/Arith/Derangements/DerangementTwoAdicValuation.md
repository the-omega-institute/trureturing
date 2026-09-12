# Parity and Binary Valuation of Derangement Numbers

## Abstract

Derangement numbers have index-controlled parity and exact binary valuation.

Write D_n for Mathlib's numDerangements n, and write v_2 for padicValNat 2. All variables below range over natural numbers.

**Theorem 1.1 (Parity alternates with the index).**

$$\forall n \in \mathbb{N}, Odd\left(D_{n}\right) \iff Even\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Derangements/DerangementTwoAdicValuation.numDerangements_odd_iff_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Piotr Miska (2016). *Arithmetic Properties of the Sequence of Derangements and its Generalizations*. DOI: [10.1016/j.jnt.2015.11.014](https://doi.org/10.1016/j.jnt.2015.11.014).

*Acknowledgement.* OEIS Foundation Inc.; Zhi-Wei Sun (2025). *OEIS A000166, subfactorial or rencontres numbers*. URL: <https://oeis.org/A000166>.

*Commentary.*

The initial values are D_0=1 and D_1=0. For the induction step, D_(n+2)=(n+1)(D_n+D_(n+1)). If n is even, the multiplier and the sum are odd; if n is odd, the multiplier is even. Thus D_n is odd exactly when n is even.

**Theorem 1.2 (The exact binary valuation).**

$$\forall n \in \mathbb{N}, 2 \le n \Rightarrow \left(v_{2}\right)\left(D_{n}\right) = \left(v_{2}\right)\left(n - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Derangements/DerangementTwoAdicValuation.padicValNat_numDerangements` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Piotr Miska (2016). *Arithmetic Properties of the Sequence of Derangements and its Generalizations*. DOI: [10.1016/j.jnt.2015.11.014](https://doi.org/10.1016/j.jnt.2015.11.014).

*Acknowledgement.* OEIS Foundation Inc.; Zhi-Wei Sun (2025). *OEIS A000166, subfactorial or rencontres numbers*. URL: <https://oeis.org/A000166>.

*Commentary.*

For n at least two, D_(n-2) and D_(n-1) have opposite parity, so their sum is odd and has binary valuation zero. Applying the valuation product rule to D_n=(n-1)(D_(n-2)+D_(n-1)) leaves exactly the valuation of n-1. Miska records the same identity.

**Theorem 1.3 (A power exponent divides the preceding-index valuation).**

$$\forall n, b, k \in \mathbb{N}, \left(2 \le n \land D_{n} = b^{k}\right) \Rightarrow k \mid \left(v_{2}\right)\left(n - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Derangements/DerangementTwoAdicValuation.exponent_dvd_padicValNat_sub_one_of_numDerangements_eq_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Piotr Miska (2016). *Arithmetic Properties of the Sequence of Derangements and its Generalizations*. DOI: [10.1016/j.jnt.2015.11.014](https://doi.org/10.1016/j.jnt.2015.11.014).

*Acknowledgement.* OEIS Foundation Inc.; Zhi-Wei Sun (2025). *OEIS A000166, subfactorial or rencontres numbers*. URL: <https://oeis.org/A000166>.

*Commentary.*

Substitute D_n=b^k into the exact valuation identity. The valuation of b^k is k times the valuation of b, so k divides v_2(n-1). This also includes b=0 under padicValNat's value zero at zero. Sun's OEIS comment gives a broader perfect-power observation checked through n=1000; the universal divisibility statement here is derived from the preceding theorem.

## References

- Truth anchor: `D5/S3/Arith/Derangements/DerangementTwoAdicValuation.exponent_dvd_padicValNat_sub_one_of_numDerangements_eq_pow`
- Truth anchor: `D5/S3/Arith/Derangements/DerangementTwoAdicValuation.numDerangements_odd_iff_even`
- Truth anchor: `D5/S3/Arith/Derangements/DerangementTwoAdicValuation.padicValNat_numDerangements`
