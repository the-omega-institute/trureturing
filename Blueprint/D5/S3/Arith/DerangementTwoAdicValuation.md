# Two-Adic Valuation of Derangement Numbers

## Abstract

Derangement parity and valuation exclude nontrivial powers at indices 3 mod 4.

Write D_n for Mathlib's natural number numDerangements n and v_2 for padicValNat 2. The first declaration states all three clauses of candidate theorem 4.102 in one conjunction: the parity law, the exact valuation from index two onward, and the resulting divisibility of a power exponent. Natural subtraction is used in n - 1.

**Theorem 1.1 (Parity, exact valuation, and exponent divisibility).**

$$\begin{gathered}(\forall n \in \mathbb{N}, \operatorname{Odd}(D_{n}) \Leftrightarrow \operatorname{Even}(n)) \land\\(\forall n \in \mathbb{N}, 2 \le n \Rightarrow v_{2}(D_{n}) = v_{2}(n - 1)) \land\\(\forall n, b, k \in \mathbb{N}, 2 \le n \Rightarrow D_{n} = b^{k} \Rightarrow k \mid v_{2}(n - 1)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DerangementTwoAdicValuation.numDerangements_parity_valuation_and_power_exponent` (`✓ std3`). ∎

*Citation.* Piotr Miska (2016). *Arithmetic properties of the sequence of derangements*. DOI: [10.1016/j.jnt.2015.11.014](https://doi.org/10.1016/j.jnt.2015.11.014).

*Commentary.*

Miska (2016, Section 6.1, printed page 48) explicitly records the identity v_2(D_n) = v_2(n - 1), and the same article records the parity law. The bundled exponent-divisibility clause is the immediate repository corollary: if D_n = b^k, the power rule makes k divide v_2(D_n). The FromLiterature provenance is attached to the whole atom because its content-bearing parity and exact-valuation clauses are literature-attested; this paragraph identifies the bundled third clause as repository-derived.

The Lean proof reconstructs the parity invariant by two-step induction through numDerangements_add_two. Consecutive derangement numbers then have odd sum. Factoring D_(m+2) as (m+1)(D_m+D_(m+1)) and cancelling the odd factor with the multiplicative p-adic valuation law yields the exact identity. The result includes b = 0 under Mathlib's convention padicValNat 2 0 = 0 and contains no numerical certificate.

**Theorem 1.2 (Indices three modulo four exclude nontrivial powers).**

$$\forall t, b, k \in \mathbb{N}, 2 \le k \Rightarrow D_{4\cdot t + 3} \neq b^{k}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/DerangementTwoAdicValuation.numDerangements_four_mul_add_three_ne_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n = 4t + 3, natural subtraction gives n - 1 = 2(2t + 1), whose two-adic valuation is exactly one. The exponent-divisibility clause of the preceding declaration would force every exponent k of a power representation to divide one, contradicting 2 <= k. This is the directed companion 4.103 -> 4.102 (consumer -> prerequisite).

Zhi-Wei Sun's 2025 OEIS A000166 comment conjectures that, for n > 2, only D_4 = 3^2 is a perfect power. This repository-derived theorem settles only the infinite progression n congruent to 3 modulo 4; it does not prove that conjecture, and D_4 remains outside its scope.

## References

- Truth anchor: `D5/S3/Arith/DerangementTwoAdicValuation.numDerangements_four_mul_add_three_ne_pow`
- Truth anchor: `D5/S3/Arith/DerangementTwoAdicValuation.numDerangements_parity_valuation_and_power_exponent`
