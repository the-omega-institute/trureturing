# The odd predecessor criterion

## Abstract

The odd predecessor criterion

**Definition 1.1 (The odd predecessor part).**

$$\forall n \in \mathbb{N},\; \operatorname{oddPredecessorPart}\left(n\right) = \operatorname{ordCompl}\left(2, \prod_{q \in \operatorname{nonFermatFactors}\left(n\right)} (q - 1)\right)$$

*Formalization.* `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Criterion.oddPredecessorPart` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Graeme Cohen (1997). *On a conjecture of Mąkowski and Schinzel*. DOI: [10.4064/cm-74-1-1-8](https://doi.org/10.4064/cm-74-1-1-8). URL: <https://doi.org/10.4064/cm-74-1-1-8>.

*Commentary.*

Take the odd part of the product of q-1 over the distinct non-Fermat odd prime divisors q of n. The empty product gives the value 1.

**Definition 1.2 (The predecessor abundancy factor).**

$$\forall n \in \mathbb{N},\; \operatorname{psi}\left(n\right) = \operatorname{abundancyIndex}\left(\operatorname{oddPredecessorPart}\left(n\right)\right) \cdot \prod_{q \in \operatorname{nonFermatFactors}\left(n\right)} (1 - \frac{1}{q})$$

*Formalization.* `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Criterion.psi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Graeme Cohen (1997). *On a conjecture of Mąkowski and Schinzel*. DOI: [10.4064/cm-74-1-1-8](https://doi.org/10.4064/cm-74-1-1-8). URL: <https://doi.org/10.4064/cm-74-1-1-8>.

*Commentary.*

Multiply the odd predecessor part's abundancy index by the Euler factors 1-1/q of the non-Fermat support. This factor is positive for every natural input.

**Theorem 1.3 (A direct sigma-totient lower bound).**

$$\forall n \in \mathbb{N},\; \operatorname{psi}\left(n\right) \cdot n \le 2 \cdot \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right) \land \left(\left(\operatorname{Odd}\left(n\right) \Rightarrow \operatorname{psi}\left(n\right) \cdot n \le \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right)\right) \land \left(\operatorname{Nonempty}\left(\operatorname{nonFermatFactors}\left(n\right)\right) \Rightarrow \left(\operatorname{psi}\left(n\right) \cdot n < 2 \cdot \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right) \land \left(\operatorname{Odd}\left(n\right) \Rightarrow \operatorname{psi}\left(n\right) \cdot n < \operatorname{sigma}\left(1, \operatorname{totient}\left(n\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Criterion.psi_mul_le_sigma_totient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Graeme Cohen (1997). *On a conjecture of Mąkowski and Schinzel*. DOI: [10.4064/cm-74-1-1-8](https://doi.org/10.4064/cm-74-1-1-8). URL: <https://doi.org/10.4064/cm-74-1-1-8>.

*Commentary.*

For every natural n, psi(n)n is at most twice sigma(phi(n)); the factor two is omitted for odd n. Both comparisons are strict when the non-Fermat support is nonempty. Zero is included. The constants are sharp: n=2 gives equality in the first comparison and n=1 in the odd comparison. These examples also prevent unconditional strictness. The proof passes to the odd squarefree core. Its Fermat part f has power-of-two totient, while the odd predecessor part U is coprime to that totient. Divisibility by phi(f)U gives the weak bound; a nonempty non-Fermat support contributes another factor of two and gives the strict improvement of the power-of-two abundancy index. This also recovers the sufficient condition in Cohen's 1997 Theorem 3. Choose an odd prime r_i dividing q_i-1 for each non-Fermat q_i, and group equal choices with sizes c_j. Then the product R of the r_i divides U. Hence psi is at least the product of geom(r_j,c_j) times the group's factors (q-1)/q. Cohen's group conditions make this product at least 1. When the non-Fermat support is nonempty, the strict comparison gives sigma(phi(m))>m for the odd input. Thus the group conditions imply psi>=1; no converse is asserted.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Criterion.oddPredecessorPart`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Criterion.psi`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Criterion.psi_mul_le_sigma_totient`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/Fermat](../Fermat.md)
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/PrimeDeletion](../PrimeDeletion.md)
