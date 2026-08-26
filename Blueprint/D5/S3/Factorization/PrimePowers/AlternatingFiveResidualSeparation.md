# Prime-Power and Finite-Quotient Separation for A5

## Abstract

Prime-power quotient observations of A5 are strictly weaker than all finite quotients.

**Theorem 1.1 (Prime-power observations of A5 are completely blind).**

$$\begin{gathered}(\forall p \in \mathbb{N}, \operatorname{Prime}(p) \Rightarrow \operatorname{pGroupResidual}(p, A_{5}) = \operatorname{topSubgroup}(A_{5})) \land\\{}\operatorname{primePowerResidual}(A_{5}) = \operatorname{topSubgroup}(A_{5}) \land\\{}\operatorname{primePowerQuotientObserver}(A_{5}) = 1 \land\\{}(\exists H \in \operatorname{FiniteQuotientIndex}(A_{5}), \operatorname{kernel}(H) = \operatorname{trivialSubgroup}(A_{5})) \land\\{}\operatorname{finiteResidual}(A_{5}) = \operatorname{trivialSubgroup}(A_{5}) \land\\{}\operatorname{finiteResidual}(A_{5}) < \operatorname{primePowerResidual}(A_{5}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/PrimePowers/AlternatingFiveResidualSeparation.alternating_five_residual_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime p, the fixed-prime residual constructed from all finite p-group quotient channels is the whole alternating group A5. The canonical residual over all primes is likewise the whole group, and its canonical joint observer is the trivial map.

The all-finite quotient family contains a channel whose kernel is the trivial subgroup, representing the identity finite quotient. Consequently its canonical residual is trivial and is strictly smaller than the prime-power residual.

## References

- Truth anchor: `D5/S3/Factorization/PrimePowers/AlternatingFiveResidualSeparation.alternating_five_residual_separation`
- Dependency: [D5/S3/Factorization/PrimePowers/FinitePrimePowerQuotientCompleteness](FinitePrimePowerQuotientCompleteness.md)
- Dependency: [D5/S3/Factorization/PrimePowers/SimpleToPGroupTrivial](SimpleToPGroupTrivial.md)
