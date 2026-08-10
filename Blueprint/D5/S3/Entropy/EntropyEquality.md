# Equality Cases for Finite Shannon Entropy

## Abstract

The two endpoints of the finite Shannon-entropy bracket in nats characterize the uniform law and point masses.

**Theorem 1.1 (Maximum entropy characterizes the uniform law).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)] [\operatorname{Nonempty}(\iota)],\\\forall p: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \Rightarrow\\H(p)=\log(\operatorname{card}(\iota)) \Leftrightarrow \\p=(i\mapsto \operatorname{card}(\iota)^{-1}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/EntropyEquality.entropy_eq_log_card_iff_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entropy bucket already brackets every normalized nonnegative mass function between 0 and log card. This theorem settles the upper endpoint: the maximum is attained exactly at the uniform law. Together with the point-mass characterization below, it identifies both equality cases of that bracket.

The upper endpoint is a composition of two deposited results. The entropy-divergence identity says that divergence from the uniform law is exactly the entropy deficit log card - H(p), while GibbsEquality's zero-divergence criterion says that this divergence vanishes exactly when the two laws agree. The identity was originally proved to pin the entropy definition against corruption; here it serves as an ingredient for a different theorem, so a deposited result has become raw material.

The hypotheses are nonnegativity and normalization only; no strict positivity is required, and zero-mass letters are permitted. The units are nats because shannonEntropy uses Real.log. Nonempty is required only for this upper endpoint, where cardinality zero would make the uniform law ill-defined; the lower endpoint carries no Nonempty hypothesis.

No quantitative statement is made about how far entropy falls below the bound for a near-uniform law: there is no stability theorem or deficit estimate. Nothing is claimed about the equality cases of conditional entropy.

**Theorem 1.2 (Zero entropy characterizes point masses).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\\forall p: \iota\to \mathbb{R},\\((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \Rightarrow\\H(p)=0 \Leftrightarrow \\\exists i, p=(j\mapsto \begin{cases}1,&j=i\\0,&j\neq i\end{cases}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/EntropyEquality.entropy_eq_zero_iff_point_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This theorem settles the lower endpoint of the same entropy bracket: entropy vanishes exactly at a point mass. Here point mass has the exact form displayed in the statement: one index carries mass 1 and every other index carries mass 0.

The lower endpoint is not a rewrite of entropy nonnegativity. Each mass lies in the unit interval, so every Real.negMulLog summand is nonnegative. A vanishing finite sum of nonnegative terms forces every summand to vanish, and the zeros of Real.negMulLog on that interval are exactly 0 and 1. The unit sum then leaves precisely one index carrying mass 1 and forces all remaining masses to be 0.

As above, the only distributional hypotheses are nonnegativity and normalization; strict positivity is not assumed, and zero-mass letters are permitted. The units are nats. Unlike the maximum statement, this signature needs no Nonempty instance: normalization itself rules out an empty alphabet, while no uniform law has to be formed.

This equality characterization is qualitative only. It provides no stability or entropy-deficit estimate for laws near a point mass, and it does not characterize equality for conditional entropy.

## References

- Truth anchor: `D5/S3/Entropy/EntropyEquality.entropy_eq_log_card_iff_uniform`
- Truth anchor: `D5/S3/Entropy/EntropyEquality.entropy_eq_zero_iff_point_mass`
- Dependency: [D5/S3/Divergence/GibbsEquality](../Divergence/GibbsEquality.md)
- Dependency: [D5/S3/Entropy/EntropyDivergenceIdentity](EntropyDivergenceIdentity.md)
