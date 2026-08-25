# Chernoff Information Zero Criterion

## Abstract

Chernoff information vanishes exactly when two finite probability laws agree.

**Theorem 1.1 (Same law iff Chernoff information is zero).**

$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)],\\{}\forall P, Q: \iota \to \mathbb{R},\\{}((\forall i, 0 \le \operatorname{P}(i)) \land \sum_{i} \operatorname{P}(i) = 1 \land\\{}(\forall i, 0 \le \operatorname{Q}(i)) \land \sum_{i} \operatorname{Q}(i) = 1) \Rightarrow\\{}[(P = Q \iff \operatorname{ChernoffInformation}(P, Q) = 0) \land\\{}(0 < \operatorname{ChernoffInformation}(P, Q) \Rightarrow P \neq Q)].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/ChernoffInformationZeroCriterion.same_law_iff_chernoff_information_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The optimized coefficient is the infimum, over lambda in the closed unit interval, of the finite sum of p(i)^lambda times q(i)^(1-lambda). Chernoff information is its negative extended-real logarithm, so a zero coefficient has infinite information rather than being collapsed by the totalized real logarithm at zero.

At lambda one half, the coefficient is the repository's canonical Bhattacharyya affinity. If the optimized coefficient is one, this half-parameter slice is forced to be one; the frozen complementary square bound then forces total variation to vanish and hence the two laws to agree.

The second public clause records the source consequence: a strictly positive exponent certifies a genuine difference between the laws, independently of how many repeated samples are later taken.

## References

- Truth anchor: `D5/S3/Estimation/ErrorExponents/ChernoffInformationZeroCriterion.same_law_iff_chernoff_information_zero`
- Dependency: [D5/S3/TotalVariation/Bhattacharyya](../../TotalVariation/Bhattacharyya.md)
