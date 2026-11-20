# A sharp obstruction for least nondivisor four

## Abstract

For the factor six, every range constant below three fails in the subset-sum inverse theorem.

**Theorem 1.1 (Every range constant below three fails).**

$$\forall\theta\in\mathbb{R},\theta<3\implies\exists\varepsilon>0,\forall K\in\mathbb{N},\exists E,T\in\mathbb{N},\exists A\subseteq[1,E],(K\leq T\land1\leq E\land\theta E\leq6T\land \frac{E}{4}+\varepsilon T\leq\Vert A\Vert\land(\forall B\subseteq A,\sum_{x\in B}x\neq6T))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSums/Erdos361InverseRange.every_range_below_three_fails` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mateo Matijasevick (2026). *Forbidden subset sums in a linear range: an inverse theorem and the Erdős-Graham irregularity problem*. DOI: [10.48550/arXiv.2611.17205](https://doi.org/10.48550/arXiv.2611.17205). URL: <https://arxiv.org/html/2611.17205v1#S9>.

*Commentary.*

Use all multiples of five in the interval and add a terminal segment of the residue class one. The target has residue four, so any representation needs at least four terms from the terminal segment. The sum of those terms exceeds the target. The two surviving residue classes give a positive density excess.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSums/Erdos361InverseRange.every_range_below_three_fails`
