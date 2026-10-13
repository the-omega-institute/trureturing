# M-resistant qudit states exist in every admissible range

## Abstract

For every N at least three and every m at most N minus two, a normalized pure state is entangled after every m-particle loss and fully separable after every (m+1)-particle loss.

**Definition 1.1 (Resistance to particle loss).**

$$\forall V \in Type,\; \forall L \in Type,\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)], [\operatorname{Fintype}\left(L\right)] [\operatorname{DecidableEq}\left(L\right)], \forall m \in \mathbb{N},\; \forall psi \in ((V)\to L)\to \mathbb{C},\; \operatorname{IsMResistant}\left(m, psi\right) \Leftrightarrow ((\neg \operatorname{IsFullySeparableLocal}\left(\operatorname{rankOneDensity}\left(psi\right)\right)) \land ((\forall J \in \operatorname{Finset}\left(V\right),\; (\operatorname{Finset.card}\left(J\right) = m) \Rightarrow (\neg \operatorname{IsFullySeparableLocal}\left(\operatorname{partialTraceLocal}\left(\operatorname{rankOneDensity}\left(psi\right), J\right)\right))) \land (\forall J \in \operatorname{Finset}\left(V\right),\; (\operatorname{Finset.card}\left(J\right) = m + 1) \Rightarrow (\operatorname{IsFullySeparableLocal}\left(\operatorname{partialTraceLocal}\left(\operatorname{rankOneDensity}\left(psi\right), J\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/MResistantQuditExistence.IsMResistant` (`✓ std3`).

*Citation.* G. M. Quinta; R. André; A. Burchardt; K. Życzkowski (2019). *Cut-resistant links and multipartite entanglement resistant to particle loss*. DOI: [10.1103/PhysRevA.100.062329](https://doi.org/10.1103/PhysRevA.100.062329). URL: <https://arxiv.org/abs/1908.10390v1>.

*Commentary.*

Quinta, Andre, Burchardt and Zyczkowski, arXiv:1908.10390v1, Section III, page 3: "Definition: (m-resistance) An entangled state of N parties is called m-resistant if:" "It remains entangled as any m of its N subsystems are traced away;" "It becomes separable if a partial trace is performed over an arbitrary set of m + 1 subsystems." The initial entangled state gives the first conjunct. Separability means full separability, as in the later pure-state restatement. V labels sites and L labels a local basis; psi is the amplitude function. Both loss quantifiers range over every finite loss set J.

The pure density uses D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity. Its implicit index type n is V -> L here; its amplitude argument precedes the row and column indices x and y. The outer product Matrix.vecMulVec psi (star psi) has entries:

$$
\forall n \in Type,\; \forall psi \in (n)\to \mathbb{C},\; \forall x \in n,\; \forall y \in n,\; \operatorname{D5.S3.Quantum.PureState.PureStateHandshake.rankOneDensity}\left(psi, x, y\right) = psi\left(x\right) \cdot \operatorname{star}\left(psi\left(y\right)\right)
$$

**Definition 1.2 (The qudit existence conjecture).**

$$claim \Leftrightarrow (\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; (3 \le N) \Rightarrow ((m + 2 \le N) \Rightarrow (\exists d \in \mathbb{N},\; \exists psi \in ((\operatorname{Fin}\left(N\right))\to \operatorname{Fin}\left(d\right))\to \mathbb{C},\; (\sum_{x:(\operatorname{Fin}\left(N\right))\to \operatorname{Fin}\left(d\right)} (\operatorname{Complex.normSq}\left(psi\left(x\right)\right)) = 1) \land (\operatorname{IsMResistant}\left(m, psi\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/MResistantQuditExistence.claim` (`✓ std3`).

*Citation.* G. M. Quinta; R. André; A. Burchardt; K. Życzkowski (2019). *Cut-resistant links and multipartite entanglement resistant to particle loss*. DOI: [10.1103/PhysRevA.100.062329](https://doi.org/10.1103/PhysRevA.100.062329). URL: <https://arxiv.org/abs/1908.10390v1>.

*Commentary.*

Quinta, Andre, Burchardt and Zyczkowski, arXiv:1908.10390v1, Section V, page 10: "Conjecture 1. For any N and m, there exists an m-resistant N-qudit state in some local dimension d." Fin N replaces particle labels by 0,...,N-1 and Fin d labels a common local basis. Natural m is nonnegative. The whole admissible pure-state range is N >= 3 and m + 2 <= N: a remaining single particle cannot be entangled. Complex.normSq is the squared absolute value, so the finite sum fixes unit normalization.

**Theorem 1.3 (Existence by shared labels and localized bits).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/MResistantQuditExistence.result` (`✓ std3`). ∎

*Resolves.* `Problems/quinta-andre-burchardt-zyczkowski-2019-m-resistant-states` (proved) by `D5/S3/Quantum/Entanglement/MResistantQuditExistence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"quinta-andre-burchardt-zyczkowski-2019-m-resistant-states","declaration_gid":"D5/S3/Quantum/Entanglement/MResistantQuditExistence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* G. M. Quinta; R. André; A. Burchardt; K. Życzkowski (2019). *Cut-resistant links and multipartite entanglement resistant to particle loss*. DOI: [10.1103/PhysRevA.100.062329](https://doi.org/10.1103/PhysRevA.100.062329). URL: <https://arxiv.org/abs/1908.10390v1>.

*Commentary.*

Put k = N-m. Superpose the two bit branches of each k-element subset S. Every site records the common label S, while the branch bit is recorded only at sites in S. Tracing out m+1 sites meets every S and removes every off-diagonal entry; the diagonal marginal is a convex mixture of products of local basis projectors. After tracing out m sites, the kept k-element set supplies a surviving nonzero coherence. Exchanging one bit produces a zero diagonal, which the full-separability exchange theorem excludes. The same obstruction proves initial entanglement. The Lean construction embeds labels from Finset (Fin N) times Bool into Fin d by Fintype.equivFin; this full carrier has cardinality 2^(N+1), and only k-element labels occur in its support.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/MResistantQuditExistence.IsMResistant`
- Truth anchor: `D5/S3/Quantum/Entanglement/MResistantQuditExistence.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/MResistantQuditExistence.result`
- Dependency: [D5/S3/Quantum/Entanglement/FullySeparableExchangeObstruction](FullySeparableExchangeObstruction.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../Information/OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
