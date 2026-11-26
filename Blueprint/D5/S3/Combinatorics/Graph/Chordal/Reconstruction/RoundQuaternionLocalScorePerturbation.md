# The local quaternion score

## Abstract

The pure Fourier rim estimate extends to all edges with controlled losses from the second Fourier mode and the scalar perturbation.

The three cyclic rim gains A determine the hub-gauged assignment G. Write W for the two-mode transverse field, E for the maximum absolute scalar perturbation, and Rho for three fiftieths. The potential X uses the positive-root complex-pair rim coordinates after the second mode has been given the prescribed phase.

**Theorem 1.1 (Quantitative score on each directed edge).**

$$\forall A \in \operatorname{Fin}\left(3\right) \to S,\; \forall p \in \mathbb{C},\; \forall q \in \mathbb{C},\; \forall eta \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall gamma \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; (\lvert p \rvert \leq \operatorname{Rho}) \Rightarrow ((\lvert q \rvert \leq \operatorname{Rho}) \Rightarrow ((\operatorname{E}\left(eta\right) \leq \operatorname{Rho}) \Rightarrow ((\forall k \in \operatorname{Fin}\left(3\right),\; \operatorname{val}\left(gamma, k\right) = \sqrt{1-(\operatorname{val}\left(eta, k\right))^{2}-(\lvert \operatorname{W}\left(p, q, k\right) \rvert)^{2}}) \Rightarrow ((\forall k \in \operatorname{Fin}\left(3\right),\; \operatorname{gain}\left(A, k\right) = \operatorname{QPair}\left((-\operatorname{val}\left(eta, k\right),\operatorname{val}\left(gamma, k\right)), \operatorname{W}\left(p, q, k\right)\right)) \Rightarrow ((q \cdot (\operatorname{zeta}-1) = \sqrt{3} \cdot \lvert q \rvert) \Rightarrow (\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; (i \neq j) \Rightarrow (\frac{1}{\sqrt{3}}+\frac{\lvert q \rvert}{\sqrt{6}}-\frac{\sqrt{3}}{12} \cdot (\lvert p \rvert)^{2}-\frac{2}{5} \cdot (\lvert p \rvert)^{3}-3 \cdot (\lvert p \rvert)^{4}-\frac{627}{100} \cdot \operatorname{Rho} \cdot \lvert q \rvert-2 \cdot \operatorname{Rho} \cdot \operatorname{E}\left(eta\right) \leq \langle \operatorname{edge}\left(\operatorname{G}\left(A\right), i, j\right), (\operatorname{val}\left(\operatorname{X}\left(p, q\right), i\right))^{-1} \cdot \operatorname{val}\left(\operatorname{X}\left(p, q\right), j\right) \rangle)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalScorePerturbation.local_minScore` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rationalize the difference of the two real fibre coordinates as the real coordinate increases. The linear response of the potential subtracts one copy of the second-mode term, while the new transverse gain adds two copies. The scalar and axial dot-product estimates bound the remaining gain changes. The spokes have the prescribed real score and reversing an edge preserves its score.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalScorePerturbation.local_minScore`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalPureScore](RoundQuaternionLocalPureScore.md)
