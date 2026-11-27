# The Banach reconstruction limit for path powers

## Abstract

The real Banach reconstruction coefficient of a path power tends to two minus two over its width.

Write P(n,k) for the graph on Fin(n) joining distinct indices at distance at most k. Write R(V,g) for skew symmetry on every ordered pair in V. Write T(G,g,e) for triangle defect at most e in the target norm on every ordered triangle of G. For a potential p the edge residual is the gain from i to j minus the potential difference (p(j) minus p(i)). Its norm is denoted by error(g,p,i,j). The assertion F(G,g,p,e) bounds this norm by e on every ordered edge.

**Theorem 1.1 (The averaged block upper bound).**

$$\forall E \in \mathrm{Type},\; [\operatorname{SeminormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] \forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (0 < k) \Rightarrow (\forall g \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to E\right),\; \forall e \in \mathbb{R},\; (0 \leq e) \Rightarrow ((\operatorname{R}\left(\operatorname{Fin}\left(n\right), g\right)) \Rightarrow ((\operatorname{T}\left(\operatorname{P}\left(n, k\right), g, e\right)) \Rightarrow (\exists p \in \operatorname{Fin}\left(n\right) \to E,\; \operatorname{F}\left(\operatorname{P}\left(n, k\right), g, p, (2-\frac{2}{k}) \cdot e\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ChordalBanachLimitTwo.pathPower_banach_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each offset integrate the gains along the clamped block heads and along the spokes. A cross-block edge is compared through the later head. The two triangle comparisons vanish respectively when the earlier and later endpoints are heads. Same-block comparisons cost at most one triangle, with zero error when the earlier endpoint is the head. Each endpoint is marked as a head by one offset. The norm of the mean residual is bounded by the mean of the norms.

**Theorem 1.2 (The finite path lower bound).**

$$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; (1 \leq k) \Rightarrow ((k+1 \leq n) \Rightarrow (\exists E \in \mathrm{Type},\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{CompleteSpace}\left(E\right)] [\operatorname{FiniteDimensional}\left(\mathbb{R}, E\right)] \exists g \in \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to E\right),\; (\operatorname{R}\left(\operatorname{Fin}\left(n\right), g\right)) \land ((\operatorname{T}\left(\operatorname{P}\left(n, k\right), g, 1\right)) \land (\forall p \in \operatorname{Fin}\left(n\right) \to E,\; \exists i \in \operatorname{Fin}\left(n\right),\; \exists j \in \operatorname{Fin}\left(n\right),\; (\operatorname{Adj}\left(\operatorname{P}\left(n, k\right), i, j\right)) \land (\frac{n-k}{n+k-2} \cdot (2-\frac{2}{k}) \leq \operatorname{error}\left(g, p, i, j\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ChordalBanachLimitTwo.pathPower_banach_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed existence assertion includes all four indicated target structures. Use centered indicators of residues modulo the width and put the periodic gains in consecutive-edge gauge. Take the finite max norm over the individual samples and the sums in consecutive-edge windows. A triangle defect is a centered indicator or a difference of two indicators, so it has absolute sum at most one on every partial period. Sum the diagonal residuals of all width-length edges and subtract the residual sums of the consecutive edges. The full windows cancel and at most twice the width minus two boundary windows remain.

**Theorem 1.3 (The exact limit).**

$$\forall k \in \mathbb{N},\; (1 \leq k) \Rightarrow (\operatorname{Tendsto}\left((n:\mathbb{N} \mapsto \operatorname{CBan}\left(n, k\right)), \operatorname{atTop}\left(\mathbb{N}\right), \operatorname{nhds}\left(2-\frac{2}{k}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ChordalBanachLimitTwo.pathPower_banach_limit_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient is the infimum of the nonnegative uniform reconstruction constants at unit triangle defect. The prefactor in the lower bound tends to one for fixed width, so the upper and lower bounds have the same limit.

**Theorem 1.4 (A chordal obstruction to every coefficient below two).**

$$\neg (\exists C \in \mathbb{R},\; (C < 2) \land (\forall V \in \mathrm{Type},\; [\operatorname{Finite}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{Chordal}\left(G\right)) \Rightarrow (\forall E \in \mathrm{Type},\; [\operatorname{NormedAddCommGroup}\left(E\right)] [\operatorname{NormedSpace}\left(\mathbb{R}, E\right)] [\operatorname{CompleteSpace}\left(E\right)] \forall g \in V \to \left(V \to E\right),\; \forall e \in \mathbb{R},\; (0 \leq e) \Rightarrow ((\operatorname{R}\left(V, g\right)) \Rightarrow ((\operatorname{T}\left(G, g, e\right)) \Rightarrow (\exists p \in V \to E,\; \operatorname{F}\left(G, g, p, (C) \cdot e\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/ChordalBanachLimitTwo.not_subtwo_banach_chordal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each proposed coefficient below two, first choose the width and then the number of vertices so that the finite lower bound exceeds it. Every path power is chordal because the two cycle neighbours of a least vertex of a cycle of length at least four give a chord.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ChordalBanachLimitTwo.not_subtwo_banach_chordal`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ChordalBanachLimitTwo.pathPower_banach_limit_tendsto`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ChordalBanachLimitTwo.pathPower_banach_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/ChordalBanachLimitTwo.pathPower_banach_upper_bound`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Dirac](Dirac.md)
