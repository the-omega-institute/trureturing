# Transversal gluing of symmetric unitary bases

## Abstract

Transversal gluing and conditional attainment of the symmetric Werner–Holevo rank in powers of three.

**Definition 1.1 (Gluing across nine fibers).**

$$m>0,\quad3 \mid m,\quad\operatorname{HasBasis}\left(m\right),\quad\operatorname{TD}\left(9, m\right)\quad\longrightarrow\quad\operatorname{HasBasis}\left(9m\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing.glueTD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HasBasis denotes a Hilbert–Schmidt orthogonal basis of the entire complex symmetric matrix space whose basis matrices are unitary. The supplied resolvable transversal design on nine fibers of size m has m parallel classes with m blocks each. Each block meets every fiber once. Each pair of vertices in distinct fibers occurs together in exactly one class.

Character phases on the seed matrices fill the entries within fibers, including the diagonal. The hypothesis that three divides m gives a partition of each class into triples of blocks. The labeling `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineLabels.edgeLabel_bijective` supplies the hollow orthogonal unitaries on a triple. Characters handle repetition across the triples. The class supports are disjoint and the resulting family has (9m)(9m+1)/2 matrices, the dimension of the symmetric matrix space in order 9m.

**Definition 1.2 (Transversal classes over a field).**

$$\operatorname{B}\left(s, t\right)=\{(j,s\operatorname{a}\left(j\right)+t) \mid j \in \mathbb{F}_{9}\}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing.affineTD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose nine distinct field elements a(j). For each field element s, the intercept t ranges over the field and the displayed transversals partition the vertices. A pair from different fibers determines s and t uniquely by solving the two linear equations.

**Theorem 1.3 (A basis in order 3^r extends to order 3^(r+2)).**

$$r\geq2,\quad\operatorname{HasBasis}\left(3^{r}\right)\quad\longrightarrow\quad\operatorname{HasBasis}\left(3^{r+2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing.primePowerStep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The field of order 3^r has at least nine elements, which supplies distinct slopes. Three divides its order, so the gluing construction applies to the supplied basis in that dimension.

**Theorem 1.4 (Exact mixed-unitary rank from a full basis).**

$$\begin{aligned}n>0,\quad\operatorname{HasBasis}\left(n\right)&\\\phi^{+}(X)&=\frac{\operatorname{tr}\left(X\right)I+X^{T}}{n+1},\quad\forall X \in M_{n}(\mathbb{C})\\\operatorname{murank}\left(\phi^{+}\right)&=\frac{n(n+1)}{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing.rank_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous (2022). *On the Mixed-Unitary Rank of Quantum Channels*. DOI: [10.1007/s00220-022-04412-y](https://doi.org/10.1007/s00220-022-04412-y). URL: <https://arxiv.org/abs/2003.14405>.

*Commentary.*

The basis gives a uniform mixture of unitary conjugations with the displayed action. The Choi rank is a lower bound on the length of every finite decomposition with nonnegative real weights summing to one. Together with the field step, this gives the rank at n = 3^(r+2) whenever r is at least two and a full basis is supplied at 3^r.

**Theorem 1.5 (Rank in powers of three from the order-27 seed).**

$$\begin{aligned}\operatorname{HasBasis}\left(27\right),\quad n=3^{r},\quad r\geq3&\\\phi^{+}(X)&=\frac{\operatorname{tr}\left(X\right)I+X^{T}}{n+1},\quad\forall X \in M_{n}(\mathbb{C})\\\operatorname{murank}\left(\phi^{+}\right)&=\frac{n(n+1)}{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing.mixedUnitaryRank_power_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Mark Girard; Debbie Leung; Jeremy Levick; Chi-Kwong Li; Vern I. Paulsen; Yiu-Tung Poon; John Watrous (2022). *On the Mixed-Unitary Rank of Quantum Channels*. DOI: [10.1007/s00220-022-04412-y](https://doi.org/10.1007/s00220-022-04412-y). URL: <https://arxiv.org/abs/2003.14405>.

*Commentary.*

The hypothesis is a full Hilbert–Schmidt orthogonal basis of 378 symmetric unitary matrices in order 27. Induction applies the field step to each odd exponent beginning at three. For even r, write r = 2d with d at least two and apply `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineWernerHolevo.mixedUnitaryRank_power_nine`.

Ma obtains the order-27 basis by an external Krawczyk interval computation. The Lean theorem takes the basis as an explicit hypothesis. The Girard literature note gives the locator for Ma’s certificate.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineWernerHolevo.mixedUnitaryRank_power_nine`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing.affineTD`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing.glueTD`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing.mixedUnitaryRank_power_three`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing.primePowerStep`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineGluing.rank_exact`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineLabels.edgeLabel_bijective`
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/AffineNineWernerHolevo](AffineNineWernerHolevo.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/WernerHolevo/TransversalNineLabels](TransversalNineLabels.md)
