# The symmetric Bell polytope need not be a cross-polytope

## Abstract

At three parties and seventeen inputs, single-frequency strategies remain exposed while a mixed strategy lies outside their convex hull; at least nineteen extreme points exclude a nine-dimensional cross-polytope.

**Definition 1.1 (Correlation tensors).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{Tensor}\left(N, m\right) = \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.Tensor` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

The real Euclidean tensor carrier has one coordinate for each input tuple. Inputs are numbered from zero.

**Definition 1.2 (Antiperiodic index reduction).**

$$\forall m \in \mathbb{N},\; \forall v \in \mathbb{Z},\; \operatorname{normIdx}\left(m, v\right) = ((-1:\mathbb{R})^{\operatorname{Int.ediv}\left(v, (m:\mathbb{Z})\right)}, \operatorname{Int.toNat}\left(\operatorname{Int.emod}\left(v, (m:\mathbb{Z})\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.normIdx` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

The antiperiodic rule is e(x+m) = -e(x). Int.ediv is floor division; Int.emod is the nonnegative remainder for positive m. The exponent uses integer powers.

**Definition 1.3 (Reduction into the finite input carrier).**

$$\forall m \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(m\right),\; \forall v \in \mathbb{Z},\; \operatorname{reduceIdx}\left(x, v\right) = (\operatorname{Prod.fst}\left(\operatorname{normIdx}\left(m, v\right)\right), \operatorname{Fin.mk}\left(\operatorname{Prod.snd}\left(\operatorname{normIdx}\left(m, v\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.reduceIdx` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

reduceIdx uses normIdx and packages its residue in Fin(m). The bound proof follows from the existence of x : Fin(m); the displayed Fin.mk suppresses only this proof.

**Definition 1.4 (Swap the first two parties).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right),\; \operatorname{gen1}\left(x\right) = (1, \lambda (n:\operatorname{Fin}\left(N\right)) \mapsto \operatorname{ite}\left(1 < N, x\left(\operatorname{Equiv.swap}\left(\operatorname{Fin.mk}\left(0\right), \operatorname{Fin.mk}\left(1\right)\right)\left(n\right)\right), x\left(n\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.gen1` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

Equation (23): g1 swaps the first two parties. For N <= 1 the total Lean definition is the identity. Fin.mk suppresses the index-bound proofs supplied by 1 < N.

**Definition 1.5 (Cycle the parties).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right),\; \operatorname{gen2}\left(x\right) = (1, \lambda (n:\operatorname{Fin}\left(N\right)) \mapsto x\left(\operatorname{Fin.mk}\left(\operatorname{Nat.mod}\left(\operatorname{val}\left(n\right) + N - 1, N\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.gen2` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

Equation (23): g2 cycles the parties. Subtraction in this index is natural subtraction; the index-bound proof is suppressed.

**Definition 1.6 (Opposite shifts of the first two inputs).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right),\; \forall n \in \operatorname{Fin}\left(N\right),\; \operatorname{shiftParty}\left(x, n\right) = \operatorname{reduceIdx}\left(x\left(n\right), (x\left(n\right):\mathbb{Z}) + \operatorname{ite}\left(\operatorname{val}\left(n\right) = 0, 1, \operatorname{ite}\left(\operatorname{val}\left(n\right) = 1, -1, 0\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.shiftParty` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

Equation (23): g3 shifts party zero by +1 and party one by -1, leaving all other inputs fixed. Reduction applies the antiperiodic sign.

**Definition 1.7 (The opposite-shift generator).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right),\; \operatorname{gen3}\left(x\right) = (\prod_{n:\operatorname{Fin}\left(N\right)} \operatorname{Prod.fst}\left(\operatorname{shiftParty}\left(x, n\right)\right), \lambda (n:\operatorname{Fin}\left(N\right)) \mapsto \operatorname{Prod.snd}\left(\operatorname{shiftParty}\left(x, n\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.gen3` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

Equation (23): the product collects the local antiperiodic signs of the opposite shifts.

**Definition 1.8 (The reflection generator).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right),\; \operatorname{gen4}\left(x\right) = (\prod_{n:\operatorname{Fin}\left(N\right)} -\operatorname{Prod.fst}\left(\operatorname{reduceIdx}\left(x\left(n\right), (m:\mathbb{Z}) - (x\left(n\right):\mathbb{Z})\right)\right), \lambda (n:\operatorname{Fin}\left(N\right)) \mapsto \operatorname{Prod.snd}\left(\operatorname{reduceIdx}\left(x\left(n\right), (m:\mathbb{Z}) - (x\left(n\right):\mathbb{Z})\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.gen4` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

Equation (23): reflection sends each input to m-x, with one additional minus sign per party, followed by antiperiodic reduction.

**Definition 1.9 (The four generators).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(4\right),\; \forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right),\; \operatorname{gen}\left(i\right)\left(x\right) = ![\operatorname{gen1},\operatorname{gen2},\operatorname{gen3},\operatorname{gen4}]\left(i\right)\left(x\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.gen` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

The finite vector is ordered as gen1, gen2, gen3, gen4. All four actions have the same tensor carrier.

**Definition 1.10 (Action on tensor coordinates).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall g \in \left(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right)\right) \to \mathbb{R}\times(\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right)),\; \forall p \in \operatorname{Tensor}\left(N, m\right),\; \operatorname{act}\left(g, p\right) = \operatorname{WithLp.toLp}\left(2, \lambda (y:\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right)) \mapsto \sum_{x:\operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right)} \operatorname{ite}\left(\operatorname{Prod.snd}\left(g\left(x\right)\right) = y, \operatorname{Prod.fst}\left(g\left(x\right)\right) \cdot p\left(x\right), 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.act` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

This is the literal signed basis action, wrapped by WithLp.toLp to obtain the Euclidean tensor carrier.

**Definition 1.11 (The common fixed subspace).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall p \in \operatorname{Tensor}\left(N, m\right),\; p \in \operatorname{symSub}\left(N, m\right) \Leftrightarrow (\forall i \in \operatorname{Fin}\left(4\right),\; \operatorname{act}\left(\operatorname{gen}\left(i\right), p\right) = p)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.symSub` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

The defining carrier consists of tensors fixed by every generator in Eq. (23). Linearity makes this carrier a real submodule.

**Definition 1.12 (Orthogonal projection onto symmetric tensors).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{Gamma}\left(N, m\right) = \operatorname{Submodule.starProjection}\left(\operatorname{symSub}\left(N, m\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.Gamma` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

Equation (27) defines the Reynolds average over the generated group. Gamma uses the permitted orthogonal-projection convention for the same common fixed subspace. Equality with the literal finite-group average is not a separately kernel-checked statement here. Equation (28) gives the signed total-residue coordinates.

**Definition 1.13 (The full local deterministic polytope).**

$$\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \operatorname{localPolytope}\left(N, m\right) = \operatorname{convexHull}\left(\mathbb{R}, \{d:\operatorname{Tensor}\left(N, m\right)\mid\exists a \in \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(m\right) \to \mathbb{R}\right),\; (\forall n \in \operatorname{Fin}\left(N\right),\; \forall x \in \operatorname{Fin}\left(m\right),\; (a\left(n, x\right) = 1) \lor (a\left(n, x\right) = -1)) \land (\forall x \in \operatorname{Fin}\left(N\right) \to \operatorname{Fin}\left(m\right),\; d\left(x\right) = \prod_{n:\operatorname{Fin}\left(N\right)} a\left(n, x\left(n\right)\right))\}\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.localPolytope` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

Equations (1)-(2) define d(x1,...,xN) as the product of the local signs and the local polytope as the convex hull of all deterministic strategies. The formula ranges over every real sign strategy, with no frequency restriction.

**Definition 1.14 (The cross-polytope).**

$$\forall k \in \mathbb{N},\; \operatorname{crossPolytope}\left(k\right) = \operatorname{convexHull}\left(\mathbb{R}, \operatorname{Set.range}\left(\lambda (i:\operatorname{Fin}\left(k\right)) \mapsto \operatorname{EuclideanSpace.single}\left(i, 1\right)\right)\cup\operatorname{Set.range}\left(\lambda (i:\operatorname{Fin}\left(k\right)) \mapsto -\operatorname{EuclideanSpace.single}\left(i, 1\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.crossPolytope` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

The cross-polytope is the convex hull of all positive and negative standard unit vectors in real dimension k.

**Definition 1.15 (The cross-polytope conjecture).**

$$\operatorname{claim} \Leftrightarrow (\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; (3 \le N) \Rightarrow \left((2 \le m) \Rightarrow \left(\exists f \in \operatorname{Tensor}\left(N, m\right) \to^{a}[\mathbb{R}]\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(\operatorname{Nat.div}\left(m + 1, 2\right)\right)\right),\; (\operatorname{Set.InjOn}\left(f, \operatorname{Set.image}\left(\operatorname{Gamma}\left(N, m\right), \operatorname{localPolytope}\left(N, m\right)\right)\right)) \land (\operatorname{Set.image}\left(f, \operatorname{Set.image}\left(\operatorname{Gamma}\left(N, m\right), \operatorname{localPolytope}\left(N, m\right)\right)\right) = \operatorname{crossPolytope}\left(\operatorname{Nat.div}\left(m + 1, 2\right)\right))\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.claim` (`✓ std3`).

*Citation.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

Section V, p. 4: "This seems to indicate that the symmetric polytope is affinely equivalent to the cross-polytope in dimension ⌈m/2⌉. Although we considered the orbits giving rise to the extreme points of this polytope and tried to infer a generalisable pattern, we could not establish this fact. We conjecture, however, that it holds in general, and hope that further research will identify these general extreme points." The encoding takes N >= 3 and m >= 2, the range of parties in Table II. The dimension uses Nat.div(m+1,2), natural integer division. Affine equivalence is expressed by an affine map injective on the projected polytope and with image the cross-polytope; no ambient-dimensional isomorphism is required.

**Theorem 1.16 (A counterexample with seventeen inputs).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sébastien Designolle, Tamás Vértesi, Sebastian Pokutta (2023). *Symmetric multipartite Bell inequalities via Frank-Wolfe algorithms*. DOI: [10.1103/PhysRevA.109.022205](https://doi.org/10.1103/PhysRevA.109.022205). URL: <https://arxiv.org/abs/2310.20677v3>.

*Commentary.*

At N = 3 and m = 17 the nine single-frequency strategies and their negatives are uniquely exposed vertices. Writing q_r = 289 (Γ 3 17 d)_[r,0,0], a mixed strategy has scaled projected coordinates (-141,133,-109,69,-13,-43,91,-123,139). In these scaled coordinates the functional (-15,27,-21,8,59,24,-5,-6,10) takes value 8421 there and at most 8417 on the eighteen frequency vertices. A finite convex hull therefore has an additional extreme point. Nineteen extreme points cannot inject into the extreme points of a nine-dimensional cross-polytope. The coordinate scaling by 17 squared preserves this obstruction.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.Gamma`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.Tensor`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.act`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.crossPolytope`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.gen`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.gen1`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.gen2`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.gen3`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.gen4`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.localPolytope`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.normIdx`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.reduceIdx`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.shiftParty`
- Truth anchor: `D5/S3/Quantum/Entanglement/SymmetricBellPolytopeNotCrossPolytope.symSub`
- Dependency: [D5/S3/Quantum/Entanglement/SymmetricBellPolytopeSupport](SymmetricBellPolytopeSupport.md)
