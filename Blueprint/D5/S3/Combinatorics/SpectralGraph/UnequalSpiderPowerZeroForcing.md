# Ordinary zero forcing, symmetric maximum nullity, and minimum rank of unequal-leg spider powers

## Abstract

For integers m >= 2 and k >= 1 and independently chosen leg lengths ell_0, ..., ell_{m - 1} >= k + 1, the ordinary distance-at-most-k power G = T^k of the spider T on N = 1 + sum_{i = 0}^{m - 1} ell_i vertices has ordinary zero forcing number Z(G) = (m - 1) k, real symmetric maximum nullity M_R(G) = (m - 1) k, and real symmetric minimum rank mr_R(G) = N - (m - 1) k. The upper bound Z(G) <= (m - 1) k is realized by the tail set consisting of the last k vertices on each of the first m - 1 legs, while the matching lower bound and symmetric extremum are realized by one explicit real symmetric matrix combining per-leg sliding-window Gram blocks D_{ell_i}^T D_{ell_i} with cross-leg and center indicator couplings.

**Definition 1.1 (Vertex type of a spider with independently chosen leg lengths).**

$$\forall m \in \mathbb{N},\; \forall ell \in \operatorname{Fin}\left(m\right) \to \mathbb{N},\; \operatorname{Vertex}\left(m, ell\right) = \operatorname{Option}\left((\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For m : Nat and leg-length profile ell : Fin m -> Nat, Vertex m ell is Option (Sigma i : Fin m, Fin (ell i)). The constructor none denotes the center vertex c, while some <i, d> denotes the vertex on 1-based leg i_1 = i.val + 1 (1 <= i_1 <= m) at 1-based depth d_1 = d.val + 1 (1 <= d_1 <= ell i) from the center.

**Definition 1.2 (Spider tree on independently varying leg lengths).**

$$\forall m \in \mathbb{N},\; \forall ell \in \operatorname{Fin}\left(m\right) \to \mathbb{N},\; (((\operatorname{spiderTree}\left(m, ell\right)).\operatorname{Adj}\left(\operatorname{none}, \operatorname{none}\right)) \Leftrightarrow (\operatorname{False})) \land ((\forall p \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; ((\operatorname{spiderTree}\left(m, ell\right)).\operatorname{Adj}\left(\operatorname{none}, \operatorname{some}\left(p\right)\right)) \Leftrightarrow (p.2.\operatorname{val} = 0)) \land ((\forall p \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; ((\operatorname{spiderTree}\left(m, ell\right)).\operatorname{Adj}\left(\operatorname{some}\left(p\right), \operatorname{none}\right)) \Leftrightarrow (p.2.\operatorname{val} = 0)) \land (\forall p \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; \forall q \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; ((\operatorname{spiderTree}\left(m, ell\right)).\operatorname{Adj}\left(\operatorname{some}\left(p\right), \operatorname{some}\left(q\right)\right)) \Leftrightarrow ((p.1 = q.1) \land (\operatorname{Nat}.\operatorname{dist}\left(p.2.\operatorname{val}, q.2.\operatorname{val}\right) = 1)))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.spiderTree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

The simple graph spiderTree m ell joins the center none to some <i, d> precisely when d.val = 0 (1-based depth 1), and joins two leg vertices some <i, d> and some <j, e> precisely when i = j and Nat.dist d.val e.val = 1.

**Definition 1.3 (Closed-form spider-tree distance).**

$$\forall m \in \mathbb{N},\; \forall ell \in \operatorname{Fin}\left(m\right) \to \mathbb{N},\; (\operatorname{distance}\left(m, ell, \operatorname{none}, \operatorname{none}\right) = 0) \land ((\forall p \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; \operatorname{distance}\left(m, ell, \operatorname{none}, \operatorname{some}\left(p\right)\right) = p.2.\operatorname{val} + 1) \land ((\forall p \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; \operatorname{distance}\left(m, ell, \operatorname{some}\left(p\right), \operatorname{none}\right) = p.2.\operatorname{val} + 1) \land (\forall p \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; \forall q \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; \operatorname{distance}\left(m, ell, \operatorname{some}\left(p\right), \operatorname{some}\left(q\right)\right) = \operatorname{if} p.1 = q.1 \operatorname{then} \operatorname{Nat}.\operatorname{dist}\left(p.2.\operatorname{val}, q.2.\operatorname{val}\right) \operatorname{else} p.2.\operatorname{val} + q.2.\operatorname{val} + 2)))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.distance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

The function distance m ell evaluates to 0 at (none, none), to d.val + 1 between none and some <i, d> (matching 1-based depth d_1 = d.val + 1), to Nat.dist d.val e.val = |d_1 - e_1| for two vertices on the same leg i = j, and to d.val + e.val + 2 = d_1 + e_1 for two vertices on distinct legs i != j.

**Definition 1.4 (Ordinary distance-at-most-k spider power).**

$$\forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall ell \in \operatorname{Fin}\left(m\right) \to \mathbb{N},\; \forall u \in \operatorname{Vertex}\left(m, ell\right),\; \forall v \in \operatorname{Vertex}\left(m, ell\right),\; ((\operatorname{power}\left(m, k, ell\right)).\operatorname{Adj}\left(u, v\right)) \Leftrightarrow ((u \ne v) \land (\operatorname{distance}\left(m, ell, u, v\right) \le k))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.power` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

The simple graph power m k ell on Vertex m ell joins distinct vertices u != v precisely when distance m ell u v <= k.

**Definition 1.5 (Real symmetric matrix family of a simple graph).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{SymGraphMatrices}\left(G\right) = \{A : \operatorname{Matrix}\left(V, V, \mathbb{R}\right) | (A.\operatorname{IsSymm}) \land (\forall u \in V,\; \forall v \in V,\; (u \ne v) \Rightarrow ((A\left(u, v\right) \ne 0) \Leftrightarrow (G.\operatorname{Adj}\left(u, v\right))))\}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.SymGraphMatrices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For a simple graph G on V : Type, SymGraphMatrices G is the set of real matrices A : Matrix V V R that are symmetric (A.IsSymm) and satisfy A u v != 0 <-> G.Adj u v for all distinct vertices u != v, with diagonal entries unconstrained.

**Definition 1.6 (Right-kernel dimension of a real square matrix).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall A \in \operatorname{Matrix}\left(V, V, \mathbb{R}\right),\; \operatorname{matrixNullity}\left(A\right) = \operatorname{Module}.\operatorname{finrank}\left(\mathbb{R}, \operatorname{LinearMap}.\operatorname{ker}\left(A.\operatorname{mulVecLin}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.matrixNullity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For a finite vertex type V and matrix A : Matrix V V R, matrixNullity A is Module.finrank R (LinearMap.ker A.mulVecLin).

**Definition 1.7 (Maximum symmetric nullity of a finite simple graph).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{maxSymNullity}\left(G\right) = \operatorname{sSup}\left(\operatorname{matrixNullity} '' \operatorname{SymGraphMatrices}\left(G\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.maxSymNullity` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For a simple graph G on a finite vertex type V, maxSymNullity G is the supremum sSup (matrixNullity '' SymGraphMatrices G) in Nat.

**Definition 1.8 (Minimum symmetric rank of a finite simple graph).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{minSymRank}\left(G\right) = \operatorname{sInf}\left(\operatorname{Matrix}.\operatorname{rank} '' \operatorname{SymGraphMatrices}\left(G\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.minSymRank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For a simple graph G on a finite vertex type V, minSymRank G is the infimum sInf (Matrix.rank '' SymGraphMatrices G) in Nat.

**Definition 1.9 (One-sided (k + 1)-term zero-sum sliding-window subspace).**

$$\forall k \in \mathbb{N},\; \forall x \in \mathbb{N} \to \mathbb{R},\; (x \in \operatorname{slidingWindowSpace}\left(k\right)) \Leftrightarrow (\forall s \in \mathbb{N},\; \sum_{t \in \operatorname{Finset}.\operatorname{range}\left(k + 1\right)} x\left(s + t\right) = 0)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.slidingWindowSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For k : Nat, slidingWindowSpace k is the R-submodule of sequences x : Nat -> R such that sum_{t in Finset.range (k + 1)} x(s + t) = 0 for every start index s : Nat.

**Definition 1.10 (Initial-coordinate linear equivalence on the sliding-window subspace).**

$$\forall k \in \mathbb{N},\; (\forall x \in \operatorname{slidingWindowSpace}\left(k\right),\; \forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{slidingWindowEquiv}\left(k, x, i\right) = x.1\left(i.\operatorname{val}\right)) \land (\forall v \in \operatorname{Fin}\left(k\right) \to \mathbb{R},\; \forall n \in \mathbb{N},\; (\operatorname{slidingWindowEquiv}\left(k\right)).\operatorname{symm}\left(v\right).1\left(n\right) = \operatorname{if} h : n \bmod \left(k + 1\right) < k \operatorname{then} v\left(\langle n \bmod \left(k + 1\right), h \rangle\right) \operatorname{else} -\sum_{i : \operatorname{Fin}\left(k\right)} v\left(i\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.slidingWindowEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For k : Nat, slidingWindowEquiv k : slidingWindowSpace k ≃_l[R] (Fin k -> R) evaluates a sequence x on its first k coordinates i |-> x.1 i.val, with explicit (k + 1)-periodic inverse sending v : Fin k -> R at index n : Nat to v (n mod (k + 1)) when n mod (k + 1) < k and to -sum_{i : Fin k} v i when n mod (k + 1) = k.

**Definition 1.11 (Rectangular sliding-window indicator matrix).**

$$\forall k \in \mathbb{N},\; \forall L \in \mathbb{N},\; \forall s \in \operatorname{Fin}\left(L - k\right),\; \forall d \in \operatorname{Fin}\left(L\right),\; \operatorname{windowMatrix}\left(k, L, s, d\right) = \operatorname{if} (s.\operatorname{val} \le d.\operatorname{val}) \land (d.\operatorname{val} \le s.\operatorname{val} + k) \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.windowMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For k, L : Nat, windowMatrix k L is the (L - k) x L real matrix D_L whose entry at row s : Fin (L - k) and column d : Fin L equals 1 when s.val <= d.val <= s.val + k and 0 otherwise.

**Definition 1.12 (Tail zero-forcing set on the first m - 1 legs).**

$$\forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall ell \in \operatorname{Fin}\left(m\right) \to \mathbb{N},\; \operatorname{spiderTailForcingSet}\left(m, k, ell\right) = (((\operatorname{Finset}.\operatorname{univ}).\operatorname{filter} (\operatorname{fun} (i : \operatorname{Fin}\left(m\right)) \mapsto i.\operatorname{val} < m - 1)).\operatorname{sigma} (\operatorname{fun} i \mapsto (\operatorname{Finset}.\operatorname{univ}).\operatorname{filter} (\operatorname{fun} (d : \operatorname{Fin}\left(ell\left(i\right)\right)) \mapsto ell\left(i\right) - k \le d.\operatorname{val}))).\operatorname{map} \langle \operatorname{Option}.\operatorname{some}, \operatorname{Option}.\operatorname{some}_{\operatorname{injective}} (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)) \rangle$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.spiderTailForcingSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For m, k : Nat and leg-length profile ell : Fin m -> Nat, spiderTailForcingSet m k ell collects the leg vertices some <i, d> with i.val < m - 1 (the first m - 1 legs) and ell i - k <= d.val (the last k depths on leg i).

**Definition 1.13 (Center-to-leg coupling entry).**

$$\forall k \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{centerCoupling}\left(k, d\right) = \operatorname{if} d + 1 \le k \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.centerCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For k, d : Nat, centerCoupling k d equals 1 when d + 1 <= k (so 1-based depth d_1 = d + 1 lies within distance k of the center) and 0 otherwise.

**Definition 1.14 (Cross-leg coupling entry).**

$$\forall k \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall e \in \mathbb{N},\; \operatorname{crossCoupling}\left(k, d, e\right) = \operatorname{if} (d + 1 \le k - 1) \land ((e + 1 \le k - 1) \land (d + 1 + e + 1 \le k)) \operatorname{then} 1 \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.crossCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

For k, d, e : Nat, crossCoupling k d e equals 1 when d + 1 <= k - 1, e + 1 <= k - 1, and (d + 1) + (e + 1) <= k (equivalently d + e + 2 <= k, matching 1-based cross-leg distance d_1 + e_1 <= k) and 0 otherwise.

**Definition 1.15 (Explicit extremal real symmetric matrix for an unequal-leg spider power).**

$$\forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall ell \in \operatorname{Fin}\left(m\right) \to \mathbb{N},\; (\operatorname{spiderSymmMatrix}\left(m, k, ell, \operatorname{none}, \operatorname{none}\right) = 0) \land ((\forall p \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; \operatorname{spiderSymmMatrix}\left(m, k, ell, \operatorname{none}, \operatorname{some}\left(p\right)\right) = \operatorname{centerCoupling}\left(k, p.2.\operatorname{val}\right)) \land ((\forall p \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; \operatorname{spiderSymmMatrix}\left(m, k, ell, \operatorname{some}\left(p\right), \operatorname{none}\right) = \operatorname{centerCoupling}\left(k, p.2.\operatorname{val}\right)) \land (\forall p \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; \forall q \in (\Sigma (i : \operatorname{Fin}\left(m\right)), \operatorname{Fin}\left(ell\left(i\right)\right)),\; \operatorname{spiderSymmMatrix}\left(m, k, ell, \operatorname{some}\left(p\right), \operatorname{some}\left(q\right)\right) = (\operatorname{if} h : p.1 = q.1 \operatorname{then} ((\operatorname{windowMatrix}\left(k, ell\left(p.1\right)\right))^{\mathrm{T}} \cdot \operatorname{windowMatrix}\left(k, ell\left(p.1\right)\right))\left(p.2, \operatorname{Fin}.\operatorname{cast}\left(\operatorname{congrArg}\left(ell, h.\operatorname{symm}\right), q.2\right)\right) \operatorname{else} 0) + \operatorname{crossCoupling}\left(k, p.2.\operatorname{val}, q.2.\operatorname{val}\right))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.spiderSymmMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

On Vertex m ell, spiderSymmMatrix m k ell places 0 at (none, none), centerCoupling k p.2.val between none and any leg vertex some p, crossCoupling k p.2.val q.2.val between vertices on distinct legs, and (D_{ell_i}^T D_{ell_i})_{d, e} + crossCoupling k d.val e.val between vertices at 0-based depths d, e on the same leg i, where D_{ell_i} = windowMatrix k (ell i).

**Theorem 1.16 (Recurrence, dimension, truncation annihilation, and Gram band support of sliding windows).**

$$\forall k \in \mathbb{N},\; (\forall x \in \mathbb{N} \to \mathbb{R},\; (x \in \operatorname{slidingWindowSpace}\left(k\right)) \Leftrightarrow (\forall s \in \mathbb{N},\; x\left(s + k\right) = -\sum_{t \in \operatorname{Finset}.\operatorname{range}\left(k\right)} x\left(s + t\right))) \land ((\forall x \in \operatorname{slidingWindowSpace}\left(k\right),\; \forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{slidingWindowEquiv}\left(k, x, i\right) = x.1\left(i.\operatorname{val}\right)) \land ((\forall v \in \operatorname{Fin}\left(k\right) \to \mathbb{R},\; \exists! (x : \mathbb{N} \to \mathbb{R}), (x \in \operatorname{slidingWindowSpace}\left(k\right)) \land (\forall i \in \operatorname{Fin}\left(k\right),\; x\left(i.\operatorname{val}\right) = v\left(i\right))) \land ((\operatorname{Module}.\operatorname{finrank}\left(\mathbb{R}, \operatorname{slidingWindowSpace}\left(k\right)\right) = k) \land ((\forall L \in \mathbb{N},\; (k + 1 \le L) \Rightarrow (\forall x \in \mathbb{N} \to \mathbb{R},\; (x \in \operatorname{slidingWindowSpace}\left(k\right)) \Rightarrow ((\operatorname{windowMatrix}\left(k, L\right)) *_{v} (\operatorname{fun} (d : \operatorname{Fin}\left(L\right)) \mapsto x\left(d.\operatorname{val}\right)) = 0))) \land (\forall L \in \mathbb{N},\; (k + 1 \le L) \Rightarrow (\forall d \in \operatorname{Fin}\left(L\right),\; \forall e \in \operatorname{Fin}\left(L\right),\; (d \ne e) \Rightarrow ((0 < ((\operatorname{windowMatrix}\left(k, L\right))^{\mathrm{T}} \cdot \operatorname{windowMatrix}\left(k, L\right))\left(d, e\right)) \Leftrightarrow (\operatorname{Nat}.\operatorname{dist}\left(d.\operatorname{val}, e.\operatorname{val}\right) \le k))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.sliding_window_kernel_and_band_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

Every sequence x : Nat -> R belongs to slidingWindowSpace k if and only if it satisfies the order-k recurrence x(s + k) = -sum_{t < k} x(s + t) for all s : Nat. Consequently, initial-coordinate evaluation slidingWindowEquiv k establishes unique extension from Fin k -> R and gives Module.finrank R (slidingWindowSpace k) = k for every k : Nat (including k = 0). Whenever L >= k + 1, truncating any x in slidingWindowSpace k to Fin L lies in the right kernel of windowMatrix k L, while for all distinct d, e : Fin L the Gram entry ((windowMatrix k L)^T * windowMatrix k L) d e is strictly positive if and only if Nat.dist d.val e.val <= k, realized when Nat.dist d.val e.val <= k by the window start s_0 = max(d.val, e.val) - k < L - k.

**Theorem 1.17 (Zero forcing number, maximum symmetric nullity, and minimum symmetric rank of unequal-leg spider powers).**

$$\forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall ell \in \operatorname{Fin}\left(m\right) \to \mathbb{N},\; (2 \le m) \Rightarrow ((1 \le k) \Rightarrow ((\forall i \in \operatorname{Fin}\left(m\right),\; k + 1 \le ell\left(i\right)) \Rightarrow ((\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Vertex}\left(m, ell\right)\right) = 1 + \sum_{i : \operatorname{Fin}\left(m\right)} ell\left(i\right)) \land ((\forall u \in \operatorname{Vertex}\left(m, ell\right),\; \forall v \in \operatorname{Vertex}\left(m, ell\right),\; (\operatorname{spiderTree}\left(m, ell\right)).\operatorname{dist}\left(u, v\right) = \operatorname{distance}\left(m, ell, u, v\right)) \land ((\forall u \in \operatorname{Vertex}\left(m, ell\right),\; \forall v \in \operatorname{Vertex}\left(m, ell\right),\; ((\operatorname{power}\left(m, k, ell\right)).\operatorname{Adj}\left(u, v\right)) \Leftrightarrow ((u \ne v) \land ((\operatorname{spiderTree}\left(m, ell\right)).\operatorname{dist}\left(u, v\right) \le k))) \land ((\operatorname{IsZeroForcing}\left(\operatorname{power}\left(m, k, ell\right), (\operatorname{spiderTailForcingSet}\left(m, k, ell\right) : \operatorname{Set}\left(\operatorname{Vertex}\left(m, ell\right)\right))\right)) \land (((\operatorname{spiderTailForcingSet}\left(m, k, ell\right)).\operatorname{card} = (m - 1) \cdot k) \land ((\operatorname{spiderSymmMatrix}\left(m, k, ell\right) \in \operatorname{SymGraphMatrices}\left(\operatorname{power}\left(m, k, ell\right)\right)) \land ((\operatorname{matrixNullity}\left(\operatorname{spiderSymmMatrix}\left(m, k, ell\right)\right) = (m - 1) \cdot k) \land (((\operatorname{spiderSymmMatrix}\left(m, k, ell\right)).\operatorname{rank} = (1 + \sum_{i : \operatorname{Fin}\left(m\right)} ell\left(i\right)) - (m - 1) \cdot k) \land ((\forall H \in \operatorname{Matrix}\left(\operatorname{Vertex}\left(m, ell\right), \operatorname{Vertex}\left(m, ell\right), \mathbb{R}\right),\; (H \in \operatorname{SymGraphMatrices}\left(\operatorname{power}\left(m, k, ell\right)\right)) \Rightarrow ((\operatorname{matrixNullity}\left(H\right) \le (m - 1) \cdot k) \land ((1 + \sum_{i : \operatorname{Fin}\left(m\right)} ell\left(i\right)) - (m - 1) \cdot k \le H.\operatorname{rank}))) \land ((\operatorname{IsGreatest}\left(\operatorname{matrixNullity} '' \operatorname{SymGraphMatrices}\left(\operatorname{power}\left(m, k, ell\right)\right), (m - 1) \cdot k\right)) \land ((\operatorname{IsLeast}\left(\operatorname{Matrix}.\operatorname{rank} '' \operatorname{SymGraphMatrices}\left(\operatorname{power}\left(m, k, ell\right)\right), (1 + \sum_{i : \operatorname{Fin}\left(m\right)} ell\left(i\right)) - (m - 1) \cdot k\right)) \land ((\operatorname{zeroForcingNumber}\left(\operatorname{power}\left(m, k, ell\right)\right) = (m - 1) \cdot k) \land ((\operatorname{maxSymNullity}\left(\operatorname{power}\left(m, k, ell\right)\right) = (m - 1) \cdot k) \land (\operatorname{minSymRank}\left(\operatorname{power}\left(m, k, ell\right)\right) = (1 + \sum_{i : \operatorname{Fin}\left(m\right)} ell\left(i\right)) - (m - 1) \cdot k))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

Assume m >= 2, k >= 1, and ell i >= k + 1 for every i : Fin m. Then Vertex m ell has cardinality N = 1 + sum_i ell i, the graph metric (spiderTree m ell).dist equals distance m ell everywhere, and adjacency in power m k ell coincides with distinctness and spider-tree distance at most k. The tail set spiderTailForcingSet m k ell has cardinality (m - 1) k and zero-forces power m k ell in four phases: inward along each of the first m - 1 legs, from 0-based depth k - 1 on leg 0 to the center, from depths k - t - 2 on leg 0 to depths t < k - 1 on leg m - 1, from the center to depth k - 1 on leg m - 1, and outward along leg m - 1. Conversely, spiderSymmMatrix m k ell belongs to SymGraphMatrices (power m k ell) because nonnegativity of crossCoupling and the Gram band support of windowMatrix k (ell i) match same-leg adjacency while crossCoupling and centerCoupling match cross-leg and center adjacency. Assigning arbitrary sequences from slidingWindowSpace k to the first m - 1 legs and their negative sum to leg m - 1 embeds (Fin (m - 1) x Fin k -> R) injectively into ker(spiderSymmMatrix m k ell), giving nullity >= (m - 1) k. For every H in SymGraphMatrices (power m k ell) and every finite zero-forcing set S, induction along Black shows that any kernel vector of H vanishing on S vanishes on all of Vertex m ell, so matrixNullity H <= S.card. Combining both inequalities with rank-nullity yields matrixNullity (spiderSymmMatrix m k ell) = (m - 1) k, (spiderSymmMatrix m k ell).rank = N - (m - 1) k, the universal bounds and extremal characterizations IsGreatest and IsLeast across SymGraphMatrices (power m k ell), and the exact invariants zeroForcingNumber (power m k ell) = maxSymNullity (power m k ell) = (m - 1) k and minSymRank (power m k ell) = N - (m - 1) k.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.SymGraphMatrices`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.Vertex`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.centerCoupling`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.crossCoupling`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.distance`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.matrixNullity`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.maxSymNullity`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.minSymRank`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.power`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.slidingWindowEquiv`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.slidingWindowSpace`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.sliding_window_kernel_and_band_support`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.spiderSymmMatrix`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.spiderTailForcingSet`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.spiderTree`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.unequal_spider_power_zero_forcing`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/UnequalSpiderPowerZeroForcing.windowMatrix`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree](../GeneralizedPetersen/ZeroForcingThree.md)
