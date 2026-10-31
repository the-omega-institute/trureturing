# The nonlocality–contextuality trade-off on a binary cycle

## Abstract

Normalized Bell and contextuality inequalities satisfy the trade-off for every binary n-cycle.

**Definition 1.1 (Joint probability tables).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right): Type\right) = \left(\left(\operatorname{Fin}\left(2\right)\right) \to \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.Behavior` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

A behavior is a real table indexed by Alice's setting x in Fin 2, Bob's cyclic context i in Fin n, Alice's outcome a and Bob's ordered outcomes b,c in Bool. The context contains measurements i and finRotate n i. Boolean outcomes label the two signs of the source's binary scenario (final_version.tex, lines 181–196 and 225). The type alone imposes no positivity or normalization.

**Definition 1.2 (Bob's context tables).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right): Type\right) = \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.BobBehavior` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

Bob's table assigns a real number to each context i and pair of Boolean outcomes b,c. The two outcomes belong to consecutive measurements of the cycle (final_version.tex, lines 181–196 and 225).

**Definition 1.3 (Alice's response tables).**

$$\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.AliceResponse}: Type\right) = \left(\left(\operatorname{Fin}\left(2\right)\right) \to \left(\left(\operatorname{Bool}\right) \to \left(\mathbb{R}\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.AliceResponse` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

An Alice response is a real table on her two settings and two outcomes. Such responses are the Alice factors in the generalized-local decomposition (final_version.tex, lines 213–219 and 225).

**Definition 1.4 (Nondisturbing cycle probabilities).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(r: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsND}\left(r\right)\right) \Leftrightarrow \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(b: \operatorname{Bool}\right), \left(\forall \left(c: \operatorname{Bool}\right), \left(\left(0: \mathbb{R}\right) \le r\left(i, b, c\right)\right)\right)\right)\right) \land \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(c: \operatorname{Bool}\right) \mapsto \left(r\left(i, b, c\right)\right)\right)\right)\right) = \left(1: \mathbb{R}\right)\right)\right) \land \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(c: \operatorname{Bool}\right), \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(b: \operatorname{Bool}\right) \mapsto \left(r\left(i, b, c\right)\right)\right) = \operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(d: \operatorname{Bool}\right) \mapsto \left(r\left(\operatorname{Equiv.toFun}\left(\operatorname{finRotate}\left(n\right)\right)\left(i\right), c, d\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsND` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

Each context has a nonnegative probability distribution. Summing over the first outcome in context i gives the same distribution for the shared measurement as summing over the second outcome in the next context. This is nondisturbance on the cycle (final_version.tex, lines 144–149 and 225).

**Definition 1.5 (Nonsignaling and nondisturbing joint probabilities).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(p: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNSND}\left(p\right)\right) \Leftrightarrow \left(\left(\forall \left(x: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(a: \operatorname{Bool}\right), \left(\forall \left(b: \operatorname{Bool}\right), \left(\forall \left(c: \operatorname{Bool}\right), \left(\left(0: \mathbb{R}\right) \le p\left(x, i, a, b, c\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall \left(x: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(a: \operatorname{Bool}\right) \mapsto \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(c: \operatorname{Bool}\right) \mapsto \left(p\left(x, i, a, b, c\right)\right)\right)\right)\right)\right)\right) = \left(1: \mathbb{R}\right)\right)\right)\right) \land \left(\left(\forall \left(x: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(a: \operatorname{Bool}\right), \left(\forall \left(c: \operatorname{Bool}\right), \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(b: \operatorname{Bool}\right) \mapsto \left(p\left(x, i, a, b, c\right)\right)\right) = \operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(d: \operatorname{Bool}\right) \mapsto \left(p\left(x, \operatorname{Equiv.toFun}\left(\operatorname{finRotate}\left(n\right)\right)\left(i\right), a, c, d\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall \left(x: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(y: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(b: \operatorname{Bool}\right), \left(\forall \left(c: \operatorname{Bool}\right), \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(a: \operatorname{Bool}\right) \mapsto \left(p\left(x, i, a, b, c\right)\right)\right) = \operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(a: \operatorname{Bool}\right) \mapsto \left(p\left(y, i, a, b, c\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\forall \left(x: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(a: \operatorname{Bool}\right), \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(c: \operatorname{Bool}\right) \mapsto \left(p\left(x, i, a, b, c\right)\right)\right)\right)\right) = \operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(c: \operatorname{Bool}\right) \mapsto \left(p\left(x, j, a, b, c\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsNSND` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

The five conditions are nonnegativity, normalization for each setting and context, agreement of the joint Alice/shared-Bob marginal in consecutive contexts, independence of Bob's context marginal from Alice's setting, and independence of Alice's marginal from Bob's context. They specialize the source's NSND conditions to the binary cycle (final_version.tex, lines 181–196 and 225).

**Definition 1.6 (The Bob marginal at setting zero).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(p: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.bobMarginal}\left(p\right): \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right)\right) = \lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\lambda \left(c: \operatorname{Bool}\right) \mapsto \left(\operatorname{Finset.sum}\left(\left(\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Bool}\right)\right), \lambda \left(a: \operatorname{Bool}\right) \mapsto \left(p\left(\left(0: \operatorname{Fin}\left(2\right)\right), i, a, b, c\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.bobMarginal` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

Sum over Alice's outcome at setting zero. For an NSND table the result is independent of which Alice setting is used (final_version.tex, lines 187–196).

**Definition 1.7 (Independent product probabilities).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(\alpha: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.AliceResponse}\right), \left(\forall \left(r: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.productBehavior}\left(\alpha, r\right): \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right) = \lambda \left(x: \operatorname{Fin}\left(2\right)\right) \mapsto \left(\lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\lambda \left(a: \operatorname{Bool}\right) \mapsto \left(\lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\lambda \left(c: \operatorname{Bool}\right) \mapsto \left(\left(\alpha\left(x, a\right)\right) \cdot \left(r\left(i, b, c\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.productBehavior` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

Multiply Alice's response probability by Bob's context probability. These independent products are the terms mixed in generalized locality (final_version.tex, lines 213–219).

**Definition 1.8 (Tables from a global outcome assignment).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(s: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.deterministic}\left(s\right): \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right)\right) = \lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\lambda \left(b: \operatorname{Bool}\right) \mapsto \left(\lambda \left(c: \operatorname{Bool}\right) \mapsto \left(\operatorname{ite}\left(\left(s\left(i\right) = b\right) \land \left(s\left(\operatorname{Equiv.toFun}\left(\operatorname{finRotate}\left(n\right)\right)\left(i\right)\right) = c\right), \left(1: \mathbb{R}\right), \left(0: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.deterministic` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

A global Boolean assignment s gives probability one to its ordered pair of outcomes in each context and zero to every other pair. These are the deterministic noncontextual behaviors (final_version.tex, lines 151–159 and 225). The curried table applies the repository's deterministic postprocessing kernel to ordered outcome pairs.

**Definition 1.9 (Generalized-local joint tables).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(p: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsGeneralizedLocal}\left(p\right)\right) \Leftrightarrow \left(p \in \operatorname{convexHull}\left(\mathbb{R}, \{\left(q: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right) \mid \left(\exists \left(\alpha: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.AliceResponse}\right), \left(\exists \left(r: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.Estimation.DecisionRisk.DescentDefectBounds.IsRowStochastic}\left(\alpha\right)\right) \land \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsND}\left(r\right)\right) \land \left(q = \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.productBehavior}\left(\alpha, r\right)\right)\right)\right)\right)\right)\}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsGeneralizedLocal` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

Alice responses satisfy the row-stochastic predicate: nonnegative entries and row sum one. Take the real convex hull of independent products of such a response for Alice and a nondisturbing behavior for Bob. Bob's hidden response may itself be contextual, as allowed in the generalized-local definition (final_version.tex, lines 213–219).

**Definition 1.10 (Noncontextual Bob tables).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(r: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNoncontextual}\left(r\right)\right) \Leftrightarrow \left(r \in \operatorname{convexHull}\left(\mathbb{R}, \operatorname{Set.range}\left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.deterministic}: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right) \to \left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsNoncontextual` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

A Bob table is noncontextual when it is a finite convex combination of context tables from global deterministic assignments (final_version.tex, lines 151–159).

**Definition 1.11 (Normalized affine Bell inequalities).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(f: \left(\operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right), \mathbb{R}\right)\right) \times \mathbb{R}\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNormalizedGBell}\left(f\right)\right) \Leftrightarrow \left(\left(\forall \left(p: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsGeneralizedLocal}\left(p\right)\right) \Rightarrow \left(\left(\operatorname{DFunLike.coe}\left(\operatorname{Prod.fst}\left(f\right)\right)\left(p\right)\right) + \left(\operatorname{Prod.snd}\left(f\right)\right) \le \left(0: \mathbb{R}\right)\right)\right)\right) \land \left(\left(\forall \left(p: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNSND}\left(p\right)\right) \Rightarrow \left(\left(\operatorname{DFunLike.coe}\left(\operatorname{Prod.fst}\left(f\right)\right)\left(p\right)\right) + \left(\operatorname{Prod.snd}\left(f\right)\right) \le \left(1: \mathbb{R}\right)\right)\right)\right) \land \left(\exists \left(p: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNSND}\left(p\right)\right) \land \left(\left(\operatorname{DFunLike.coe}\left(\operatorname{Prod.fst}\left(f\right)\right)\left(p\right)\right) + \left(\operatorname{Prod.snd}\left(f\right)\right) = \left(1: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsNormalizedGBell` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

The pair f consists of a real linear functional and a real offset. Its affine value is nonpositive on every generalized-local table, is at most one on every NSND table, and equals one on some NSND table. Thus the maximum is attained, as required by the source's normalization (final_version.tex, line 276).

**Definition 1.12 (Normalized affine contextuality inequalities).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(t: \left(\operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right), \mathbb{R}\right)\right) \times \mathbb{R}\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNormalizedNC}\left(t\right)\right) \Leftrightarrow \left(\left(\forall \left(r: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNoncontextual}\left(r\right)\right) \Rightarrow \left(\left(\operatorname{DFunLike.coe}\left(\operatorname{Prod.fst}\left(t\right)\right)\left(r\right)\right) + \left(\operatorname{Prod.snd}\left(t\right)\right) \le \left(0: \mathbb{R}\right)\right)\right)\right) \land \left(\left(\forall \left(p: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNSND}\left(p\right)\right) \Rightarrow \left(\left(\operatorname{DFunLike.coe}\left(\operatorname{Prod.fst}\left(t\right)\right)\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.bobMarginal}\left(p\right)\right)\right) + \left(\operatorname{Prod.snd}\left(t\right)\right) \le \left(1: \mathbb{R}\right)\right)\right)\right) \land \left(\exists \left(p: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNSND}\left(p\right)\right) \land \left(\left(\operatorname{DFunLike.coe}\left(\operatorname{Prod.fst}\left(t\right)\right)\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.bobMarginal}\left(p\right)\right)\right) + \left(\operatorname{Prod.snd}\left(t\right)\right) = \left(1: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsNormalizedNC` (`✓ std3`).

*Citation.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

The pair t consists of a real linear functional on Bob tables and a real offset. Its affine value is nonpositive on every noncontextual table and has attained maximum one over Bob marginals of NSND tables (final_version.tex, line 276).

**Definition 1.13 (The trade-off for every cycle length at least three).**

$$\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.claim}\right) \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\left(\left(3: \mathbb{N}\right) \le n\right) \Rightarrow \left(\forall \left(f: \left(\operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right), \mathbb{R}\right)\right) \times \mathbb{R}\right), \left(\forall \left(t: \left(\operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right), \mathbb{R}\right)\right) \times \mathbb{R}\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNormalizedGBell}\left(f\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNormalizedNC}\left(t\right)\right) \Rightarrow \left(\forall \left(p: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNSND}\left(p\right)\right) \Rightarrow \left(\left(\left(\operatorname{DFunLike.coe}\left(\operatorname{Prod.fst}\left(f\right)\right)\left(p\right)\right) + \left(\operatorname{Prod.snd}\left(f\right)\right)\right) + \left(\left(\operatorname{DFunLike.coe}\left(\operatorname{Prod.fst}\left(t\right)\right)\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.bobMarginal}\left(p\right)\right)\right) + \left(\operatorname{Prod.snd}\left(t\right)\right)\right) \le \left(1: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

For every natural n at least three, every pair of normalized affine inequalities f,t and every NSND table p, the Bell value at p plus the contextuality value at its Bob marginal is at most one. This is the binary two-setting reading of the all-cycle conjecture (final_version.tex, lines 373–375), with the inequality of lines 279–286 and the scenario of line 225.

**Theorem 1.14 (The normalized trade-off holds for every binary cycle).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(\left(3: \mathbb{N}\right) \le n\right) \Rightarrow \left(\forall \left(f: \left(\operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right), \mathbb{R}\right)\right) \times \mathbb{R}\right), \left(\forall \left(t: \left(\operatorname{LinearMap}\left(\operatorname{RingHom.id}\left(\mathbb{R}\right), \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.BobBehavior}\left(n\right), \mathbb{R}\right)\right) \times \mathbb{R}\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNormalizedGBell}\left(f\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNormalizedNC}\left(t\right)\right) \Rightarrow \left(\forall \left(p: \operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.Behavior}\left(n\right)\right), \left(\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.IsNSND}\left(p\right)\right) \Rightarrow \left(\left(\left(\operatorname{DFunLike.coe}\left(\operatorname{Prod.fst}\left(f\right)\right)\left(p\right)\right) + \left(\operatorname{Prod.snd}\left(f\right)\right)\right) + \left(\left(\operatorname{DFunLike.coe}\left(\operatorname{Prod.fst}\left(t\right)\right)\left(\operatorname{D5.S3.QuantumContext.NCycleNonlocalityContextualityTradeoff.bobMarginal}\left(p\right)\right)\right) + \left(\operatorname{Prod.snd}\left(t\right)\right)\right) \le \left(1: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.result` (`✓ std3`). ∎

*Resolves.* `Problems/porto-et-al-2024-n-cycle-nonlocality-contextuality-tradeoff` (proved) by `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"porto-et-al-2024-n-cycle-nonlocality-contextuality-tradeoff","declaration_gid":"D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Lucas E. A. Porto, Gabriel Ruffolo, Rafael Rabelo, Marcelo Terra Cunha and Paweł Kurzyński (2024). *Trade-off relations between Bell nonlocality and local Kochen–Specker contextuality in generalized Bell scenarios*. DOI: [10.1088/1367-2630/ad7167](https://doi.org/10.1088/1367-2630/ad7167). URL: <https://arxiv.org/abs/2405.02964v2>.

*Commentary.*

Summing an NSND table over Alice gives a nondisturbing Bob table. Conversely, the independent product of any probability response for Alice with any nondisturbing Bob table is NSND: the normalizations factor, the shared marginals agree, and each party's marginal is independent of the other party's choice.

For a Boolean edge pattern γ, let Vγ assign probability one half when b xor c equals γ(i), and zero otherwise. Every such table is nondisturbing. The product of the edge signs, taking sign −1 at true and +1 at false, is determined by the Boolean sum of γ: apply Mathlib's map_sum to the additive map into multiplicative real signs, using the repository's boolSign. The parity table itself uses the existing parityBox scalar law. If that sum is false, prefix Boolean sums, using Mathlib's Iio_insert identity for the prefix sets, construct a global assignment s whose consecutive xor values are γ. The wraparound edge follows from the total sum being false. Then Vγ is the equal mixture of the deterministic assignments s and its pointwise complement, so it is noncontextual.

Apply the cyclic circulation decomposition to a nondisturbing table. It lies in the convex hull of deterministic tables and all the tables Vγ. Replace each even-parity Vγ by its noncontextual deterministic mixture. This leaves deterministic tables and odd-parity Vγ as sufficient generating tables. For two distinct odd patterns γ,η, choose a position where they differ and flip that bit in both patterns. The resulting patterns are even by Mathlib's sum_eq_sum_iff_single criterion: only the flipped summand changes. Their two V tables have the same midpoint as the original pair: away from the chosen position nothing changes, and at that position the opposite parities still average equally. The midpoint is consequently noncontextual. The source also gives the midpoint property in final_version.tex, lines 521–532.

Write T(r) = t.1(r) + t.2. A uniform Alice response turns every Vγ into the Bob marginal of an NSND product, so normalization gives T(Vγ) ≤ 1. Some odd-pattern Vγ must attain one. Otherwise every deterministic table and every odd-pattern V table lies in the strict affine half-space T < 1, which is convex. Their convex hull would then contain no Bob marginal attaining the required maximum. Fix a maximizing pattern γ. For every other odd η, noncontextuality of the midpoint gives (T(Vη) + T(Vγ))/2 ≤ 0 and hence T(Vη) ≤ 0.

In a finite convex decomposition of a nondisturbing table r, collect the weights of all terms equal to Vγ into v. All other terms have nonpositive T value, so T(r) ≤ v. Nonnegativity of every generating table also gives v Vγ(i,b,c) ≤ r(i,b,c) at every coordinate.

For each Alice setting x and outcome a, take the subnormalized Bob table q(i,b,c) = p(x,i,a,b,c). Its mass m is independent of i. If m is zero, nonnegativity forces the whole slice to vanish. If m is positive, divide by m to obtain a nondisturbing table and apply the preceding weight bound. Multiplying back by m gives a nonnegative weight w(x,a) with t.1(q) + m t.2 ≤ w(x,a) and w(x,a) Vγ ≤ q.

Put c = T(bobMarginal p) and suppose c > 0. Summing the slice inequalities over a gives c ≤ W(x), where W(x) is the sum of w(x,a). This uses Bob's independence from x and normalization of p. Each W(x) is positive, so α(x,a) = w(x,a)/W(x) is a probability response. Since c α(x,a) ≤ w(x,a), the independent product L(x,i,a,b,c′) = α(x,a)Vγ(i,b,c′) satisfies c L ≤ p coordinatewise. This L is both generalized-local and NSND.

For any NSND generalized-local L with c L ≤ p and 0 < c ≤ 1, the affine Bell value F(p) = f.1(p) + f.2 is at most 1 − c. If c = 1, equal total masses and coordinatewise domination force L = p, and locality gives F(p) ≤ 0. If c < 1, set R = (p − c L)/(1 − c). Domination makes R nonnegative, and the linear normalization and marginal identities show that R is NSND. The identity p = c L + (1 − c) R and affinity give F(p) = c F(L) + (1 − c) F(R) ≤ 1 − c.

Finally, fix n ≥ 3, normalized f,t and an NSND p. If T(bobMarginal p) ≤ 0, the bound F(p) ≤ 1 immediately proves the sum bound. Otherwise the maximizing odd pattern and the slice construction give the product L above. Normalization of t gives c ≤ 1, so the dominated-product argument yields F(p) ≤ 1 − c. Adding c proves the stated inequality. The statement concerns binary cyclic NSND probability tables with two Alice settings; it assumes no quantum realization.

## References

- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.AliceResponse`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.Behavior`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.BobBehavior`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsGeneralizedLocal`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsND`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsNSND`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsNoncontextual`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsNormalizedGBell`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.IsNormalizedNC`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.bobMarginal`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.claim`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.deterministic`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.productBehavior`
- Truth anchor: `D5/S3/QuantumContext/NCycleNonlocalityContextualityTradeoff.result`
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Coordinates](../QuantumBounds/MerminMeasurementDependence/Coordinates.md)
- Dependency: [D5/S3/QuantumContext/NCycleNondisturbingGenerators](NCycleNondisturbingGenerators.md)
