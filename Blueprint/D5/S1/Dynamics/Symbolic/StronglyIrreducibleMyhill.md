# Myhill's theorem for strongly irreducible subshifts

## Abstract

Every preinjective continuous equivariant endomorphism of a nonempty strongly irreducible finite-alphabet subshift over a right-counting amenable group is surjective.

Let G and A lie in independent universes. G is any group, and A has a topology. A native MulSubshift X is a closed subset of the product G → A invariant under mulShift(g,x)(h)=x(g*h). Elements of Cfg(X) retain their membership in this same X. When A is finite and discrete, X is compact. No countability, commutativity, finite generation or finite-type assumption is made.

**Definition 1.1 (The actual configuration carrier).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\operatorname{Cfg}(X) = \{x:(G \to A) \mid x \in \operatorname{carrier}(X)\}}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.Cfg` (`✓ std3`).

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

The subtype consists of complete configurations together with their membership in the original subshift.

**Definition 1.2 (The left-action convention).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\forall g: G,}\\{\forall x: \operatorname{Cfg}(X),}\\{\forall h: G,}\\{\operatorname{paperShift}(X, g, x, h) = \operatorname{x}((g)^{-1} * h)}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.paperShift` (`✓ std3`).

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

This is the paper's action g*x(h)=x(g⁻¹*h). Native invariance under mulShift supplies its membership proof. Products retain their displayed order.

**Definition 1.3 (Finite two-pattern strong irreducibility).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\forall Delta: \operatorname{Finset}(G),}\\{\operatorname{SI}(X, Delta) \iff \forall F: \operatorname{Finset}(G),\forall K: \operatorname{Finset}(G),(\operatorname{Disjoint}(F * (Delta)^{-1}, K)) \Rightarrow \forall x: \operatorname{Cfg}(X),\forall y: \operatorname{Cfg}(X),\exists z: \operatorname{Cfg}(X),(\forall g: G,(g \in F) \Rightarrow \operatorname{z}(g) = \operatorname{x}(g)) \land (\forall g: G,(g \in K) \Rightarrow \operatorname{z}(g) = \operatorname{y}(g))}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.SI` (`✓ std3`).

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

The collar is F*Delta⁻¹. The two patterns are restrictions of configurations already in X; the common configuration must also belong to X. Only finite supports are assumed here. Delta need not be symmetric.

**Definition 1.4 (Globally occurring finite patterns).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\forall F: \operatorname{Finset}(G),}\\{\operatorname{PatX}(X, F) = \{p:(F \to A) \mid \exists x: \operatorname{Cfg}(X),\forall g: F,\operatorname{p}(g) = \operatorname{x}(g)\}}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.PatX` (`✓ std3`).

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

A finite pattern occurs when it extends to one complete configuration in X. This is a relative language, rather than the set of all alphabet words.

**Theorem 1.5 (Realize a pattern with a common infinite exterior).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{[\operatorname{Finite}(A)],[\operatorname{DiscreteTopology}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\forall Delta: \operatorname{Finset}(G),}\\{\forall F: \operatorname{Finset}(G),}\\{(\operatorname{SI}(X, Delta)) \Rightarrow \forall x: \operatorname{Cfg}(X),\forall x0: \operatorname{Cfg}(X),\exists z: \operatorname{Cfg}(X),(\forall g: G,(g \in F) \Rightarrow \operatorname{z}(g) = \operatorname{x}(g)) \land (\forall g: G,(\neg(g \in F * (Delta)^{-1})) \Rightarrow \operatorname{z}(g) = \operatorname{x0}(g))}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.common_exterior` (`✓ std3`). ∎

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

For every occurring F-pattern and every background x0 in X, a configuration z in X realizes that pattern and agrees with x0 at every point outside F*Delta⁻¹. There is no symmetry or identity-membership premise on Delta. Every finite exterior constraint is supplied by SI; compactness of the closed finite-alphabet product realizes all exterior constraints together.

**Definition 1.6 (A left-translated finite window).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{\forall t: G,}\\{\forall E: \operatorname{Finset}(G),}\\{\operatorname{tile}(t, E) = \{t * e \mid e \in E\}}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.tile` (`✓ std3`).

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

The tile t*E is the image of E under left multiplication by t.

**Definition 1.7 (Occurring patterns avoiding assigned local words).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\forall C: \operatorname{Finset}(G),}\\{\forall F: \operatorname{Finset}(G),}\\{\forall T: \operatorname{Finset}(G),}\\{\forall w: (T \to (C \to A)),}\\{\operatorname{AvoidPatX}(X, C, F, T, w) = \{p:(F \to A) \mid \exists x: \operatorname{Cfg}(X),(\forall f: F,\operatorname{p}(f) = \operatorname{x}(f)) \land (\forall t: T,\exists c: C,\operatorname{x}(t * c) \neq \operatorname{w}(t, c))\}}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.AvoidPatX` (`✓ std3`).

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

Avoidance at every selected tile belongs to one complete realization in X. The forbidden word may vary with the tile.

**Theorem 1.8 (Strict relative admissible-pattern counting).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{[\operatorname{Finite}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\forall Delta: \operatorname{Finset}(G),}\\{\forall C: \operatorname{Finset}(G),}\\{\forall E: \operatorname{Finset}(G),}\\{\forall F: \operatorname{Finset}(G),}\\{\forall T: \operatorname{Finset}(G),}\\{\forall w: (T \to (C \to A)),}\\{\operatorname{Set.Nonempty}(\operatorname{carrier}(X)) \Rightarrow}\\{1 \in Delta \Rightarrow}\\{\operatorname{SI}(X, Delta) \Rightarrow}\\{C * (Delta)^{-1} \subseteq E \Rightarrow}\\{(\forall t: T,\operatorname{tile}(t, E) \subseteq F) \Rightarrow}\\{(\forall t: T,\forall s: T,(t \neq s) \Rightarrow \operatorname{Disjoint}(\operatorname{tile}(t, E), \operatorname{tile}(s, E))) \Rightarrow}\\{(\forall t: T,\exists x: \operatorname{Cfg}(X),\forall c: C,\operatorname{x}(t * c) = \operatorname{w}(t, c)) \Rightarrow}\\{\operatorname{Nat.card}(\operatorname{AvoidPatX}(X, C, F, T, w)) * (\operatorname{Nat.card}(\operatorname{PatX}(X, E)))^{\operatorname{card}(T)} \le \operatorname{Nat.card}(\operatorname{PatX}(X, F)) * (\operatorname{Nat.card}(\operatorname{PatX}(X, E)) - 1)^{\operatorname{card}(T)}}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.relative_pattern_bound` (`✓ std3`). ∎

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

Assume X is nonempty, 1 lies in Delta and SI(X,Delta) holds. Each t*E lies inside F, distinct E-tiles are disjoint, C*Delta⁻¹ is contained in E, and every assigned C-pattern occurs in X at its assigned translate. With rho=card(PatX(X,E)), excluding all assigned patterns gives the displayed integer inequality, including empty tile sets and rho=1. In each nonempty exterior fiber there are m≤rho completions. SI supplies one excluded completion without disturbing earlier exclusions. Thus rho*a≤(rho−1)*m for the avoiding completions a; summing the fibers and iterating gives the bound.

**Definition 1.9 (Memory on the actual subshift).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\forall tau: (\operatorname{Cfg}(X) \to \operatorname{Cfg}(X)),}\\{\forall M: \operatorname{Finset}(G),}\\{\operatorname{HasMemory}(X, tau, M) \iff \forall x: \operatorname{Cfg}(X),\forall y: \operatorname{Cfg}(X),(\forall g: G,(g \in M) \Rightarrow \operatorname{x}(g) = \operatorname{y}(g)) \Rightarrow \operatorname{tau}(x, 1) = \operatorname{tau}(y, 1)}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.HasMemory` (`✓ std3`).

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

Agreement on M determines only the output at the identity. Equivariance transports this to agreement on g*M determining the output at g.

**Theorem 1.10 (Continuity supplies finite memory).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{[\operatorname{Finite}(A)],[\operatorname{DiscreteTopology}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\forall tau: (\operatorname{Cfg}(X) \to \operatorname{Cfg}(X)),}\\{(\operatorname{Continuous}(tau)) \Rightarrow \exists M: \operatorname{Finset}(G),\operatorname{HasMemory}(X, tau, M)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.finite_memory` (`✓ std3`). ∎

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

Pairs with different identity outputs form a compact subset of Cfg(X)×Cfg(X). The open sets where a coordinate differs cover it. A finite subcover supplies M. This derives memory from continuity on X, without extending tau to the full shift.

**Definition 1.11 (Restrictions of complete images).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\forall tau: (\operatorname{Cfg}(X) \to \operatorname{Cfg}(X)),}\\{\forall F: \operatorname{Finset}(G),}\\{\operatorname{ImagePat}(X, tau, F) = \{p:(F \to A) \mid \exists x: \operatorname{Cfg}(X),\forall f: F,\operatorname{p}(f) = \operatorname{tau}(x, f)\}}\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.ImagePat` (`✓ std3`).

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

All output coordinates in a counted pattern come from one complete image tau(x), with x and tau(x) both in X.

**Theorem 1.12 (A relative lower injection from preinjectivity).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{[\operatorname{Finite}(A)],[\operatorname{DiscreteTopology}(A)],}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\forall Delta: \operatorname{Finset}(G),}\\{\forall F: \operatorname{Finset}(G),}\\{\forall M: \operatorname{Finset}(G),}\\{\forall U: \operatorname{Finset}(G),}\\{\operatorname{SI}(X, Delta) \Rightarrow}\\{\forall x0: \operatorname{Cfg}(X),}\\{\forall tau: (\operatorname{Cfg}(X) \to \operatorname{Cfg}(X)),}\\{\operatorname{HasMemory}(X, tau, M) \Rightarrow}\\{(\forall g: G,\forall x: \operatorname{Cfg}(X),\operatorname{tau}(\operatorname{paperShift}(X, g, x)) = \operatorname{paperShift}(X, g, \operatorname{tau}(x))) \Rightarrow}\\{(\forall x: \operatorname{Cfg}(X),\forall y: \operatorname{Cfg}(X),(\operatorname{Set.Finite}(\{g:G \mid \operatorname{x}(g) \neq \operatorname{y}(g)\})) \Rightarrow (\operatorname{tau}(x) = \operatorname{tau}(y)) \Rightarrow x = y) \Rightarrow}\\{F * (Delta)^{-1} * (M)^{-1} \subseteq U \Rightarrow}\\{\operatorname{Nat.card}(\operatorname{PatX}(X, F)) \le \operatorname{Nat.card}(\operatorname{ImagePat}(X, tau, U))}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.preinjective_pattern_lower` (`✓ std3`). ∎

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

Choose a common-exterior representative z_p for each occurring F-pattern p. Put N=F*Delta⁻¹. If their images agree on U containing N*M⁻¹, locality and the common background make them agree at every point outside U as well. Their complete images are therefore equal. The representatives disagree only inside the finite N, so preinjectivity makes them equal and hence recovers p. This injects the actual relative language into actual image patterns.

**Theorem 1.13 (The full arbitrary-group Myhill theorem).**

$$\begin{aligned}{\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall G: \operatorname{Type}(u),\forall A: \operatorname{Type}(v),[\operatorname{Group}(G)],[\operatorname{TopologicalSpace}(A)],}\\{[\operatorname{Finite}(A)],[\operatorname{DiscreteTopology}(A)],}\\{\operatorname{MeasurableSpace}(G):=\operatorname{discrete}(),}\\{\operatorname{NeBot}(\operatorname{maxFoelner}((G)^{\mathrm{op}}, \operatorname{Measure.count}(G))) \Rightarrow}\\{\forall X: \operatorname{MulSubshift}(A, G),}\\{\operatorname{Set.Nonempty}(\operatorname{carrier}(X)) \Rightarrow}\\{(\exists Delta: \operatorname{Finset}(G),\operatorname{SI}(X, Delta)) \Rightarrow}\\{\forall tau: (\operatorname{Cfg}(X) \to \operatorname{Cfg}(X)),}\\{\operatorname{Continuous}(tau) \Rightarrow}\\{(\forall g: G,\forall x: \operatorname{Cfg}(X),\operatorname{tau}(\operatorname{paperShift}(X, g, x)) = \operatorname{paperShift}(X, g, \operatorname{tau}(x))) \Rightarrow}\\{(\forall x: \operatorname{Cfg}(X),\forall y: \operatorname{Cfg}(X),(\operatorname{Set.Finite}(\{g:G \mid \operatorname{x}(g) \neq \operatorname{y}(g)\})) \Rightarrow (\operatorname{tau}(x) = \operatorname{tau}(y)) \Rightarrow x = y) \Rightarrow}\\{\operatorname{Function.Surjective}(tau)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.myhill` (`✓ std3`). ∎

*Citation.* Tullio Ceccherini-Silberstein, Michel Coornaert (2010). *The Myhill property for strongly irreducible subshifts over amenable groups*. DOI: [10.1007/s00605-010-0256-2](https://doi.org/10.1007/s00605-010-0256-2). URL: <https://arxiv.org/abs/1004.2422v2>.

*Commentary.*

Give G the discrete measurable structure and assume its native maximal right-counting Foelner filter is nontrivial. A finite witness to SI may be enlarged to contain 1; no symmetry is required. Every continuous equivariant endomorphism of a nonempty X that is injective on finite disagreements is surjective. Empty A has no such nonempty X, while singleton alphabets, singleton subshifts and finite groups are included. The result is the classical Theorem 1.1 of Ceccherini-Silberstein and Coornaert, not a claim of a new mathematical theorem.

If the image were proper, compactness would give a nonempty occurring C-pattern missing from all its translates. Take E=C*Delta⁻¹ and K={1}∪E∪(Delta⁻¹*M⁻¹). For every finite F, disjoint E-tiles with centers in F have positive density relative to card(F). The lower injection uses the single outer window U=F*K. Relative exclusion bounds the image count using rho=card(PatX(X,E)); restriction to F and U minus F bounds card(PatX(X,U)) by card(PatX(X,F))*card(A)^card(U minus F). Cancel the positive relative source count. If rho=1, any tile contradicts the resulting inequality. If rho≥2, its logarithm forces a fixed positive loss per unit volume. The right-boundary ratios on maxFoelner(Gᵐᵒᵖ,Measure.count) tend to zero, so card(U minus F)/card(F) tends to zero. This contradicts that loss. Here (op e) • h=h*e. The filter is indexed by arbitrary subsets of G and is eventually supported on finite nonempty sets; no countable subsequence or divergent-volume premise is used.

The finite packing, finite-shape and right-padding estimates come from AmenableGardenOfEden. The relative language and the gluing argument extend their use from full shifts to closed strongly irreducible subshifts with constraints. Common-exterior realization and the relative counting bound can be reused for other equivariant maps on such a subshift: the lower injection compares its occurring source patterns with actual image patterns, while the exclusion bound controls a proper invariant image. Each application must retain the same subshift and verify the stated collar, memory and disjoint-tile conditions.

The conclusion is the Myhill direction, from preinjectivity to surjectivity, without a finite-type assumption. Under the additional hypothesis IsFiniteType(X), FiniteTypeMoore.moore gives the reverse implication, from surjectivity to preinjectivity, for the same X and continuous equivariant endomorphism tau : Cfg(X) → Cfg(X). Combining it directly with myhill yields the equivalence of preinjectivity and surjectivity for this same X and tau under all the stated hypotheses and the additional finite-type hypothesis. The amenability premise is the native right-counting Foelner filter condition; no equivalence with an invariant-mean formulation is asserted.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.AvoidPatX`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.Cfg`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.HasMemory`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.ImagePat`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.PatX`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.SI`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.common_exterior`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.finite_memory`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.myhill`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.paperShift`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.preinjective_pattern_lower`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.relative_pattern_bound`
- Truth anchor: `D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.tile`
- Dependency: [D5/S1/Dynamics/Symbolic/AmenableGardenOfEden](AmenableGardenOfEden.md)
