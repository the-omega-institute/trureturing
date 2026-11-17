# Full cellular maps on groups

## Abstract

Surjectivity and finite-disagreement preinjectivity coincide for full cellular maps over every finite alphabet on every discrete group with a nontrivial right counting Følner filter.

Let A be a finite alphabet in an arbitrary universe and G a group in an independent universe. A finite neighborhood S and a rule φ : (S → A) → A define the full map Φ(x)(g) = φ(s ↦ x(g*s)). Configurations are all functions G → A; the group need not be countable, finitely generated or commutative. The neighborhood may be empty or asymmetric. Empty and singleton alphabets are included.

**Definition 1.1 (The full local map).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\forall G: \operatorname{Type}(v),[\operatorname{Group}(G)],\\\forall S: \operatorname{Finset}(G),\forall \varphi: ((S \to A) \to A),\\\forall x: (G \to A),\forall g: G,\operatorname{localMap}(S, \varphi, x, g) = \varphi((s \mapsto \operatorname{x}(g * s)))\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.localMap` (`✓ std3`).

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

All products are written in the displayed order. The neighborhood coordinates multiply on the right. Left translation of a configuration therefore commutes with the map.

**Definition 1.2 (Preinjectivity on finite disagreements).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\forall G: \operatorname{Type}(v),[\operatorname{Group}(G)],\\\forall S: \operatorname{Finset}(G),\forall \varphi: ((S \to A) \to A),\\\operatorname{Preinjective}(S, \varphi) \iff\\\forall x: (G \to A),\forall y: (G \to A),\operatorname{Set.Finite}(\operatorname{disagreement}(x, y)) \Rightarrow \operatorname{localMap}(S, \varphi, x) = \operatorname{localMap}(S, \varphi, y) \Rightarrow x = y\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.Preinjective` (`✓ std3`).

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

The disagreement set is exactly {g | x(g)≠y(g)}. Two configurations with finite disagreement and equal complete images must be equal. Equality of images is equality at every group element.

**Definition 1.3 (Jointly realized image patterns).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\forall G: \operatorname{Type}(v),[\operatorname{Group}(G)],\\\forall S: \operatorname{Finset}(G),\forall \varphi: ((S \to A) \to A),\\\forall F: \operatorname{Finset}(G),\forall p: (F \to A),p \in \operatorname{ImagePatterns}(S, \varphi, F) \iff\\\exists x: (G \to A),\forall f: F,\operatorname{p}(f) = \operatorname{localMap}(S, \varphi, x, f)\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.ImagePatterns` (`✓ std3`).

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

ImagePatterns(S,φ,F) is the range of x ↦ (f ↦ Φ(x)(f)) on all complete configurations x. One x must realize all coordinates of a pattern simultaneously.

**Definition 1.4 (Replace a pattern on a left translate).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\forall G: \operatorname{Type}(v),[\operatorname{Group}(G)],\\\forall C: \operatorname{Finset}(G),\forall p: (C \to A),\forall t: G,\forall x: (G \to A),\forall g: G,\\\operatorname{writePattern}(C, p, t, x, g) = \operatorname{ite}(t^{-1} * g \in C, \operatorname{p}(t^{-1} * g), \operatorname{x}(g))\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.writePattern` (`✓ std3`).

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

On the translate t*C the new value at g is p(t⁻¹*g); outside that translate it is the original value. The coordinate t⁻¹*g is unique and keeps the order of multiplication explicit.

**Theorem 1.5 (Uniform replacement and actual-image counting from a collision).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\forall G: \operatorname{Type}(v),[\operatorname{Group}(G)],\\{}[\operatorname{Finite}(A)],\\\forall S: \operatorname{Finset}(G),\forall \varphi: ((S \to A) \to A),\\\forall x: (G \to A),\forall y: (G \to A),x \neq y \land \operatorname{Set.Finite}(\operatorname{disagreement}(x, y)) \land \operatorname{localMap}(S, \varphi, x) = \operatorname{localMap}(S, \varphi, y) \Rightarrow\\\exists C: \operatorname{Finset}(G),\exists p: (C \to A),\exists q: (C \to A),p \neq q \land\\(\forall t: G,\forall z: (G \to A),(\forall c: C,\operatorname{z}(t * c) = \operatorname{p}(c)) \Rightarrow \operatorname{localMap}(S, \varphi, \operatorname{writePattern}(C, q, t, z)) = \operatorname{localMap}(S, \varphi, z)) \land\\\forall F: \operatorname{Finset}(G),\exists T: \operatorname{Finset}(G),T \subseteq F \land\\(\forall t: T,\forall r: T,t \neq r \Rightarrow \forall c: C,\forall e: C,t * c \neq r * e) \land\\\operatorname{card}(F) \le \operatorname{card}(T) * {\operatorname{card}(C)}^{2} \land\\\operatorname{card}(T) * \operatorname{card}(C) \le \operatorname{card}(F * \operatorname{insert}(1, \operatorname{union}(S, C))) \land\\\operatorname{Nat.card}(\operatorname{ImagePatterns}(S, \varphi, F)) \le {{\operatorname{Nat.card}(A)}^{\operatorname{card}(C)} - 1}^{\operatorname{card}(T)} * {\operatorname{Nat.card}(A)}^{\operatorname{card}(F * \operatorname{insert}(1, \operatorname{union}(S, C))) - \operatorname{card}(T) * \operatorname{card}(C)}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.collision_replacement_count` (`✓ std3`). ∎

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

For distinct configurations x,y with finite disagreement and Φ(x)=Φ(y), there are a finite C and distinct patterns p,q on C. Whenever an ambient z has pattern p on t*C, replacing that pattern by q preserves the complete image Φ(z), for every t and z. This finite statement needs no amenability assumption.

For every finite F there is T contained in F whose translates t*C are pairwise disjoint. Writing a=Nat.card(A), E={1}∪S∪C and U=F*E, the simultaneous bounds are card(F) ≤ card(T)*card(C)², card(T)*card(C) ≤ card(U), and Nat.card(ImagePatterns(S,φ,F)) ≤ (a^card(C)−1)^card(T) * a^(card(U)−card(T)*card(C)).

The collar of the actual disagreement core D is D∪D*S⁻¹*S. Every neighborhood window touching D lies in it. Successive replacements on disjoint left translates preserve one complete image and eliminate p from every selected translate. For each actual image pattern choose one complete source and normalize it in this way. Record the avoiding C-patterns together with the source on the residual part of U. Equal records force equal inputs on every window used to compute the restriction to F, hence equal actual image patterns. This injection gives the count without selecting independent output coordinates.

**Theorem 1.6 (Surjectivity is equivalent to finite-disagreement preinjectivity).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall v: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\forall G: \operatorname{Type}(v),[\operatorname{Group}(G)],\\{}[\operatorname{Finite}(A)],\\\operatorname{MeasurableSpace}(G):=\operatorname{discrete}(),\\\operatorname{NeBot}(\operatorname{maxFoelner}(G^{\mathrm{op}}, \operatorname{Measure.count}(G))) \Rightarrow\\\forall S: \operatorname{Finset}(G),\forall \varphi: ((S \to A) \to A),\\\operatorname{Function.Surjective}(\operatorname{localMap}(S, \varphi)) \iff \operatorname{Preinjective}(S, \varphi)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.garden_of_eden` (`✓ std3`). ∎

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

Give G the discrete measurable structure. Assume NeBot(maxFoelner(Gᵐᵒᵖ,Measure.count)), where the opposite group acts by (op a) • g = g*a. For every finite S and every rule φ, Function.Surjective(Φ) is equivalent to finite-disagreement preinjectivity. The hypothesis uses the maximal counting Følner filter itself, not a chosen sequence. Finite and trivial groups satisfy this hypothesis; uncountable groups remain in scope. There is no assumption that finite-set volumes diverge.

For every finite E containing 1, finite unions of right translates give 1 ≤ card(F*E)/card(F) ≤ 1 + Σ(e∈E) card((F*e)△F)/card(F) whenever F is nonempty. The maximal filter is eventually supported on finite nonempty sets, and each right boundary ratio tends to zero. Thus each fixed finite padding has volume ratio tending to one. The logarithmic packing bound converts avoidance of one C-pattern into a positive deficit independent of F.

Surjectivity realizes every finite output pattern. A finite collision would supply the replacement and joint-count bounds above, contradicting this full count and the padding limit. Conversely, preinjectivity injects arbitrary patterns on F, extended into one constant ambient configuration, into actual image patterns on F*({1}∪S⁻¹). Nonsurjectivity of the continuous map on the compact full product would give a nonempty finite missing output pattern. Left equivariance makes it missing at every left translate. Disjoint placements yield the same positive counting deficit and contradict the preinjective lower count. Product compactness applies to arbitrary G; no enumeration or sequential compactness is used.

Subsingleton alphabets are treated directly before choosing any ambient letter. The result therefore includes empty and singleton alphabets as well as empty neighborhoods. This is the classical amenable-group Moore–Myhill theorem. The multiplicative finite-pattern argument extends the lattice formulation while retaining the same jointly realized meaning of image patterns.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.ImagePatterns`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.Preinjective`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.collision_replacement_count`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.garden_of_eden`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.localMap`
- Truth anchor: `D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.writePattern`
- Dependency: [D5/S1/Dynamics/Symbolic/LatticeGardenOfEden](LatticeGardenOfEden.md)
