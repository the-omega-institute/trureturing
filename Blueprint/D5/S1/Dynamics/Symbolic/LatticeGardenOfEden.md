# The lattice Garden-of-Eden theorem

## Abstract

Surjectivity and finite-disagreement preinjectivity coincide for every finite-alphabet local rule on every finite-dimensional integer lattice.

Fix an arbitrary universe u, a finite A : Type(u), a natural rank d, a finite subset S of the lattice Fin(d) → Z, and a rule φ : (S → A) → A. Full configurations are arbitrary functions from that lattice to A. The full map Φ reads the translated S-pattern at each site. The neighborhood may be empty, nonrectangular or asymmetric. No permutativity, local injectivity, separation into rows or coordinate directions, periodicity, finite configuration domain, finite complete-output fiber, entropy certificate or alphabet lower bound is part of the equivalence.

**Definition 1.1 (The full local map).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\\forall d: \mathbb{N},\forall S: \operatorname{Finset}((\operatorname{Fin}(d) \to \mathbb{Z})),\forall \varphi: ((S \to A) \to A),\\\forall x: ((\operatorname{Fin}(d) \to \mathbb{Z}) \to A),\\\forall z: (\operatorname{Fin}(d) \to \mathbb{Z}),\\\operatorname{localMap}(S, \varphi, x, z) = \varphi((s \mapsto \operatorname{x}(z + s)))\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.localMap` (`✓ std3`).

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

The definition is also available on any additive commutative group. The theorem specializes its group to the full integer lattice; it does not restrict the rule to one-dimensional or separable dynamics.

**Definition 1.2 (Preinjectivity on finite disagreements).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\\forall d: \mathbb{N},\forall S: \operatorname{Finset}((\operatorname{Fin}(d) \to \mathbb{Z})),\forall \varphi: ((S \to A) \to A),\\\operatorname{Preinjective}(S, \varphi) \iff\\\forall x: ((\operatorname{Fin}(d) \to \mathbb{Z}) \to A),\\\forall y: ((\operatorname{Fin}(d) \to \mathbb{Z}) \to A),\\\operatorname{Set.Finite}(\operatorname{disagreement}(x, y)) \Rightarrow \operatorname{localMap}(S, \varphi, x) = \operatorname{localMap}(S, \varphi, y) \Rightarrow x = y\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.Preinjective` (`✓ std3`).

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

The disagreement set is exactly the set of sites z at which x(z) and y(z) differ. Equality of images means equality at every lattice site, not just on a finite observation window.

**Definition 1.3 (Jointly realized image patterns).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\\forall d: \mathbb{N},\forall S: \operatorname{Finset}((\operatorname{Fin}(d) \to \mathbb{Z})),\forall \varphi: ((S \to A) \to A),\\\forall F: \operatorname{Finset}((\operatorname{Fin}(d) \to \mathbb{Z})),\\\forall p: (F \to A),\\p \in \operatorname{ImagePatterns}(S, \varphi, F) \iff\\\exists x: ((\operatorname{Fin}(d) \to \mathbb{Z}) \to A),\\\forall z: F,\\\operatorname{p}(z) = \operatorname{localMap}(S, \varphi, x, z)\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.ImagePatterns` (`✓ std3`).

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

One complete configuration x must realize the entire pattern p simultaneously. The count imagePatternCount(F,S,φ) is Nat.card of this actual image-pattern type. It does not count independent local witnesses or arbitrary compatible patches.

**Theorem 1.4 (A packing count gives a uniform logarithmic deficit).**

$$\begin{aligned}\forall a: \mathbb{N},\forall b: \mathbb{N},\forall k: \mathbb{N},\forall u: \mathbb{N},\forall v: \mathbb{N},\forall f: \mathbb{N},\\2 \le a \land 0 < b \land 0 < v \land 0 < f \land\\v \le k * {b}^{2} \land k * b \le u \land\\f \le {{a}^{b} - 1}^{k} * {a}^{u - k * b} \Rightarrow\\0 < (\operatorname{cast}(b) * \operatorname{Real.log}(\operatorname{cast}(a)) - \operatorname{Real.log}(\operatorname{cast}({a}^{b} - 1)))/{\operatorname{cast}(b)}^{2} \land\\\operatorname{Real.log}(\operatorname{cast}(f))/\operatorname{cast}(v) \le (\operatorname{cast}(u)/\operatorname{cast}(v)) * \operatorname{Real.log}(\operatorname{cast}(a)) - (\operatorname{cast}(b) * \operatorname{Real.log}(\operatorname{cast}(a)) - \operatorname{Real.log}(\operatorname{cast}({a}^{b} - 1)))/{\operatorname{cast}(b)}^{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.logarithmic_packing_bound` (`✓ std3`). ∎

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

For natural a,b,k,u,v,f with a≥2, b,v,f positive, v≤k*b², k*b≤u and f≤(a^b−1)^k*a^(u−k*b), put δ=(b*log(a)−log(a^b−1))/b². Then δ>0 and log(f)/v≤(u/v)*log(a)−δ. This scalar estimate has no group hypothesis and applies to both lattice boxes and arbitrary-group finite-pattern counts.

**Theorem 1.5 (A finite collision forces strict logarithmic image loss).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\{}[\operatorname{Finite}(A)],\\\forall d: \mathbb{N},\\1 \le d \Rightarrow\\\forall S: \operatorname{Finset}((\operatorname{Fin}(d) \to \mathbb{Z})),\\\forall \varphi: ((S \to A) \to A),\\2 \le \operatorname{Nat.card}(A) \Rightarrow\\\forall x: ((\operatorname{Fin}(d) \to \mathbb{Z}) \to A),\\\forall y: ((\operatorname{Fin}(d) \to \mathbb{Z}) \to A),\\\operatorname{Set.Finite}(\operatorname{disagreement}(x, y)) \Rightarrow \operatorname{localMap}(S, \varphi, x) = \operatorname{localMap}(S, \varphi, y) \Rightarrow x \neq y \Rightarrow\\\exists c: \mathbb{R},\\c < \operatorname{Real.log}(\operatorname{cast}(\operatorname{Nat.card}(A))) \land\\\exists N: \mathbb{N},\\\forall n: \mathbb{N},\\N \le n \Rightarrow\operatorname{Real.log}(\operatorname{cast}(\operatorname{imagePatternCount}(\operatorname{box}(d, n + 1), S, \varphi)))/\operatorname{pow}(\operatorname{cast}(n + 1), d) \le c\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.strict_image_box_loss` (`✓ std3`). ∎

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

Here box(d,n+1) consists exactly of lattice sites whose every coordinate lies between zero and n inclusive, and has (n+1)^d sites. Thus the denominator is the actual box volume. The finite collision, its finite disagreement set, and equality of the complete images are the only dynamical hypotheses.

For a disagreement core D, retain D together with all points a−s+t for a in D and s,t in S. Every local window touching D lies in this finite collar. Replacing the colliding collar pattern in a matching ambient context preserves the entire image. On disjoint translates, successive replacements eliminate one prescribed collar pattern without changing any image coordinate.

A maximal disjoint family of translates with centers in a finite F covers the possible centers by translated pairs of collar sites. If the collar has b sites, the family has at least card(F)/b² members. For any padded input shape U containing these translates and all local windows needed for F, actual image patterns inject into a product with (card(A)^b−1) choices on each translate and card(A) choices on the remaining sites. The resulting count is at most (card(A)^b−1)^k card(A)^(card(U)−kb). This product counts restrictions of the same normalized full configuration.

The supplied lattice-box geometry makes every fixed finite padding have volume ratio tending to one. The positive deficit [b log(card(A))−log(card(A)^b−1)]/b² therefore yields a uniform eventual strict upper bound. The box-through-boundary estimates are due to Tom Ole Diem. They control the padding volume; the collision and packing arguments supply the strict image-count deficit.

**Theorem 1.6 (Surjectivity is equivalent to preinjectivity in every finite rank).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\{}[\operatorname{Finite}(A)],\\\forall d: \mathbb{N},\forall S: \operatorname{Finset}((\operatorname{Fin}(d) \to \mathbb{Z})),\forall \varphi: ((S \to A) \to A),\\\operatorname{Function.Surjective}(\operatorname{localMap}(S, \varphi)) \iff \operatorname{Preinjective}(S, \varphi)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.garden_of_eden` (`✓ std3`). ∎

*Citation.* Simon Wacker (2016). *The Garden of Eden Theorem for Cellular Automata on Group Sets*. DOI: [10.1007/978-3-319-44365-2_7](https://doi.org/10.1007/978-3-319-44365-2_7). URL: <https://arxiv.org/html/1603.07272v2>.

*Commentary.*

All natural ranks are included, including zero. All finite alphabet universes are included, including empty and singleton alphabets. A subsingleton alphabet makes both assertions immediate. At rank zero the configuration space is finite, finite-disagreement preinjectivity is ordinary injectivity, and the finite endomap theorem applies.

At rank one, the coordinate equivalence with Z, a finite enclosing integer window and an output translation transport both assertions to the existing native GardenOfEden.garden_of_eden theorem, which is applied directly. In higher rank and for at least two letters, surjectivity realizes every pattern on every box. Its logarithmic count per site is exactly log(card(A)), contradicting the strict collision loss if preinjectivity fails.

For the reverse implication, the full finite-alphabet shift is compact and the local map is continuous. A configuration outside the closed image has a finite cylinder missing the image. Translation gives one finite output pattern absent at every site. The same disjoint-packing count then gives a strict upper deficit. Preinjectivity gives the opposing lower comparison: arbitrary source patterns on a finite F, inserted in one fixed constant context, inject into actual output patterns on the finite set obtained by padding F by the negative neighborhood. Equal observations there give equal complete images because every output that can be affected lies in that padded set. No assumption on the cardinality of a complete-output fiber is used. The fixed padding has asymptotically unit volume ratio, so the two bounds contradict.

This is the classical Moore–Myhill equivalence specialized to finite-dimensional integer lattices.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.ImagePatterns`
- Truth anchor: `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.Preinjective`
- Truth anchor: `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.garden_of_eden`
- Truth anchor: `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.localMap`
- Truth anchor: `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.logarithmic_packing_bound`
- Truth anchor: `D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.strict_image_box_loss`
- Dependency: [D5/S1/Dynamics/Symbolic/GardenOfEden](GardenOfEden.md)
