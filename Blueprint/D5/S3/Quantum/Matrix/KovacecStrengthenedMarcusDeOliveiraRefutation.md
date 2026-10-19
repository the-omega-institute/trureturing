# Kovačec's strengthened Marcus–de Oliveira conjecture is false

## Abstract

The determinant of a rational orthogonal conjugate escapes the bounded region enclosed by the exterior boundary of a three-dimensional sigma-point graph.

**Definition 1.1 (Permutation products).**

$$\forall (n: \mathbb{N}), \forall (a: \operatorname{Fin}\left(n\right) \to \mathbb{C}), \forall (b: \operatorname{Fin}\left(n\right) \to \mathbb{C}), \forall (sigma: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{sigmaPoint}\left(a, b, sigma\right) = \prod_{i: \operatorname{Fin}\left(n\right)} (a\left(i\right) + b\left(sigma\left(i\right)\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.sigmaPoint` (`✓ std3`).

*Citation.* A. Kovačec (2026). *A conjecture more precise and stronger than the one by Marcus and de Oliveira*. URL: <https://www.mat.uc.pt/preprints/ps/p2611.pdf>.

*Commentary.*

Section 1, p. 2: "Often one writes z_σ = z_σ(A, B) = ∏ᵢ₌₁ⁿ (aᵢ + b_{σ(i)}), and calls these points σ-points." Functions a and b on Fin n represent the two multisets, retaining multiplicity. The product runs over all zero-based indices i in Fin n; sigma is a permutation of these indices.

**Definition 1.2 (Determinants of unitary conjugates).**

$$\forall (n: \mathbb{N}), \forall (a: \operatorname{Fin}\left(n\right) \to \mathbb{C}), \forall (b: \operatorname{Fin}\left(n\right) \to \mathbb{C}), \operatorname{detRange}\left(a, b\right) = \{z: \mathbb{C} \mid \exists (U: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (U \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(n\right), \mathbb{C}\right)) \land (z = \operatorname{Matrix}.\operatorname{det}\left((\operatorname{Matrix}.\operatorname{diagonal}\left(a\right) + U \cdot \operatorname{Matrix}.\operatorname{diagonal}\left(b\right) \cdot \operatorname{star}\left(U\right))\right))\}$$

*Formalization.* `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.detRange` (`✓ std3`).

*Citation.* A. Kovačec (2026). *A conjecture more precise and stronger than the one by Marcus and de Oliveira*. URL: <https://www.mat.uc.pt/preprints/ps/p2611.pdf>.

*Commentary.*

Section 1, p. 2: "Putting ∆ = ∆(A, B) = {det(D_A + U D_B U*) : U ∈ U(n)}, we can say this also this way: Conjecture 1’’. For any n-multisets of complex numbers A, B we have ∆(A, B) ⊆ C(A, B)." Matrix.diagonal forms the two diagonal matrices, and star on a complex matrix is its conjugate transpose. Membership in Matrix.unitaryGroup supplies the unitary condition.

**Definition 1.3 (The transposition-segment graph).**

$$\forall (n: \mathbb{N}), \forall (a: \operatorname{Fin}\left(n\right) \to \mathbb{C}), \forall (b: \operatorname{Fin}\left(n\right) \to \mathbb{C}), \operatorname{graph}\left(a, b\right) = \cup_{sigma: \operatorname{Equiv}.\operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)} \cup_{i: \operatorname{Fin}\left(n\right)} \cup_{j: \operatorname{Fin}\left(n\right)} \cup_{i \ne j} \operatorname{segment}\left(\mathbb{R}, \operatorname{sigmaPoint}\left(a, b, sigma\right), \operatorname{sigmaPoint}\left(a, b, sigma \cdot \operatorname{Equiv}.\operatorname{swap}\left(i, j\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.graph` (`✓ std3`).

*Citation.* A. Kovačec (2026). *A conjecture more precise and stronger than the one by Marcus and de Oliveira*. URL: <https://www.mat.uc.pt/preprints/ps/p2611.pdf>.

*Commentary.*

Section 2, p. 4, joins permutations "that differ by exactly one transposition". Definitions 6a, p. 4: "A metric (linear) graph G = G(V, E) is a subset of the plane consisting of a family V of complex numbers (or pairs of reals) as vertices and a family E of segments [v, w] with v, w ∈ V as edges." Here the vertices are the sigma-points and the edges are the real closed segments joining sigma and sigma * Equiv.swap i j, for i ≠ j. The repeated orientation of an edge does not change its union.

**Definition 1.4 (Points with arbitrarily long unobstructed segments).**

$$\forall (G: \operatorname{Set}\left(\mathbb{C}\right)), \operatorname{exterior}\left(G\right) = \{p: \mathbb{C} \mid \forall (M: \mathbb{R}), (0 < M) \Rightarrow \exists (q: \mathbb{C}), (\operatorname{dist}\left(p, q\right) = M) \land (\operatorname{Disjoint}\left(\operatorname{segment}\left(\mathbb{R}, p, q\right), G\right))\}$$

*Formalization.* `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.exterior` (`✓ std3`).

*Citation.* A. Kovačec (2026). *A conjecture more precise and stronger than the one by Marcus and de Oliveira*. URL: <https://www.mat.uc.pt/preprints/ps/p2611.pdf>.

*Commentary.*

Definitions 6b, p. 5: "A point p is an exterior point of a finite metric linear graph G if for all M > 0 there is a point q at distance M from p such that [p, q] does not intersect any edge of G. The set of all exterior points is the exterior of G." Disjointness from the union G is exactly disjointness from every edge. The length M is a positive real number and the endpoint q is complex.

**Definition 1.5 (Simple closed curves).**

$$\forall (J: \operatorname{Set}\left(\mathbb{C}\right)), \operatorname{IsJordanCurve}\left(J\right) \Leftrightarrow (\exists (gamma: Circle \to \mathbb{C}), (\operatorname{Continuous}\left(gamma\right)) \land ((\operatorname{Function}.\operatorname{Injective}\left(gamma\right)) \land (\operatorname{Set}.\operatorname{range}\left(gamma\right) = J)))$$

*Formalization.* `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.IsJordanCurve` (`✓ std3`).

*Citation.* A. Kovačec (2026). *A conjecture more precise and stronger than the one by Marcus and de Oliveira*. URL: <https://www.mat.uc.pt/preprints/ps/p2611.pdf>.

*Commentary.*

Page 5: "the exterior of such a graph is certainly connected and typically will have a boundary which is a Jordan-curve J." A Jordan curve is represented as the range of a continuous injective map gamma from Circle to the complex plane. Circle is the unit circle, and equality of ranges specifies the whole curve.

**Definition 1.6 (The strengthened conjecture).**

$$claim \Leftrightarrow (\forall (n: \mathbb{N}), \forall (a: \operatorname{Fin}\left(n\right) \to \mathbb{C}), \forall (b: \operatorname{Fin}\left(n\right) \to \mathbb{C}), (\operatorname{IsJordanCurve}\left(\operatorname{frontier}\left(\operatorname{exterior}\left(\operatorname{graph}\left(a, b\right)\right)\right)\right)) \Rightarrow \forall (x: \mathbb{C}), (\neg (x \in \operatorname{frontier}\left(\operatorname{exterior}\left(\operatorname{graph}\left(a, b\right)\right)\right))) \Rightarrow \left((\operatorname{Bornology}.\operatorname{IsBounded}\left(\operatorname{connectedComponentIn}\left((\operatorname{frontier}\left(\operatorname{exterior}\left(\operatorname{graph}\left(a, b\right)\right)\right))^{c}, x\right)\right)) \Rightarrow \operatorname{detRange}\left(a, b\right) \subseteq \operatorname{closure}\left(\operatorname{connectedComponentIn}\left((\operatorname{frontier}\left(\operatorname{exterior}\left(\operatorname{graph}\left(a, b\right)\right)\right))^{c}, x\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.claim` (`✓ std3`).

*Citation.* A. Kovačec (2026). *A conjecture more precise and stronger than the one by Marcus and de Oliveira*. URL: <https://www.mat.uc.pt/preprints/ps/p2611.pdf>.

*Commentary.*

Conjecture 7 (strengthened MOC), p. 5: "Given any two n-multisets of complex numbers A, B such that a Jordan curve J and the bounded component J(A, B) are defined, there holds ∆(A, B) ⊆ closure(J(A, B))." The frontier of exterior(graph a b) is J. For each x outside J whose connected component in Jᶜ is bounded, the assertion includes detRange a b in the closure of that component. This formulation quantifies over every bounded component and does not assume a Jordan curve theorem. The finite indexing includes multiplicities and all natural dimensions.

**Theorem 1.7 (An escaping determinant at dimension three).**

$$\neg (\forall (n: \mathbb{N}), \forall (a: \operatorname{Fin}\left(n\right) \to \mathbb{C}), \forall (b: \operatorname{Fin}\left(n\right) \to \mathbb{C}), (\operatorname{IsJordanCurve}\left(\operatorname{frontier}\left(\operatorname{exterior}\left(\operatorname{graph}\left(a, b\right)\right)\right)\right)) \Rightarrow \forall (x: \mathbb{C}), (\neg (x \in \operatorname{frontier}\left(\operatorname{exterior}\left(\operatorname{graph}\left(a, b\right)\right)\right))) \Rightarrow \left((\operatorname{Bornology}.\operatorname{IsBounded}\left(\operatorname{connectedComponentIn}\left((\operatorname{frontier}\left(\operatorname{exterior}\left(\operatorname{graph}\left(a, b\right)\right)\right))^{c}, x\right)\right)) \Rightarrow \operatorname{detRange}\left(a, b\right) \subseteq \operatorname{closure}\left(\operatorname{connectedComponentIn}\left((\operatorname{frontier}\left(\operatorname{exterior}\left(\operatorname{graph}\left(a, b\right)\right)\right))^{c}, x\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kovacec-2026-strengthened-marcus-de-oliveira` (refuted) by `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kovacec-2026-strengthened-marcus-de-oliveira","declaration_gid":"D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Kovačec (2026). *A conjecture more precise and stronger than the one by Marcus and de Oliveira*. URL: <https://www.mat.uc.pt/preprints/ps/p2611.pdf>.

*Commentary.*

Take a=(−3−i,−5−2i,4−3i), b=(−2+i,4+3i,−2−5i), and Q=(1/7)[[−3,−2,6],[−2,−6,−3],[−6,3,−2]]. The real orthogonal Q is unitary and gives determinant (2864+1840i)/49. The exterior is the complement of the x-monotone hexagon with vertices −130+10i, 232+376i, 280+280i, (7672+4424i)/155, 24−20i and −28−56i. Its frontier is parametrized continuously and injectively by Circle. The component containing zero is bounded and its closure is contained in the hexagon. The determinant lies below its lower boundary, since 12 Re d−280−11 Im d=408/49>0. Thus the stated inclusion fails. The original convex-hull Marcus–de Oliveira conjecture is a separate assertion.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.IsJordanCurve`
- Truth anchor: `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.detRange`
- Truth anchor: `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.exterior`
- Truth anchor: `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.graph`
- Truth anchor: `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.result`
- Truth anchor: `D5/S3/Quantum/Matrix/KovacecStrengthenedMarcusDeOliveiraRefutation.sigmaPoint`
- Dependency: [D5/S3/Quantum/Matrix/ProjectionAMGMRefutation](ProjectionAMGMRefutation.md)
