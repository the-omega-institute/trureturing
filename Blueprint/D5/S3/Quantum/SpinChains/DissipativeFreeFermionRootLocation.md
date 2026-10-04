# Dissipative free-fermion roots in the upper half-plane

## Abstract

For a finite claw-free, even-hole-free graph with a simplicial clique, real couplings, a positive dissipation rate and no common root of the two independence polynomials, every root of the dissipative polynomial lies in the open upper half-plane.

**Definition 1.1 (Claw-free graphs).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{ClawFree}\left(G\right)) \Leftrightarrow (\forall v \in V,\; \forall a \in V,\; \forall b \in V,\; \forall c \in V,\; (a \neq b) \Rightarrow ((a \neq c) \Rightarrow ((b \neq c) \Rightarrow ((\operatorname{Adj}\left(G, v, a\right)) \Rightarrow ((\operatorname{Adj}\left(G, v, b\right)) \Rightarrow ((\operatorname{Adj}\left(G, v, c\right)) \Rightarrow ((\neg (\operatorname{Adj}\left(G, a, b\right))) \Rightarrow ((\neg (\operatorname{Adj}\left(G, a, c\right))) \Rightarrow ((\neg (\operatorname{Adj}\left(G, b, c\right))) \Rightarrow (\operatorname{False}\left(\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.ClawFree` (`✓ std3`).

*Citation.* K. Fukai; H. Yoshida; H. Katsura (2026). *Dissipative free fermions in disguise*. DOI: [10.48550/arXiv.2603.22163](https://doi.org/10.48550/arXiv.2603.22163). URL: <https://arxiv.org/abs/2603.22163v1>.

*Commentary.*

On printed p. 2: "A graph is claw-free if it has no claw as an induced subgraph (Fig. 1(a)), and even-hole-free if it has no even hole as an induced subgraph (Fig. 1(b))." The formula excludes a center v with three distinct pairwise nonadjacent leaves a, b, c. In a simple graph adjacency already forces each leaf to differ from v.

**Definition 1.2 (Even-hole-free graphs).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; (\operatorname{EvenHoleFree}\left(G\right)) \Leftrightarrow (\forall m \in \mathbb{N},\; (4 \leq m) \Rightarrow ((\operatorname{Even}\left(m\right)) \Rightarrow (\forall f \in \operatorname{Fin}\left(m\right) \to V,\; (\operatorname{Injective}\left(f\right)) \Rightarrow (\neg (\forall i \in \operatorname{Fin}\left(m\right),\; \forall j \in \operatorname{Fin}\left(m\right),\; (\operatorname{Adj}\left(G, f\left(i\right), f\left(j\right)\right)) \Leftrightarrow ((\operatorname{mod}\left(\operatorname{val}\left(i\right) + 1, m\right) = \operatorname{val}\left(j\right)) \lor (\operatorname{mod}\left(\operatorname{val}\left(j\right) + 1, m\right) = \operatorname{val}\left(i\right))))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.EvenHoleFree` (`✓ std3`).

*Citation.* K. Fukai; H. Yoshida; H. Katsura (2026). *Dissipative free fermions in disguise*. DOI: [10.48550/arXiv.2603.22163](https://doi.org/10.48550/arXiv.2603.22163). URL: <https://arxiv.org/abs/2603.22163v1>.

*Commentary.*

On printed p. 2: "A graph is claw-free if it has no claw as an induced subgraph (Fig. 1(a)), and even-hole-free if it has no even hole as an induced subgraph (Fig. 1(b))." An even hole is an induced cycle of even length at least four. The injection f lists its vertices with zero-based Fin m indices. The adjacency equivalence requires exactly the cyclic edges and forbids chords. The operator mod is natural-number remainder, and val extracts a Fin index's natural-number value.

**Definition 1.3 (Simplicial cliques).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall K \in \operatorname{Finset}\left(V\right),\; (\operatorname{Simplicial}\left(G, K\right)) \Leftrightarrow ((\operatorname{IsClique}\left(G, \operatorname{coe}\left(K\right)\right)) \land (\forall j \in V,\; (j \in K) \Rightarrow (\operatorname{IsClique}\left(G, \operatorname{coe}\left((\operatorname{insert}\left(j, \operatorname{neighborFinset}\left(G, j\right)\right) \setminus K)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.Simplicial` (`✓ std3`).

*Citation.* K. Fukai; H. Yoshida; H. Katsura (2026). *Dissipative free fermions in disguise*. DOI: [10.48550/arXiv.2603.22163](https://doi.org/10.48550/arXiv.2603.22163). URL: <https://arxiv.org/abs/2603.22163v1>.

*Commentary.*

On printed p. 3: "The edge operator χ is associated with a clique K_s ⊆ V(G), i.e., a subset of mutually adjacent vertices." "Equivalently, denoting the closed neighborhood of j by Γ[j] ≡ {j} ∪ {ℓ ∈ V(G) | A_jℓ = 1}, K_s is simplicial if and only if Γ[j] \ K_s is a clique for all j ∈ K_s." K is K_s; neighborFinset gives the open neighborhood and insert j gives the closed neighborhood. Finsets are coerced to vertex sets for IsClique.

**Definition 1.4 (The weighted independence polynomial).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall U \in \operatorname{Finset}\left(V\right),\; \forall b \in V \to \mathbb{R},\; \operatorname{P}\left(G, U, b\right) = \operatorname{partition}\left(G, U, ((j : V) \mapsto -\operatorname{C}\left(b\left(j\right)^{2}\right) \cdot X)\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.P` (`✓ std3`).

*Citation.* K. Fukai; H. Yoshida; H. Katsura (2026). *Dissipative free fermions in disguise*. DOI: [10.48550/arXiv.2603.22163](https://doi.org/10.48550/arXiv.2603.22163). URL: <https://arxiv.org/abs/2603.22163v1>.

*Commentary.*

Printed p. 3, Eq. (7): "The independence polynomial is defined as" P_G(x) ≡ Σ_{S∈S_G} (−x)^{|S|} Π_{j∈S} b_j², "where S_G denotes the collection of all independent sets." The partition G U w is the sum over independent subsets of U of the product of w j. Thus the defining activity −C(b j²)X yields exactly Eq. (7) on the induced vertex domain U. C and X belong to ℝ[X], and b has real values.

**Definition 1.5 (The dissipative polynomial).**

$$\forall V \in \operatorname{Type}\left(\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall K \in \operatorname{Finset}\left(V\right),\; \forall b \in V \to \mathbb{R},\; \forall gamma \in \mathbb{R},\; \operatorname{Pt}\left(G, K, b, gamma\right) = \operatorname{comp}\left(\operatorname{map}\left(\operatorname{ofRealHom}\left(\right), \operatorname{P}\left(G, \operatorname{univ}\left(\right), b\right)\right), X^{2}\right) + \operatorname{C}\left(\operatorname{I}\left(\right) \cdot \operatorname{coe}\left(gamma, \mathbb{C}\right)\right) \cdot X \cdot \operatorname{comp}\left(\operatorname{map}\left(\operatorname{ofRealHom}\left(\right), \operatorname{P}\left(G, (\operatorname{univ}\left(\right) \setminus K), b\right)\right), X^{2}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.Pt` (`✓ std3`).

*Citation.* K. Fukai; H. Yoshida; H. Katsura (2026). *Dissipative free fermions in disguise*. DOI: [10.48550/arXiv.2603.22163](https://doi.org/10.48550/arXiv.2603.22163). URL: <https://arxiv.org/abs/2603.22163v1>.

*Commentary.*

Printed p. 4, Eq. (16): P̃_G^±(u) ≡ P_G(u²) ± iγu P_{G\K_s}(u²). Pt is the plus polynomial. The map ofRealHom embeds real coefficients into ℂ; comp substitutes X². The displayed coercion sends gamma : ℝ to ℂ. univ is the full finite vertex domain and univ \ K deletes the clique.

**Definition 1.6 (The Fukai–Yoshida–Katsura expectation).**

$$\operatorname{claim}\left(\right) = (\forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall K \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall b \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \forall gamma \in \mathbb{R},\; (\operatorname{ClawFree}\left(G\right)) \Rightarrow ((\operatorname{EvenHoleFree}\left(G\right)) \Rightarrow ((\operatorname{Simplicial}\left(G, K\right)) \Rightarrow ((0 < gamma) \Rightarrow ((\forall x \in \mathbb{C},\; \neg ((\operatorname{aeval}\left(x, \operatorname{P}\left(G, \operatorname{univ}\left(\right), b\right)\right) = 0) \land (\operatorname{aeval}\left(x, \operatorname{P}\left(G, (\operatorname{univ}\left(\right) \setminus K), b\right)\right) = 0))) \Rightarrow (\forall u \in \mathbb{C},\; (\operatorname{eval}\left(u, \operatorname{Pt}\left(G, K, b, gamma\right)\right) = 0) \Rightarrow (0 < \operatorname{im}\left(u\right))))))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.claim` (`✓ std3`).

*Citation.* K. Fukai; H. Yoshida; H. Katsura (2026). *Dissipative free fermions in disguise*. DOI: [10.48550/arXiv.2603.22163](https://doi.org/10.48550/arXiv.2603.22163). URL: <https://arxiv.org/abs/2603.22163v1>.

*Commentary.*

Printed p. 4, after Eq. (17): "We expect Im ũ_k > 0 to hold for general ECF graphs, as observed numerically in the boundary-driven Fendley model, so that ε̃_k ≡ 1/ũ_k satisfies Im ε̃_k < 0." Here ũ_k are the roots of the plus polynomial in Eq. (16). ECF means even-hole-free and claw-free. Printed p. 3, Eq. (7): P_G(x) ≡ Σ_{S∈S_G} (−x)^{|S|} Π_{j∈S} b_j², "where S_G denotes the collection of all independent sets." Printed p. 4, Eq. (16): P̃_G^±(u) ≡ P_G(u²) ± iγu P_{G\K_s}(u²). Printed p. 3: "Equivalently, denoting the closed neighborhood of j by Γ[j] ≡ {j} ∪ {ℓ ∈ V(G) | A_jℓ = 1}, K_s is simplicial if and only if Γ[j] \ K_s is a clique for all j ∈ K_s." Printed p. 7, after Eq. (26): "Equation (26) shows that N_k = 0 if P_G and P_{G\K_s} share the root u_k². Throughout this work, we exclude this nongeneric case [80]." The encoding quantifies every finite graph on Fin n, every real coupling vector b, every positive gamma, and every complex root u. The common-root exclusion quantifies all complex x. Polynomial aeval evaluates real polynomials at complex points; eval evaluates Pt in ℂ. No ordering or simplicity of the roots is assumed.

**Theorem 1.7 (Every dissipative root has positive imaginary part).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall K \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall b \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \forall gamma \in \mathbb{R},\; (\operatorname{ClawFree}\left(G\right)) \Rightarrow ((\operatorname{EvenHoleFree}\left(G\right)) \Rightarrow ((\operatorname{Simplicial}\left(G, K\right)) \Rightarrow ((0 < gamma) \Rightarrow ((\forall x \in \mathbb{C},\; \neg ((\operatorname{aeval}\left(x, \operatorname{P}\left(G, \operatorname{univ}\left(\right), b\right)\right) = 0) \land (\operatorname{aeval}\left(x, \operatorname{P}\left(G, (\operatorname{univ}\left(\right) \setminus K), b\right)\right) = 0))) \Rightarrow (\forall u \in \mathbb{C},\; (\operatorname{eval}\left(u, \operatorname{Pt}\left(G, K, b, gamma\right)\right) = 0) \Rightarrow (0 < \operatorname{im}\left(u\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Clique deletion splits the independent configurations according to their unique vertex in K, when present. Claw exclusion makes the neighbors of each deleted clique vertex into a simplicial clique in the remaining domain. For Im z < 0, induction on that domain constructs a multiplier r with Im r > 0 and P_U(z²) = z P_(U\K)(z²) r. Its recursive expression is r = 1/z − Σ_(j∈K) b_j²/r_j, with every Im r_j > 0. Only nonzero recursive multipliers are divided by. A lower-half-plane root would force both independence polynomials to vanish; real roots are excluded by their real and imaginary parts, using P_U(0) = 1. The proof retains EvenHoleFree in the displayed statement but does not use it: the same root argument applies to every claw-free graph with a simplicial clique and the remaining hypotheses.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.ClawFree`
- Truth anchor: `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.EvenHoleFree`
- Truth anchor: `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.P`
- Truth anchor: `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.Pt`
- Truth anchor: `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.Simplicial`
- Truth anchor: `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.result`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](../../StatisticalMechanics/HardCore/IndependentPartitionDeletion.md)
