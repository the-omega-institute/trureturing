# An annihilator shear changes graph balance

## Abstract

Degenerate natural bases with graph balances two and one.

Over any field take the natural basis (a,b,u,z), with a squared equal to b, b squared equal to a+u, u squared equal to z, z squared equal to zero, and all mixed products zero. Replacing a by a+z preserves naturality. In the second basis b squared equals (a+z)+u-z. The coefficient -1 remains nonzero in characteristic two.

**Definition 1.1 (associatedGraph).**

$$\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] \forall (\iota : \operatorname{Type}), (\forall (\mu : \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), V, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), V, V\right)\right)), (\forall (B : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\operatorname{associatedGraph}\left(\mu, B\right) = \{\operatorname{Adj} := fun (i : \iota) \mapsto fun (j : \iota) \mapsto \operatorname{Module}.\operatorname{Basis}.\operatorname{repr}\left(B, \mu\left(B\left(i\right), B\left(i\right)\right), j\right) \ne 0\})))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.associatedGraph` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Survey section 1.1, page 3: “To A and B one attaches the directed graph Γ(A,B) with vertex set Λ and an arrow i→j whenever ωᵢⱼ≠0 [48]; this graph is the single most useful tool of the theory.” The row coefficient is obtained by applying Module.Basis.repr to the square of B(i). The displayed record specifies the entire adjacency relation.

**Definition 1.2 (Path).**

$$\forall (V : \operatorname{Type}), (\forall (\Gamma : \operatorname{Digraph}\left(V\right)), (\forall (n : \mathbb{N}), (\operatorname{Path}\left(\Gamma, n\right) := \{vertex : \operatorname{Fin}\left(n + 1\right) \to V; edge : \operatorname{Fin}\left(n\right) \to V \times V; \operatorname{isEdge} : \forall (i : \operatorname{Fin}\left(n\right)), (\operatorname{Digraph}.\operatorname{Adj}\left(\Gamma, \operatorname{Prod}.\operatorname{fst}\left(edge\left(i\right)\right), \operatorname{Prod}.\operatorname{snd}\left(edge\left(i\right)\right)\right)); \operatorname{traverses} : \forall (i : \operatorname{Fin}\left(n\right)), ((edge\left(i\right) = (vertex\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), vertex\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right))) \lor (edge\left(i\right) = (vertex\left(\operatorname{Fin}.\operatorname{succ}\left(i\right)\right), vertex\left(\operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right))))\})))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.Path` (`✓ std3`).

*Citation.* I. Alshatnawi; C. Costoya; A. Viruel (2026). *On the Grothendieck Ring of Finite-Dimensional Non-Degenerate Evolution Algebras*. DOI: [10.48550/arXiv.2607.15154](https://doi.org/10.48550/arXiv.2607.15154). URL: <https://arxiv.org/abs/2607.15154v1>.

*Commentary.*

Definition 2.2, page 4: “A path in Γ is a sequence γ=(v₀,e₁,v₁,…,vₙ₋₁,eₙ,vₙ), n ≥ 0, with v₀,…,vₙ∈V and e₁,…,eₙ∈E such that, for each i∈{1,…,n}, either eᵢ=(vᵢ₋₁,vᵢ) (the edge is traversed forwards) or eᵢ=(vᵢ,vᵢ₋₁) (traversed backwards).” Vertices use Fin(n+1) and edges use Fin n, starting at zero. Fin.castSucc and Fin.succ give the endpoints of edge i. The actual directed arrow is retained, including when opposing arrows both exist.

**Definition 1.3 (IsCycle).**

$$\forall (V : \operatorname{Type}), (\forall (\Gamma : \operatorname{Digraph}\left(V\right)), (\forall (n : \mathbb{N}), (\forall (p : \operatorname{Path}\left(\Gamma, n\right)), ((\operatorname{IsCycle}\left(p\right)) \Leftrightarrow (\operatorname{Path}.\operatorname{vertex}\left(p, 0\right) = \operatorname{Path}.\operatorname{vertex}\left(p, \operatorname{Fin}.\operatorname{last}\left(n\right)\right))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.IsCycle` (`✓ std3`).

*Citation.* I. Alshatnawi; C. Costoya; A. Viruel (2026). *On the Grothendieck Ring of Finite-Dimensional Non-Degenerate Evolution Algebras*. DOI: [10.48550/arXiv.2607.15154](https://doi.org/10.48550/arXiv.2607.15154). URL: <https://arxiv.org/abs/2607.15154v1>.

*Commentary.*

Definition 2.2, page 4: “A (non-simple) cycle is a path with v₀=vₙ.” The last vertex is indexed by Fin.last n; paths of length zero are included.

**Definition 1.4 (pathBalance).**

$$\forall (V : \operatorname{Type}), (\forall (\Gamma : \operatorname{Digraph}\left(V\right)), (\forall (n : \mathbb{N}), (\forall (p : \operatorname{Path}\left(\Gamma, n\right)), (\operatorname{pathBalance}\left(p\right) = (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(fun (i : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{Path}.\operatorname{edge}\left(p, i\right) = (\operatorname{Path}.\operatorname{vertex}\left(p, \operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right), \operatorname{Path}.\operatorname{vertex}\left(p, \operatorname{Fin}.\operatorname{succ}\left(i\right)\right)), (\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)\right) : \mathbb{Z}) - (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(fun (i : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{Path}.\operatorname{edge}\left(p, i\right) = (\operatorname{Path}.\operatorname{vertex}\left(p, \operatorname{Fin}.\operatorname{succ}\left(i\right)\right), \operatorname{Path}.\operatorname{vertex}\left(p, \operatorname{Fin}.\operatorname{castSucc}\left(i\right)\right)), (\operatorname{Finset}.\operatorname{univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)\right) : \mathbb{Z})))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.pathBalance` (`✓ std3`).

*Citation.* I. Alshatnawi; C. Costoya; A. Viruel (2026). *On the Grothendieck Ring of Finite-Dimensional Non-Degenerate Evolution Algebras*. DOI: [10.48550/arXiv.2607.15154](https://doi.org/10.48550/arXiv.2607.15154). URL: <https://arxiv.org/abs/2607.15154v1>.

*Commentary.*

Definition 2.2, page 4: “The balance of γ is the integer b(γ)=#{ i : eᵢ=(vᵢ₋₁,vᵢ) }−#{ i : eᵢ=(vᵢ,vᵢ₋₁) }”. Both finite cardinalities are cast to integers before subtraction. A loop belongs to both sets and contributes zero. Both graphs used here have no loops.

**Definition 1.5 (graphBalance).**

$$\forall (V : \operatorname{Type}), (\forall (\Gamma : \operatorname{Digraph}\left(V\right)), (\operatorname{graphBalance}\left(\Gamma\right) = \operatorname{Int}.\operatorname{natAbs}\left(\operatorname{Submodule}.\operatorname{IsPrincipal}.\operatorname{generator}\left(\operatorname{Ideal}.\operatorname{span}\left(\{z : \mathbb{Z} \mid \exists (n : \mathbb{N}), (\exists (p : \operatorname{Path}\left(\Gamma, n\right)), ((\operatorname{IsCycle}\left(p\right)) \land (z = (\operatorname{Int}.\operatorname{natAbs}\left(\operatorname{pathBalance}\left(p\right)\right) : \mathbb{Z}))))\}\right)\right)\right)))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.graphBalance` (`✓ std3`).

*Citation.* I. Alshatnawi; C. Costoya; A. Viruel (2026). *On the Grothendieck Ring of Finite-Dimensional Non-Degenerate Evolution Algebras*. DOI: [10.48550/arXiv.2607.15154](https://doi.org/10.48550/arXiv.2607.15154). URL: <https://arxiv.org/abs/2607.15154v1>.

*Commentary.*

Definition 2.4, page 4: “The balance of Γ is the greatest common divisor of the absolute values of the balances of its cycles, b(Γ)=gcd{ |b(γ)| : γ a cycle in Γ }.” The integer ideal is generated by the natural absolute values, cast to integers, of all finite closed-path balances. The natural absolute value of its generator is this gcd. There is no length cutoff; the gcd is zero when every balance is zero. The graph and path definitions also apply to infinite vertex types, although claim uses finite bases.

**Definition 1.6 (claim).**

$$(claim) \Leftrightarrow (\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), V, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), V, V\right)\right)), ((\operatorname{DerivationAnnihilatorObstruction}.\operatorname{IsEvolutionAlgebra}\left(\mu\right)) \Rightarrow (\forall (\iota : \operatorname{Type}), (\forall (\kappa : \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] [\operatorname{Fintype}\left(\kappa\right)] \forall (B : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\forall (F : \operatorname{Module}.\operatorname{Basis}\left(\kappa, k, V\right)), ((\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(B\left(i\right), B\left(j\right)\right) = 0)))) \Rightarrow ((\forall (i : \kappa), (\forall (j : \kappa), ((i \ne j) \Rightarrow (\mu\left(F\left(i\right), F\left(j\right)\right) = 0)))) \Rightarrow (\operatorname{graphBalance}\left(\operatorname{associatedGraph}\left(\mu, B\right)\right) = \operatorname{graphBalance}\left(\operatorname{associatedGraph}\left(\mu, F\right)\right))))))))))))$$

*Formalization.* `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.claim` (`✓ std3`).

*Citation.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Commentary.*

Question 27, page 24: “Is the balance independent of the natural basis for arbitrary (possibly degenerate) evolution algebras?” Section 1.1, page 3: “Unless stated otherwise, algebras are finite-dimensional.” The assertion quantifies every field k, every finite-dimensional k-module V with bilinear multiplication μ satisfying IsEvolutionAlgebra, and every pair B,F of natural bases indexed by finite types ι,κ. No nondegeneracy, perfectness, characteristic or connectedness restriction is added.

**Theorem 1.7 (result).**

$$\neg (\forall (k : \operatorname{Type}), ([\operatorname{Field}\left(k\right)] \forall (V : \operatorname{Type}), ([\operatorname{AddCommGroup}\left(V\right)] [\operatorname{Module}\left(k, V\right)] [\operatorname{FiniteDimensional}\left(k, V\right)] \forall (\mu : \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), V, \operatorname{LinearMap}\left(\operatorname{RingHom}.\operatorname{id}\left(k\right), V, V\right)\right)), ((\operatorname{DerivationAnnihilatorObstruction}.\operatorname{IsEvolutionAlgebra}\left(\mu\right)) \Rightarrow (\forall (\iota : \operatorname{Type}), (\forall (\kappa : \operatorname{Type}), ([\operatorname{Fintype}\left(\iota\right)] [\operatorname{Fintype}\left(\kappa\right)] \forall (B : \operatorname{Module}.\operatorname{Basis}\left(\iota, k, V\right)), (\forall (F : \operatorname{Module}.\operatorname{Basis}\left(\kappa, k, V\right)), ((\forall (i : \iota), (\forall (j : \iota), ((i \ne j) \Rightarrow (\mu\left(B\left(i\right), B\left(j\right)\right) = 0)))) \Rightarrow ((\forall (i : \kappa), (\forall (j : \kappa), ((i \ne j) \Rightarrow (\mu\left(F\left(i\right), F\left(j\right)\right) = 0)))) \Rightarrow (\operatorname{graphBalance}\left(\operatorname{associatedGraph}\left(\mu, B\right)\right) = \operatorname{graphBalance}\left(\operatorname{associatedGraph}\left(\mu, F\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kmv27-evobalance` (refuted) by `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kmv27-evobalance","declaration_gid":"D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ivan Kaygorodov; Cándido Martín González; Antonio Viruel (2026). *Evolution algebras: a survey of results and a list of open problems*. DOI: [10.48550/arXiv.2610.22248](https://doi.org/10.48550/arXiv.2610.22248). URL: <https://arxiv.org/abs/2610.22248v1>.

*Acknowledgement.* I. Alshatnawi; C. Costoya; A. Viruel (2026). *On the Grothendieck Ring of Finite-Dimensional Non-Degenerate Evolution Algebras*. DOI: [10.48550/arXiv.2607.15154](https://doi.org/10.48550/arXiv.2607.15154). URL: <https://arxiv.org/abs/2607.15154v1>.

*Commentary.*

In the first graph the arrows are 0→1, 1→0, 1→2 and 2→3. The heights (0,1,0,1) in ZMod 2 increase along every arrow; telescoping along every closed signed path forces even balance. The directed two-cycle has balance two, so the graph balance is two. The second graph adds 1→3. Its path 1→2→3←1 has balance one, so its graph balance is one. Both bases are natural over every field. Specializing to the rational field contradicts the universal equality. The mechanism is the shear through the annihilator, which changes square-support coordinates while preserving the mixed-product equations. This addresses the final assertion of Question 27.

## References

- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.IsCycle`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.Path`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.associatedGraph`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.claim`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.graphBalance`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.pathBalance`
- Truth anchor: `D5/S3/QuadraticForms/EvolutionAlgebras/DegenerateGraphBalanceRefutation.result`
- Dependency: [D5/S3/QuadraticForms/EvolutionAlgebras/DerivationAnnihilatorObstruction](DerivationAnnihilatorObstruction.md)
