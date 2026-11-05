# The dimension shift for deterministic simplicial degree sets

## Abstract

The distinct upper degrees in positive dimension are zero together with the vertex degrees at the dimension-shifted generation.

**Definition 1.1 (The growing family of nonempty faces).**

$$\forall (V: \operatorname{Type}), ([\operatorname{DecidableEq}\left(V\right)], (\forall (v_{0}: V), (\forall (v: (\mathbb{N}) \to ((\operatorname{Finset}\left(V\right)) \to (V))), (((\operatorname{dsc}\left(v_{0}, v, 0\right): \operatorname{Finset}\left(\operatorname{Finset}\left(V\right)\right)) = \{\{v_{0}\}\}) \land (\forall (s: \mathbb{N}), (\operatorname{dsc}\left(v_{0}, v, (s) + (1)\right) = (\operatorname{dsc}\left(v_{0}, v, s\right))\cup(\operatorname{Finset.biUnion}\left(\operatorname{dsc}\left(v_{0}, v, s\right), \lambda (\sigma: \operatorname{Finset}\left(V\right)) \mapsto (\operatorname{Finset.image}\left(\lambda (\beta: \operatorname{Finset}\left(V\right)) \mapsto (\operatorname{insert}\left(v\left((s) + (1), \sigma\right), \beta\right)), \operatorname{Finset.powerset}\left(\sigma\right)\right))\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.dsc` (`✓ std3`).

*Citation.* S. N. Dorogovtsev; P. L. Krapivsky (2025). *Deterministic simplicial complexes*. DOI: [10.1088/1742-5468/ae2092](https://doi.org/10.1088/1742-5468/ae2092). URL: <https://arxiv.org/abs/2507.07402v1>.

*Commentary.*

The initial family consists of the singleton containing v₀. At step s + 1, each existing face σ contributes a vertex v(s + 1, σ) and every face obtained by adjoining that vertex to a subset β of σ, including the empty subset. All earlier faces remain. These are finite sets of nonempty faces; the empty face is omitted from the family. The single-vertex initial condition and growth rule are described in Section II.1 and the abstract (TeX lines 118 and 82). The recursion itself accepts any labels; injectivity and avoidance of v₀ are assumptions of the degree-set identity.

**Definition 1.2 (The upper degree of a face).**

$$\forall (V: \operatorname{Type}), ([\operatorname{DecidableEq}\left(V\right)], (\forall (C: \operatorname{Finset}\left(\operatorname{Finset}\left(V\right)\right)), (\forall (\tau: \operatorname{Finset}\left(V\right)), ((\operatorname{upperDegree}\left(C, \tau\right): \mathbb{N}) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (\rho: \operatorname{Finset}\left(V\right)) \mapsto ((\tau \subseteq \rho) \land (\operatorname{Finset.card}\left(\rho\right) = (\operatorname{Finset.card}\left(\tau\right)) + (1))), C\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.upperDegree` (`✓ std3`).

*Citation.* S. N. Dorogovtsev; P. L. Krapivsky (2025). *Deterministic simplicial complexes*. DOI: [10.1088/1742-5468/ae2092](https://doi.org/10.1088/1742-5468/ae2092). URL: <https://arxiv.org/abs/2507.07402v1>.

*Commentary.*

For a finite family C and a finite set τ of vertices, the upper degree counts the members ρ of C that contain τ and have exactly one more vertex. This agrees with the upper degree of a simplex described at TeX line 106. The expression is defined for arbitrary C and τ, without requiring τ to belong to C. Every cardinality and degree in the formula is a natural number.

**Definition 1.3 (The set of distinct degrees in a dimension).**

$$\forall (V: \operatorname{Type}), ([\operatorname{DecidableEq}\left(V\right)], (\forall (C: \operatorname{Finset}\left(\operatorname{Finset}\left(V\right)\right)), (\forall (d: \mathbb{N}), ((\operatorname{degreeSet}\left(C, d\right): \operatorname{Set}\left(\mathbb{N}\right)) = \{(k: \mathbb{N}) \mid \exists (\tau: \operatorname{Finset}\left(V\right)), ((\tau \in C) \land ((\operatorname{Finset.card}\left(\tau\right) = (d) + (1)) \land (\operatorname{upperDegree}\left(C, \tau\right) = k)))\}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.degreeSet` (`✓ std3`).

*Citation.* S. N. Dorogovtsev; P. L. Krapivsky (2025). *Deterministic simplicial complexes*. DOI: [10.1088/1742-5468/ae2092](https://doi.org/10.1088/1742-5468/ae2092). URL: <https://arxiv.org/abs/2507.07402v1>.

*Commentary.*

A natural number k belongs to this set precisely when a face τ in C has d + 1 vertices and upper degree k. Multiplicities are discarded. Thus this set expresses the same distinct values as the increasing lists K⁽ᵈ⁾(n) in Section II.3 (TeX lines 427–503). An empty collection of faces of the specified size gives the empty degree set.

**Definition 1.4 (The degree-set identity).**

$$(\operatorname{claim}: \operatorname{Prop}) = (\forall (V: \operatorname{Type}), ([\operatorname{DecidableEq}\left(V\right)], (\forall (v_{0}: V), (\forall (v: (\mathbb{N}) \to ((\operatorname{Finset}\left(V\right)) \to (V))), ((\operatorname{Function.Injective}\left(\operatorname{Function.uncurry}\left(v\right)\right)) \to ((\forall (s: \mathbb{N}), (\forall (\sigma: \operatorname{Finset}\left(V\right)), (v\left(s, \sigma\right) \ne v_{0}))) \to (\forall (d: \mathbb{N}), (\forall (n: \mathbb{N}), ((1 \le d) \to (((d) + (1) \le n) \to (\operatorname{degreeSet}\left(\operatorname{dsc}\left(v_{0}, v, n\right), d\right) = \operatorname{insert}\left(0, \operatorname{degreeSet}\left(\operatorname{dsc}\left(v_{0}, v, (n) - (d)\right), 0\right)\right))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.claim` (`✓ std3`).

*Citation.* S. N. Dorogovtsev; P. L. Krapivsky (2025). *Deterministic simplicial complexes*. DOI: [10.1088/1742-5468/ae2092](https://doi.org/10.1088/1742-5468/ae2092). URL: <https://arxiv.org/abs/2507.07402v1>.

*Commentary.*

The labeling is injective as a function of the pair consisting of the step and the parent face, and no label equals v₀. For every natural dimension d at least one and generation n at least d + 1, the d-degree set is the vertex-degree set at generation n − d with zero adjoined. The subtraction is natural subtraction; the stated inequalities imply n − d ≥ 1. This is relation (34), stated as a conjecture at TeX lines 505–510, with the labeling assumptions and the sets of distinct values made explicit.

**Theorem 1.5 (The identity holds in every positive dimension).**

$$\forall (V: \operatorname{Type}), ([\operatorname{DecidableEq}\left(V\right)], (\forall (v_{0}: V), (\forall (v: (\mathbb{N}) \to ((\operatorname{Finset}\left(V\right)) \to (V))), ((\operatorname{Function.Injective}\left(\operatorname{Function.uncurry}\left(v\right)\right)) \to ((\forall (s: \mathbb{N}), (\forall (\sigma: \operatorname{Finset}\left(V\right)), (v\left(s, \sigma\right) \ne v_{0}))) \to (\forall (d: \mathbb{N}), (\forall (n: \mathbb{N}), ((1 \le d) \to (((d) + (1) \le n) \to (\operatorname{degreeSet}\left(\operatorname{dsc}\left(v_{0}, v, n\right), d\right) = \operatorname{insert}\left(0, \operatorname{degreeSet}\left(\operatorname{dsc}\left(v_{0}, v, (n) - (d)\right), 0\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.result` (`✓ std3`). ∎

*Resolves.* `Problems/dorogovtsev-krapivsky-2025-deterministic-simplicial-degree-shift` (proved) by `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"dorogovtsev-krapivsky-2025-deterministic-simplicial-degree-shift","declaration_gid":"D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. N. Dorogovtsev; P. L. Krapivsky (2025). *Deterministic simplicial complexes*. DOI: [10.1088/1742-5468/ae2092](https://doi.org/10.1088/1742-5468/ae2092). URL: <https://arxiv.org/abs/2507.07402v1>.

*Commentary.*

Fix V, v₀ and v satisfying the two labeling hypotheses. For a face τ in a family C, write L_C(τ) for the finite family of sets α disjoint from τ such that τ ∪ α belongs to C. Equivalently, take all members of C containing τ and remove τ from each. Define the binomial transform B_f(r) = ∑_{j=0}^r binom(r,j) f(j). Start with w₀(r) equal to one when r = 1 and zero otherwise, and set w_{q+1}(r) = w_q(r) + ∑_{j=0}^r binom(r,j) w_q(j + 1). Let A(t,r) = B_{w_t}(r). These natural numbers describe the evolution of the number of vertices among the residual faces.

A face at generation n + 1 is either an earlier face or has the form {v(n + 1, σ)} ∪ β for an earlier parent σ and a subset β of σ. Induction shows that every vertex in a generation-n face is either v₀ or a label from a step at most n. Injectivity and avoidance of v₀ therefore make all later labels absent from earlier faces. Every face at generation n has between one and n + 1 vertices. The family is closed under nonempty subsets: a subset of a new face either contains its new vertex and is produced by the same parent, or is an earlier subset of that parent. Repeatedly adjoining the vertex assigned to a largest face produces a face with n + 1 vertices. Taking subsets yields a face of every cardinality from one through n + 1.

The description of L_C(τ) by disjoint sets follows because removing τ and adjoining it again are inverse on the faces containing τ. Also, a label v(n + 1, σ) belongs to a new face {v(n + 1, ρ)} ∪ β exactly when σ = ρ: it cannot belong to the earlier subset β, and equality of the two new labels determines the parent. The upper degree of τ is ∑_{α ∈ L_C(τ)} w₀(|α|), since these are precisely the singleton residual sets.

Fix a face τ at generation n, let C be the family at that generation, and put L = L_C(τ). Its residual family after one step consists of L together with all {u_α} ∪ β, where α belongs to L, β is a subset of α, and u_α = v(n + 1, τ ∪ α). Indeed, a new face containing τ must come from a parent containing τ; removing τ identifies that parent with τ ∪ α. Conversely every such choice produces a face containing τ. The vertices u_α are distinct and occur in no earlier residual set. Hence the new families for different α are pairwise disjoint and are disjoint from L. For any function f on natural numbers, the sum of f of cardinalities after this step is ∑_{α ∈ L}(f(|α|) + ∑_{j=0}^{|α|} binom(|α|,j) f(j + 1)). Here adjoining u_α increases cardinality by one, and subsets of each cardinality j are counted by the binomial coefficient.

Applying this equality with f = w_q turns a sum of w_q at the next generation into a sum of w_{q+1} at the present generation. Earlier faces persist, so induction over t gives a sum of w_{q+t} at birth after t further steps. For a face {v(s + 1, σ)} ∪ η born from η ⊆ σ, the residual family at birth is exactly the powerset of σ ∖ η. Its new vertex forces the parent of every containing new face to be σ, while disjointness removes η. Grouping the residual subsets by cardinality consequently gives upper degree A(t, |σ| − |η|) at generation s + 1 + t. Every face is either the primordial singleton or has this birth description, by induction on the generation. The primordial singleton has residual family {∅} initially, so its degree at generation n is A(n,0).

For d ≥ 1, a face with d + 1 vertices cannot be the primordial singleton. In its birth description |η| = d. Set r = |σ| − |η| and let t be its age. Since |σ| ≤ s + 1 and s + 1 + t = n, one has t + r ≤ n − d. Conversely, for any natural t,r with this inequality, set s = n − t − 1, choose at generation s a parent σ of cardinality d + r, and choose η ⊆ σ of cardinality d. The face {v(s + 1, σ)} ∪ η persists to generation n and has degree A(t,r). Thus the d-degree set consists exactly of these values A(t,r).

At generation m the vertex degrees consist of A(m,0) from the primordial vertex and the values A(t,r) with 1 ≤ r and t + r ≤ m. For a new vertex η is empty, so r is the nonzero cardinality of its parent. Conversely, each such pair is realized by choosing a parent of cardinality r at generation m − t − 1 and adjoining its assigned vertex.

The binomial recurrence gives A(0,0) = 0 and A(t + 1,0) = A(t,1). For m ≥ 1, compare all pairs t,r with t + r ≤ m to the vertex description. A pair with r ≥ 1 already occurs there. If r = 0 and t ≥ 1, replace (t,0) by (t − 1,1), preserving its value and the bound on the sum. The sole remaining case (0,0) gives zero. In the reverse direction zero comes from (0,0), the primordial value comes from (m,0), and all other vertex values already satisfy the bound. Taking m = n − d ≥ 1 proves the asserted equality.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.degreeSet`
- Truth anchor: `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.dsc`
- Truth anchor: `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.result`
- Truth anchor: `D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift.upperDegree`
