# Fixed resistance does not force an invariant Fiedler maximizer

## Abstract

Invariant weights cannot maximize the Fiedler value at fixed resistance on K23.

Positive edge conductances determine a weighted Laplacian. Algebraic connectivity is its least Rayleigh quotient on nonzero vectors orthogonal to the constants. Effective resistance comes from a harmonic voltage with boundary values one and zero; total resistance sums over unordered pairs of distinct vertices.

**Definition 1.1 (Weighted Laplacian).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{wLap}\left(G, w\right)\left(i, j\right) = \operatorname{ite}\left(i = j, \sum_{k : \operatorname{Fin}\left(n\right) \mid \operatorname{SimpleGraph}.\operatorname{Adj}\left(G, i, k\right)} w\left(s(i,k)\right), \operatorname{ite}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G, i, j\right), -w\left(s(i,j)\right), 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap` (`✓ std3`).

*Citation.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

Section 2, page 3, states: “The laplacian of a weighted graph (G;ω) is the operator on ℓ(V) given by” (L(G,ω)x)i = ∑{vi,vj}∈E ωi,j(xi−xj). The displayed matrix has the weighted degree on the diagonal and negative conductance on each edge. Vertex labels are Fin n; weights are functions on Sym2 (Fin n).

**Definition 1.2 (Algebraic connectivity).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \operatorname{lambda2}\left(G, w\right) = \operatorname{sInf}\left(\{r : \mathrm{Real} \mid \exists x \in \operatorname{Fin}\left(n\right) \to \mathrm{Real},\; x \ne 0 \land \left(\sum_{i : \operatorname{Fin}\left(n\right)} x\left(i\right) = 0 \land r = \frac{\operatorname{dotProduct}\left(x, \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{wLap}\left(G, w\right), x\right)\right)}{\operatorname{dotProduct}\left(x, x\right)}\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.lambda2` (`✓ std3`).

*Citation.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

Section 3, page 4, states: “By the Courant-Fischer-Weyl theorem, the algebraic connectivity of a weighted graph is” λ2(G;ω) = min x⊥J ⟨L(G,ω)x,x⟩/⟨x,x⟩. The encoding excludes the zero vector explicitly and uses the infimum of the Rayleigh values.

**Definition 1.3 (Harmonic boundary data).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \forall x \in \operatorname{Fin}\left(n\right) \to \mathrm{Real},\; \operatorname{Harmonic}\left(G, w, i, j, x\right) = \left(x\left(i\right) = 1 \land \left(x\left(j\right) = 0 \land \left(\forall k \in \operatorname{Fin}\left(n\right),\; k \ne i \Rightarrow \left(k \ne j \Rightarrow \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{wLap}\left(G, w\right), x\right)\left(k\right) = 0\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.Harmonic` (`✓ std3`).

*Citation.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

A harmonic voltage has value one at i, zero at j, and zero weighted Laplacian at every other vertex. These are the boundary data used in Section 4 to define current and effective resistance.

**Definition 1.4 (Harmonic extension).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{harmonicExt}\left(G, w, i, j\right) = \operatorname{if} h : (\exists x \in \operatorname{Fin}\left(n\right) \to \mathrm{Real},\; \operatorname{Harmonic}\left(G, w, i, j, x\right)) \operatorname{then} \operatorname{Classical}.\operatorname{choose}\left(h\right) \operatorname{else} 0$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.harmonicExt` (`✓ std3`).

*Citation.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

Section 4, page 5, states: “The vector x̃ is known as the harmonic extension of x.” It requires (Lω x̃)v=0 outside the boundary set. A harmonic vector is chosen when one exists, and the value is zero otherwise. For the positive conductances used on K23, the explicit harmonic certificates exist and are unique for every ordered pair i<j used in totalRes; the zero fallback contributes to none of those resistances.

**Definition 1.5 (Effective resistance).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{effRes}\left(G, w, i, j\right) = \operatorname{ite}\left(i = j, 0, \frac{1}{\operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{wLap}\left(G, w\right), \operatorname{harmonicExt}\left(G, w, i, j\right)\right)\left(i\right)}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.effRes` (`✓ std3`).

*Citation.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

Section 4, Definition 4.1, page 5, states: “Given two vertices vi≠vj of the weighted graph (G;ω), let U={vi,vj}. For h∈ℓ(V) the harmonic extension of the function in ℓ(U) given by hi=1, hj=0, define” r(vi,vj)=⟨Lωh,h⟩⁻¹=(Lωh)i⁻¹. Thus resistance is the reciprocal of the boundary current. The source also defines r(v,v)=0; effRes uses zero on the diagonal.

**Definition 1.6 (Unordered-pair resistance).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{pairRes}\left(G, w, s(i,j)\right) = \operatorname{effRes}\left(G, w, \operatorname{min}\left(i, j\right), \operatorname{max}\left(i, j\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.pairRes` (`✓ std3`).

*Citation.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

Sym2.lift orients the representatives of an unordered pair by min and max. Thus each off-diagonal pair uses the same harmonic boundary convention irrespective of the order of its representatives.

**Definition 1.7 (Total resistance).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \operatorname{totalRes}\left(G, w\right) = \sum_{p : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \mid \neg \operatorname{Sym2}.\operatorname{IsDiag}\left(p\right)} \operatorname{pairRes}\left(G, w, p\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.totalRes` (`✓ std3`).

*Citation.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

Section 4, page 5, states: “The total effective resistance of (G,ω) is” R(G;ω)=∑{vi,vj} r(vi,vj). The non-diagonal Sym2 pairs count each unordered pair once.

**Definition 1.8 (Fixed-resistance feasible weights).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \operatorname{Feasible}\left(G, w\right) = \left(\left(\forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right),\; e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right) \Rightarrow 0 < w\left(e\right)\right) \land \operatorname{totalRes}\left(G, w\right) = \operatorname{totalRes}\left(G, 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.Feasible` (`✓ std3`).

*Citation.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

Feasible weights are strictly positive on edges and have the same total resistance as the unweighted graph. Values on nonedges are unrestricted; edgewise equality suffices to preserve both lambda2 and totalRes.

**Definition 1.9 (Automorphism invariance).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \operatorname{AutInvariant}\left(G, w\right) = \left(\forall sigma \in \operatorname{SimpleGraph}.\operatorname{Iso}\left(G, G\right),\; \forall e \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right),\; e \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right) \Rightarrow w\left(\operatorname{Sym2}.\operatorname{map}\left(sigma, e\right)\right) = w\left(e\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.AutInvariant` (`✓ std3`).

*Citation.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

An automorphism-invariant weight function has the same value on each edge and its image under every graph automorphism. This condition constrains edges only.

**Definition 1.10 (The labelled complete bipartite graph).**

$$\operatorname{K23} = \operatorname{SimpleGraph}.\operatorname{comap}\left(\operatorname{Equiv}.\operatorname{symm}\left(\operatorname{finSumFinEquiv}\left(2, 3\right)\right), \operatorname{completeBipartiteGraph}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(3\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.K23` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse of finSumFinEquiv labels the two hubs by 0 and 1 and the three leaves by 2, 3 and 4.

**Definition 1.11 (Decidable adjacency).**

$$\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(\operatorname{K23}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.K23_dec` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Adjacency in the labelled complete bipartite graph is decidable.

**Lemma 1.12 (Connectivity of the complete bipartite graph).**

$$\operatorname{SimpleGraph}.\operatorname{Connected}\left(\operatorname{K23}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.K23_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every vertex is reachable from vertex 2 by a path of length at most two.

**Definition 1.13 (The Section 5 conjecture).**

$$\operatorname{claim} = \left(\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right) \Rightarrow \left(3 \le n \Rightarrow \left(\exists w \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \operatorname{Feasible}\left(G, w\right) \land \left(\operatorname{AutInvariant}\left(G, w\right) \land \left(\forall v \in \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \mathrm{Real},\; \operatorname{Feasible}\left(G, v\right) \Rightarrow \operatorname{lambda2}\left(G, v\right) \le \operatorname{lambda2}\left(G, w\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.claim` (`✓ std3`).

*Citation.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

Section 5, page 7, states verbatim: “We conjecture that – in the same fashion of what happens with the absolute algebraic connectivity – the maximal value of (3) is attained always for weight distributions that are invariant under automorphisms of the graph.” Equation (3) defines ă(G) = max {λ2(G;ω) | R(G;ω)=R(G)}. The encoding quantifies over connected finite simple graphs of order at least three and asserts an invariant feasible assignment dominating every feasible assignment; it does not assume existence of a maximum separately.

**Theorem 1.14 (Refutation on K23).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/cruz-menendez-2023-fiedler-resistance-invariant-weights` (refuted) by `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cruz-menendez-2023-fiedler-resistance-invariant-weights","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. Cruz Ortega; F. Menéndez-Conde (2023). *Conectividad algebraica máxima para caminos con resistencia total fija*. DOI: [10.15381/pesquimat.v26i2.24218](https://doi.org/10.15381/pesquimat.v26i2.24218). URL: <https://arxiv.org/abs/2306.08187v1>.

*Commentary.*

Let the hubs be 0 and 1 and the leaves be 2, 3 and 4. Conductances 32/23 on the edges incident to hub 0 and 16/23 on those incident to hub 1 give total resistance 23/3, equal to the unweighted value, and algebraic connectivity 48/23. Rayleigh lower bounds and the leaf-difference eigenvector certify that value, while explicit harmonic voltages certify the resistances. Hub and leaf swaps force every invariant feasible assignment to have weight one on each edge and algebraic connectivity two. Since 48/23>2, no invariant assignment can attain the constrained maximum, whether or not the maximum exists.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.AutInvariant`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.Feasible`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.Harmonic`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.K23`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.K23_connected`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.K23_dec`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.effRes`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.harmonicExt`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.lambda2`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.pairRes`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.totalRes`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceInvariantWeightsRefutation.wLap`
