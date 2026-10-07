# The Mermin-CGLMP facet conjecture

## Abstract

The Mermin-CGLMP inequality has a saturating face of affine codimension one for every K >= 2.

**Definition 1.1 (Deterministic full behaviours).**

$$\forall K \in \mathbb{N},\; \forall s \in ((\operatorname{Fin}\left(2\right))\to\operatorname{Fin}\left(K\right))\times((\operatorname{Fin}\left(2\right))\to\operatorname{Fin}\left(K\right))\times((\operatorname{Fin}\left(2\right))\to\operatorname{Fin}\left(K\right)),\; \forall q \in (\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(2\right))\times(\operatorname{Fin}\left(K\right)\times\operatorname{Fin}\left(K\right)\times\operatorname{Fin}\left(K\right)),\; \operatorname{vertex}\left(K, s, q\right) = \operatorname{if}\left((s.1(q.1.1) = q.2.1) \land ((s.2.1(q.1.2.1) = q.2.2.1) \land (s.2.2(q.1.2.2) = q.2.2.2))\right)\operatorname{then}\left(1\right)\operatorname{else}\left(0\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminCglmpFacet.vertex` (`✓ std3`).

*Citation.* B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin (2012). *Bell inequalities for three systems and arbitrarily many measurement outcomes*. DOI: [10.48550/arXiv.1204.3829](https://doi.org/10.48550/arXiv.1204.3829). URL: <https://arxiv.org/abs/1204.3829v2>.

*Commentary.*

Section II, PDF p. 1, states: “We consider a scenario involving three spatially separated parties (henceforth referred as Alice, Bob and Charlie), and with each of them performing 2 alternative K-outcome measurements.” Input 0 is source setting 1 and input 1 is source setting 2. Each of the three components of s assigns an output to both settings. The value of vertex is one exactly when all three observed outputs match these assignments, and is zero otherwise. The coordinates include all eight setting triples and all K-cubed output triples.

**Definition 1.2 (The local polytope).**

$$\forall K \in \mathbb{N},\; \operatorname{L}\left(K\right) = \operatorname{convexHull}\left(\mathbb{R}, \operatorname{Set}.\operatorname{range}\left(\operatorname{vertex}\left(K\right)\right)\right)$$

*Formalization.* `D5/S3/QuantumBounds/MerminCglmpFacet.L` (`✓ std3`).

*Citation.* B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin (2012). *Bell inequalities for three systems and arbitrarily many measurement outcomes*. DOI: [10.48550/arXiv.1204.3829](https://doi.org/10.48550/arXiv.1204.3829). URL: <https://arxiv.org/abs/1204.3829v2>.

*Commentary.*

Section II, PDF p. 2, states: “It suffices to consider deterministic classical strategies for determining the minimal value of S^(K) allowed in a local theory”. A local behaviour is a shared-randomness mixture of product response functions. Each response function is a mixture of deterministic assignments to its two settings; distributing these finite mixtures gives precisely the convex hull of the deterministic full behaviours. Thus L is the source's local polytope, with its normalisation and no-signalling relations inherited from those generators.

**Definition 1.3 (Least nonnegative residues).**

$$\forall K \in \mathbb{N},\; \forall t \in \mathbb{Z},\; \operatorname{bracket}\left(K, t\right) = (\operatorname{Int}.\operatorname{emod}\left(t, (K:\mathbb{Z})\right):\mathbb{R})$$

*Formalization.* `D5/S3/QuantumBounds/MerminCglmpFacet.bracket` (`✓ std3`).

*Citation.* B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin (2012). *Bell inequalities for three systems and arbitrarily many measurement outcomes*. DOI: [10.48550/arXiv.1204.3829](https://doi.org/10.48550/arXiv.1204.3829). URL: <https://arxiv.org/abs/1204.3829v2>.

*Commentary.*

Section II, PDF p. 1, states: “where [X]_K stands for X modulo K”. Int.emod is integer Euclidean remainder, with K first cast to the integers and the remainder then cast to the reals. For K >= 2 the value is in the interval from 0 through K-1, including for negative arguments.

**Definition 1.4 (The literal Bell functional).**

$$\forall K \in \mathbb{N},\; \forall p \in ((\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(2\right))\times(\operatorname{Fin}\left(K\right)\times\operatorname{Fin}\left(K\right)\times\operatorname{Fin}\left(K\right)))\to\mathbb{R},\; \operatorname{I}\left(K, p\right) = \sum_{a:\operatorname{Fin}\left(K\right)}(\sum_{b:\operatorname{Fin}\left(K\right)}(\sum_{c:\operatorname{Fin}\left(K\right)}(\operatorname{bracket}\left(K, (a:\mathbb{Z}) - (b:\mathbb{Z}) + (c:\mathbb{Z})\right) \cdot p(((1,0,0),(a,b,c)))))) + \sum_{a:\operatorname{Fin}\left(K\right)}(\sum_{b:\operatorname{Fin}\left(K\right)}(\sum_{c:\operatorname{Fin}\left(K\right)}(\operatorname{bracket}\left(K, (a:\mathbb{Z}) + (b:\mathbb{Z}) - (c:\mathbb{Z})\right) \cdot p(((0,1,0),(a,b,c)))))) + \sum_{a:\operatorname{Fin}\left(K\right)}(\sum_{b:\operatorname{Fin}\left(K\right)}(\sum_{c:\operatorname{Fin}\left(K\right)}(\operatorname{bracket}\left(K, -((a:\mathbb{Z})) + (b:\mathbb{Z}) + (c:\mathbb{Z})\right) \cdot p(((0,0,1),(a,b,c)))))) + \sum_{a:\operatorname{Fin}\left(K\right)}(\sum_{b:\operatorname{Fin}\left(K\right)}(\sum_{c:\operatorname{Fin}\left(K\right)}(\operatorname{bracket}\left(K, -((a:\mathbb{Z})) - (b:\mathbb{Z}) - (c:\mathbb{Z}) - 1\right) \cdot p(((1,1,1),(a,b,c))))))$$

*Formalization.* `D5/S3/QuantumBounds/MerminCglmpFacet.I` (`✓ std3`).

*Citation.* B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin (2012). *Bell inequalities for three systems and arbitrarily many measurement outcomes*. DOI: [10.48550/arXiv.1204.3829](https://doi.org/10.48550/arXiv.1204.3829). URL: <https://arxiv.org/abs/1204.3829v2>.

*Commentary.*

Section II, PDF p. 1, gives (1): “S^(K) = ⟨[A_2−B_1+C_1]_K⟩ + ⟨[A_1+B_2−C_1]_K⟩ + ⟨[−A_1+B_1+C_2]_K⟩ + ⟨[−A_2−B_2−C_2−1]_K⟩ ≥ K−1”. Equation (2) defines ⟨[X]_K⟩ = ∑_{j=0}^{K−1} j P(X = j mod K). Summing each residue against the full joint probabilities groups exactly into these residue events. The four input triples are respectively (1,0,0), (0,1,0), (0,0,1) and (1,1,1); these encode (2,1,1), (1,2,1), (1,1,2) and (2,2,2) in the source. All integer output casts and all four signs and offsets are retained.

**Definition 1.5 (The conjecture for every K).**

$$(claim) \Leftrightarrow (\forall K \in \mathbb{N},\; (2 \le K) \Rightarrow ((\forall p \in ((\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(2\right))\times(\operatorname{Fin}\left(K\right)\times\operatorname{Fin}\left(K\right)\times\operatorname{Fin}\left(K\right)))\to\mathbb{R},\; (p \in \operatorname{L}\left(K\right)) \Rightarrow ((K:\mathbb{R}) - 1 \le \operatorname{I}\left(K, p\right))) \land (\operatorname{Module}.\operatorname{finrank}\left(\mathbb{R}, \operatorname{vectorSpan}\left(\mathbb{R}, \{p\mid(p \in \operatorname{L}\left(K\right)) \land (\operatorname{I}\left(K, p\right) = (K:\mathbb{R}) - 1)\}\right)\right) + 1 = \operatorname{Module}.\operatorname{finrank}\left(\mathbb{R}, \operatorname{vectorSpan}\left(\mathbb{R}, \operatorname{L}\left(K\right)\right)\right))))$$

*Formalization.* `D5/S3/QuantumBounds/MerminCglmpFacet.claim` (`✓ std3`).

*Citation.* B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin (2012). *Bell inequalities for three systems and arbitrarily many measurement outcomes*. DOI: [10.48550/arXiv.1204.3829](https://doi.org/10.48550/arXiv.1204.3829). URL: <https://arxiv.org/abs/1204.3829v2>.

*Commentary.*

Section II, PDF p. 2, states verbatim: “We conjecture that inequality (1) is indeed facet-defining for all K ≥ 2.” The parameter K is natural-valued, so this is exactly the stated integer range. The first conjunct is validity on the entire local polytope. The second uses vectorSpan, the direction space of the affine span, so its finrank is affine dimension. The saturating face has dimension one less than L. The carrier is the full behaviour space; there is no projection to correlators or restriction to a family of strategies.

**Theorem 1.6 (The inequality defines a facet).**

$$\forall K \in \mathbb{N},\; (2 \le K) \Rightarrow ((\forall p \in ((\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(2\right)\times\operatorname{Fin}\left(2\right))\times(\operatorname{Fin}\left(K\right)\times\operatorname{Fin}\left(K\right)\times\operatorname{Fin}\left(K\right)))\to\mathbb{R},\; (p \in \operatorname{L}\left(K\right)) \Rightarrow ((K:\mathbb{R}) - 1 \le \operatorname{I}\left(K, p\right))) \land (\operatorname{Module}.\operatorname{finrank}\left(\mathbb{R}, \operatorname{vectorSpan}\left(\mathbb{R}, \{p\mid(p \in \operatorname{L}\left(K\right)) \land (\operatorname{I}\left(K, p\right) = (K:\mathbb{R}) - 1)\}\right)\right) + 1 = \operatorname{Module}.\operatorname{finrank}\left(\mathbb{R}, \operatorname{vectorSpan}\left(\mathbb{R}, \operatorname{L}\left(K\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MerminCglmpFacet.result` (`✓ std3`). ∎

*Resolves.* `Problems/grandjean-liang-bancal-brunner-gisin-2012-mermin-cglmp-facet` (proved) by `D5/S3/QuantumBounds/MerminCglmpFacet.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"grandjean-liang-bancal-brunner-gisin-2012-mermin-cglmp-facet","declaration_gid":"D5/S3/QuantumBounds/MerminCglmpFacet.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin (2012). *Bell inequalities for three systems and arbitrarily many measurement outcomes*. DOI: [10.48550/arXiv.1204.3829](https://doi.org/10.48550/arXiv.1204.3829). URL: <https://arxiv.org/abs/1204.3829v2>.

*Commentary.*

Fixing Charlie's two outputs relabels each slice to CGLMP. The short-arc rigidity theorem supplies a multiplier for each slice. Additive separability in Charlie's outputs imposes a rectangular identity. Strategies with A_1+A_2+B_2−B_1 equal to 0 or −1 force each multiplier to be independent of both Charlie outputs. The common multiplier gives global rigidity. The convex-geometric bridge then proves the affine-dimension equation, while linearity extends validity from deterministic generators to their convex hull.

## References

- Truth anchor: `D5/S3/QuantumBounds/MerminCglmpFacet.I`
- Truth anchor: `D5/S3/QuantumBounds/MerminCglmpFacet.L`
- Truth anchor: `D5/S3/QuantumBounds/MerminCglmpFacet.bracket`
- Truth anchor: `D5/S3/QuantumBounds/MerminCglmpFacet.claim`
- Truth anchor: `D5/S3/QuantumBounds/MerminCglmpFacet.result`
- Truth anchor: `D5/S3/QuantumBounds/MerminCglmpFacet.vertex`
- Dependency: [D5/S3/QuantumBounds/CglmpFacetRigidity](CglmpFacetRigidity.md)
- Dependency: [D5/S3/QuantumBounds/FacetRigidityBridge](FacetRigidityBridge.md)
