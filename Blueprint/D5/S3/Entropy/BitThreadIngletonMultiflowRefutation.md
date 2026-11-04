# An Ingleton counterexample for max multiflows

## Abstract

A capacitated star separates the Ingleton combination of minimum cuts from that of a max multiflow.

**Definition 1.1 (The capacity of a vertex cut).**

$$\forall (vtx: \operatorname{Type}), ([\operatorname{Fintype}\left(vtx\right)] [\operatorname{DecidableEq}\left(vtx\right)], (\forall (cap: (vtx) \to ((vtx) \to (\mathbb{R}))), (\forall (w: \operatorname{Finset}\left(vtx\right)), ((\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.cutValue}\left(cap, w\right): \mathbb{R}) = \sum_{(u: vtx)} (\sum_{(v: vtx)} (\operatorname{ite}\left((u \in w) \land (\neg (v \in w)), cap\left(u, v\right), (0: \mathbb{R})\right)))))))$$

*Formalization.* `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.cutValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ning Bao; Jonathan Harper (2020). *Bit threads on hypergraphs*. DOI: [10.48550/arXiv.2012.07872](https://doi.org/10.48550/arXiv.2012.07872). URL: <https://arxiv.org/abs/2012.07872v1>.

*Commentary.*

For a real capacity function cap on a finite vertex type vtx, cutValue cap w sums the capacities directed from w to its complement. Each ordered pair contributes cap u v exactly when u lies in w and v does not. No symmetry or positivity is required by this definition.

**Definition 1.2 (Cuts with a prescribed boundary side).**

$$\forall (vtx: \operatorname{Type}), ([\operatorname{Fintype}\left(vtx\right)] [\operatorname{DecidableEq}\left(vtx\right)], (\forall (k: \mathbb{N}), (\forall (b: \operatorname{Function.Embedding}\left(\operatorname{Fin}\left(k\right), vtx\right)), (\forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), ((\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.admissibleCuts}\left(b, s\right): \operatorname{Finset}\left(\operatorname{Finset}\left(vtx\right)\right)) = \operatorname{Finset.filter}\left(\lambda (w: \operatorname{Finset}\left(vtx\right)) \mapsto (\forall (i: \operatorname{Fin}\left(k\right)), ((b\left(i\right) \in w) \Leftrightarrow (i \in s))), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Finset}\left(vtx\right)\right))\right))))))$$

*Formalization.* `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.admissibleCuts` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ning Bao; Jonathan Harper (2020). *Bit threads on hypergraphs*. DOI: [10.48550/arXiv.2012.07872](https://doi.org/10.48550/arXiv.2012.07872). URL: <https://arxiv.org/abs/2012.07872v1>.

*Commentary.*

The embedding b labels k distinct boundary vertices. An admissible cut for s contains precisely the labelled boundary vertices whose indices belong to s; membership of every other vertex is unrestricted. Filtering all vertex subsets gives a finite collection of such cuts.

**Definition 1.3 (The minimum boundary cut).**

$$\forall (vtx: \operatorname{Type}), ([\operatorname{Fintype}\left(vtx\right)] [\operatorname{DecidableEq}\left(vtx\right)], (\forall (k: \mathbb{N}), (\forall (cap: (vtx) \to ((vtx) \to (\mathbb{R}))), (\forall (b: \operatorname{Function.Embedding}\left(\operatorname{Fin}\left(k\right), vtx\right)), (\forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), ((\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.minCut}\left(cap, b, s\right): \mathbb{R}) = \operatorname{Finset.min}'\left(\operatorname{Finset.image}\left(\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.cutValue}\left(cap\right), \operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.admissibleCuts}\left(b, s\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.minCut` (`✓ std3`).

*Citation.* Ning Bao; Jonathan Harper (2020). *Bit threads on hypergraphs*. DOI: [10.48550/arXiv.2012.07872](https://doi.org/10.48550/arXiv.2012.07872). URL: <https://arxiv.org/abs/2012.07872v1>.

*Commentary.*

The entropy of s is the least capacity among its admissible vertex cuts. The collection is nonempty because the image of s under b is an admissible cut. Thus the finite minimum exists even for arbitrary real capacities and an empty boundary. This is the finite graph form of the source's minimum-cut entropy in the footnote at BT_Hyper.tex line 417.

**Definition 1.4 (Pair flows with a shared capacity bound).**

$$\forall (vtx: \operatorname{Type}), ([\operatorname{Fintype}\left(vtx\right)] [\operatorname{DecidableEq}\left(vtx\right)], (\forall (k: \mathbb{N}), (\forall (cap: (vtx) \to ((vtx) \to (\mathbb{R}))), (\forall (b: \operatorname{Function.Embedding}\left(\operatorname{Fin}\left(k\right), vtx\right)), (\forall (f: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to ((vtx) \to ((vtx) \to (\mathbb{R}))))), (\forall (n: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to (\mathbb{R}))), ((\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.IsMultiflow}\left(cap, b, f, n\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(k\right)), (\forall (j: \operatorname{Fin}\left(k\right)), (\forall (u: vtx), (\forall (v: vtx), ((i < j) \to (f\left(i, j, u, v\right) = -f\left(i, j, v, u\right))))))) \land ((\forall (i: \operatorname{Fin}\left(k\right)), (\forall (j: \operatorname{Fin}\left(k\right)), (\forall (u: vtx), ((i < j) \to ((u \ne b\left(i\right)) \to ((u \ne b\left(j\right)) \to (\sum_{(v: vtx)} (f\left(i, j, u, v\right)) = (0: \mathbb{R})))))))) \land ((\forall (i: \operatorname{Fin}\left(k\right)), (\forall (j: \operatorname{Fin}\left(k\right)), ((i < j) \to (((0: \mathbb{R}) \le n\left(i, j\right)) \land ((\sum_{(v: vtx)} (f\left(i, j, b\left(i\right), v\right)) = n\left(i, j\right)) \land (\sum_{(v: vtx)} (f\left(i, j, b\left(j\right), v\right)) = -n\left(i, j\right))))))) \land (\forall (u: vtx), (\forall (v: vtx), (\sum_{(i: \operatorname{Fin}\left(k\right))} (\sum_{(j: \operatorname{Fin}\left(k\right))} (\operatorname{ite}\left(i < j, \left|f\left(i, j, u, v\right)\right|, (0: \mathbb{R})\right))) \le cap\left(u, v\right))))))))))))))$$

*Formalization.* `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.IsMultiflow` (`✓ std3`).

*Citation.* Ning Bao; Jonathan Harper (2020). *Bit threads on hypergraphs*. DOI: [10.48550/arXiv.2012.07872](https://doi.org/10.48550/arXiv.2012.07872). URL: <https://arxiv.org/abs/2012.07872v1>.

*Commentary.*

For each boundary pair i < j, f i j is antisymmetric in its vertex arguments and has zero divergence away from b i and b j. Its divergences at those endpoints are respectively n i j and minus n i j, with n i j nonnegative. On every ordered vertex pair, the sum of the absolute pair-flow values is at most cap u v. Entries with i not less than j do not contribute to this load or impose flow conditions. These are finite graph versions of the multiflow constraints in BT_Hyper.tex lines 100–107, with the endpoint fluxes written explicitly.

**Definition 1.5 (Threads crossing a boundary region).**

$$\forall (k: \mathbb{N}), (\forall (n: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to (\mathbb{R}))), (\forall (s: \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)), ((\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.subflow}\left(n, s\right): \mathbb{R}) = \sum_{(i: \operatorname{Fin}\left(k\right)) \in s} (\sum_{(j: \operatorname{Fin}\left(k\right))} (\operatorname{ite}\left(\neg (j \in s), \operatorname{ite}\left(i < j, n\left(i, j\right), n\left(j, i\right)\right), (0: \mathbb{R})\right))))))$$

*Formalization.* `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.subflow` (`✓ std3`).

*Citation.* Ning Bao; Jonathan Harper (2020). *Bit threads on hypergraphs*. DOI: [10.48550/arXiv.2012.07872](https://doi.org/10.48550/arXiv.2012.07872). URL: <https://arxiv.org/abs/2012.07872v1>.

*Commentary.*

The subflow of s sums the thread numbers for pairs with one boundary index in s and the other outside. The lesser index is always the first argument of n, so each crossing pair is counted once. This is Definition 1 in BT_Hyper.tex lines 110–115, using one representative of each unordered pair.

**Definition 1.6 (Simultaneous singleton saturation).**

$$\forall (vtx: \operatorname{Type}), ([\operatorname{Fintype}\left(vtx\right)] [\operatorname{DecidableEq}\left(vtx\right)], (\forall (k: \mathbb{N}), (\forall (cap: (vtx) \to ((vtx) \to (\mathbb{R}))), (\forall (b: \operatorname{Function.Embedding}\left(\operatorname{Fin}\left(k\right), vtx\right)), (\forall (f: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to ((vtx) \to ((vtx) \to (\mathbb{R}))))), (\forall (n: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to (\mathbb{R}))), ((\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.IsMaxMultiflow}\left(cap, b, f, n\right)) \Leftrightarrow ((\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.IsMultiflow}\left(cap, b, f, n\right)) \land (\forall (i: \operatorname{Fin}\left(k\right)), (\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.subflow}\left(n, \{i\}\right) = \operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.minCut}\left(cap, b, \{i\}\right)))))))))))$$

*Formalization.* `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.IsMaxMultiflow` (`✓ std3`).

*Citation.* Ning Bao; Jonathan Harper (2020). *Bit threads on hypergraphs*. DOI: [10.48550/arXiv.2012.07872](https://doi.org/10.48550/arXiv.2012.07872). URL: <https://arxiv.org/abs/2012.07872v1>.

*Commentary.*

A max multiflow is a multiflow whose subflow at each singleton equals the minimum cut for that singleton. This is the saturation condition of Theorem 1 in BT_Hyper.tex lines 117–124. No saturation of larger boundary regions is included in the predicate.

**Definition 1.7 (The proposed equality for every max multiflow).**

$$(\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.claim}) \Leftrightarrow (\forall (vtx: \operatorname{Type}), ([\operatorname{Fintype}\left(vtx\right)] [\operatorname{DecidableEq}\left(vtx\right)], (\forall (k: \mathbb{N}), (\forall (cap: (vtx) \to ((vtx) \to (\mathbb{R}))), (\forall (b: \operatorname{Function.Embedding}\left(\operatorname{Fin}\left(k\right), vtx\right)), (\forall (\alpha: (\operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)) \to (\mathbb{R})), ((\forall (u: vtx), (\forall (v: vtx), (cap\left(u, v\right) = cap\left(v, u\right)))) \to ((\forall (u: vtx), (cap\left(u, u\right) = (0: \mathbb{R}))) \to ((\forall (u: vtx), (\forall (v: vtx), ((0: \mathbb{R}) \le cap\left(u, v\right)))) \to ((\forall (f: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to ((vtx) \to ((vtx) \to (\mathbb{R}))))), (\forall (n: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to (\mathbb{R}))), ((\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.IsMultiflow}\left(cap, b, f, n\right)) \to (\operatorname{dotProduct}\left(\alpha, \operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.subflow}\left(n\right)\right) \ge (0: \mathbb{R}))))) \to ((\exists (f: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to ((vtx) \to ((vtx) \to (\mathbb{R}))))), (\exists (n: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to (\mathbb{R}))), ((\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.IsMultiflow}\left(cap, b, f, n\right)) \land (\operatorname{dotProduct}\left(\alpha, \operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.subflow}\left(n\right)\right) \ne (0: \mathbb{R}))))) \to (\forall (f: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to ((vtx) \to ((vtx) \to (\mathbb{R}))))), (\forall (n: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(k\right)) \to (\mathbb{R}))), ((\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.IsMaxMultiflow}\left(cap, b, f, n\right)) \to (\operatorname{dotProduct}\left(\alpha, \operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.minCut}\left(cap, b\right)\right) = \operatorname{dotProduct}\left(\alpha, \operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.subflow}\left(n\right)\right))))))))))))))))$$

*Formalization.* `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ning Bao; Jonathan Harper (2020). *Bit threads on hypergraphs*. DOI: [10.48550/arXiv.2012.07872](https://doi.org/10.48550/arXiv.2012.07872). URL: <https://arxiv.org/abs/2012.07872v1>.

*Commentary.*

For every finite vertex type, every natural boundary size, every symmetric loopless nonnegative real capacity function, every boundary embedding and every real coefficient family, consider the same linear functional of minimum cuts and of subflows. If the functional is nonnegative on every multiflow and nonzero on at least one, the proposed conclusion equates its minimum-cut value with its value on every max multiflow. The coefficients are unrestricted real numbers; the source writes their positive and negative parts separately at BT_Hyper.tex lines 409–416. This is the finite graph reading of Conjecture 1 at lines 419–424; the footnote at line 417 includes 2-graphs among its geometries.

**Theorem 1.8 (A five-boundary star refutes the equality).**

$$\neg (\operatorname{D5.S3.Entropy.BitThreadIngletonMultiflowRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bao-harper-2020-bit-thread-ingleton-multiflow` (refuted) by `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bao-harper-2020-bit-thread-ingleton-multiflow","declaration_gid":"D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ning Bao; Jonathan Harper (2020). *Bit threads on hypergraphs*. DOI: [10.48550/arXiv.2012.07872](https://doi.org/10.48550/arXiv.2012.07872). URL: <https://arxiv.org/abs/2012.07872v1>.

*Commentary.*

Use the six vertices 0, 1, 2, 3, 4, 5, with centre 5 and boundary labels A, B, C, D, E at 0, 1, 2, 3, 4. The boundary embedding is the natural inclusion of Fin 5 into Fin 6. The four edges from the centre to A, B, C, D have capacity 1, and the edge to E has capacity 2, in both directions; all other capacities are zero. For a boundary region I, let w(I) sum these boundary capacities, whose total is 6.

Choose the linear functional R(x) = x(AB) + x(AC) + x(AD) + x(BC) + x(BD) − x(A) − x(B) − x(CD) − x(ABC) − x(ABD), where juxtaposed labels denote their union. Expanding its coefficients first gives this ten-term expression for every region function x. Substituting the definition of subflow and collecting each pair's contributions then gives R(subflow n) = 2 n 0 1 + 2 n 2 3 for every real thread-number family n. The other eight unordered pairs have coefficient zero. The source also gives this 2-graph identity at BT_Hyper.tex lines 395–399.

For any admissible vertex cut W of I, its capacity is w(I) when the centre is outside W, and 6 − w(I) when the centre is inside W. Both cases are attained: take the boundary image of I alone, or add the centre. These two cuts give the upper bounds for the minimum, while the two-case expression bounds every admissible cut from below. Consequently minCut(I) = min(w(I), 6 − w(I)).

Set n 0 1 = n 2 4 = n 3 4 = 1 and all other entries to zero. For each selected pair, send one unit along the two-edge path from its smaller boundary vertex through the centre to its larger boundary vertex, and assign the negatives on reversed edges. All unselected pair flows are zero. Checking the finite vertex and pair cases establishes antisymmetry, zero divergence away from the two endpoints, endpoint divergences equal to the prescribed nonnegative thread numbers and the shared capacity bounds. The edge loads are 1, 1, 1, 1, 2, respectively. The singleton subflows are also 1, 1, 1, 1, 2; applying the minimum-cut formula at each singleton shows that this is a max multiflow.

Evaluating the ten minimum cuts gives 2, 2, 2, 2, 2 for the positive terms and 1, 1, 2, 3, 3 for the negative terms. Hence R(minCut) = 0. The pair-coefficient identity gives R(subflow n) = 2 for the chosen threads. For an arbitrary multiflow, its nonnegative thread numbers at pairs (0,1) and (2,3), together with the same identity, give R(subflow n) ≥ 0. The capacity function is symmetric, vanishes on the diagonal and is nonnegative, as its explicit finite values show.

Assuming claim, apply it to this graph, its five boundary vertices and R. Universal nonnegativity supplies the first functional hypothesis; the constructed multiflow with value 2 supplies the nonzero example. Applying the resulting equality to that same max multiflow yields 0 = 2, a contradiction. Thus the proposed equality fails already for a finite 2-graph and the Ingleton combination named in BT_Hyper.tex line 426. Its minimum-cut value here is zero, so the counterexample does not violate the Ingleton inequality itself.

## References

- Truth anchor: `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.IsMaxMultiflow`
- Truth anchor: `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.IsMultiflow`
- Truth anchor: `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.admissibleCuts`
- Truth anchor: `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.claim`
- Truth anchor: `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.cutValue`
- Truth anchor: `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.minCut`
- Truth anchor: `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.result`
- Truth anchor: `D5/S3/Entropy/BitThreadIngletonMultiflowRefutation.subflow`
