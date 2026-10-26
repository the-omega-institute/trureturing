# Exact source reconstruction and coordinate counting

## Abstract

Bounded weak coordinate data and literal triangular closure have exactly the same finite objects and first-column count. The coordinate description permits every zero and tie, while ordered exceptional bits make reconstruction unique.

**Definition 1.1 (Reconstruct the labelled finite edges).**

$$\forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall B \in \operatorname{Fin}\left(i\right) \to \left(\operatorname{Fin}\left(i\right) \to \operatorname{Prop}\left(\right)\right),\; \forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; ((a, b) \in \operatorname{coordinateEdgeSet}\left(M, p, c, B\right)) \Leftrightarrow (\exists u \in \operatorname{BoundedCoordinateVertex}\left(M, p\right),\; \exists v \in \operatorname{BoundedCoordinateVertex}\left(M, p\right),\; ((\operatorname{coordinateEdges}\left(p, c, B\right)(\operatorname{val}\left(u\right), \operatorname{val}\left(v\right))) \land (\operatorname{coordinateLabel}\left(p, \operatorname{val}\left(u\right)\right) = a)) \land (\operatorname{coordinateLabel}\left(p, \operatorname{val}\left(v\right)\right) = b))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.coordinateEdgeSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Take all pairs of bounded coordinate vertices joined by coordinateEdges and apply the canonical natural label to both endpoints. This definition keeps actual edges; it contains no assumed counting formula. For a weakly increasing position list the label map is increasing and bijective onto zero through M+i.

**Theorem 1.2 (Reconstruction preserves the complete literal family).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; (i \le n + \operatorname{one}\left(\right)) \Rightarrow (\forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall B \in \operatorname{Fin}\left(i\right) \to \left(\operatorname{Fin}\left(i\right) \to \operatorname{Prop}\left(\right)\right),\; ((((\operatorname{Monotone}\left(p\right)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; p(j) \le n + \operatorname{one}\left(\right) - i)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; c(j) \le n + \operatorname{one}\left(\right) - i)) \land (\operatorname{Rules}\left(\operatorname{boundedCoordinateEdges}\left(n + \operatorname{one}\left(\right) - i, p, c, B\right)\right))) \Rightarrow (\operatorname{coordinateEdgeSet}\left(n + \operatorname{one}\left(\right) - i, p, c, B\right) \in \operatorname{edgeFamily}\left(n, n + \operatorname{one}\left(\right) - i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.coordinateEdgeSet_mem_edgeFamily` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

An increasing image transports both ordered closure rules and their maxima. The endpoint labels stay between zero and n+1. The anchor is ordinary rank zero; its neighbors are exactly ordinary ranks one through M, independently of all cutoffs and exceptional bits. Filtering the image edges by first coordinate zero therefore has cardinality M. The literal edge family and its triangle-point bijection retain the repeated-point source condition and both forced conclusions.

**Theorem 1.3 (Every source graph has canonical weak coordinate data).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; (i \le n + \operatorname{one}\left(\right)) \Rightarrow (\forall A \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right),\; (A \in \operatorname{edgeFamily}\left(n, n + \operatorname{one}\left(\right) - i\right)) \Rightarrow (\exists p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \exists c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \exists B \in \operatorname{Fin}\left(i\right) \to \left(\operatorname{Fin}\left(i\right) \to \operatorname{Prop}\left(\right)\right),\; (((((\operatorname{Monotone}\left(p\right)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; p(j) \le n + \operatorname{one}\left(\right) - i)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; c(j) \le n + \operatorname{one}\left(\right) - i)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; (\operatorname{B}\left(j, k\right)) \Rightarrow (j < k))) \land (\operatorname{Rules}\left(\operatorname{boundedCoordinateEdges}\left(n + \operatorname{one}\left(\right) - i, p, c, B\right)\right))) \land (\operatorname{coordinateEdgeSet}\left(n + \operatorname{one}\left(\right) - i, p, c, B\right) = A)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.edgeFamily_eq_coordinateEdgeSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The exact source realization gives an increasing bijection into the full finite natural interval. Its range equals the range of coordinateLabel, so uniqueness of increasing enumerations identifies the two maps. Restriction and extension across the supported finite vertex set give bounded Rules. Every actual source edge then agrees with the reconstructed edge set. Exceptional bits imply increasing exceptional labels, leaving no unused reverse or loop bits.

**Definition 1.4 (The finite coordinate carrier).**

$$\forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \operatorname{CoordinateDataCarrier}\left(M, i\right) = \operatorname{Prod}\left(\operatorname{Fin}\left(i\right) \to \operatorname{Fin}\left(M + \operatorname{one}\left(\right)\right), \operatorname{Prod}\left(\operatorname{Fin}\left(i\right) \to \operatorname{Fin}\left(M + \operatorname{one}\left(\right)\right), \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(i\right), \operatorname{Fin}\left(i\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.CoordinateDataCarrier` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

A datum consists of a position array, a cutoff array, and a finite set of labelled exceptional edges. Both arrays take values zero through M. There are no positivity or distinctness assumptions.

**Definition 1.5 (The finite admissible data family).**

$$\forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall d \in \operatorname{CoordinateDataCarrier}\left(M, i\right),\; (d \in \operatorname{coordinateDataFamily}\left(M, i\right)) \Leftrightarrow (((\operatorname{Monotone}\left(\operatorname{values}\left(\operatorname{fst}\left(d\right)\right)\right)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; ((j, k) \in \operatorname{snd}\left(\operatorname{snd}\left(d\right)\right)) \Rightarrow (j < k))) \land (\operatorname{Rules}\left(\operatorname{boundedCoordinateEdges}\left(M, \operatorname{values}\left(\operatorname{fst}\left(d\right)\right), \operatorname{values}\left(\operatorname{fst}\left(\operatorname{snd}\left(d\right)\right)\right), \operatorname{membership}\left(\operatorname{snd}\left(\operatorname{snd}\left(d\right)\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.coordinateDataFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Filter the finite carrier by a weakly increasing position array, exceptional bits supported on j<k, and the exact bounded closure rules. The notation values(f) in the display denotes the pointwise natural values of a Fin-valued array. Bounds are built into the carrier, and the empty exceptional index set is allowed.

**Theorem 1.6 (Exact coordinate enumeration on every original rank).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; (i \le n + \operatorname{one}\left(\right)) \Rightarrow (\operatorname{count}\left(n, n + \operatorname{one}\left(\right) - i\right) = \operatorname{card}\left(\operatorname{coordinateDataFamily}\left(n + \operatorname{one}\left(\right) - i, i\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.count_eq_coordinateDataFamily_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Reconstruction maps the finite admissible data family into edgeFamily. For injectivity, the increasing missing anchor-neighbor labels p(j)+j+1 recover p; ordinary incidence at rank c(j)+1 distinguishes any two bounded cutoffs; the remaining increasing exceptional edges recover B. The source reconstruction supplies surjectivity. The finite bijection and the literal point-edge count bridge give the displayed equality for every valid n and i, including M=0, i=0 and n=0. The separate binomial-basis coefficient identity and its top coefficient are not asserted by this cardinality theorem.

**Theorem 1.7 (Generic admissibility forces the exceptional bits).**

$$\forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall B \in \operatorname{Fin}\left(i\right) \to \left(\operatorname{Fin}\left(i\right) \to \operatorname{Prop}\left(\right)\right),\; ((((((\operatorname{StrictMono}\left(p\right)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; p(j) \le M)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; c(j) \le M)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{zero}\left(\right) < p(j))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; \neg (c(j) = p(k)))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; (\operatorname{B}\left(j, k\right)) \Rightarrow (j < k))) \Rightarrow ((\operatorname{Rules}\left(\operatorname{boundedCoordinateEdges}\left(M, p, c, B\right)\right)) \Rightarrow (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; (\operatorname{B}\left(j, k\right)) \Leftrightarrow (((j < k) \land (c(j) < p(k))) \land (c(k) < p(j)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.coordinate_generic_bits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Assume positive strictly increasing positions, bounded cutoffs, no cutoff equal to any position, and exceptional bits supported on j<k. Transport the actual coordinate graph to the natural canonical labels. The existing generic_exceptional_edge theorem applies with the ordinary rank list and its exact Position and Cutoff statements. It forces every exceptional bit by the displayed criterion. This theorem assumes admissibility and does not count arrays.

**Theorem 1.8 (The generic exceptional criterion is sufficient as well).**

$$\forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall B \in \operatorname{Fin}\left(i\right) \to \left(\operatorname{Fin}\left(i\right) \to \operatorname{Prop}\left(\right)\right),\; ((((((\operatorname{StrictMono}\left(p\right)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; p(j) \le M)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; c(j) \le M)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{zero}\left(\right) < p(j))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; \neg (c(j) = p(k)))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; (\operatorname{B}\left(j, k\right)) \Rightarrow (j < k))) \Rightarrow ((\operatorname{Rules}\left(\operatorname{boundedCoordinateEdges}\left(M, p, c, B\right)\right)) \Leftrightarrow (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; (\operatorname{B}\left(j, k\right)) \Leftrightarrow (((j < k) \land (c(j) < p(k))) \land (c(k) < p(j)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.coordinate_generic_rules_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The forward direction uses coordinate_generic_bits. For the converse, apply the existing exists_cutoff_completion to the canonical ordinary and exceptional labels. Verify every bounded coordinate edge against that graph: ordinary clique edges, mixed cutoff incidence including rank zero, and the supplied exceptional criterion. Pullback and restriction transport both closure rules. This gives actual admissibility of the specified bits, rather than a presumed generic graph. Zero cutoffs and empty index sets remain allowed under the stated positive-position and separation hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.CoordinateDataCarrier`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.coordinateDataFamily`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.coordinateEdgeSet`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.coordinateEdgeSet_mem_edgeFamily`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.coordinate_generic_bits`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.coordinate_generic_rules_iff`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.count_eq_coordinateDataFamily_card`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuReconstruction.edgeFamily_eq_coordinateEdgeSet`
- Dependency: [D5/S3/Combinatorics/BinomialBases/MazorchukXuPatterns](MazorchukXuPatterns.md)
