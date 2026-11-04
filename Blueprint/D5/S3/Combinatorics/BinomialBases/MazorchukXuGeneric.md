# Forced edges in generic patterns

## Abstract

Finite position and cutoff data reconstruct the labelled source graphs and give unique generic completions.

**Definition 1.1 (Position relative to the ordinary list).**

$$\forall M \in \operatorname{Nat}\left(\right),\; \forall g \in \operatorname{Fin}\left(M\right) \to \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Nat}\left(\right),\; (\operatorname{Position}\left(g, s, p\right)) \Leftrightarrow ((p \le M) \land (\forall r \in \operatorname{Fin}\left(M\right),\; ((\operatorname{g}\left(r\right) < s) \Leftrightarrow (\operatorname{val}\left(r\right) < p)) \land ((s < \operatorname{g}\left(r\right)) \Leftrightarrow (p \le \operatorname{val}\left(r\right)))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.Position` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The zero-indexed list has M vertices. Exactly the indices below p occur before s, and exactly the indices at least p occur after s. The bound includes p=0 and p=M; no listed vertex equals s.

**Definition 1.2 (Incidence cutoff).**

$$\forall M \in \operatorname{Nat}\left(\right),\; \forall E \in \operatorname{Nat}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \operatorname{Prop}\left(\right)\right),\; \forall g \in \operatorname{Fin}\left(M\right) \to \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Nat}\left(\right),\; (\operatorname{Cutoff}\left(E, g, s, c\right)) \Leftrightarrow ((c \le M) \land (\forall r \in \operatorname{Fin}\left(M\right),\; (\operatorname{Incident}\left(E, s, \operatorname{g}\left(r\right)\right)) \Leftrightarrow (c \le \operatorname{val}\left(r\right))))$$

*Formalization.* `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.Cutoff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

The cutoff lies between zero and M. Incidence starts at the zero-indexed cutoff. Both empty and full incidence are included.

**Theorem 1.3 (The forced generic edge criterion).**

$$\forall E \in \operatorname{Nat}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \operatorname{Prop}\left(\right)\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall g \in \operatorname{Fin}\left(M\right) \to \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Nat}\left(\right),\; \forall t \in \operatorname{Nat}\left(\right),\; \forall ps \in \operatorname{Nat}\left(\right),\; \forall pt \in \operatorname{Nat}\left(\right),\; \forall cs \in \operatorname{Nat}\left(\right),\; \forall ct \in \operatorname{Nat}\left(\right),\; ((((((((((\operatorname{Rules}\left(E\right)) \land (\forall r \in \operatorname{Fin}\left(M\right),\; \operatorname{E}\left(0, \operatorname{g}\left(r\right)\right))) \land (0 < ps)) \land (ps < pt)) \land (\operatorname{Position}\left(g, s, ps\right))) \land (\operatorname{Position}\left(g, t, pt\right))) \land (\operatorname{Cutoff}\left(E, g, s, cs\right))) \land (\operatorname{Cutoff}\left(E, g, t, ct\right))) \land (\neg (cs = pt))) \land (\neg (ct = ps))) \Rightarrow ((\operatorname{E}\left(s, t\right)) \Leftrightarrow ((cs < pt) \land (ct < ps)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.generic_exceptional_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Assume the rules P and J, a list of vertices joined to zero, positions 0<ps<pt, and the two incidence cutoffs. When cs differs from pt and ct differs from ps, the edge from s to t exists exactly when cs<pt and ct<ps. Necessity uses the ordinary vertex just after s, then the vertices around t; when pt=M the latter bound follows directly from the cutoff bound. Sufficiency uses ordinary vertices immediately before s and t in J. No strict-monotonicity hypothesis on the list is needed because the position predicates already give the inequalities used in the proof. This criterion determines the exceptional edges whenever the listed generic inequalities hold.

**Theorem 1.4 (A completion for arbitrary cutoffs).**

$$\forall N \in \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall g \in \operatorname{Fin}\left(M\right) \to \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; ((((\operatorname{StrictMono}\left(g\right)) \land (\forall r \in \operatorname{Fin}\left(M\right),\; (0 < \operatorname{g}\left(r\right)) \land (\operatorname{g}\left(r\right) \le N))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; (((0 < \operatorname{s}\left(j\right)) \land (\operatorname{s}\left(j\right) \le N)) \land (\operatorname{Position}\left(g, \operatorname{s}\left(j\right), \operatorname{p}\left(j\right)\right))) \land (\operatorname{c}\left(j\right) \le M))) \land (\operatorname{Injective}\left(s\right))) \Rightarrow (\exists E \in \operatorname{Nat}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \operatorname{Prop}\left(\right)\right),\; ((((\operatorname{Rules}\left(E\right)) \land (\forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; (E(a, b)) \Rightarrow (b \le N))) \land (\forall a \in \operatorname{Nat}\left(\right),\; (\operatorname{E}\left(0, a\right)) \Leftrightarrow (((0 < a) \land (a \le N)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \neg (\operatorname{s}\left(j\right) = a))))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{Cutoff}\left(E, g, \operatorname{s}\left(j\right), \operatorname{c}\left(j\right)\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; (\operatorname{s}\left(j\right) < \operatorname{s}\left(k\right)) \Rightarrow ((\operatorname{E}\left(\operatorname{s}\left(j\right), \operatorname{s}\left(k\right)\right)) \Leftrightarrow ((\operatorname{c}\left(j\right) < \operatorname{p}\left(k\right)) \land (\operatorname{c}\left(k\right) < \operatorname{p}\left(j\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.exists_cutoff_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

An increasing ordinary list and an injective exceptional list lie in the positive vertices up to N. Position predicates separate the two lists. Every cutoff lies between zero and M, with no distinctness requirement. Assign height zero to all nonexceptional vertices. An exceptional height is the ordinary vertex at its cutoff, or N+1 for an empty terminal segment. Join a<b exactly when both endpoints lie below the bound and each height is at most the opposite endpoint. These integer threshold edges satisfy both rules. The anchor edges, every ordinary incidence and the displayed exceptional-edge criterion follow. Zero cutoffs, coincident data and empty lists are included.

**Theorem 1.5 (Reconstruction from the finite data).**

$$\forall N \in \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall E \in \operatorname{Nat}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \operatorname{Prop}\left(\right)\right),\; \forall F \in \operatorname{Nat}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \operatorname{Prop}\left(\right)\right),\; \forall g \in \operatorname{Fin}\left(M\right) \to \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; ((((((((((\operatorname{Rules}\left(E\right)) \land (\operatorname{Rules}\left(F\right))) \land (\forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; (E(a, b)) \Rightarrow (b \le N))) \land (\forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; (F(a, b)) \Rightarrow (b \le N))) \land (\forall a \in \operatorname{Nat}\left(\right),\; ((0 < a) \land (a \le N)) \Rightarrow ((\exists r \in \operatorname{Fin}\left(M\right),\; \operatorname{g}\left(r\right) = a) \lor (\exists j \in \operatorname{Fin}\left(i\right),\; \operatorname{s}\left(j\right) = a)))) \land (\forall r \in \operatorname{Fin}\left(M\right),\; \operatorname{E}\left(0, \operatorname{g}\left(r\right)\right))) \land (\forall a \in \operatorname{Nat}\left(\right),\; (\operatorname{E}\left(0, a\right)) \Leftrightarrow (\operatorname{F}\left(0, a\right)))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{Cutoff}\left(E, g, \operatorname{s}\left(j\right), \operatorname{c}\left(j\right)\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{Cutoff}\left(F, g, \operatorname{s}\left(j\right), \operatorname{c}\left(j\right)\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; (\operatorname{E}\left(\operatorname{s}\left(j\right), \operatorname{s}\left(k\right)\right)) \Leftrightarrow (\operatorname{F}\left(\operatorname{s}\left(j\right), \operatorname{s}\left(k\right)\right)))) \Rightarrow (E = F)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.edges_determined_by_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Suppose the ordinary and exceptional lists together cover every positive vertex up to N. Two bounded graphs satisfying the rules agree if their anchor edges, their incidence cutoffs and all exceptional-edge bits agree. Ordinary-to-ordinary edges are forced by the anchor edges. The mixed pairs are determined by the cutoffs. The remaining pairs are exactly the exceptional bits. This is an equality of labelled relations, without an isomorphism quotient.

**Theorem 1.6 (Unique generic completion).**

$$\forall N \in \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall g \in \operatorname{Fin}\left(M\right) \to \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; ((((((((\operatorname{StrictMono}\left(g\right)) \land (\forall r \in \operatorname{Fin}\left(M\right),\; (0 < \operatorname{g}\left(r\right)) \land (\operatorname{g}\left(r\right) \le N))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; (((0 < \operatorname{s}\left(j\right)) \land (\operatorname{s}\left(j\right) \le N)) \land (\operatorname{Position}\left(g, \operatorname{s}\left(j\right), \operatorname{p}\left(j\right)\right))) \land (\operatorname{c}\left(j\right) \le M))) \land (\operatorname{StrictMono}\left(s\right))) \land (\operatorname{StrictMono}\left(p\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; 0 < \operatorname{p}\left(j\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \forall k \in \operatorname{Fin}\left(i\right),\; \neg (\operatorname{c}\left(j\right) = \operatorname{p}\left(k\right)))) \land (\forall a \in \operatorname{Nat}\left(\right),\; ((0 < a) \land (a \le N)) \Rightarrow ((\exists r \in \operatorname{Fin}\left(M\right),\; \operatorname{g}\left(r\right) = a) \lor (\exists j \in \operatorname{Fin}\left(i\right),\; \operatorname{s}\left(j\right) = a)))) \Rightarrow (\exists E \in \operatorname{Nat}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \operatorname{Prop}\left(\right)\right),\; ((((\operatorname{Rules}\left(E\right)) \land (\forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; (E(a, b)) \Rightarrow (b \le N))) \land (\forall a \in \operatorname{Nat}\left(\right),\; (E(0, a)) \Leftrightarrow (\exists r \in \operatorname{Fin}\left(M\right),\; \operatorname{g}\left(r\right) = a))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{Cutoff}\left(E, g, \operatorname{s}\left(j\right), \operatorname{c}\left(j\right)\right))) \land (\forall F \in \operatorname{Nat}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \operatorname{Prop}\left(\right)\right),\; ((((\operatorname{Rules}\left(F\right)) \land (\forall a \in \operatorname{Nat}\left(\right),\; \forall b \in \operatorname{Nat}\left(\right),\; (F(a, b)) \Rightarrow (b \le N))) \land (\forall a \in \operatorname{Nat}\left(\right),\; (F(0, a)) \Leftrightarrow (\exists r \in \operatorname{Fin}\left(M\right),\; \operatorname{g}\left(r\right) = a))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{Cutoff}\left(F, g, \operatorname{s}\left(j\right), \operatorname{c}\left(j\right)\right))) \Rightarrow (F = E)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.exists_unique_generic_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Assume both vertex lists increase, the positive positions strictly increase, and no cutoff equals any position. Every fully specified coordinate datum then has exactly one bounded graph satisfying the rules and the prescribed anchor edges and cutoffs. Existence uses the integer threshold construction; the forced-edge criterion and reconstruction give uniqueness. This does not count the coordinate data or prove the binomial counting identity.

**Theorem 1.7 (Positions reconstruct the labels).**

$$\forall N \in \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall g \in \operatorname{Fin}\left(M\right) \to \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \forall p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; (((((\operatorname{Injective}\left(g\right)) \land (\operatorname{StrictMono}\left(s\right))) \land (\forall r \in \operatorname{Fin}\left(M\right),\; 0 < \operatorname{g}\left(r\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; ((0 < \operatorname{s}\left(j\right)) \land (\operatorname{s}\left(j\right) \le N)) \land (\operatorname{Position}\left(g, \operatorname{s}\left(j\right), \operatorname{p}\left(j\right)\right)))) \land (\forall a \in \operatorname{Nat}\left(\right),\; ((0 < a) \land (a \le N)) \Rightarrow ((\exists r \in \operatorname{Fin}\left(M\right),\; \operatorname{g}\left(r\right) = a) \lor (\exists j \in \operatorname{Fin}\left(i\right),\; \operatorname{s}\left(j\right) = a)))) \Rightarrow (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{s}\left(j\right) = \operatorname{p}\left(j\right) + \operatorname{val}\left(j\right) + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.exceptional_label_eq_position_add_index` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Let the injective ordinary list and increasing exceptional list cover all positive vertices up to N, and let p record ordinary positions. The vertices below the j-th exception split into zero, p(j) ordinary vertices and j preceding exceptions. Taking finite cardinalities gives s(j)=p(j)+j+1. The two prefix images are disjoint by the position conditions. The formula includes p(j)=0, adjacent exceptions and an empty ordinary list.

**Theorem 1.8 (Extraction of positions and cutoffs).**

$$\forall N \in \operatorname{Nat}\left(\right),\; \forall M \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall E \in \operatorname{Nat}\left(\right) \to \left(\operatorname{Nat}\left(\right) \to \operatorname{Prop}\left(\right)\right),\; \forall g \in \operatorname{Fin}\left(M\right) \to \operatorname{Nat}\left(\right),\; \forall s \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; ((((((\operatorname{Rules}\left(E\right)) \land (\operatorname{StrictMono}\left(g\right))) \land (\operatorname{StrictMono}\left(s\right))) \land (\forall r \in \operatorname{Fin}\left(M\right),\; \operatorname{E}\left(0, \operatorname{g}\left(r\right)\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; ((\neg (\operatorname{E}\left(0, \operatorname{s}\left(j\right)\right))) \land (0 < \operatorname{s}\left(j\right))) \land (\operatorname{s}\left(j\right) \le N))) \land (\forall a \in \operatorname{Nat}\left(\right),\; ((0 < a) \land (a \le N)) \Rightarrow ((\exists r \in \operatorname{Fin}\left(M\right),\; \operatorname{g}\left(r\right) = a) \lor (\exists j \in \operatorname{Fin}\left(i\right),\; \operatorname{s}\left(j\right) = a)))) \Rightarrow (\exists p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \exists c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; (((\operatorname{Monotone}\left(p\right)) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{Position}\left(g, \operatorname{s}\left(j\right), \operatorname{p}\left(j\right)\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{Cutoff}\left(E, g, \operatorname{s}\left(j\right), \operatorname{c}\left(j\right)\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{s}\left(j\right) = \operatorname{p}\left(j\right) + \operatorname{val}\left(j\right) + 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.exists_coordinate_encoding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

Given an increasing list of anchor neighbors and an increasing list of missing anchor neighbors covering the positive vertices, every graph satisfying the rules yields a monotone position list and one cutoff for each exception. Prefix cardinality supplies each position; monotonicity follows because an ordinary vertex cannot lie before an earlier exception and after a later one. The cutoff theorem supplies the incidence data, and prefix partitioning reconstructs the original natural labels. This extracts the coordinates but does not yet identify their compression classes or enumerate them.

**Theorem 1.9 (Coordinates of the literal finite family).**

$$\forall n \in \operatorname{Nat}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall A \in \operatorname{Finset}\left(\operatorname{Prod}\left(\operatorname{Nat}\left(\right), \operatorname{Nat}\left(\right)\right)\right),\; ((i \le n + 1) \land (A \in \operatorname{edgeFamily}\left(n, n + 1 - i\right))) \Rightarrow (\exists g \in \operatorname{Fin}\left(n + 1 - i\right) \to \operatorname{Nat}\left(\right),\; \exists s \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \exists p \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; \exists c \in \operatorname{Fin}\left(i\right) \to \operatorname{Nat}\left(\right),\; ((((((((\operatorname{StrictMono}\left(g\right)) \land (\operatorname{StrictMono}\left(s\right))) \land (\operatorname{Monotone}\left(p\right))) \land (\forall a \in \operatorname{Nat}\left(\right),\; ((0, a) \in A) \Leftrightarrow (\exists r \in \operatorname{Fin}\left(n + 1 - i\right),\; \operatorname{g}\left(r\right) = a))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; ((\neg ((0, \operatorname{s}\left(j\right)) \in A)) \land (0 < \operatorname{s}\left(j\right))) \land (\operatorname{s}\left(j\right) \le n + 1))) \land (\forall a \in \operatorname{Nat}\left(\right),\; ((0 < a) \land (a \le n + 1)) \Rightarrow ((\exists r \in \operatorname{Fin}\left(n + 1 - i\right),\; \operatorname{g}\left(r\right) = a) \lor (\exists j \in \operatorname{Fin}\left(i\right),\; \operatorname{s}\left(j\right) = a)))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{Position}\left(g, \operatorname{s}\left(j\right), \operatorname{p}\left(j\right)\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{Cutoff}\left(\operatorname{pairMembership}\left(A\right), g, \operatorname{s}\left(j\right), \operatorname{c}\left(j\right)\right))) \land (\forall j \in \operatorname{Fin}\left(i\right),\; \operatorname{s}\left(j\right) = \operatorname{p}\left(j\right) + \operatorname{val}\left(j\right) + 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.edgeFamily_has_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Volodymyr Mazorchuk, Shuoyang Xu (2026). *On the number of cokernel-closed additive subcategories for uniformly oriented A_n quivers*. DOI: [10.48550/arXiv.2610.07999](https://doi.org/10.48550/arXiv.2610.07999). URL: <https://arxiv.org/html/2610.07999v2>.

*Commentary.*

For every natural n and every deficit i at most n+1, a member of edgeFamily with n+1-i anchor edges has an increasing ordinary list of length n+1-i and an increasing exceptional list of length i. Sort the actual anchor-neighbor set and its complement in one through n+1. Their cardinalities give the two list lengths. The lists cover the entire positive vertex interval; position and cutoff extraction then gives all the displayed coordinates and exact exceptional labels. The notation pairMembership(A)(a,b) means (a,b) belongs to A. The point-to-edge counted equivalence identifies this with the literal source family. This supplies extraction for every valid source parameter, including i=n+1; a two-way compressed-pattern bijection and its cardinality are still needed.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.Cutoff`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.Position`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.edgeFamily_has_coordinates`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.edges_determined_by_data`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.exceptional_label_eq_position_add_index`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.exists_coordinate_encoding`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.exists_cutoff_completion`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.exists_unique_generic_completion`
- Truth anchor: `D5/S3/Combinatorics/BinomialBases/MazorchukXuGeneric.generic_exceptional_edge`
- Dependency: [D5/S3/Combinatorics/BinomialBases/MazorchukXuFamilies](MazorchukXuFamilies.md)
- Dependency: [D5/S3/Combinatorics/BinomialBases/MazorchukXuOrder](MazorchukXuOrder.md)
