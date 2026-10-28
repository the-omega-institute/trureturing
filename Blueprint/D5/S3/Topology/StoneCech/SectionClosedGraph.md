# A closed graph on a countably compact principal extension

## Abstract

The actual principal extension of a section-dense selector carries a closed fibre graph with finite cliques of every size.

For arbitrary types A and B in Type and q : A -> B, put X=principalExtension(Y)=range(pure : A -> Ultrafilter A) union Y, with the topology inherited as a subspace of Ultrafilter A. This is an actual vertex subspace, hence Hausdorff by the inherited T2 instance. The principalEmbedding sends a to pure(a) regarded as a vertex of X and is injective. fibreGraph(q,Y) relates x and y precisely when there are distinct a,b in A with x.val=pure(a), y.val=pure(b), and q(a)=q(b). It is symmetric and irreflexive by construction. Its adjacency is principal-only; when Y is section-good, its vertices are free and receive no edges.

Formula notation is shared across the four statements: fibre(q,b) is q-inverse({b}); map(q) is Ultrafilter.map q; SectionGood(q) means free and containing an actual injectivity set of q; Card is Cardinal.mk and c is the continuum. AdjSet(q,Y) is exactly {p : X times X | (fibreGraph q Y).Adj p.1 p.2}, a subset of the entire product X squared. IsClique is SimpleGraph.IsClique, Finite and Infinite are the set predicates, and ncard is Set.ncard. IsCountablyCompact is the ambient set predicate, whereas CountablyCompactSpace is the native typeclass on the indicated subspace. None of these statements asserts sequential compactness.

**Theorem 1.1 (Closedness in the entire product, including the diagonal).**

$$\forall A: Type, \forall B: Type, \forall q: A \to B, \forall Y: \operatorname{Set}\left(\operatorname{Ultrafilter}\left(A\right)\right), {{Y \subseteq \operatorname{SectionGood}\left(q\right)} \land {\operatorname{InjOn}\left(\operatorname{map}\left(q\right), Y\right)}} \Rightarrow {\operatorname{IsClosed}\left(\operatorname{AdjSet}\left(q, Y\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/SectionClosedGraph.isClosed_fibreGraph_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

The only hypotheses are Y contained in SectionGood(q) and injectivity of Ultrafilter.map q on Y. No countability, finite fibres, density or countable compactness is needed. The proof constructs an open nonedge rectangle around every nonadjacent ordered pair, including every diagonal pair. Basic neighborhoods are {x : X | S in x.val}, the restrictions of ambient membership clopens.

For two principal points use their singleton basic neighborhoods; nonadjacency excludes the only possible edge in that rectangle. For a mixed principal/selector pair, use the principal singleton and the complement of its whole q-fibre at the selector point. That complement belongs to every section-good ultrafilter: its section witness meets the fibre in at most one point, and freeness rules out that finite intersection. The reversed mixed case is handled symmetrically.

For equal selector values choose an actual section S in that ultrafilter and use its basic neighborhood squared. Two distinct principal points in S cannot share a q-value, so this square is edge-free. This is the necessary diagonal argument. For unequal selector values, projection injectivity makes their projected ultrafilters distinct. Choose T contained in B with T in one projection and its complement in the other. The basic neighborhoods of q-inverse(T) and q-inverse(complement T) form an edge-free rectangle. Thus the source addresses full-product closedness rather than only closedness away from the diagonal.

**Theorem 1.2 (Countable compactness from finite fibres and section density).**

$$\forall A: Type, \forall B: Type, \forall q: A \to B, \forall Y: \operatorname{Set}\left(\operatorname{Ultrafilter}\left(A\right)\right), {{Y \subseteq \operatorname{SectionGood}\left(q\right)} \land {\operatorname{IsCountablyCompact}\left(Y\right)} \land {\forall S: \operatorname{Set}\left(A\right), {{\operatorname{Infinite}\left(S\right)} \land {\operatorname{InjOn}\left(q, S\right)}} \Rightarrow {\exists u: \operatorname{Ultrafilter}\left(A\right), {u \in Y} \land {S \in u}}} \land {\forall b: B, \operatorname{Finite}\left(\operatorname{fibre}\left(q, b\right)\right)}} \Rightarrow {\operatorname{IsCountablyCompact}\left(\operatorname{principalExtension}\left(Y\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/SectionClosedGraph.isCountablyCompact_principalExtension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Commentary.*

Assume Y is section-good and countably compact, every infinite injectivity set S of q belongs to some u in Y, and every q-fibre is finite. Then the actual principal extension is countably compact as a subset of Ultrafilter A. This theorem does not assume a countable A or B, a bound on Card(Y), or projection injectivity.

For an infinite subset C of the extension, if C intersect Y is infinite, countable compactness of Y supplies its AccPt in Y. Otherwise C has infinitely many principal points. Let P be their preimage in A. Finite fibres force q(P) to be infinite, since the preimage of a finite image would be a finite union of finite fibres. Choose a subset S of P on which q is injective with q(S)=q(P); it is infinite. Section density gives u in Y containing S. Principal ultrafilters converge to u along u itself; freeness makes u different from every principal point, giving a genuine punctured AccPt of pure(S), hence of C. The native T1 infinite-subset characterization gives IsCountablyCompact, without producing a convergent subsequence.

**Theorem 1.3 (Every clique is finite).**

$$\forall A: Type, \forall B: Type, \forall q: A \to B, \forall Y: \operatorname{Set}\left(\operatorname{Ultrafilter}\left(A\right)\right), \forall K: \operatorname{Set}\left(\operatorname{principalExtension}\left(Y\right)\right), {{\forall b: B, \operatorname{Finite}\left(\operatorname{fibre}\left(q, b\right)\right)} \land {\operatorname{IsClique}\left(\operatorname{fibreGraph}\left(q, Y\right), K\right)}} \Rightarrow {\operatorname{Finite}\left(K\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/SectionClosedGraph.fibreGraph_clique_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary Y, finite q-fibres alone imply that every clique K of fibreGraph(q,Y) is finite. An empty clique is finite. A singleton clique is finite even when its sole vertex is a selector point; the proof handles both through the subsingleton case. Otherwise choose two distinct members. Their edge makes the first a principal point pure(a). Every other member is either that vertex or is adjacent to it, hence principal and in the same q-fibre. Thus the whole clique lies in the image under principalEmbedding of the finite fibre over q(a). No goodness, projection injectivity, topology or countability assumption on Y is used.

**Theorem 1.4 (Constructing the selector, space and finite unbounded cliques).**

$$\forall A: Type, \forall B: Type, \forall q: A \to B, {{\operatorname{Countable}\left(A\right)} \land {\forall b: B, \operatorname{Finite}\left(\operatorname{fibre}\left(q, b\right)\right)} \land {\forall n: Nat, \exists b: B, n \le \operatorname{ncard}\left(\operatorname{fibre}\left(q, b\right)\right)}} \Rightarrow {\exists Y: \operatorname{Set}\left(\operatorname{Ultrafilter}\left(A\right)\right), {Y \subseteq \operatorname{SectionGood}\left(q\right)} \land {\operatorname{Card}\left(Y\right) \le c} \land {\operatorname{InjOn}\left(\operatorname{map}\left(q\right), Y\right)} \land {\operatorname{IsCountablyCompact}\left(Y\right)} \land {\forall S: \operatorname{Set}\left(A\right), {{\operatorname{Infinite}\left(S\right)} \land {\operatorname{InjOn}\left(q, S\right)}} \Rightarrow {\exists u: \operatorname{Ultrafilter}\left(A\right), {u \in Y} \land {S \in u}}} \land {\operatorname{CountablyCompactSpace}\left(\operatorname{principalExtension}\left(Y\right)\right)} \land {\operatorname{IsClosed}\left(\operatorname{AdjSet}\left(q, Y\right)\right)} \land {\forall K: \operatorname{Set}\left(\operatorname{principalExtension}\left(Y\right)\right), {\operatorname{IsClique}\left(\operatorname{fibreGraph}\left(q, Y\right), K\right)} \Rightarrow {\operatorname{Finite}\left(K\right)}} \land {\forall n: Nat, \exists K: \operatorname{Set}\left(\operatorname{principalExtension}\left(Y\right)\right), {\operatorname{Finite}\left(K\right)} \land {\operatorname{IsClique}\left(\operatorname{fibreGraph}\left(q, Y\right), K\right)} \land {\operatorname{ncard}\left(K\right) = n}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StoneCech/SectionClosedGraph.exists_countablyCompact_closed_fibreGraph` (`✓ std3`). ∎

*Resolves.* `Problems/feldman-wilce-countably-compact-unbounded-cliques` (proved) by `D5/S3/Topology/StoneCech/SectionClosedGraph.exists_countablyCompact_closed_fibreGraph`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"feldman-wilce-countably-compact-unbounded-cliques","declaration_gid":"D5/S3/Topology/StoneCech/SectionClosedGraph.exists_countablyCompact_closed_fibreGraph","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* David V. Feldman and Alexander Wilce (2026). *A Note on Compactness and Clique Size*. DOI: [10.48550/arXiv.2608.13320](https://doi.org/10.48550/arXiv.2608.13320). URL: <https://arxiv.org/abs/2608.13320>.

*Acknowledgement.* Zdeněk Frolík (1960). *The topological product of countably compact spaces*. DOI: [10.21136/cmj.1960.100417](https://doi.org/10.21136/cmj.1960.100417). URL: <https://dml.cz/handle/10338.dmlcz/100417>.

*Acknowledgement.* John Ginsburg and Victor Saks (1975). *Some applications of ultrafilters in topology*. DOI: [10.2140/pjm.1975.57.403](https://doi.org/10.2140/pjm.1975.57.403). URL: <https://doi.org/10.2140/pjm.1975.57.403>.

*Commentary.*

Assume Countable A, all q-fibres finite, and for every natural n a fibre with n <= its ncard. There is no assumed selector or section-dense seed. The conclusion constructs Y contained in SectionGood(q), of cardinal at most c, with projection injective on Y, Y countably compact and section-dense; its principal extension has CountablyCompactSpace, its fibre adjacency is closed in all X squared, every clique is finite, and for every n there is a finite clique K with K.ncard=n. Hausdorffness is inherited from Ultrafilter A, not an extra conclusion field or a supplied hypothesis in this theorem.

The proof consumes SectionDenseSelector.exists_countablyCompact_sectionDense_selector q to obtain the actual Y. The preceding principal-extension and closedness theorems then supply the two native topological properties, and the clique theorem supplies finiteness. For exact size n choose a fibre with n <= its ncard, take a subset T of that fibre of exactly n elements, and map T through principalEmbedding. Distinct images are adjacent and injectivity preserves ncard. This includes n=0 with the empty clique, n=1, and every larger prescribed size; there is no uniform finite bound.

The primary paper's Question 1, printed page 5, asks for a countably compact T1 or Hausdorff space carrying a closed orthogonality relation with finite yet unbounded cliques. Its page 3 requires closure in X squared, including the diagonal. Page 10 partitions a countable discrete set into finite blocks of size n, calls sets meeting each block at most once partial sections, and proposes X=omega union Y for a dense countably compact Y of free ultrafilters containing partial sections. The paper uses the restriction of the ambient closure of the block relation. Here q labels the blocks and its injectivity sets are precisely partial sections; the additional projection-injectivity condition on Y excludes off-principal edges and allows the principal-only fibre relation itself to be closed. For finite fibres, every infinite set has an infinite partial section, so section density meets every nonempty basic clopen in the free remainder. This explains the correspondence of the constructions without treating the paper's conditional existence of Y as an established supplier.

The exact finite-block parameter map is A = Sigma (fun n : Nat => Fin (n+1)), B=Nat, q=Sigma.fst. The countable sigma of finite types is countable. For each b, q-inverse({b}) equals range(Sigma.mk b): a point in the fibre has first coordinate b, and every Sigma.mk b i lies in it. This range is finite. Injectivity of Sigma.mk b and Set.ncard_range_of_injective identify its ncard with Nat.card(Fin(b+1)); Nat.card_fin gives exactly b+1. For requested n take b=n and use n <= n+1. The endpoint supplies Y and fibreGraph, while T2Space(principalExtension Y) is inherited by the subspace instance. These blocks of sizes 1,2,... merely reindex the nonempty blocks of the paper's size-n partition. For any proposed natural bound N, take the supplied clique K of size N+1. Its finiteness and K.ncard=N+1 contradict K.ncard <= N. Thus this actual X is countably compact, Hausdorff and T1, and its symmetric irreflexive relation is closed in the entire product, has every clique finite and has no uniform finite clique bound. These are exactly the clauses of Question 1. The parameter discharge and the explicit no-bound inference passed a transient exact Lean application through the canonical targeted build and scoped statement/axiom report. Its axiom closure contains only Classical.choice, Quot.sound and propext; the existing generic module completed canonical FirstFreeze. This is an application of the existing theorem; it introduces no retained named application theorem or separate Describe.

The classical method sources have narrower statements: Frolik's Lemma 2.8 requires no accumulation point in the separable metrizable base P, and Lemma 2.9 gives avoidance and omega1 closing-off; Ginsburg-Saks Theorem 2.12 concerns one fixed free-ultrafilter D and completely regular spaces. They are not sources for the exact arbitrary-q selector or this endpoint. The canonical notes distinguish these methods from repository-derived proof composition. The countable finite-block application supplies an affirmative mathematical answer to Question 1; it neither attributes this exact selector construction to the method papers nor addresses Questions 2 and 3. The primary-source status and source-fidelity boundaries are recorded in the Library note and Problems dossier. Open status in the inspected sources does not establish worldwide absence, publication priority or official acceptance.

## References

- Truth anchor: `D5/S3/Topology/StoneCech/SectionClosedGraph.exists_countablyCompact_closed_fibreGraph`
- Truth anchor: `D5/S3/Topology/StoneCech/SectionClosedGraph.fibreGraph_clique_finite`
- Truth anchor: `D5/S3/Topology/StoneCech/SectionClosedGraph.isClosed_fibreGraph_adj`
- Truth anchor: `D5/S3/Topology/StoneCech/SectionClosedGraph.isCountablyCompact_principalExtension`
- Dependency: [D5/S3/Topology/StoneCech/SectionDenseSelector](SectionDenseSelector.md)
