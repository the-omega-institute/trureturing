# Real-root configurations of book domination polynomials

## Abstract

The literal arXiv v1/v2 all-positive-order book domination-root conjecture fails at the four-cycle.

The source is Conjecture 5.4 in arXiv v1/v2, with the shared-edge four-cycle books of Section 2 for every natural n at least one. Root locations lie on the Euclidean real line, and multiplicities count repeated points. The graph and ordinary dominating-set count are retained in full.

**Definition 1.1 (Directed page edges).**

$$\forall (n : \mathrm{Nat}), \forall (u : \operatorname{Fin}\left((2 \cdot n + 2)\right)), \forall (v : \operatorname{Fin}\left((2 \cdot n + 2)\right)), \operatorname{pageForward}\left(n, u, v\right) = (((\operatorname{Fin.val}\left(u\right) = 0) \land (\operatorname{Fin.val}\left(v\right) = 1)) \lor (\exists (i : \operatorname{Fin}\left(n\right)), ((\operatorname{Fin.val}\left(u\right) = 1) \land (\operatorname{Fin.val}\left(v\right) = 2 \cdot \operatorname{Fin.val}\left(i\right) + 2)) \lor (((\operatorname{Fin.val}\left(u\right) = 2 \cdot \operatorname{Fin.val}\left(i\right) + 2) \land (\operatorname{Fin.val}\left(v\right) = 2 \cdot \operatorname{Fin.val}\left(i\right) + 3)) \lor ((\operatorname{Fin.val}\left(u\right) = 2 \cdot \operatorname{Fin.val}\left(i\right) + 3) \land (\operatorname{Fin.val}\left(v\right) = 0)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.pageForward` (`✓ std3`).

*Citation.* Bilal Ahmad Rather (2026). *On roots of domination polynomials for friendship and book graphs*. URL: <https://arxiv.org/abs/2604.08998v2>.

*Commentary.*

Section 2, printed page 3 and Figure 1(b): n copies of C4 have one common edge and otherwise disjoint vertices. The vertices are Fin (2*n+2); the displayed Fin.val maps explicitly take each vertex or page index to Nat. The shared edge is 0--1, and page i continues 1--(2*i.val+2)--(2*i.val+3)--0. These are all the forward edges.

**Definition 1.2 (Deciding a directed page edge).**

$$\forall (n : \mathrm{Nat}), \forall (u : \operatorname{Fin}\left((2 \cdot n + 2)\right)), \forall (v : \operatorname{Fin}\left((2 \cdot n + 2)\right)), (\operatorname{instDecidablePageForward}\left(n, u, v\right) : \operatorname{Decidable}\left((\operatorname{pageForward}\left(n, u, v\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.instDecidablePageForward` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bilal Ahmad Rather (2026). *On roots of domination polynomials for friendship and book graphs*. URL: <https://arxiv.org/abs/2604.08998v2>.

*Commentary.*

The instance unfolds pageForward and uses infer_instance: natural equalities, conjunctions and disjunctions are decidable, and the existential page index ranges over Fin n. This supplies the decisions used by the adjacency instance and the finite comparison with cycleGraph 4.

**Definition 1.3 (The undirected loopless book).**

$$\forall (n : \mathrm{Nat}), \operatorname{SimpleGraph.Adj}\left((\operatorname{bookGraph}\left(n\right) : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left((2 \cdot n + 2)\right)\right))\right) = (\lambda (u : \operatorname{Fin}\left((2 \cdot n + 2)\right)) \mapsto \lambda (v : \operatorname{Fin}\left((2 \cdot n + 2)\right)) \mapsto (\operatorname{pageForward}\left(n, u, v\right)) \lor (\operatorname{pageForward}\left(n, v, u\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.bookGraph` (`✓ std3`).

*Citation.* Bilal Ahmad Rather (2026). *On roots of domination polynomials for friendship and book graphs*. URL: <https://arxiv.org/abs/2604.08998v2>.

*Commentary.*

Section 2 defines the simple undirected shared-edge book. The defining Adj field is exactly the displayed symmetrization. The symm field is the proof fun u v h => h.symm, packaged as Std.Symm. The loopless field has type Std.Irrefl for this adjacency. For loopless, both disjuncts reduce to pageForward n v v: the shared-edge equalities force 0=1; each page alternative forces either 1=2*i.val+2, consecutive naturals equal, or 2*i.val+3=0. The source proves all cases with omega and combines the two exclusions by h.elim. Thus the structure has no loops and no additional edges.

**Definition 1.4 (Deciding book adjacency).**

$$\forall (n : \mathrm{Nat}), \forall (u : \operatorname{Fin}\left((2 \cdot n + 2)\right)), \forall (v : \operatorname{Fin}\left((2 \cdot n + 2)\right)), (\operatorname{instDecidableRelFinHAddNatHMulOfNatAdjBookGraph}\left(n\right) : \operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(\operatorname{bookGraph}\left(n\right)\right)\right))\left(u, v\right) = \operatorname{inferInstanceAs}\left((\operatorname{Decidable}\left(((\operatorname{pageForward}\left(n, u, v\right)) \lor (\operatorname{pageForward}\left(n, v, u\right)))\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.instDecidableRelFinHAddNatHMulOfNatAdjBookGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Bilal Ahmad Rather (2026). *On roots of domination polynomials for friendship and book graphs*. URL: <https://arxiv.org/abs/2604.08998v2>.

*Commentary.*

The defining method is fun u v => inferInstanceAs (Decidable (pageForward n u v or pageForward n v u)). The two previously defined directed-edge decisions supply the decidable disjunction. This is a decision procedure for precisely the displayed adjacency relation.

**Definition 1.5 (Ordinary domination polynomial).**

$$\forall (V : Type), \forall (instF : \operatorname{Fintype}\left(V\right)), \forall (instD : \operatorname{DecidableEq}\left(V\right)), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \operatorname{dominationPolynomial}\left(V, instF, instD, G\right) = \sum_{S \in \operatorname{DominatingSetAverage.domSets}\left(V, instF, G\right)} ((\operatorname{Polynomial.X} : \operatorname{Polynomial}\left(\mathrm{Real}\right)))^{\operatorname{Finset.card}\left(S\right)}$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.dominationPolynomial` (`✓ std3`).

*Citation.* Bilal Ahmad Rather (2026). *On roots of domination polynomials for friendship and book graphs*. URL: <https://arxiv.org/abs/2604.08998v2>.

*Commentary.*

The source definition of D(G,x) counts ordinary dominating subsets once, by their cardinality. Here instF and instD name the Fintype and DecidableEq arguments; applications display these normally implicit arguments explicitly in their Lean order. The sum uses the existing DominatingSetAverage.domSets, whose membership theorem is mem_domSets and whose predicate is the existing SimpleGraph.IsDominating: every vertex belongs to S or has a neighbor in S. Coefficients are real and Polynomial.X has type Polynomial Real. No count is assumed.

**Definition 1.6 (Exact multiplicities and exhaustive roots).**

$$\forall (p : \operatorname{Polynomial}\left(\mathrm{Real}\right)), \forall (a : \mathrm{Real}), \forall (b : \mathrm{Real}), \operatorname{FourRealRoots}\left(p, a, b\right) = ((a \ne 0) \land ((b \ne 0) \land ((a \ne b) \land ((\operatorname{Polynomial.IsRoot}\left(p, 0\right)) \land ((\operatorname{Polynomial.IsRoot}\left(p, a\right)) \land ((\operatorname{Polynomial.IsRoot}\left(p, b\right)) \land ((\operatorname{Polynomial.rootMultiplicity}\left(0, p\right) = 2) \land ((\operatorname{Polynomial.rootMultiplicity}\left(a, p\right) = 1) \land ((\operatorname{Polynomial.rootMultiplicity}\left(b, p\right) = 1) \land (\forall (r : \mathrm{Real}), \operatorname{Polynomial.IsRoot}\left(p, r\right) \Leftrightarrow ((r = 0) \lor ((r = a) \lor (r = b)))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.FourRealRoots` (`✓ std3`).

*Citation.* Bilal Ahmad Rather (2026). *On roots of domination polynomials for friendship and book graphs*. URL: <https://arxiv.org/abs/2604.08998v2>.

*Commentary.*

Conjecture 5.4, printed page 12: exactly four real roots counting multiplicity means a double zero and two distinct simple nonzero roots. Polynomial.IsRoot and Polynomial.rootMultiplicity are the actual polynomial predicates. The final equivalence ranges over every real r and excludes any further real root.

**Definition 1.7 (The complete arXiv conjecture).**

$$(claim : Prop) = (\forall (n : \mathrm{Nat}), (1 \le n) \Rightarrow (((\operatorname{Even}\left(n\right)) \Rightarrow (\exists (a : \mathrm{Real}), \exists (b : \mathrm{Real}), (a < -2) \land ((-\frac{(1 : \mathrm{Real})}{(2 : \mathrm{Real})} < b) \land ((b < 0) \land (\operatorname{FourRealRoots}\left(\operatorname{dominationPolynomial}\left(\operatorname{bookGraph}\left(n\right)\right), a, b\right)))))) \land ((\operatorname{Odd}\left(n\right)) \Rightarrow (\exists (a : \mathrm{Real}), \exists (b : \mathrm{Real}), (-\frac{(1 : \mathrm{Real})}{(2 : \mathrm{Real})} < a) \land ((a < 0) \land ((-\frac{(1 : \mathrm{Real})}{(2 : \mathrm{Real})} < b) \land ((b < 0) \land (\operatorname{FourRealRoots}\left(\operatorname{dominationPolynomial}\left(\operatorname{bookGraph}\left(n\right)\right), a, b\right)))))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.claim` (`✓ std3`).

*Citation.* Bilal Ahmad Rather (2026). *On roots of domination polynomials for friendship and book graphs*. URL: <https://arxiv.org/abs/2604.08998v2>.

*Commentary.*

Conjecture 5.4 retains every n at least one and both parity implications. For even n the simple roots lie below -2 and between -1/2 and zero. For odd n both lie between -1/2 and zero. FourRealRoots includes all exact multiplicities and the root equivalence for every real number. The rational endpoint is negative one divided by two in Real.

**Theorem 1.8 (The order-one book contradicts the universal conjecture).**

$$\neg (\forall (n : \mathrm{Nat}), (1 \le n) \Rightarrow (((\operatorname{Even}\left(n\right)) \Rightarrow (\exists (a : \mathrm{Real}), \exists (b : \mathrm{Real}), (a < -2) \land ((-\frac{(1 : \mathrm{Real})}{(2 : \mathrm{Real})} < b) \land ((b < 0) \land (\operatorname{FourRealRoots}\left(\operatorname{dominationPolynomial}\left(\operatorname{bookGraph}\left(n\right)\right), a, b\right)))))) \land ((\operatorname{Odd}\left(n\right)) \Rightarrow (\exists (a : \mathrm{Real}), \exists (b : \mathrm{Real}), (-\frac{(1 : \mathrm{Real})}{(2 : \mathrm{Real})} < a) \land ((a < 0) \land ((-\frac{(1 : \mathrm{Real})}{(2 : \mathrm{Real})} < b) \land ((b < 0) \land (\operatorname{FourRealRoots}\left(\operatorname{dominationPolynomial}\left(\operatorname{bookGraph}\left(n\right)\right), a, b\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bilal Ahmad Rather (2026). *On roots of domination polynomials for friendship and book graphs*. URL: <https://arxiv.org/abs/2604.08998v2>.

*Commentary.*

The order-one book equals SimpleGraph.cycleGraph 4. Exactly its six two-element subsets, four three-element subsets and full vertex set dominate; the empty set and four singletons do not. The finite comparison and enumeration are checked by kernel decision, using mem_domSets. Summing the eleven actual subsets gives 6*X^2+4*X^3+X^4. Evaluation at a factors as a^2*((a+2)^2+2), strictly positive for every nonzero a. Instantiating the odd implication at n=1 supplies a nonzero root a, a contradiction. The private book_one_eq_cycle and cycle_domSets establish book_one_polynomial, which supplies this evaluation. The C4 count, book polynomial and positive-cofactor argument are established ingredients; no new general root theorem is asserted.

The author bibliography lists the paper as Filomat (2026), to appear. The journal text and any corrections remain unread, so agreement with a journal statement is not asserted. The relevant six-page 2013 article also remains unread; its located arXiv document contains only an abstract. The argument refutes the literal arXiv v1/v2 universal statement at n=1. The separately amended n at least two statement remains unsettled. No global literature priority or exhaustive ownership conclusion follows.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.FourRealRoots`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.bookGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.dominationPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.instDecidablePageForward`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.instDecidableRelFinHAddNatHMulOfNatAdjBookGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.pageForward`
- Truth anchor: `D5/S3/Combinatorics/Graph/Domination/RatherBookRootRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverage](../DominatingSetAverage.md)
