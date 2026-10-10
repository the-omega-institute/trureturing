# Support forests and edge-word reflection

## Abstract

Support counts and sound reflection of edge-word character moments.

**Definition 1.1 (Endpoint set).**

$$\forall (n : \mathbb{N}), \forall (S : \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), endpointSet\left(S\right) = \operatorname{Finset.biUnion}\left(S, \operatorname{Sym2.toFinset}\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.endpointSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The union of the endpoint sets of the unordered edges. Loops, if supplied as raw symmetric pairs, contribute their one endpoint.

**Definition 1.2 (Graph on the endpoints).**

$$\forall (n : \mathbb{N}), \forall (S : \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), endpointGraph\left(S\right) = \operatorname{SimpleGraph.induce}\left(\operatorname{SimpleGraph.fromEdgeSet}\left((S : \operatorname{Set}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right))\right), (endpointSet\left(S\right) : \operatorname{Set}\left(\operatorname{Fin}\left(n\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.endpointGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The graph from the supplied edge set is induced on exactly its endpoints. This induction changes the vertex carrier; it does not impose ambient inducedness.

**Definition 1.3 (Support-subgraph count).**

$$\forall (n : \mathbb{N}), \forall (h : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (H : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(h\right)\right)), N_{H}\left(G, H\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(fun (S : \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)) \mapsto \operatorname{Nonempty}\left((endpointGraph\left(S\right) \equiv_{g} H)\right), \operatorname{Finset.powerset}\left(\operatorname{SimpleGraph.edgeFinset}\left(G\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.N_H` (`✓ std3`).

*Citation.* Boris Shapiro (2026). *The (n−2,2)-Spectrum of a Graph*. URL: <https://arxiv.org/abs/2605.17501v2>.

*Commentary.*

Section 6.1, page 5: "For a finite simple graph H without isolated vertices, let N_H(G) denote the number of edge subsets S ⊆ E(G) for which the graph with edge set S and vertex set formed by the endpoints of S is isomorphic to H. No inducedness condition is imposed on the ambient graph G." Vertices are Fin n and Fin h; each edge subset is counted once, independently of how many isomorphisms it admits.

**Definition 1.4 (Fixed points).**

$$\forall (n : \mathbb{N}), \forall (sigma : \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)), c1\left(sigma\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(fun (v : \operatorname{Fin}\left(n\right)) \mapsto sigma\left(v\right) = v, (\operatorname{Finset.univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right))\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.c1` (`✓ std3`).

*Citation.* Boris Shapiro (2026). *The (n−2,2)-Spectrum of a Graph*. URL: <https://arxiv.org/abs/2605.17501v2>.

*Commentary.*

Section 6, page 4: "If σ ∈ Sₙ, let c₁(σ) be the number of fixed points of σ and let c₂(σ) be the number of two-cycles in its cycle decomposition." The encoding names these counts c1 and c2. The finite filter tests equality of the permutation value and its input.

**Definition 1.5 (Two-cycles).**

$$\forall (n : \mathbb{N}), \forall (sigma : \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)), c2\left(sigma\right) = \operatorname{Multiset.count}\left(2, \operatorname{Equiv.Perm.cycleType}\left(sigma\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.c2` (`✓ std3`).

*Citation.* Boris Shapiro (2026). *The (n−2,2)-Spectrum of a Graph*. URL: <https://arxiv.org/abs/2605.17501v2>.

*Commentary.*

Section 6, page 4: "If σ ∈ Sₙ, let c₁(σ) be the number of fixed points of σ and let c₂(σ) be the number of two-cycles in its cycle decomposition." Mathlib's cycleType omits fixed points and retains the other cycle lengths with multiplicity.

**Definition 1.6 (The character).**

$$\forall (n : \mathbb{N}), \forall (sigma : \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)), chi\left(sigma\right) = (\operatorname{Nat.choose}\left(c1\left(sigma\right), 2\right) : \mathbb{Z}) + (c2\left(sigma\right) : \mathbb{Z}) - (c1\left(sigma\right) : \mathbb{Z})$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.chi` (`✓ std3`).

*Citation.* Boris Shapiro (2026). *The (n−2,2)-Spectrum of a Graph*. URL: <https://arxiv.org/abs/2605.17501v2>.

*Commentary.*

Section 6, page 4, (6.1): chi^(n−2,2)(σ) = binom(c1(σ),2) + c2(σ) − c1(σ). Each natural count is cast to the integers; the subtraction is integer subtraction.

**Definition 1.7 (Edge transposition).**

$$\forall (n : \mathbb{N}), (edgeSwap : \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right) \to \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)) = \operatorname{Sym2.lift}\left(\langle\operatorname{Equiv.swap}, \operatorname{Equiv.swap_{comm}}\rangle\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap` (`✓ std3`).

*Citation.* Boris Shapiro (2026). *The (n−2,2)-Spectrum of a Graph*. URL: <https://arxiv.org/abs/2605.17501v2>.

*Commentary.*

Section 6, page 4: "Let τ_e = (ij) denote the transposition corresponding to an edge e = ij." Sym2.lift uses Equiv.swap_comm, so the transposition is independent of endpoint order.

**Definition 1.8 (Edge-word moment).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (r : \mathbb{N}), M_{r2}\left(G, r\right) = (\sum_{w : \operatorname{Fin}\left(r\right) \to \operatorname{SimpleGraph.edgeFinset}\left(G\right)} (chi\left(\operatorname{List.prod}\left(\operatorname{List.ofFn}\left(fun (i : \operatorname{Fin}\left(r\right)) \mapsto edgeSwap\left(\operatorname{val}\left(w\left(i\right)\right)\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.M_r2` (`✓ std3`).

*Citation.* Boris Shapiro (2026). *The (n−2,2)-Spectrum of a Graph*. URL: <https://arxiv.org/abs/2605.17501v2>.

*Commentary.*

Section 6, page 4, (6.2): M_r^(2)(G) is the sum over all edge words (e₁,…,e_r) of chi(τ_e₁⋯τ_e_r). List.ofFn lists indices in increasing order and List.prod preserves the displayed multiplication order. The definition uses this right side, as the source identifies it with the trace. The extension r = 0 is included in the evaluator; the inversion statement only uses r = 2, 3, 4.

**Definition 1.9 (No isolated vertices).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), noIsolated\left(G\right) \Leftrightarrow (\forall (v : \operatorname{Fin}\left(n\right)), \exists (w : \operatorname{Fin}\left(n\right)), \operatorname{SimpleGraph.Adj}\left(G, v, w\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.noIsolated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every vertex has an adjacent vertex; the empty vertex carrier satisfies this condition.

**Definition 1.10 (Points in two-cycles).**

$$\forall (alpha : Type), [\operatorname{Fintype}\left(alpha\right)], [\operatorname{DecidableEq}\left(alpha\right)], \forall (sigma : \operatorname{Equiv.Perm}\left(alpha\right)), twoPoints\left(sigma\right) = \operatorname{Finset.sdiff}\left(\operatorname{Equiv.Perm.support}\left(sigma\right), \operatorname{Equiv.Perm.support}\left(sigma^{2}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.twoPoints` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point lies in the support of the permutation but not in the support of its square precisely when its orbit has length two.

**Theorem 1.11 (Counting points in two-cycles).**

$$\forall (alpha : Type), [\operatorname{Fintype}\left(alpha\right)], [\operatorname{DecidableEq}\left(alpha\right)], \forall (sigma : \operatorname{Equiv.Perm}\left(alpha\right)), \operatorname{Finset.card}\left(twoPoints\left(sigma\right)\right) = 2 \cdot \operatorname{Multiset.count}\left(2, \operatorname{Equiv.Perm.cycleType}\left(sigma\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.twoPoints_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cycle induction separates a cycle of length two from every other nontrivial cycle. Disjoint products give disjoint unions of these point sets and additive cycle multiplicities.

**Theorem 1.12 (Enumerating support counts).**

$$\forall (n : \mathbb{N}), \forall (h : \mathbb{N}), \forall (r : \mathbb{N}), \forall (t : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (H : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(h\right)\right)), \forall (a : \operatorname{Fin}\left(t\right) \to \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), (\operatorname{Function.Injective}\left(a\right)) \Rightarrow ((\operatorname{Finset.image}\left(a, (\operatorname{Finset.univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(t\right)\right))\right) = \operatorname{Finset.powersetCard}\left(r, \operatorname{SimpleGraph.edgeFinset}\left(G\right)\right)) \Rightarrow ((\operatorname{Finset.card}\left(\operatorname{SimpleGraph.edgeFinset}\left(H\right)\right) = r) \Rightarrow (N_{H}\left(G, H\right) = (\sum_{i : \operatorname{Fin}\left(t\right)} (\operatorname{ite}\left(\operatorname{Nonempty}\left((endpointGraph\left(a\left(i\right)\right) \equiv_{g} H)\right), 1, 0\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.N_H_of_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective enumeration of all r-edge subsets rewrites the support count as a sum of isomorphism indicators, provided H has r edges.

**Theorem 1.13 (Matched support enumerations).**

$$\forall (n : \mathbb{N}), \forall (h : \mathbb{N}), \forall (r : \mathbb{N}), \forall (t : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (Gprime : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (H : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(h\right)\right)), \forall (a : \operatorname{Fin}\left(t\right) \to \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (b : \operatorname{Fin}\left(t\right) \to \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), (\operatorname{Function.Injective}\left(a\right)) \Rightarrow ((\operatorname{Function.Injective}\left(b\right)) \Rightarrow ((\operatorname{Finset.image}\left(a, (\operatorname{Finset.univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(t\right)\right))\right) = \operatorname{Finset.powersetCard}\left(r, \operatorname{SimpleGraph.edgeFinset}\left(G\right)\right)) \Rightarrow ((\operatorname{Finset.image}\left(b, (\operatorname{Finset.univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(t\right)\right))\right) = \operatorname{Finset.powersetCard}\left(r, \operatorname{SimpleGraph.edgeFinset}\left(Gprime\right)\right)) \Rightarrow ((\forall (i : \operatorname{Fin}\left(t\right)), endpointGraph\left(a\left(i\right)\right) \equiv_{g} endpointGraph\left(b\left(i\right)\right)) \Rightarrow ((\operatorname{Finset.card}\left(\operatorname{SimpleGraph.edgeFinset}\left(H\right)\right) = r) \Rightarrow (N_{H}\left(G, H\right) = N_{H}\left(Gprime, H\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.counts_eq_of_iso_enumerations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two injective exhaustive enumerations paired by endpoint-graph isomorphisms give equal counts for every r-edge model H.

**Definition 1.14 (Radix digit).**

$$\forall (b : \mathbb{N}), \forall (p : \mathbb{N}), \forall (i : \mathbb{N}), digit\left(b, p, i\right) = \operatorname{Nat.mod}\left(\operatorname{Nat.div}\left(p, b^{i}\right), b\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.digit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.div is integer quotient and Nat.mod is the remainder, including Lean's total conventions at base zero.

**Definition 1.15 (Packing radix digits).**

$$\forall (b : \mathbb{N}), \forall (n : \mathbb{N}), \forall (f : \mathbb{N} \to \mathbb{N}), pack\left(b, n, f\right) = \operatorname{Nat.ofDigits}\left(b, \operatorname{List.map}\left(f, \operatorname{List.range}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.pack` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nat.ofDigits reads the finite digit list in little-endian order.

**Theorem 1.16 (Decoding a bounded digit).**

$$\forall (b : \mathbb{N}), \forall (n : \mathbb{N}), (0 < b) \Rightarrow (\forall (f : \mathbb{N} \to \mathbb{N}), (\forall (j : \mathbb{N}), (j < n) \Rightarrow (f\left(j\right) < b)) \Rightarrow (\forall (i : \mathbb{N}), (i < n) \Rightarrow (digit\left(b, pack\left(b, n, f\right), i\right) = f\left(i\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.digit_pack` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive base and digits below the base, integer quotient and remainder recover each digit at an index below the packed length.

**Definition 1.17 (Endpoint isomorphism from relabelling).**

$$\forall (n : \mathbb{N}), \forall (S : \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (Sprime : \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)\right)), \forall (q : \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(n\right)\right)), \forall (hq : \operatorname{Finset.image}\left(\operatorname{Sym2.map}\left(q\right), S\right) = Sprime), (endpointIso_{image}\left(S, Sprime, q, hq\right) : endpointGraph\left(S\right) \equiv_{g} endpointGraph\left(Sprime\right)) \land (\forall (v : \{x : \operatorname{Fin}\left(n\right) | x \in endpointSet\left(S\right)\}), \operatorname{val}\left(endpointIso_{image}\left(S, Sprime, q, hq\right)\left(v\right)\right) = q\left(\operatorname{val}\left(v\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.endpointIso_image` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image hypothesis transports endpoint membership. The isomorphism sends each endpoint vertex v to q(v), using q.subtypeEquiv; its adjacency proof is the membership transport for unordered pairs.

**Definition 1.18 (Counting a Boolean predicate).**

$$\forall (n : \mathbb{N}), \forall (p : \mathbb{N} \to Bool), countNat\left(n, p\right) = \operatorname{List.length}\left(\operatorname{List.filter}\left(p, \operatorname{List.range}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.countNat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Filter the natural numbers below n, then take the list length.

**Definition 1.19 (Character on a natural-number action).**

$$\forall (n : \mathbb{N}), \forall (p : \mathbb{N} \to \mathbb{N}), natChi\left(n, p\right) = (\operatorname{Nat.choose}\left(countNat\left(n, fun (v : \mathbb{N}) \mapsto \operatorname{BEq.beq}\left(p\left(v\right), v\right)\right), 2\right) : \mathbb{Z}) + (\operatorname{Nat.div}\left(countNat\left(n, fun (v : \mathbb{N}) \mapsto \operatorname{Bool.and}\left(\operatorname{bne}\left(p\left(v\right), v\right), \operatorname{BEq.beq}\left(p\left(p\left(v\right)\right), v\right)\right)\right), 2\right) : \mathbb{Z}) - (countNat\left(n, fun (v : \mathbb{N}) \mapsto \operatorname{BEq.beq}\left(p\left(v\right), v\right)\right) : \mathbb{Z})$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.natChi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed expression is the literal body of natChi. The two local counts test fixed points and nonfixed points fixed by the square. Dividing the latter by two uses Nat.div; both counts and the quotient are cast to integers.

**Definition 1.20 (Word action on natural numbers).**

$$(\forall (x : \mathbb{N}), natProd\left([], x\right) = x) \land (\forall (u : \mathbb{N}), \forall (v : \mathbb{N}), \forall (w : \operatorname{List}\left(\mathbb{N} \times \mathbb{N}\right)), \forall (x : \mathbb{N}), natProd\left(\operatorname{List.cons}\left((u, v), w\right), x\right) = \operatorname{Equiv.swapCore}\left(u, v, natProd\left(w, x\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.natProd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The list head acts after the tail, matching multiplication of permutations.

**Definition 1.21 (Recursive edge-word evaluator).**

$$\forall (n : \mathbb{N}), \forall (edges : \operatorname{List}\left(\mathbb{N} \times \mathbb{N}\right)), \forall (w : \operatorname{List}\left(\mathbb{N} \times \mathbb{N}\right)), (evalMoment\left(n, edges, 0, w\right) = natChi\left(n, natProd\left(w\right)\right)) \land (\forall (r : \mathbb{N}), evalMoment\left(n, edges, r + 1, w\right) = \operatorname{List.sum}\left(\operatorname{List.map}\left(fun (e : \mathbb{N} \times \mathbb{N}) \mapsto evalMoment\left(n, edges, r, \operatorname{List.append}\left(w, [e]\right)\right), edges\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.evalMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At depth zero evaluate the accumulated word. At positive depth append each edge once and sum the recursive values. Repeated edges and all edge orders are included.

**Theorem 1.22 (Soundness of the evaluator).**

$$\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \forall (e : \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)), \forall (r : \mathbb{N}), \forall (w : \operatorname{List}\left(\operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)\right)), evalMoment\left(n, \operatorname{List.map}\left(fun (i : \operatorname{Fin}\left(m\right)) \mapsto (\operatorname{val}\left(\operatorname{Prod.fst}\left(e\left(i\right)\right)\right), \operatorname{val}\left(\operatorname{Prod.snd}\left(e\left(i\right)\right)\right)), \operatorname{List.finRange}\left(m\right)\right), r, \operatorname{List.map}\left(fun (a : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{val}\left(\operatorname{Prod.fst}\left(a\right)\right), \operatorname{val}\left(\operatorname{Prod.snd}\left(a\right)\right)), w\right)\right) = (\sum_{v : \operatorname{Fin}\left(r\right) \to \operatorname{Fin}\left(m\right)} (chi\left(\operatorname{List.prod}\left(\operatorname{List.map}\left(fun (a : \operatorname{Fin}\left(n\right) \times \operatorname{Fin}\left(n\right)) \mapsto \operatorname{Equiv.swap}\left(\operatorname{Prod.fst}\left(a\right), \operatorname{Prod.snd}\left(a\right)\right), w\right)\right) \cdot \operatorname{List.prod}\left(\operatorname{List.ofFn}\left(fun (i : \operatorname{Fin}\left(r\right)) \mapsto \operatorname{Equiv.swap}\left(\operatorname{Prod.fst}\left(e\left(v\left(i\right)\right)\right), \operatorname{Prod.snd}\left(e\left(v\left(i\right)\right)\right)\right)\right)\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.evalMoment_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the remaining word length identifies the recursive sum with the sum over functions Fin r → Fin m. Natural-number actions agree with the corresponding permutations on Fin n, including repeated or equal endpoints.

**Theorem 1.23 (Two-prefix decomposition).**

$$\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \forall (e : \operatorname{Fin}\left(m\right) \to \mathbb{N} \times \mathbb{N}), \forall (r : \mathbb{N}), \forall (w : \operatorname{List}\left(\mathbb{N} \times \mathbb{N}\right)), evalMoment\left(n, \operatorname{List.map}\left(e, \operatorname{List.finRange}\left(m\right)\right), r + 2, w\right) = (\sum_{i : \operatorname{Fin}\left(m\right)} ((\sum_{j : \operatorname{Fin}\left(m\right)} (evalMoment\left(n, \operatorname{List.map}\left(e, \operatorname{List.finRange}\left(m\right)\right), r, \operatorname{List.append}\left(w, [e\left(i\right), e\left(j\right)]\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.evalMoment_two_fin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two applications of the evaluator recursion expose the first two edge choices as finite sums, leaving the remaining r choices recursive.

**Definition 1.24 (Moment indexed by an edge enumeration).**

$$\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \forall (e : \operatorname{Fin}\left(m\right) \to \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)), \forall (r : \mathbb{N}), wordMoment\left(e, r\right) = (\sum_{w : \operatorname{Fin}\left(r\right) \to \operatorname{Fin}\left(m\right)} (chi\left(\operatorname{List.prod}\left(\operatorname{List.ofFn}\left(fun (i : \operatorname{Fin}\left(r\right)) \mapsto edgeSwap\left(e\left(w\left(i\right)\right)\right)\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.wordMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index function chooses unordered edges; the list of their transpositions has length r and is multiplied in increasing index order.

**Theorem 1.25 (Reindexing graph edge words).**

$$\forall (n : \mathbb{N}), \forall (m : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \forall (e : \operatorname{Fin}\left(m\right) \to \operatorname{Sym2}\left(\operatorname{Fin}\left(n\right)\right)), (\operatorname{Finset.image}\left(e, (\operatorname{Finset.univ} : \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right))\right) = \operatorname{SimpleGraph.edgeFinset}\left(G\right)) \Rightarrow ((\operatorname{Function.Injective}\left(e\right)) \Rightarrow (\forall (r : \mathbb{N}), M_{r2}\left(G, r\right) = wordMoment\left(e, r\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.moment_reindex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective exhaustive edge enumeration supplies an equivalence with the graph's edge subtype. The induced equivalence on word functions reindexes the finite sum.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.M_r2`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.N_H`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.N_H_of_enumeration`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.c1`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.c2`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.chi`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.countNat`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.counts_eq_of_iso_enumerations`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.digit`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.digit_pack`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.endpointGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.endpointIso_image`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.endpointSet`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.evalMoment`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.evalMoment_sound`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.evalMoment_two_fin`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.moment_reindex`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.natChi`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.natProd`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.noIsolated`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.pack`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.twoPoints`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.twoPoints_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.wordMoment`
