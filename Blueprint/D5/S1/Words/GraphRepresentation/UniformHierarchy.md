# Strict Positive Uniform Hierarchy

## Abstract

For every positive k, the finite graphs represented by two k-uniform words form a proper subclass of those represented by two (k+1)-uniform words.

The representation is `D5/S1/Words/GraphRepresentation/UniformVertexExtension.InG`. Both actual List words contain every vertex exactly k times. For every ordered distinct pair, adjacency is equivalent to equality of the actual two-letter projections, using `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.twoProjection`. Positive k begins at one. Inclusion covers all finite carriers, including the empty carrier, at every type universe. Decidable equality is available on every carrier. No alternation or union-of-languages representation is used.

**Definition 1.1 (The finite membership graph).**

$$\begin{gathered}\forall m:\mathbb{N}, a,b:\operatorname{Fin}\left(m\right), S,T:\operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)\\\operatorname{Omega}\left(m\right) = \operatorname{Sum}\left(\operatorname{Fin}\left(m\right), \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right)\right)\\\operatorname{membershipGraph}\left(m\right):\operatorname{SimpleGraph}\left(\operatorname{Omega}\left(m\right)\right)\\(\operatorname{Adj}\left(\operatorname{membershipGraph}\left(m\right), \operatorname{inl}\left(a\right), \operatorname{inr}\left(S\right)\right)) \iff (a \in S)\\(\operatorname{Adj}\left(\operatorname{membershipGraph}\left(m\right), \operatorname{inr}\left(S\right), \operatorname{inl}\left(a\right)\right)) \iff (a \in S)\\(\neg\operatorname{Adj}\left(\operatorname{membershipGraph}\left(m\right), \operatorname{inl}\left(a\right), \operatorname{inl}\left(b\right)\right)) \land (\neg\operatorname{Adj}\left(\operatorname{membershipGraph}\left(m\right), \operatorname{inr}\left(S\right), \operatorname{inr}\left(T\right)\right))\end{gathered}$$

*Formalization.* `D5/S1/Words/GraphRepresentation/UniformHierarchy.membershipGraph` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

Omega(m) is Fin(m) plus all finite subsets of Fin(m), with disjoint tags. A point and a subset are adjacent exactly when the point belongs to the subset. Both same-tag adjacency relations are false. The graph is finite, undirected and loopless. This parameterized definition supplies the actual obstruction in the full consumer.

**Definition 1.2 (The complete positive-k source assertion).**

$$\forall k: \mathbb{N}, (0 < k) \implies ((\forall V: \operatorname{Type}, (\operatorname{Finite}\left(V\right)) \implies (\forall G: \operatorname{SimpleGraph}\left(V\right), (\operatorname{InG}\left(k, G\right)) \implies (\operatorname{InG}\left(k + 1, G\right)))) \land (\exists s: \operatorname{Finset}\left(\operatorname{Omega}\left(64 \cdot k^{2}\right)\right), (\operatorname{InG}\left(k + 1, \operatorname{H}\left(s\right)\right)) \land (\neg\operatorname{InG}\left(k, \operatorname{H}\left(s\right)\right))))$$

*Formalization.* `D5/S1/Words/GraphRepresentation/UniformHierarchy.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

For k>0 put m=64k^2 and Omega=Omega(m). For a finite subset s of Omega, X(s) is its subtype and H(s) is U(m).comap(val). The first conjunct quantifies over every finite vertex type with decidable equality and every simple graph on it. The second supplies a finite subset s, with the same H(s) on the same X(s) in its positive and negative clauses. Actual word witnesses are supplied by InG. This is Conjecture 31 of the primary source with an explicit finite ambient graph for its existential separator. IFIG Report 2501 Conjecture 3.2 states the same problem and is not an additional settlement.

**Remark 1.3 (The published source question).**

Lean statement: `D5/S1/Words/GraphRepresentation/UniformHierarchy.claim`

*Formalization.* `D5/S1/Words/GraphRepresentation/UniformHierarchy.claim` (`✓ std3`).

*Citation.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

Conjecture 31 states: for each k in the source's natural numbers, the inclusion G_k subset G_(k+1) is proper. The source natural numbers begin at one. The claim retains this whole assertion and strengthens its existential clause by specifying the finite ambient membership graph. This additional witness refinement is repository-derived, not attributed to the source.

`D5/L/Words/adamson2026twoword`: Theorem 29 supplies the known conclusion that no fixed positive-k class contains every finite graph. The full consumer discharges that conclusion internally, using the actual membership graph and the repository cut reconstruction. Its chosen bound m=64k^2 and local proof are not attributed to the paper. No independent known-result declaration or theorem parameter is introduced.

**Theorem 1.4 (Every adjacent inclusion is proper).**

$$\forall k: \mathbb{N}, (0 < k) \implies ((\forall V: \operatorname{Type}, (\operatorname{Finite}\left(V\right)) \implies (\forall G: \operatorname{SimpleGraph}\left(V\right), (\operatorname{InG}\left(k, G\right)) \implies (\operatorname{InG}\left(k + 1, G\right)))) \land (\exists s: \operatorname{Finset}\left(\operatorname{Omega}\left(64 \cdot k^{2}\right)\right), (\operatorname{InG}\left(k + 1, \operatorname{H}\left(s\right)\right)) \land (\neg\operatorname{InG}\left(k, \operatorname{H}\left(s\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/GraphRepresentation/UniformHierarchy.result` (`✓ std3`). ∎

*Resolves.* `Problems/adamson-positive-uniform-hierarchy` (proved) by `D5/S1/Words/GraphRepresentation/UniformHierarchy.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"adamson-positive-uniform-hierarchy","declaration_gid":"D5/S1/Words/GraphRepresentation/UniformHierarchy.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Duncan Adamson, Amanita Dietz, Pamela Fleischmann, Annika Huch, and Silas Cato Sacher (2026). *2-word-π-representable Graphs*. URL: <https://arxiv.org/abs/2605.27183v1>.

*Commentary.*

For inclusion, enumerate the finite carrier once in q and append the same q to both words. Counts increase by one; projected suffixes are identical, so right cancellation preserves every edge and nonedge. For separation, discharge the known Theorem 29 nonuniversality component from the source literature inside this proof. In a hypothetical representation of U(m), each left restriction has length km. Each right vertex has two ordered k-cut lists bounded by km. Encode each list as Fin(k) -> Fin(km+1), preserving tied cuts and order. The signature count is (km+1)^(2k). The estimates km+1 <= 128k^3 <= 2^(7+3k) <= 2^(10k) give at most 2^(20k^2) signatures, strictly fewer than the 2^(64k^2) subsets. Pigeonhole gives distinct subsets with equal signatures. Use arbitrary-cut reconstruction separately in each actual word and cancel each fixed right label's own injective Unit-marker renaming. Equal normalized cut data then give equal adjacency truth at every left point; finite-set extensionality contradicts distinctness. The left orders may differ. Original projections carrying different right labels are never equated. Nat.find selects a nonrepresented induced subset s of minimum cardinality. The whole carrier is a witness by actual word transport through the whole-set subtype equivalence. The empty subtype has []/[] representations, so s contains x. Minimality supplies an actual k-uniform representation of the smaller erased subset t. Let d identify X(t) with the subtype of X(s) excluding x, keeping underlying vertices. E=optionCongr(d).trans(optionSubtypeNe(x)) maps none to x and some(z) to its original retained vertex. For K=H(s).comap(E), the actual deletion K.comap(some) equals H(t). Apply the frozen vertex extension and map its returned words through E. Injective count transport and filter/map identities preserve every count and both directions of each adjacency iff. Pair InG(k+1,H(s)) with the original nonmembership in InG(k,H(s)) on precisely X(s). No nonuniversality, closure, minimum, relabeling or extension premise is assumed.

The live inference directly reuses `D5/S0/Diagonal/PigeonholeFiber.finite_reading_has_fiber`, `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.projection_eq_reconstruction` and `D5/S1/Words/GraphRepresentation/UniformVertexExtension.vertex_extension`. Known nonuniversality and local word transports remain inside this single full consumer. No exponentially large graph is enumerated. The inaccessible SSRN and Gradiva full bodies limit priority claims. Reg enrollment is paused.

## References

- Truth anchor: `D5/S0/Diagonal/PigeonholeFiber.finite_reading_has_fiber`
- Truth anchor: `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.projection_eq_reconstruction`
- Truth anchor: `D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform.twoProjection`
- Truth anchor: `D5/S1/Words/GraphRepresentation/UniformHierarchy.claim`
- Truth anchor: `D5/S1/Words/GraphRepresentation/UniformHierarchy.claim`
- Truth anchor: `D5/S1/Words/GraphRepresentation/UniformHierarchy.membershipGraph`
- Truth anchor: `D5/S1/Words/GraphRepresentation/UniformHierarchy.result`
- Truth anchor: `D5/S1/Words/GraphRepresentation/UniformVertexExtension.InG`
- Truth anchor: `D5/S1/Words/GraphRepresentation/UniformVertexExtension.vertex_extension`
- Dependency: [D5/S1/Words/GraphRepresentation/UniformVertexExtension](UniformVertexExtension.md)
