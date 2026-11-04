# All named outputs and their comparison graph

## Abstract

Residual occurrences in a total most-general free-term substitution

A presentation enumerates the entire finite family X of declared names, including unused names. C is any finite list of equations of free ordered binary terms with two distinct primitive labels. S is the actual successful result of the existing unifier from the empty substitution. Its total action assigns a term to every declared name. An unbound name is retained as its own variable. Interpreted native powers do not occur in this free-term problem. ListMem in the display denotes ordinary list membership, and sort is the third coordinate of an occurrence.

**Definition 1.1 (Residual positions retain their owners).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover.Occurrence`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover.Occurrence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An occurrence is a triple (x,p,y): the declared output name x, an ordered Boolean address p, and the residual sort y. IsOccurrence means that the subtree of the total output at x and p is exactly the variable y. The finite list occurrenceVertices enumerates every such position in every declared output; it does not restrict to names visible in the input equations.

**Definition 1.2 (Edges come from every positive comparison).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover.occurrenceEdges`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover.occurrenceEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

decorate gives each residual position its own occurrence label, consistently whenever a declared name is reused. comparisonTerm substitutes these decorated total outputs into each side of a supplied equation. comparisonEdges descends through corresponding constructors and records corresponding residual leaves. occurrenceEdges concatenates these finite lists over all equations, retaining their order and repetitions. Connected is the equivalence closure of this edge relation, so edges may be traversed in either direction.

**Theorem 1.3 (Exact finite vertices, valid edges and residual-sort components).**

$$\forall X: Type, (\forall p: \operatorname{Presentation}\left(X\right), (\forall C: \operatorname{Equations}\left(X\right), (\forall S: SubstInfo, ((\operatorname{unify}\left(\operatorname{encodeEquations}\left(p, C\right), empty\right) = \operatorname{ok}\left(S\right)) \implies ((\forall o: \operatorname{Occurrence}\left(X\right), ((\operatorname{ListMem}\left(o, \operatorname{occurrenceVertices}\left(p, \operatorname{action}\left(p, S\right)\right)\right)) \iff (\operatorname{IsOccurrence}\left(\operatorname{action}\left(p, S\right), o\right)))) \land ((\forall a: \operatorname{Occurrence}\left(X\right), (\forall b: \operatorname{Occurrence}\left(X\right), ((\operatorname{ListMem}\left(\operatorname{pair}\left(a, b\right), \operatorname{occurrenceEdges}\left(C, \operatorname{action}\left(p, S\right)\right)\right)) \implies ((\operatorname{ListMem}\left(a, \operatorname{occurrenceVertices}\left(p, \operatorname{action}\left(p, S\right)\right)\right)) \land ((\operatorname{ListMem}\left(b, \operatorname{occurrenceVertices}\left(p, \operatorname{action}\left(p, S\right)\right)\right)) \land (\operatorname{sort}\left(a\right) = \operatorname{sort}\left(b\right))))))) \land (\forall a: \operatorname{Occurrence}\left(X\right), (\forall b: \operatorname{Occurrence}\left(X\right), ((\operatorname{ListMem}\left(a, \operatorname{occurrenceVertices}\left(p, \operatorname{action}\left(p, S\right)\right)\right)) \implies ((\operatorname{ListMem}\left(b, \operatorname{occurrenceVertices}\left(p, \operatorname{action}\left(p, S\right)\right)\right)) \implies ((\operatorname{Connected}\left(C, \operatorname{action}\left(p, S\right), a, b\right)) \iff (\operatorname{sort}\left(a\right) = \operatorname{sort}\left(b\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover.mgu_occurrence_graph_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every presentation, every finite equation list and every actual successful unifier result, the computed vertex list contains exactly the residual occurrences of the total action. Every computed edge joins two valid vertices of the same residual sort. Among valid vertices, connectivity is equivalent to equality of their residual sorts. Thus each occurring residual sort has exactly one connected component. There is no connectedness assertion for an empty residual sort. An unused original name contributes its own isolated residual occurrence.

To prove the nontrivial direction, color the component of one occurrence by one primitive ground leaf and all other components by the other primitive ground leaf. Evaluate each decorated output with these colors. Corresponding residual positions on every positive comparison are joined by an edge, so this modified total assignment still solves all equations. The existing most-generality restriction identity forces that assignment to factor through the actual total action. At each occurrence, its color must therefore be the value of its residual sort. Two occurrences of the same sort have equal colors and hence belong to the same component. Structural traversal supplies the exact vertex and edge correspondence.

This theorem concerns the free-shape stage of native positive equation elimination. It supplies no interpreted constructor/collapse reduction, rank offsets, minimum bases, executable positive image charts or full-tuple native reconstruction. Those require additional arguments; free unification is not applied directly to interpreted native equations.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover.Occurrence`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover.mgu_occurrence_graph_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativePositiveImageCover.occurrenceEdges`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeGroundSolutionSpace](../NativeGroundSolutionSpace.md)
