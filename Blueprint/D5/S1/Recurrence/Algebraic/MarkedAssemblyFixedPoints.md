# Assemblies with a finite marker family

## Abstract

Signed assemblies with any finite number of independently transported markers split exactly into fixed and moved blocks.

**Theorem 1.1 (Splitting invariant assemblies).**

$$\forall k: \mathbb{N}, \forall V: \operatorname{FiniteTypes}, \forall C: \operatorname{FiniteTypes}, \forall allowed: \operatorname{Predicate}\left(\mathbb{N}, C\right), \forall S: \operatorname{Finset}\left(V\right), \forall T: \operatorname{Finset}\left(V\right), \forall g: \operatorname{Perm}\left(V\right), \forall sign: \operatorname{Function}\left(C, \mathbb{Z}\right), \operatorname{fixedSum}\left(k, allowed, S, T, g, sign\right) = \operatorname{assemblySum}\left(k, allowed, \operatorname{Fix}\left(g, S\right), \operatorname{Fix}\left(g, T\right), sign\right) \cdot \operatorname{fixedSum}\left(k, allowed, \operatorname{Moved}\left(g, S\right), T, g, sign\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MarkedAssemblyFixedPoints.fixed_assembly_weight_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be any natural number, V and C finite types, and V have decidable equality. A block consists of an ordered list of distinct vertices, a color, and a function from Fin k to V. An assembly is a finite set of nonempty blocks whose vertex lists partition S; each color satisfies allowed(length,color), and every marker coordinate belongs to T. Coordinates may repeat, and T is independent of the vertex support S. Its integer weight is the product of sign(color), with arbitrary integer signs. The displayed sums range over these actual assemblies. Fix(g,S) and Moved(g,S) are the vertices of S fixed and moved by the permutation g. Invariant means stability under simultaneous relabeling of the ordered list and every marker, leaving colors unchanged. A block containing a fixed vertex must be invariant, because its image shares that vertex. The order then fixes each vertex individually, and every marker is fixed. Filtering by fixed and moved supports is an equivalence with inverse disjoint union. Its weights multiply. The moved blocks retain T; the fixed blocks restrict their markers to Fix(g,T). Empty sets, zero markers and all integer color weights are included. No stability premise on S or T is imposed.

**Theorem 1.2 (Removing the block at a chosen vertex).**

$$\forall k: \mathbb{N}, \forall V: \operatorname{FiniteTypes}, \forall C: \operatorname{FiniteTypes}, \forall allowed: \operatorname{Predicate}\left(\mathbb{N}, C\right), \forall S: \operatorname{Finset}\left(V\right), \forall T: \operatorname{Finset}\left(V\right), \forall sign: \operatorname{Function}\left(C, \mathbb{Z}\right), \forall x: V, (\operatorname{mem}\left(x, S\right)) \implies (\operatorname{assemblySum}\left(k, allowed, S, T, sign\right) = \operatorname{rootSum}\left(k, allowed, S, T, x, sign\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/MarkedAssemblyFixedPoints.assembly_weight_point_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x in S, rootSum sums sign(color(b)) times the assembly sum on S minus the vertices of b, with the same T, over all admissible ordered decorated blocks b containing x. Coverage and disjointness give exactly one such block in every assembly. Removing and inserting this block are inverse operations, and insertion multiplies its color weight into the remaining assembly weight. The theorem includes every k and imposes no invariance hypothesis. MarkedAssemblyCoefficients uses this recurrence to prove the exponential coefficient formula.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/MarkedAssemblyFixedPoints.assembly_weight_point_recursion`
- Truth anchor: `D5/S1/Recurrence/Algebraic/MarkedAssemblyFixedPoints.fixed_assembly_weight_factorization`
- Dependency: [D5/S1/Recurrence/Algebraic/HannaA300591FixedAssemblies](HannaA300591FixedAssemblies.md)
