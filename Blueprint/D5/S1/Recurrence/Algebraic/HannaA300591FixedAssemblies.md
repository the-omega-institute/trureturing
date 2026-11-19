# Fixed and moved blocks in Hanna's signed assemblies

## Abstract

Invariant assemblies of ordered decorated blocks split into their fixed and moved parts, with an exact product formula for arbitrary integer block weights.

**Theorem 1.1 (The signed fixed-assembly factorization).**

$$\forall V: \operatorname{FiniteTypes}\left(\right), \forall C: \operatorname{FiniteTypes}\left(\right), \forall allowed: \operatorname{Predicate}\left(\mathbb{N}, C\right), \forall S: \operatorname{Finset}\left(V\right), \forall T: \operatorname{Finset}\left(V\right), \forall g: \operatorname{Perm}\left(V\right), \forall sign: \operatorname{Function}\left(C, \mathbb{Z}\right), \operatorname{fixedSum}\left(allowed, S, T, g, sign\right) = \operatorname{assemblySum}\left(allowed, \operatorname{Fix}\left(g, S\right), \operatorname{Fix}\left(g, T\right), sign\right) \cdot \operatorname{fixedSum}\left(allowed, \operatorname{Moved}\left(g, S\right), T, g, sign\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591FixedAssemblies.fixed_assembly_weight_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

Let V and C be arbitrary finite types, with decidable equality, and let allowed(j,c) be any predicate on block sizes and colors. A block is a nonempty list of distinct vertices, a color c, and an ordered pair of ambient markers; the two markers may coincide. An assembly on S with markers in T is an unordered finite set of these decorated blocks. The vertex lists are pairwise disjoint, cover exactly S, and satisfy allowed(length,c). Relabeling by g preserves the block order and color and applies g to every vertex and both markers. FixedAssembly consists of assemblies closed under this relabeling. The weight of an assembly is the product of sign(c) over its blocks; sign may be any integer-valued function, so negative and zero weights are included. The notation assemblySum means the sum of these weights over all assemblies, and fixedSum means the sum over invariant assemblies. Fix(g,S) is the subset of S fixed by g; Moved(g,S) is its complement within S.

If an invariant assembly has a block containing a fixed vertex, its relabeling shares that vertex with the original block. Disjointness forces equality of the decorated blocks. Equality of their ordered lists forces every vertex of the block to be fixed, and equality of their two markers forces both markers to be fixed. Thus a block cannot mix fixed and moved vertices. Restricting to the two kinds of block gives an equivalence; its inverse is disjoint union. The moved part retains the original marker set T. Multiplicativity of the weight under this disjoint union gives the displayed identity.

No stability assumption on S or T is required, and the empty fixed or moved set is included. Taking S=T=V gives the unpointed fixed assembly split. Taking S=V with one fixed distinguished vertex removed and T=V preserves the ambient markers for the pointed subtraction term. Size restrictions and finite signed color sets can be expressed by allowed. HannaA300591AssemblyCoefficients identifies the assembly sums with ordinary exponential coefficients and realizes every integer strict prefix by a finite signed palette. That module also proves the actual actions, signed Burnside identity and Sylow arithmetic, which are used by the all-degree source induction in HannaA300591RationalModel.

**Theorem 1.2 (Removing the block at a chosen vertex).**

$$\forall V: \operatorname{FiniteTypes}\left(\right), \forall C: \operatorname{FiniteTypes}\left(\right), \forall allowed: \operatorname{Predicate}\left(\mathbb{N}, C\right), \forall S: \operatorname{Finset}\left(V\right), \forall T: \operatorname{Finset}\left(V\right), \forall x: S, \forall sign: \operatorname{Function}\left(C, \mathbb{Z}\right), \operatorname{assemblySum}\left(allowed, S, T, sign\right) = \operatorname{rootSum}\left(allowed, S, T, x, sign\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591FixedAssemblies.assembly_weight_point_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300591 squared-exponential ordinary series*. URL: <https://oeis.org/A300591>.

*Commentary.*

For any chosen x in S, RootBlock consists of the allowed decorated blocks b whose list contains x, whose vertices belong to S, and whose two markers belong to T. The expression rootSum is the sum over b of sign(color(b)) times assemblySum on S with the vertices of b removed, with the same marker set T. The theorem equates this expression with the signed sum over all assemblies on S. There is no permutation invariance hypothesis in this recurrence.

Disjointness and coverage give a unique block containing x. Remove it to obtain an assembly on the remaining vertices. Conversely, insert any admissible root block into an assembly on its complementary support. The complementary support prevents the root block from already occurring. These operations are inverse, and inserting the block multiplies the assembly weight by its color weight. Summing over the resulting dependent pairs proves the recurrence. HannaA300591AssemblyCoefficients evaluates the root-block sum by support, order, color and ambient marker pair, then proves that this recurrence agrees with the exponential derivative recurrence. The coefficient identity is proved there without an extra counting assumption.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591FixedAssemblies.assembly_weight_point_recursion`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591FixedAssemblies.fixed_assembly_weight_factorization`
