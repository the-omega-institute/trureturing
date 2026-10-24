# Headley nonsplit extension

## Abstract

An R-cycle on a kernel and an even R-star quotient construct a cyclic ordering with every nonzero directed difference in an arbitrary finite abelian extension.

**Definition 1.1 (A complete cyclic vertex and directed-difference inventory).**

$$\forall G \in Type,\; [\operatorname{AddCommGroup}\left(G\right)] \operatorname{RCycle}\left(G\right):Type$$

*Formalization.* `D5/S3/FiniteGroups/HeadleyExtension.RCycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RCycle(G) is the type of records consisting of permutations S and Delta of G, the equality S(0)=0, the assertion that S is one cycle on all nonzero elements, and the equation Delta(x)=S(x)-x for every x in G. Thus Delta fixes zero and restricts to a bijection of the nonzero elements. Every edge is recorded, including the closing edge.

**Definition 1.2 (A quotient cycle with the additive triple used by the splice).**

$$\forall G \in Type,\; [\operatorname{AddCommGroup}\left(G\right)] [\operatorname{Finite}\left(G\right)] \operatorname{RStar}\left(G\right):Type$$

*Formalization.* `D5/S3/FiniteGroups/HeadleyExtension.RStar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RStar(G) extends RCycle(G) with even cardinality and three pairwise distinct nonzero vertices a,b,c. Its successor satisfies S(a)=b and S(b)=c, and a+c=b. Evenness is included in this interface; no additional condition is imposed on the kernel.

**Theorem 1.3 (The kernel cycle is inserted by a two-row splice).**

$$\forall E \in Type,\; [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Fintype}\left(E\right)] \forall N \in \operatorname{AddSubgroup}\left(E\right),\; \operatorname{RCycle}\left(N\right) \to \left(\operatorname{RStar}\left(E/N\right) \to \operatorname{Nonempty}\left(\operatorname{RCycle}\left(E\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/HeadleyExtension.nonsplit_extension_r_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any finite additive abelian group and N a subgroup. An R-cycle on N and an R-star cycle on the even quotient E/N imply an R-cycle on E. Representatives A,C of a,c are arbitrary, B=A+C, and the other representatives are arbitrary. The representative map has no additivity requirement, so nonsplit extensions are included. A trivial kernel is handled by the additive quotient equivalence.

Extend the kernel successor D by D(0)=0 and put F(h)=h-D(h), J=F inverse. Both F and J are orthomorphisms. The a-to-b and b-to-c lifts use F,J. The next edge uses D and the remaining edges use consecutive F,J pairs. Even quotient order makes their number even, so the unmodified return is D.

Choose v nonzero in N. Replace row zero by A,D(v),D squared(v),...,v,C+v. Replace row v by A+v,B+F(v),B,C. These are the same successor changes as two transpositions at the vertices A, v, and B+F(v). They join the zero row, the nonzero kernel cycle, and the remaining nonzero rows into one cycle. The proof identifies the actual first positive return to the A-column and excludes an intervening visit to that column. Its return permutation is D composed with the transposition of zero and v, whose cyclic traversal is zero,D(v),D squared(v),...,v.

For every ordinary edge the quotient difference identifies its coset, and the orthomorphism difference bijects that coset. The splice permutes three old labels: the label C, the cut kernel label D(v)-v, and the label -A+D(v). The fourth cross-column label C-D(v) is unchanged. The inverse three-cycle on source indices therefore gives a full ambient directed-difference bijection, rather than only a quotient inventory.

This construction belongs to the R-sequenceability program of P. Headley, R-sequenceability and R-star-sequenceability of abelian 2-groups, Discrete Mathematics 131, 345-350, DOI 10.1016/0012-365X(94)90396-4. The explicit splice is a reconstruction; no originality claim is made. The theorem supplies the extension step only. Elementary and order-eight bases, induction through abelian 2-groups, and the R-star quotient construction with arbitrary odd factors are additional obligations for the full Headley supplier. The arbitrary-subset sequencing problem is outside this theorem.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyExtension.RCycle`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyExtension.RStar`
- Truth anchor: `D5/S3/FiniteGroups/HeadleyExtension.nonsplit_extension_r_cycle`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch](../Combinatorics/PerfectMatchings/FiniteBandSwitch.md)
