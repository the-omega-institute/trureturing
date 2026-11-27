# Density and full permitted support in ordered-group cones

## Abstract

Order density is equivalent to exact full permitted support in every balanced finite-fiber transportation problem over the original nonnegative cone.

**Theorem 1.1 (The full equivalence).**

$$\forall G \in Typeu,\; [\operatorname{AddCommGroup}\left(G\right)], [\operatorname{LinearOrder}\left(G\right)], [\operatorname{IsOrderedAddMonoid}\left(G\right)], \operatorname{DenselyOrdered}\left(G\right) \Leftrightarrow \left(\forall A \in Typev,\; \forall B \in Typew,\; \forall Z \in Typez,\; [\operatorname{Fintype}\left(A\right)], [\operatorname{Fintype}\left(B\right)], \forall f \in \operatorname{Arrow}\left(A, Z\right),\; \forall g \in \operatorname{Arrow}\left(B, Z\right),\; \forall p \in \operatorname{Arrow}\left(A, \operatorname{Nonneg}\left(G\right)\right),\; \forall q \in \operatorname{Arrow}\left(B, \operatorname{Nonneg}\left(G\right)\right),\; \left(\forall c \in Z,\; \operatorname{fiberSum}\left(f, p, c\right) = \operatorname{fiberSum}\left(g, q, c\right)\right) \Rightarrow \left(\exists m \in \operatorname{Arrow}\left(A, \operatorname{Arrow}\left(B, \operatorname{Nonneg}\left(G\right)\right)\right),\; \left(\forall a \in A,\; \forall b \in B,\; \operatorname{f}\left(a\right) \ne \operatorname{g}\left(b\right) \Rightarrow \operatorname{m}\left(a, b\right) = 0\right) \land \left(\left(\forall a \in A,\; \operatorname{rowSum}\left(m, a\right) = \operatorname{p}\left(a\right)\right) \land \left(\left(\forall b \in B,\; \operatorname{columnSum}\left(m, b\right) = \operatorname{q}\left(b\right)\right) \land \left(\forall a \in A,\; \forall b \in B,\; \operatorname{m}\left(a, b\right) \ne 0 \Leftrightarrow \left(\operatorname{f}\left(a\right) = \operatorname{g}\left(b\right) \land \left(\operatorname{p}\left(a\right) \ne 0 \land \operatorname{q}\left(b\right) \ne 0\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Transportation/OrderedConeFullSupport.density_iff_full_permitted_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Albert Atserias and Phokion G. Kolaitis (2025). *Consistency Witnesses for Annotated Relations*. DOI: [10.1145/3749116.3749118](https://doi.org/10.1145/3749116.3749118). URL: <https://sigmodrecord.org/publications/sigmodRecord/2506/pdfs/03_Principles_Atserias.pdf>.

*Commentary.*

There are four independent universes u, v, w and z. G has type Typeu and carries an additive commutative group, a linear order and the compatibility IsOrderedAddMonoid. A has type Typev, B has type Typew, and Z has type Typez. Only A and B are finite. Nonneg(G) is exactly the subtype of x in G satisfying zero less than or equal to x. Its zero, addition, natural repeated addition, finite sums and equality are the original operations restricted to that subtype; no multiplication or division is used.

In the displayed formula, Arrow(U,V) denotes the function type U to V. For arbitrary label maps f and g and nonnegative margins p and q, fiberSum(f,p,c) means the sum over A of p(a) when f(a)=c and zero otherwise, and similarly for B. The expression rowSum(m,a) is the sum over B of m(a,b), and columnSum(m,b) is the sum over A of m(a,b). Balance requires equality of the two fiber sums for every c in Z. A permitted cell has equal labels and two nonzero margins. The conclusion provides one matrix m with exactly the original row and column sums, zero entries off equal labels, and a nonzero entry at every and only permitted cell.

For the forward direction, collect all strictly positive values among the two finite margin families. If this set is nonempty, let d be its minimum and n the sum of the row and column cardinalities. Density gives a positive e with n repeated additions of e strictly below d, by exists_nsmul_lt_of_pos. This uses neither an Archimedean assumption nor divisibility. Put e in every permitted cell and zero in every other cell. Each seed row is at most the column cardinality repeated additions of e, and each seed column is at most the row cardinality repeated additions of e. These bounds fit within their original margins. If there are no positive margins, the zero seed suffices.

Subtract each seed row and column sum in G. The residuals are nonnegative. For every label the two removed totals agree, because off-label seed cells vanish and finite summation commutes. The original cone is conical, and comparing the first two summands constructs binary refinement by subtraction of the smaller first margin. Apply the existing finite_fiber_transport construction to the residual cone-valued margins, then add the seed back. The same matrix has exact original margins and retains every positive seed cell. Conicality forces every entry in a zero row or column to vanish.

For the converse, fix a<b and use the positive cone element x=b-a. Take two rows and two columns, all four margins equal to x and all labels equal. Full permitted support makes both entries in the first row strictly positive; their sum is x. Its first entry t therefore satisfies zero<t<x, so a+t lies strictly between a and b. The row carrier is ULift of Bool at universe v, the column carrier is ULift of Bool at universe w, and the label carrier is ULift of Unit at universe z. Thus this argument uses the original arbitrary carrier universes, rather than restricting the statement to small types.

The statement includes the trivial group, non-Archimedean groups, empty row or column carriers, zero margins, empty fibers, and arbitrary possibly empty label types. The construction sums only over the two finite carriers, never over Z. The result gives existence and exact support, without asserting uniqueness, a uniform lower bound independent of the margins, or an algorithm with a specified running time.

The feasible transportation supplier is the conical binary-refinement construction in FiniteTransport. This ordered-cone equivalence refines that feasibility result to simultaneous full permitted support. It addresses an ordered-group-cone class related to the largest-support question in Atserias and Kolaitis, Section 8; it does not classify all coefficient monoids or settle that broader question.

## References

- Truth anchor: `D5/S3/Combinatorics/Transportation/OrderedConeFullSupport.density_iff_full_permitted_support`
