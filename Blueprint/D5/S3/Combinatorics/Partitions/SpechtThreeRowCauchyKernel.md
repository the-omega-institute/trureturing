# The finite Cauchy kernel and signed contingency Gram

## Abstract

The finite Cauchy kernel and signed contingency Gram

Use six variables Xi,Yj indexed by the disjoint union of two copies of Fin 3. An edge (i,j) has weight k at Xi and k at Yj, with all other exponents zero. Its geometric series has coefficient one exactly at these edge weights. Multiplication by 1-XiYj gives one: the shifted coefficients cancel except at the zero monomial. Define K as the product of these nine labelled series. There is no analytic convergence condition.

The coefficient of K at X^a Y^b, when the natural row margin a has total n, is the cardinality of the existing finite set contingencyTables(n,a,b). Indeed, the product coefficient formula indexes decompositions of the six-variable exponent into nine edge weights. The exponent on edge (i,j) is its table entry A(i,j); the decomposition equation is precisely the three row and three column equations. Sending a decomposition to its Xi coordinate on each edge and sending a table to its nine edge monomials are inverse maps. The total-table equation follows by summing the row margins. Unequal column total gives the empty set automatically.

For any commutative ring and elements xi,yj, let dij=1-xi*yj. The matrix whose i-th row is [di1*di2,di0*di2,di0*di1] has determinant Delta(x)Delta(y), by the three-by-three determinant formula and the polynomial ring identity. If dij*qij=1, scaling row i of q by di0*di1*di2 gives this numerator matrix. The product of the nine d's times the product of the nine q's equals one. It follows that Delta(x)Delta(y) times the product of the qij equals det(q). Applying this to the nine geometric series proves Delta(X)Delta(Y)K=det((1-XiYj) inverse). No character or Schur orthogonality enters this argument.

A term of the determinant selects one edge from each row and column. The coefficient at X^u Y^v in the product of the three selected geometric series is one if u(i)=v(s(i)) for every i and zero otherwise. Its exponent decomposition, when it exists, is unique: the Xi coordinate fixes the exponent on the selected edge. If u and v are strictly decreasing, their matching permutation is increasing and hence the identity; their entries are then equal. Thus the coefficient of Delta(X)Delta(Y)K is one when u=v and zero otherwise.

Transport the existing Vandermonde expansion into each set of three variables. Their product has six times six signed monomials. Extract at u=r+(2,1,0), v=q+(2,1,0). Removing the staircase monomial for s leaves the integer margins r(i)-i+s(i). In the nonnegative case these are exactly the natural exponent differences and have total n; the preceding table bijection applies. If a coordinate is negative, the monomial does not divide the extracted exponent and the corresponding table set is empty. No integer-to-natural truncation is used to retain a negative term. The signed contingency sum is therefore the same double coefficient. Decreasing r and q give strictly decreasing u and v, proving the signed Gram delta in every degree.

**Theorem 1.1 (Strict double coefficients of the Cauchy kernel).**

$$\forall u \in \operatorname{NatTriple},\; \forall v \in \operatorname{NatTriple},\; (\operatorname{strictlyDecreasing}\left(u\right)) \Rightarrow ((\operatorname{strictlyDecreasing}\left(v\right)) \Rightarrow (\operatorname{doubleKernelCoefficient}\left(u, v\right) = \operatorname{kroneckerDelta}\left(u, v\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchyKernel.cauchy_coefficient_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

doubleWeight(u,v) places u on the X variables and v on the Y variables. doubleVandermonde is Delta(X)Delta(Y). cauchyKernel is the product of the nine labelled edge series.

**Theorem 1.2 (The finite signed contingency identity).**

$$\forall n \in \operatorname{Nat},\; \forall r \in \operatorname{NatTriple},\; \forall q \in \operatorname{NatTriple},\; (\operatorname{totalEq}\left(r, n\right)) \Rightarrow ((\operatorname{decreasing}\left(r\right)) \Rightarrow ((\operatorname{decreasing}\left(q\right)) \Rightarrow (\operatorname{signedContingencyGram}\left(n, r, q\right) = \operatorname{kroneckerDelta}\left(r, q\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchyKernel.signedContingencyGram_eq_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The total hypothesis is sum(r)=n. The formula also permits a different total for q; when r differs from q the value is zero. Both triples decrease weakly.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchyKernel.cauchy_coefficient_delta`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchyKernel.signedContingencyGram_eq_delta`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtThreeRowMixed](SpechtThreeRowMixed.md)
