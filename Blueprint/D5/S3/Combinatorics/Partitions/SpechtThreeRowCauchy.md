# The finite Cauchy calculation and actual three-row traces

## Abstract

The finite Cauchy calculation and actual three-row traces

Use six variables Xi,Yj indexed by the disjoint union of two copies of Fin 3. An edge (i,j) has weight k at Xi and k at Yj, with all other exponents zero. Its geometric series has coefficient one exactly at these edge weights. Multiplication by 1-XiYj gives one: the shifted coefficients cancel except at the zero monomial. Define K as the product of these nine labelled series. There is no analytic convergence condition.

The coefficient of K at X^a Y^b, when the natural row margin a has total n, is the cardinality of the existing finite set contingencyTables(n,a,b). Indeed, the product coefficient formula indexes decompositions of the six-variable exponent into nine edge weights. The exponent on edge (i,j) is its table entry A(i,j); the decomposition equation is precisely the three row and three column equations. Sending a decomposition to its Xi coordinate on each edge and sending a table to its nine edge monomials are inverse maps. The total-table equation follows by summing the row margins. Unequal column total gives the empty set automatically.

For any commutative ring and elements xi,yj, let dij=1-xi*yj. The matrix whose i-th row is [di1*di2,di0*di2,di0*di1] has determinant Delta(x)Delta(y), by the three-by-three determinant formula and the polynomial ring identity. If dij*qij=1, scaling row i of q by di0*di1*di2 gives this numerator matrix. The product of the nine d's times the product of the nine q's equals one. It follows that Delta(x)Delta(y) times the product of the qij equals det(q). Applying this to the nine geometric series proves Delta(X)Delta(Y)K=det((1-XiYj) inverse). No character or Schur orthogonality enters this argument.

A term of the determinant selects one edge from each row and column. The coefficient at X^u Y^v in the product of the three selected geometric series is one if u(i)=v(s(i)) for every i and zero otherwise. Its exponent decomposition, when it exists, is unique: the Xi coordinate fixes the exponent on the selected edge. If u and v are strictly decreasing, their matching permutation is increasing and hence the identity; their entries are then equal. Thus the coefficient of Delta(X)Delta(Y)K is one when u=v and zero otherwise.

Transport the existing Vandermonde expansion into each set of three variables. Their product has six times six signed monomials. Extract at u=r+(2,1,0), v=q+(2,1,0). Removing the staircase monomial for s leaves the integer margins r(i)-i+s(i). In the nonnegative case these are exactly the natural exponent differences and have total n; the preceding table bijection applies. If a coordinate is negative, the monomial does not divide the extracted exponent and the corresponding table set is empty. No integer-to-natural truncation is used to retain a negative term. The signed contingency sum is therefore the same double coefficient. Decreasing r and q give strictly decreasing u and v, proving the signed Gram delta in every degree.

Combine the self-Gram value one with the actual mixed pairing from the preceding construction. The integral actual Specht character and Theta both have square sum n factorial and have mixed sum n factorial. Their squared difference sums to zero over the integers, so they agree at every permutation. The existing signed-character coefficient comparison then gives the actual same-literal-partition Specht trace equal to HSW.frobChar. The module remains the independently defined polytabloid module; no desired coefficient is installed as its character.

For the full weighted HSW application, this pointwise equality applies to every decreasing even triple r of total 2n and to the rectangle (n,n,0) for every n at least one, including odd n. Replace each coefficient in the two owning weighted expressions by the actual trace. The outer weight is the reciprocal of z_lambda=product k^m_k times m_k factorial. Ev independently replaces each part occurrence a by 2a or by (a,a), retaining duplicate resulting lists; the first expression also has (-1) to the resulting list length. Full cycle lists retain all one-cycles. The weighted coefficient derivation in the owning HemmerStraubWestrem Scribe uses the existing C2 centralizer owner and LatticeHalfFockChargedCoefficients.solution_unique and gives both averages binomial(n/2+2,2) for even n and zero for odd n. The pointwise bridge transports that same derivation to these actual traces; it imposes no bound on n or on the cycle-list length.

**Theorem 1.1 (Strict double coefficients of the Cauchy kernel).**

$$\forall u \in \operatorname{NatTriple},\; \forall v \in \operatorname{NatTriple},\; (\operatorname{strictlyDecreasing}\left(u\right)) \Rightarrow ((\operatorname{strictlyDecreasing}\left(v\right)) \Rightarrow (\operatorname{doubleKernelCoefficient}\left(u, v\right) = \operatorname{kroneckerDelta}\left(u, v\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.cauchy_coefficient_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

doubleWeight(u,v) places u on the X variables and v on the Y variables. doubleVandermonde is Delta(X)Delta(Y). cauchyKernel is the product of the nine labelled edge series.

**Theorem 1.2 (The finite signed contingency identity).**

$$\forall n \in \operatorname{Nat},\; \forall r \in \operatorname{NatTriple},\; \forall q \in \operatorname{NatTriple},\; (\operatorname{totalEq}\left(r, n\right)) \Rightarrow ((\operatorname{decreasing}\left(r\right)) \Rightarrow ((\operatorname{decreasing}\left(q\right)) \Rightarrow (\operatorname{signedContingencyGram}\left(n, r, q\right) = \operatorname{kroneckerDelta}\left(r, q\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.signedContingencyGram_eq_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The total hypothesis is sum(r)=n. The formula also permits a different total for q; when r differs from q the value is zero. Both triples decrease weakly.

**Theorem 1.3 (The actual same-shape ordinary trace formula).**

$$\forall n \in \operatorname{Nat},\; \forall r \in \operatorname{NatTriple},\; \forall rho \in \operatorname{Partition}\left(n\right),\; \forall g \in \operatorname{PermFin}\left(n\right),\; \forall tau \in \operatorname{ListNat},\; (\operatorname{totalEq}\left(r, n\right)) \Rightarrow ((\operatorname{decreasing}\left(r\right)) \Rightarrow ((\operatorname{hasFullConjugacyPartition}\left(g, rho\right)) \Rightarrow ((\operatorname{multisetEqParts}\left(tau, rho\right)) \Rightarrow (\operatorname{ordinarySpechtTrace}\left(\operatorname{tripleShape}\left(r\right), g\right) = \operatorname{complexIntCast}\left(\operatorname{HSWfrobChar}\left(r, tau\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.ordinaryTrace_eq_frobChar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The hypotheses identify the complete conjugacy partition of g and the complete multiset of tau. tripleShape sorts the three row sizes and deletes only zero parts, retaining equal parts with their multiplicity.

To consume the bridge in actual finite character sums, use spechtCharValue: its existing ordinaryTrace theorem certifies the actual trace at the complete cycle partition. Every Ev list has total 2n and positive parts, by induction on the original list. Construct evPartition with exactly that multiset, without sorting away repetitions or dropping one-cycles. The signed even-row sum uses each attached triple in R3(2n), whose total and decreasing hypotheses come directly from its membership. The rectangle sum uses (n,n,0). Apply the class-value bridge term by term in both sums. The existing HSW.result then gives their equality for each partition lambda. Multiplying by the literal reciprocal zPartition(lambda) and summing over lambda gives equality of the two ordinary weighted averages. The two evaluated consumers below retain the coefficient application inside the rectangular ordinary average and transport its value to the signed ordinary average.

**Theorem 1.4 (Actual class values and alternant coefficients).**

$$\forall n \in \operatorname{Nat},\; \forall r \in \operatorname{NatTriple},\; \forall rho \in \operatorname{Partition}\left(n\right),\; \forall tau \in \operatorname{ListNat},\; (\operatorname{totalEq}\left(r, n\right)) \Rightarrow ((\operatorname{decreasing}\left(r\right)) \Rightarrow ((\operatorname{multisetEqParts}\left(tau, rho\right)) \Rightarrow (\operatorname{spechtCharValue}\left(\operatorname{tripleShape}\left(r\right), rho\right) = \operatorname{HSWfrobChar}\left(r, tau\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.spechtCharValue_eq_frobChar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The class value is the trace of the independently constructed same-literal-shape complex Specht module. The partition rho is the full multiset of tau.

**Theorem 1.5 (Both actual Ev sums consume the bridge).**

$$\forall n \in \operatorname{Nat},\; \forall lambda \in \operatorname{Partition}\left(n\right),\; \operatorname{signedEvSpechtSum}\left(lambda\right) = \operatorname{signedCoefficientEv}\left(lambda\right) \land \operatorname{rectangleEvSpechtSum}\left(lambda\right) = \operatorname{rectangleCoefficientEv}\left(lambda\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.evSpechtSums_eq_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

signedCoefficientEv and rectangleCoefficientEv abbreviate the two existing inner expressions in HSW.claim, with duplicate list outcomes retained. The signed sum ranges over every attached element of R3(2n).

**Theorem 1.6 (The original per-partition ordinary Ev identity).**

$$\forall n \in \operatorname{Nat},\; (\operatorname{positive}\left(n\right)) \Rightarrow (\forall lambda \in \operatorname{Partition}\left(n\right),\; \operatorname{signedEvSpechtSum}\left(lambda\right) = \operatorname{rectangleEvSpechtSum}\left(lambda\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.ordinaryEv_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The two sums are defined using actual spechtCharValue of the complete Ev partitions; n is at least one and lambda is arbitrary.

**Theorem 1.7 (Equality of both actual reciprocal-centralizer averages).**

$$\forall n \in \operatorname{Nat},\; (\operatorname{positive}\left(n\right)) \Rightarrow (\operatorname{weightedSignedOrdinaryEv}\left(n\right) = \operatorname{weightedRectangleOrdinaryEv}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.ordinaryWeightedEv_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

weightedSignedOrdinaryEv and weightedRectangleOrdinaryEv sum over all partitions lambda of n with reciprocal zPartition(lambda) in the rationals. This equality supplies the signed evaluated consumer.

**Theorem 1.8 (The evaluated rectangular ordinary average).**

$$\forall n \in \operatorname{Nat},\; (1 \le n) \Rightarrow (\sum_{lambda \in \operatorname{Partition}\left(n\right)} (\frac{1}{\operatorname{rationalNatCast}\left(\operatorname{zPartition}\left(lambda\right)\right)} \cdot \operatorname{rationalIntCast}\left(\operatorname{rectangleEvSpechtSum}\left(lambda\right)\right)) = \operatorname{ite}\left(\operatorname{Even}\left(n\right), \operatorname{rationalNatCast}\left(\operatorname{NatChoose}\left(\operatorname{NatDiv}\left(n, 2\right)+2, 2\right)\right), 0\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.ordinaryWeightedRectangleEv_evaluated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

For every n at least one, sum over all partitions lambda of n the reciprocal of zPartition(lambda), cast to the rationals, times rectangleEvSpechtSum(lambda), also cast to the rationals. The result is the natural binomial coefficient choose(n / 2 + 2, 2), cast to the rationals, when Even(n), and zero otherwise. Nat.div supplies the quotient. The local Laurent input at positive k is 2(z^k+1+z^(-k)); deleting a marked part uses partitionWithPartEquiv and zExponent_add_single, with index k-1. The local partition series A has constant coefficient one and derivative A times the positive-cycle driver. Apply the existing LatticeHalfFockChargedCoefficients.solution_unique directly with Ring = LaurentPolynomial(rationals), first = mk(A), second = the three rescaled invOneSubPow factors of order two, and driver = mk(k maps to 2(z^(k+1)+1+z^(-k-1))). HasUniqueDiv.of_module_rat supplies additive torsion freeness. No new ODE uniqueness theorem or alternate character is defined. The owning right_coefficient and ev_right, followed by evSpechtSums_eq_coefficients, identify the rectangle sum with the constant term of (1-z^(-1)) times the Laurent product. The two geometric factors give the diagonal square sequence and adjacent consecutive sequence; their difference cancels the factor (1-t)^(-2), leaving (1-t^2)^(-3). All sums and products are formal and finite in each degree.

**Theorem 1.9 (The evaluated signed ordinary average).**

$$\forall n \in \operatorname{Nat},\; (1 \le n) \Rightarrow (\sum_{lambda \in \operatorname{Partition}\left(n\right)} (\frac{1}{\operatorname{rationalNatCast}\left(\operatorname{zPartition}\left(lambda\right)\right)} \cdot \operatorname{rationalIntCast}\left(\operatorname{signedEvSpechtSum}\left(lambda\right)\right)) = \operatorname{ite}\left(\operatorname{Even}\left(n\right), \operatorname{rationalNatCast}\left(\operatorname{NatChoose}\left(\operatorname{NatDiv}\left(n, 2\right)+2, 2\right)\right), 0\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.ordinaryWeightedSignedEv_evaluated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The same value holds for the sum over all partitions with the identical rational reciprocal zPartition weight and signedEvSpechtSum. ordinaryWeightedEv_identity transports the rectangular evaluation, retaining every weakly decreasing even triple of total 2n, zeros and equal rows included, every full positive cycle partition including ones, and every duplicate occurrence-wise Ev outcome. Both endpoints have precisely n : Nat and 1 <= n as parameters. The even/odd split introduces no extra assumption. Both evaluated endpoints compile at Lean 4.35.0 and the repository Mathlib pin with axiom closure propext, Classical.choice and Quot.sound. Their dependent-family audit proofs retain the entire unbounded weighted law; current binding is assessed by the scoped report. The remaining public-helper audit is tracked in issue 24542.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.cauchy_coefficient_delta`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.evSpechtSums_eq_coefficients`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.ordinaryEv_identity`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.ordinaryTrace_eq_frobChar`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.ordinaryWeightedEv_identity`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.ordinaryWeightedRectangleEv_evaluated`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.ordinaryWeightedSignedEv_evaluated`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.signedContingencyGram_eq_delta`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowCauchy.spechtCharValue_eq_frobChar`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtThreeRowMixed](SpechtThreeRowMixed.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2](../PerfectMatchings/DeformedJucysMurphyC2.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCoefficients](../../VertexAlgebra/LatticeHalfFockChargedCoefficients.md)
