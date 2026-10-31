# Signed three-row characters and the ordinary trace norm criterion

## Abstract

Signed three-row characters and the ordinary trace norm criterion

Let delta=(2,1,0) and Delta(X)=(X0-X1)(X0-X2)(X1-X2). The signed ordered-colouring character Theta is defined in the preceding Gram construction. The determinant with entry Xi raised to delta(s) in row s and column i is Delta. Its signed expansion gives the monomial with i-th exponent delta(s(i)); extraction at r+delta leaves the integer margin r(i)-i+s(i). If this is negative in any coordinate, the corresponding coefficient and colouring count are both zero. Thus Theta(r,g) equals the existing HSW.frobChar(r,tau) whenever tau has the full partition of g. All parts equal to one and all repeated parts are retained.

The ordinaryTrace criterion concerns the existing complex polytabloid Specht module with literal partition mu. It requires two scalar hypotheses: signedContingencyGram(n,r,r)=1 and the sum over all g of chi_mu(g)Theta(r,g)=n factorial. Here chi_mu is the integral trace of this same Specht module. Actual character orthogonality gives the sum of chi_mu(g) squared equal to n factorial because g and its inverse are conjugate in the symmetric group. The joint Gram identity supplies the same square sum for Theta from the first hypothesis. Expanding the square of chi_mu-Theta gives a sum of nonnegative integer squares equal to zero. Each square vanishes, yielding pointwise equality. Positivity is used over the integers; no positivity of a complex bilinear form is assumed.

For an unconditional same-shape formula, r must be a decreasing natural triple with sum n and mu the partition obtained by deleting its zero parts. The finite Cauchy obligation is signedContingencyGram(n,r,q)=1 when r=q and zero otherwise, for every decreasing q of total n. Its independent generating-function argument uses six formal variables and K(X,Y)=product over i,j of (1-XiYj) inverse. The coefficient at margins a,b is exactly C(n,a,b). Multiplying by Delta(X)Delta(Y) changes that coefficient into the signed contingency sum at r+delta,q+delta.

The algebraic identity Delta(X)Delta(Y)K(X,Y)=det((1-XiYj) inverse) follows after clearing the nine denominators. Its numerator is the sum over permutations t of sign(t) times product over i and j unequal to t(i) of (1-XiYj). This is alternating in each triple and has degree at most two in each single variable, so it is a scalar times the two Vandermonde factors. At X2=Y2=0, subtracting the last determinant row from the first two gives X0 X1 Y0 Y1 (X0-X1)(Y0-Y1) after clearing denominators. This is the same specialization of the two Vandermondes, fixing the scalar to one.

In the determinant expansion, the monomial with exponents u=r+delta and v=q+delta can occur in the term t exactly when u(i)=v(t(i)) for every i. Both triples are strictly decreasing. Equality of their unordered entries therefore forces u=v and the increasing matching t to be the identity. That term has coefficient one. This proves the finite Cauchy obligation independently of Specht characters or Schur orthogonality. Every coefficient in question has each total degree n+3, so truncating each geometric series after degree n+3 leaves it unchanged. There is no restriction n at most three.

The mixed-pairing obligation uses dominance. For k=1,2,3, the sum of the first k shifted entries is the sum of the first k entries of r plus the sum of s(i)-i over i less than k. The latter is nonnegative because the k distinct nonnegative values s(i) have sum at least 0+...+(k-1). If every proper-prefix increment is zero then each initial subset is preserved and s is the identity. Otherwise one increment is positive. Sorting a nonnegative shifted triple can only increase its prefix sums. Its sorted positive-part partition then strictly dominates mu. Consequently mu does not dominate that partition; the existing actual Specht-to-Young Hom vanishing forces the mixed pairing to be zero. The identity shift has the same literal partition and the existing diagonal Hom dimension is one. Negative shifts contribute zero. This proves the required mixed scalar sum once the ordered-colouring and literal Young-subgroup identification is supplied.

For the HSW application, apply the pointwise formula to every nonincreasing even-part triple r of total 2n, padded by zeros, and also to (n,n,0) for every n at least one, including odd n. Substitute it in both existing weighted coefficient expressions. The outer sum is over every partition lambda of n with weight reciprocal z_lambda, where z_lambda is product over k of k raised to its multiplicity times the factorial of that multiplicity. Ev(lambda) replaces each occurrence a independently by 2a or by the pair (a,a), retaining duplicate resulting lists. The first expression also has the sign (-1) raised to the resulting list length and the sum over all even-part triples. The second uses the rectangle (n,n,0). Reusing the coefficient owner gives each average equal to binomial(n/2+2,2) for even n and zero for odd n. The two scalar obligations above, their same-label row identification, and this final substitution are required for that unconditional application; the criterion itself retains its explicit hypotheses.

**Theorem 1.1 (The signed character equals the exact alternant coefficient).**

$$\forall n \in \operatorname{Nat},\; \forall r \in \operatorname{NatTriple},\; \forall rho \in \operatorname{Partition}\left(n\right),\; \forall g \in \operatorname{PermFin}\left(n\right),\; \forall tau \in \operatorname{ListNat},\; (\operatorname{hasFullConjugacyPartition}\left(g, rho\right)) \Rightarrow ((\operatorname{multisetEqParts}\left(tau, rho\right)) \Rightarrow (\operatorname{Theta}\left(n, r, g\right) = \operatorname{HSWfrobChar}\left(r, tau\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowVirtual.virtualCharacter_eq_frobChar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

The two hypotheses identify the full conjugacy partition of g and the full multiset of tau. No degree or positivity hypothesis on r is needed for this coefficient comparison.

**Theorem 1.2 (A sufficient finite norm criterion for the actual Specht trace).**

$$\forall n \in \operatorname{Nat},\; \forall mu \in \operatorname{Partition}\left(n\right),\; \forall rho \in \operatorname{Partition}\left(n\right),\; \forall r \in \operatorname{NatTriple},\; \forall g \in \operatorname{PermFin}\left(n\right),\; \forall tau \in \operatorname{ListNat},\; (\operatorname{signedContingencyGram}\left(n, r, r\right) = 1) \Rightarrow ((\operatorname{mixedSpechtThetaSum}\left(mu, r\right) = \operatorname{intNatCast}\left(\operatorname{factorial}\left(n\right)\right)) \Rightarrow ((\operatorname{hasFullConjugacyPartition}\left(g, rho\right)) \Rightarrow ((\operatorname{multisetEqParts}\left(tau, rho\right)) \Rightarrow (\operatorname{ordinarySpechtTrace}\left(mu, g\right) = \operatorname{complexIntCast}\left(\operatorname{HSWfrobChar}\left(r, tau\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/SpechtThreeRowVirtual.ordinaryTrace_eq_frobChar_of_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Tau Ceti contributors (2026). *TauCeti partition-indexed polytabloid Specht construction*. URL: <https://github.com/TauCetiProject/TauCeti/tree/5a01f5fe3621126cccf9ba22e700493cbc7b7156>.

*Commentary.*

ordinarySpechtTrace is LinearMap.trace over Complex of the action of the existing spechtModuleComplex(mu); mixedSpechtThetaSum is the sum of its integral character times Theta. The criterion uses genuine actual self-orthogonality and the finite joint Gram identity, without defining the Specht module or its character by the desired coefficient.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowVirtual.ordinaryTrace_eq_frobChar_of_gram`
- Truth anchor: `D5/S3/Combinatorics/Partitions/SpechtThreeRowVirtual.virtualCharacter_eq_frobChar`
- Dependency: [D5/S3/Combinatorics/Partitions/SpechtThreeRowGram](SpechtThreeRowGram.md)
