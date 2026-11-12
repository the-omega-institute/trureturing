# Wick-defect inversion

## Abstract

Quantitative inversion from all subfamily Wick deviations to distinct-index pairing defects.

Let D be finite, A a commutative real algebra, ell a real linear functional, Y a centered quadratic family, and f a family of real weights indexed by Fin k. For a label subset U, write V(U) for subsetFamilyMoment, R(U) for subsetDistinctMoment, and W_U(c) for finitePairingPolynomial with edge values c. Thus Delta(U)=R(U)-W_U(R), and the Wick deviation is V(U)-W_U(V). For a partial pairing P, let U(P) be U minus pairingSupport(P), and let T(P) be the product over its edges e of subsetWeightSum(f,e). The result is the repo-derived inequality (501.2) of Theorem 501.3 in FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II. It concerns the finite quadratic model and assumes no positivity or independence.

**Definition 1.1 (Triangular inversion constant).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion.inversionConstant`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion.inversionConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every real C, inversionConstant(C,m), denoted A_m, is defined by strong recursion on the natural order m. It is zero for m<=2. For m>2 it equals 1 plus the sum, over all nonempty partial pairings P of Fin m, of C^(2*card(P))*A_(m-2*card(P)). The entries are nonnegative because every exponent of C is even. Embedding an enumeration of any finite label set U transports its partial pairings bijectively and preserves their sizes, so the same recursion applies directly to the partial pairings of U.

**Definition 1.2 (Largest normalized subfamily Wick deviation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion.wickDeviationSup`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion.wickDeviationSup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For ell, Y, f, a real scale s, and a finite label set U, wickDeviationSup(ell,Y,f,s,U), denoted Omega(U), is the maximum of zero and the values |V(U')-W_(U')(V)|/s^card(U') over U' contained in U with card(U')>=3. Consequently the maximum is zero when there are no such subsets. Under the theorem's positive scale, these are nonnegative normalized deviations. Inclusion of label sets makes Omega monotone.

**Theorem 1.3 (Theorem 501.3: quantitative inversion).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion.pairing_defect_inversion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion.pairing_defect_inversion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type D, commutative real algebra A, natural k, real linear functional ell, family Y, weights f indexed by Fin k, and real a,b,C,H,L,M, assume ell(1)=1, ell(Y(d))=0 and Y(d)^2=a*Y(d)+b*1 for every d. Assume C>=1, H>=L>=1, |a|,|b|<=C*L, card(D)<=C*H, and |f(i,d)|<=1. Set s=sqrt(H*L) and eta=sqrt(L/H)+1/H. Assume |R_r(f(B_1),...,f(B_r))|<=C*s^r for every 2<=r<k and nonempty pairwise disjoint label subsets B_j, where f(B) is the product of the original weights over B. Finally assume M>=0 and pairingDefectConstant(j,C)<=M for every natural j<=k. Then, for every U contained in Fin k, |Delta(U)|<=A_card(U)*(Omega(U)+M*eta)*s^card(U). Here pairingDefectConstant(j,C)=j^j*2^j*2^(j*j)*(C+1)^(j+1), the error constant of quadratic_pairing_defect_transfer; M dominates this constant rather than the smaller error constant displayed in the volume. To prove the estimate, enumerate U and apply the quadratic transfer theorem to its restricted weights. Disjoint label subsets remain nonempty and disjoint after this enumeration, so the same moment hypotheses apply. Transport of moments and partial pairings gives V(U)-W_U(V)=sum_P b^card(P)*T(P)*Delta(U(P))+E_U, with |E_U|<=pairingDefectConstant(card(U),C)*s^card(U)*eta. Each edge weight has absolute value at most card(D), hence |b|^card(P)*|T(P)|<=(C^2*s^2)^card(P). The defect is zero in orders at most two. For higher orders isolate the empty pairing, whose contribution is Delta(U). Every nonempty partial pairing leaves card(U)-2*card(P) labels, strictly fewer than card(U). Strong induction bounds its defect; monotonicity of Omega replaces Omega(U(P)) by Omega(U). The powers of s combine to s^card(U), and the sum of the remaining coefficients is precisely the recursion for A_card(U).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion.inversionConstant`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion.pairing_defect_inversion`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectInversion.wickDeviationSup`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PairingDefectTransfer](PairingDefectTransfer.md)
