# Odd-half negative-parent exchanges

## Abstract

An actual odd-half negative parent gives a strict physical exchange, either by four fresh LARGE insertions or by reusing its old prefix occurrence.

Let k>=3, t be natural, rho=finRotate k, N=2^k-1=4Q-1 and C=2Q-1. The centered dyadic source f(i)=s(k,t,i) is on physical labels Fin k and its complete physical source has sum zero. Legal means physical Nodup and every natural take-prefix mass from ORIGINAL zero in [0,C], including zero and overlength takes. LARGE means abs(f)>=Q and SMALL means abs(f)<Q. G counts unused LARGE, H sums 3^abs(f) over used LARGE, U counts unused physical labels, and J=(G,H,U) is ordered lexicographically. Equal source values at different labels remain different resources.

Write W=A,[x],T0,[y],T1,[zpen],T2,[z],E, S=T0,T1,T2,E, F=A,[x],T0,[y] and Rsmall=T1,T2,E. The native data are n=rho(p), x=rho(n), f(p)=P>0, f(n)=-D with D>=Q, N<3P, and the actual beta=rho^(-1)(y), gamma=rho^(-1)(beta), a=rho^(-1)(gamma). W is Legal, p,n,beta are absent from ALL W, every S occurrence is SMALL, Q<=-f(z)<=D, and Q<=-f(zpen)<=L=f(beta). Put Y=-f(y)>P, assume Y odd and L mod 4=2, and retain the actual placement gamma in A. With d=P-D, B=C-P, delta=Y-P, a0=mass(A), h=mass(W) and v=mass(F), the residual is B<h<D, (Y+1)/2-d<=v<d, D<=3d-4, 3delta<=d-2 and D>2d+2delta+7. The zpen bound is the surviving odd-first-negative placement bound, not an assertion that an arbitrary first-negative word satisfies it.

Native expanding geometry gives N=2P+D, r=f(x)=2P-D and Q<=D<P<r<=C. Actual inverse-source parity gives 2L=N-Y, 2q=L for q=f(gamma), q odd, and f(a)=-M with 2M=N-q. Thus a is the actual negative LARGE parent, with no positive quarter-parent. Define e=M-P, theta=M-D=d+e, tau=P-L and kappa=e-tau. The source equations and residual imply D<L<P<Y<M<r, 0<theta<Q, 0<e<d, e>B-d, v>e, v>tau and delta+kappa<B-d. Old legality at x also gives 0<=a0<=B-d. These implications supply the new gates; they are not hypotheses requiring a favorable arrival or endpoint.

**Theorem 1.1 (A fresh actual negative parent improves G by two).**

Lean statement: `D5/S3/Combinatorics/Circle/OddHalfParentCore.actualSource_unused_oddHalf_parent_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/OddHalfParentCore.actualSource_unused_oddHalf_parent_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume actual a is absent from ALL W. Keep F literally and set I0=[p,a,beta,n], V0=F,I0 and Ret0=T1,[zpen],T2,[z],E. The four appended heights are v+P, v-e, v-e+L and v-e+L-D. They are in [0,C]: v<d<B controls the first upper gate, v>e controls the negative-parent step, L<P controls the next upper gate and L>D controls the final lower gate. Keeping the original F and appending these gates proves every natural zero-start prefix legal. Distinct values of the four inserted labels prove their mutual physical distinctness; absence is nevertheless required for the actual labels, not for their values.

The whole physical identity is V0,Ret0 permutes W,I0. Ordinary Inventory supplies physical Nodup, disjoint used and complementary unused partitions, exact source and energy balances, and unused source mass -mass(V0). Exactly four LARGE are inserted and two returned, so G(V0)+2=G(W), U(V0)+2=U(W)+length(Rsmall), mass(V0)=v-e+L-D and H(V0)+3^abs(f(zpen))+3^abs(f(z))=H(W)+3^P+3^M+3^L+3^D. The unused SMALL set is remainingSmall(W) disjoint-union set(Rsmall). Strict J descent follows from G regardless of H; H may increase. At a minimum over ALL Legal physical lists, the actual a therefore cannot be unused.

**Theorem 1.2 (Reuse a in its actual old prefix slot).**

Lean statement: `D5/S3/Combinatorics/Circle/OddHalfParentCore.actualSource_used_oddHalf_parent_exchange_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/OddHalfParentCore.actualSource_used_oddHalf_parent_exchange_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose A=U,[a],R and u=mass(U). Either the ENTIRE actual R is compatible, meaning each positive/negative pair has combined magnitudes at most C, or the following explicit test holds at every actual LARGE i in R=R0,[i],R1: its old positive arrival mass(U,[a],R0,[i]), respectively old negative departure mass(U,[a],R0), is at most C-theta. These measurements start from original zero. No supplied new word, order, arrival or endpoint is assumed.

Replace a's old slot by n. Old legality gives M<=u<=C, so the new start u-D lies in [0,C]. The new end a0+theta is automatically legal. For compatible full R, exists_order_between constructs Rstar. Under the old LARGE test, exists_order_preserving_large reorders every COMPLETE SMALL batch and keeps the literal LARGE order. Both lower sides survive the upward shift theta>0. A positive LARGE's old departure and a negative LARGE's old arrival are at most Q-1, hence their shifted sides remain in the strip since theta<Q; the other two upper sides are exactly the explicit test. This checks BOTH departure and arrival of every LARGE and every SMALL join.

The complete T0 is reordered from a0+theta to v+delta+e, both derived legal endpoints. Append [beta,y,p,a]. The four final heights are v+Y+kappa, v+kappa, v+kappa+P and v-tau. The bound delta+kappa<B-d gives the upper gates, while v>tau and v+kappa=v-tau+e give the lower gates. The final word is V=U,[n],Rstar,T0star,[beta,y,p,a], with Rstar permuting R and T0star permuting T0. The literal old U may contain incompatible LARGE and is kept unchanged. The original first negative y remains and actual a is moved to the end exactly once.

Relative to the ORIGINAL W, I=[n,beta,p] and Ret=[x,zpen,z],Rsmall. Thus V,Ret permutes W,I; exactly three LARGE are inserted and three returned. Ordinary Inventory gives used(V)=(used(W) minus set(Ret)) disjoint-union set(I), the complementary unused partition, full source balance, physical Nodup and all natural zero-start prefixes. The exact outputs are G(V)=G(W), U(V)=U(W)+length(Rsmall), remainingSmall(V)=remainingSmall(W) disjoint-union set(Rsmall), mass(V)=v-(P-L) and unused source mass=-(v-(P-L)). The exact energy balance is H(V)+3^r+3^abs(f(zpen))+3^abs(f(z))=H(W)+3^P+3^D+3^L. Since D,L<P<r, the inserted three powers sum to less than 3^r. Hence H(V)<H(W) and J(V)<J(W), independently of U.

**Theorem 1.3 (The old prefix and its literal retained tail).**

Lean statement: `D5/S3/Combinatorics/Circle/OddHalfParentCore.split_word`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/OddHalfParentCore.split_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every physical SourceWord, the complete original W equals F followed by ret0. This exact list identity is consumed by the core exchange and the later relocation strip splits; it identifies no equal-valued labels.

**Theorem 1.4 (Derive the complete native arithmetic gates).**

Lean statement: `D5/S3/Combinatorics/Circle/OddHalfParentCore.arithmetic`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/OddHalfParentCore.arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every SourceWord and its unchanged twenty-field Residual, derive the Arithmetic bundle of native and inverse-source equations, exact LARGE order, original-prefix bounds, strict shift and excess bounds, valley inequalities and all inserted gate bounds. The relocation theorem consumes this same bundle; none of these conclusions is replaced by an availability assumption.

**Theorem 1.5 (Read both old sides of the actual parent).**

Lean statement: `D5/S3/Combinatorics/Circle/OddHalfParentCore.old_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/OddHalfParentCore.old_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary U,R with the actual A equal to U,[a],R, original legality and Arithmetic give the zero-start strip of U, the strip of R starting at mass(U)-M, M<=mass(U)<=C, and the exact endpoint identity mass(U)-M+mass(R)=a0. This physical cut is reused by both relocation orders.

**Theorem 1.6 (One completion for every constructed physical prefix).**

Lean statement: `D5/S3/Combinatorics/Circle/OddHalfParentCore.complete_constructed`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/OddHalfParentCore.complete_constructed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given the unchanged Residual and Arithmetic, a zero-start legal Astar ending at a0+theta, and the physical permutation (Astar,[a])~(A,[n]), reorder the ENTIRE T0 and append [beta,y,p,a]. The result has original-W FullExchange, a counted exactly once, unchanged G, exact U and remaining-SMALL transport, complete source/complement balances, every natural zero-prefix bound, exact H balance and strict H. Both child relocation orders and the reused-parent exchange consume this single proof; no completion is copied.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/OddHalfParentCore.actualSource_unused_oddHalf_parent_exchange_full`
- Truth anchor: `D5/S3/Combinatorics/Circle/OddHalfParentCore.actualSource_used_oddHalf_parent_exchange_full`
- Truth anchor: `D5/S3/Combinatorics/Circle/OddHalfParentCore.arithmetic`
- Truth anchor: `D5/S3/Combinatorics/Circle/OddHalfParentCore.complete_constructed`
- Truth anchor: `D5/S3/Combinatorics/Circle/OddHalfParentCore.old_prefix`
- Truth anchor: `D5/S3/Combinatorics/Circle/OddHalfParentCore.split_word`
- Dependency: [D5/S3/Combinatorics/Circle/LargeSkeletonOrdering](LargeSkeletonOrdering.md)
- Dependency: [D5/S3/Combinatorics/Circle/OddFirstNegativePlacement](OddFirstNegativePlacement.md)
