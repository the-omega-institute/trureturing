# Actual Cloitre Unweighted Cone

## Abstract

An unweighted cone bounds every actual upper-anchor deficit at least five under the complete conditional source hypotheses.

F is the Fibonacci sequence with F(0)=0 and F(1)=1. Put phi=(1+sqrt(5))/2 and G(n)=floor((n+1)/phi). C is the actual positive-index Cloitre sequence with C(1)=C(2)=1. Its legal domain is D(N)=[1,N-1], its inner map is T(N,x)=N-C(x), and its orbit X(N,i) starts at N-1. The prescribed depth is d(N)=C(N-1), the selected point is g(N)=X(N,d(N)), and C(N)=C(g(N))+C(N-g(N)) for N>=3. Put Q(m,t)=F(m-1)-C(F(m)-t) on the full natural closed block 0<=t<=F(m-2). The upper cap makes Q the exact nonnegative integer difference. It is distinct from the golden excess C(n)-G(n).

**Theorem 1.1 (Unweighted cone on every natural closed block).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualUnweightedCone.full30_2`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CloitreActualUnweightedCone.full30_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hyp24_1(U) includes the complete inherited Hyp21_1: the finite ratio condition 22877*C(n)<=15225*n for 16384<=n<=131071; the full golden base and equality classification for 1<=n<=65535; and prescribed periodic entry for 3<=N<=52. The golden base states G(n)<=C(n), with equality implying n=F(j) or F(j)+1 for some j>=2, n+1=F(j) for an odd j>=3, or n in {11,24,25,59}. For every positive n, the global bounds are 1<=C(n) and G(n)<=C(n)<=U(n)<=n. The upper function satisfies U(1)=1, the piecewise formula U(n)=min(n-F(j-2),F(j)) on F(j)<=n<F(j+1) for j>=3, and monotonicity and increments U(n)<=U(n+1)<=U(n)+1 on positive indices. For j>=2, U(F(j))=C(F(j))=G(F(j))=F(j-1); for j>=3, C(F(j)+1)=G(F(j)+1)=F(j-1)+1. For every q>=6 and t>=0, the right collar [F(q-1),F(q-1)+t] is legal and invariant under T(F(q)+t), captures every legal orbit, and contains every legal periodic point. For each N>=3, the earliest periodic entry of X(N,i) precedes or equals d(N). Hyp24_1 also includes C(F(j)-1)=F(j-1) for j>=5, and for j>=6 and 0<=b<=F(j-1), with N=F(j+1)-b, the collar [F(j)-b,F(j)] intersected with D(N) is invariant under T(N) and captures every legal orbit. Every legal periodic point x of T(N) satisfies max(F(j-1),F(j)-b)<=x and x<=min(F(j),F(j)+F(j-3)-b).

Two additional finite full-block conditions are required. For every v<=F(18), Q(20,v)<=2 exactly when v<=35; when v>35, 3<=Q(20,v)<=max(3,v-36). For every v<=F(19), Q(21,v)<=3 exactly when v<=45; when v>45, 4<=Q(21,v)<=max(4,v-46). These conditions and the inherited foundations are premises; no instance of them is asserted.

For all natural m>=21 and all 0<=t<=F(m-2), Q(m,t)>=5 implies Q(m,t)+4*m<=t+38. Equivalently, for the exact signed upper-anchor difference, t-Q(m,t)>=4*m-38.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualUnweightedCone.full30_2`
- Dependency: [D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau](CloitreActualLeftPlateau.md)
