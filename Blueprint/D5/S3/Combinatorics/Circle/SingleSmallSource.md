# Single SMALL rigidity and forward cyclic completion

## Abstract

One physical SMALL defect forces an odd native doubling period and an exact profile; its complete forward physical cycle fits the half-modulus strip.

**Theorem 1.1 (Period closure determines the amplitude and every phase).**

$$\forall k \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall a \in \operatorname{Fin}\left(k\right),\; \left(3 \le k \land \left(\operatorname{abs}\left(\operatorname{actualSource}\left(k, t, a\right)\right) < \operatorname{quarter}\left(k\right) \land \left(\forall i \in \operatorname{Fin}\left(k\right),\; i \ne a \Rightarrow \operatorname{Large}\left(k, t, i\right)\right)\right)\right) \Rightarrow \left(\operatorname{mod}\left(k, 2\right) = 1 \land \left(3 \cdot \operatorname{abs}\left(\operatorname{actualSource}\left(k, t, a\right)\right) = \operatorname{half}\left(k\right) \land \left(\forall j \in \mathrm{Nat},\; \left(1 \le j \land j \le k\right) \Rightarrow \left(\operatorname{ite}\left(\operatorname{mod}\left(j, 2\right) = 1, 0 < \operatorname{orientedPhaseSource}\left(k, t, a, j\right), \operatorname{orientedPhaseSource}\left(k, t, a, j\right) < 0\right) \land 3 \cdot \operatorname{orientedPhaseSource}\left(k, t, a, j\right) = \operatorname{ite}\left(\operatorname{mod}\left(j, 2\right) = 1, \operatorname{modulus}\left(k\right), -\operatorname{modulus}\left(k\right)\right) - 2^{j - 1}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/SingleSmallSource.single_small_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k>=3, N=2^k-1, C=N div 2=2^(k-1)-1, Q=2^(k-2), and f(i)=SourceWidth.actualSource(k,t,i)=centered(N,2^i*t) on the physical type Fin(k). The natural parameter t is unrestricted. Assume a is SMALL, |f(a)|<Q, and each physical i different from a is LARGE, Q<=|f(i)|. No injectivity, coprimality, or least-period assumption is supplied.

phase(a,j) is the existing forward physical label (a.val+j) mod k. Its omitted argument is a proof of 0<k. orientedPhaseSource(k,t,a,j) abbreviates orient(decide(f(a)<0), f(phase(a,j))); ite denotes the ordinary conditional. These are display abbreviations, not new Lean definitions. The profile and its strict sign clause hold for every 1<=j<=k, including the returning endpoint.

Orient signs so w(0)=s=|f(a)|. The SMALL step has no wrap and w(1)=2s. Since phase(a,1) is a different physical label and LARGE, s is positive. For phases 1 through k-1, centered bounds and LARGE force a sign change at each step. A simultaneous induction proves the sign alternation and 3w(j)=(N for odd j, -N for even j)+2^(j-1)*(6s-N). The physical return w(k)=s forces k odd. Writing A=2^(k-1), closure gives 3s=N+A(6s-N), while N=2A-1 and C=A-1. Cancellation of positive N yields 3s=C and 6s-N=-1.

The sign changes belong to the native centered doubling dynamics, including its return across the physical seam. There is no upper bound on k in the statement or on the number k-1 of LARGE labels. This restricted native-source result leaves arbitrary-source Circle C3.1 open.

**Theorem 1.2 (One complete forward physical permutation at half width).**

$$\forall k \in \mathrm{Nat},\; \forall t \in \mathrm{Nat},\; \forall a \in \operatorname{Fin}\left(k\right),\; \left(3 \le k \land \left(\operatorname{abs}\left(\operatorname{actualSource}\left(k, t, a\right)\right) < \operatorname{quarter}\left(k\right) \land \left(\forall i \in \operatorname{Fin}\left(k\right),\; i \ne a \Rightarrow \operatorname{Large}\left(k, t, i\right)\right)\right)\right) \Rightarrow \left(\operatorname{Perm}\left(\operatorname{path}\left(\operatorname{ite}\left(0 < \operatorname{actualSource}\left(k, t, a\right), a, \operatorname{phase}\left(a, 2\right)\right), k\right), \operatorname{finRange}\left(k\right)\right) \land \left(\operatorname{Nodup}\left(\operatorname{path}\left(\operatorname{ite}\left(0 < \operatorname{actualSource}\left(k, t, a\right), a, \operatorname{phase}\left(a, 2\right)\right), k\right)\right) \land \left(\operatorname{toFinset}\left(\operatorname{path}\left(\operatorname{ite}\left(0 < \operatorname{actualSource}\left(k, t, a\right), a, \operatorname{phase}\left(a, 2\right)\right), k\right)\right) = \operatorname{univ}\left(\operatorname{Fin}\left(k\right)\right) \land \left(\operatorname{InStrip}\left(\operatorname{actualSource}\left(k, t\right), \operatorname{half}\left(k\right), 0, \operatorname{path}\left(\operatorname{ite}\left(0 < \operatorname{actualSource}\left(k, t, a\right), a, \operatorname{phase}\left(a, 2\right)\right), k\right)\right) \land \left(\left(\forall n \in \mathrm{Nat},\; 0 \le \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(k, t\right), \operatorname{take}\left(n, \operatorname{path}\left(\operatorname{ite}\left(0 < \operatorname{actualSource}\left(k, t, a\right), a, \operatorname{phase}\left(a, 2\right)\right), k\right)\right)\right)\right) \land \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(k, t\right), \operatorname{take}\left(n, \operatorname{path}\left(\operatorname{ite}\left(0 < \operatorname{actualSource}\left(k, t, a\right), a, \operatorname{phase}\left(a, 2\right)\right), k\right)\right)\right)\right) \le \operatorname{half}\left(k\right)\right) \land \operatorname{sum}\left(\operatorname{map}\left(\operatorname{actualSource}\left(k, t\right), \operatorname{path}\left(\operatorname{ite}\left(0 < \operatorname{actualSource}\left(k, t, a\right), a, \operatorname{phase}\left(a, 2\right)\right), k\right)\right)\right) = 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/SingleSmallSource.single_small_forward_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed word is explicit: start at a when f(a)>0, and at phase(a,2) when f(a)<0, then take all k forward physical labels. Zero at a is ruled out by rigidity. path(start,k) is the existing map of phase(start,j) over j=0,...,k-1. The theorem proves permutation equivalence with finRange(k), Nodup, exhaustive univ, InStrip at height zero and capacity C, every natural take-prefix in [0,C], and full sum zero. It preserves the whole forward LARGE cyclic order, hence also either sign's cyclic queue; there is no reversal.

For the oriented positive source g define the unsigned height v(i)=g(i)+N when g(i)<0, and v(i)=g(i) otherwise. The rigidity profile implies s<=v(i)<=4s on every physical label, v(a)=s, and v(phase(a,2))=4s. Indeed for odd j, 3v_j=N-2^(j-1); for positive even j, 3v_j=2N-2^(j-1). The inequalities 1<=2^(j-1)<=2^(k-1), and 2<=2^(j-1) on positive even phases, give the stated range using N=6s+1 and C=3s. The strict profile signs also exclude zero on every label.

For the original source use its unsigned height u=f+N when f<0 and u=f otherwise. If f(a)>0 then u=v, so a attains the minimum. If f(a)<0 then u=N-v, since no source value is zero, so phase(a,2) attains the minimum. In both cases 0<=u(i)-u(start)<=3s=C. SourceWidth.unsigned_step, path_range and path_sum telescope each forward prefix to this height difference. A natural take uses min(n,k), covering n=0, n=k and n>k; closure gives sum zero.

Physical permutation is proved using finCycle(start).map_finRange_perm. Distinct labels remain distinct occurrences even when their numerical values agree, and no numerical period quotient is used. Any shorter numerical period is handled by the same physical statement rather than excluded by a premise. The package supplies this one-defect completion only: completion for two SMALL labels, the arbitrary-source exchange, and full Circle C3.1 remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/SingleSmallSource.single_small_forward_completion`
- Truth anchor: `D5/S3/Combinatorics/Circle/SingleSmallSource.single_small_rigidity`
- Dependency: [D5/S3/Combinatorics/Circle/MixedSuffixEnergy](MixedSuffixEnergy.md)
