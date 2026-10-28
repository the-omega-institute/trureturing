# Two opposite LARGE labels: the complete three-case exchange

## Abstract

The actual two-edge expanding path and two later opposite LARGE labels admit a literal three-case exchange, with every gate and physical inventory derived.

The native source geometry, the arbitrary-endpoint SMALL ordering theorem and the physical inventory balances produce explicit competitors in each of three exhaustive cases. The source is never replaced by an abstract signed row.

**Theorem 1.1 (Derive the physical source geometry).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange.native_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange.native_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For k>=3 and t natural, s is exactly SourceWidth.actualSource on Fin(k), N=2^k-1, Q=2^(k-2), C=N/2=2Q-1. hit(k,j,p) is the j-fold iterate of finRotate(k). Assume only Q<=|s(hit(k,1,p))| and N<3|s(p)|. Then p, n=hit(k,1,p), x=hit(k,2,p) are LARGE. In orientation chosen by the sign of s(p), their values are +P,-D,+r, where P=|s(p)|, D=|s(n)|, r=|s(x)|; D=N-2P, r=4P-N, D<P<r, and 2P<=C+Q. The inserted energy 3^P+3^D is strictly less than 3^r.

hit_phase identifies the exact physical rotate iterate with the parent's modulo-k phase; phase_step includes the seam. Expansion forces p LARGE, and the genuine n-LARGE assumption supplies the other LARGE path step. The parent expanding_path_estimates supplies the strict energy estimate. Centered bounds imply r<=C and hence the budget. None of these equations, LARGE conclusions, gates or energy estimates is an input callback.

**Theorem 1.2 (Exclude Q-1 throughout the actual physical source).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange.actual_source_ne_q_sub_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange.actual_source_ne_q_sub_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural k,t with k>=3, a physical p with s(p)>0, Q<=|s(hit(k,1,p))| and N<3|s(p)|, every physical label i satisfies s(i)!=Q-1. A putative occurrence generates the actual cycle Q-1,C-1,-3,-6,...,-3*2^(k-3). Native geometry gives N<3P and 2P<=3Q-1 for P=s(p). When Q>=4 neither positive cycle value can be P; when Q=2 these inequalities already contradict one another. Every remaining cycle value is negative.

The phase covers all physical Fin k labels in fewer than k steps, including the seam and sources with shorter numerical period. No numerical source injectivity is assumed. Consequently every positive SMALL value is at most Q-2 by integer arithmetic. This source exclusion does not establish full C3.1 or arbitrary A transport.

**Theorem 1.3 (The three literal competitors and full physical accounting).**

Lean statement: `D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange.actualSource_twoOpposite_twoStep_full`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange.actualSource_twoOpposite_twoStep_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact native hypotheses are k>=3, natural t, physical p,z1,z2 and lists A,T0,T1,T2. The actual W=A++[x]++T0++[z1]++T1++[z2]++T2 is Nodup and all its zero-start natural takes lie in [0,C]. Both p and n are unused in ALL W. n is LARGE and N<3|s(p)|. Each zj is LARGE and s(p)*s(zj)<0. Every T0,T1,T2 label is SMALL, meaning |s|<Q. Appending p or n to the ORIGINAL W fails Legal. No other blocking, unit, numerical distinctness, full numerical period, source-profile premise, prelegal competitor, subset support, nonvacuity control, or global-minimum premise is present.

Write F1=A++[x]++T0++[z1], F2=F1++T1++[z2]. Let v be the old departure before z2 in the positive coordinate: actual height for s(p)>0, C minus actual height for s(p)<0. Output L.Perm(T0++T1), E.Perm(T2), and V=V2 with three literal branches. If Z1>=P, V=F1++[p,n]. Otherwise if v<P, V=F2++[p]. Otherwise V=A++[p,n]++L++[z1]++E. Thus Z1=P belongs to A and v=P to C. A and all retained physical old prefixes remain unchanged in both orientations.

In the positive coordinate put a=height(A), b=a+P-D and y=a+r. Old x legality and r=2P-D give 0<=a<=b<=a+P<=y<=C, checking BOTH inserted path prefixes. A: old arrival w1 after z1 lies in [0,C-Z1], so w1+P and w1+P-D are legal. B: old arrival w2=v-Z2 is nonnegative and w2+P<2P-Z2<=2P-Q<=C. These branches retain every prefix through z1 or z2 respectively. Their final heights are w1+P-D and w2+P.

C: the specific full SMALL list T0++T1 has endpoint f=b+sum(T0++T1)=v+Z1-P. Since v>=P and Z1<P, Z1<=f<=C and f-Z1=v-P is legal. exists_order_between produces L using exactly those labels, with no subset choice. Keeping ALL T2 requires e=h+Z2-P. Only old p/n append blocking is used: h>C-P and h<D. Consequently e>C+Z2-2P>=C+Q-2P>=0 and e<D+Z2-P<Z2<=C. The SAME generic theorem orders all T2 into E. Its pairwise compatibility follows from opposite SMALL magnitudes summing to at most 2Q-2<C.

Reflection is a proof coordinate only: coord(negative,C,h)=C-h, oriented increments are -s, and the oriented whole word starts at C when the actual word starts at zero. strip_coordinate proves the equivalence and converts back to original zero-start InStrip. It never asserts the reflected word starts at zero. All prefix bounds are for every natural take, including empty and overlength takes. Actual negative C endpoint is h+P-Z2, and actual prefixes of A, F1, F2 remain their original heights.

Let S=W.toFinset, Rold=S complement, I the inserted physical list and R the returned physical list. In A, I=[p,n], R=T1++[z2]++T2. In B, I=[p], R=T2. In C, I=[p,n], R=[x,z2]. The proof verifies (V++R).Perm(W++I), I.Nodup, I disjoint from W, and R subset W. This gives V.Nodup and EXACT disjoint partitions Snew=(S minus set(R)) union set(I), Rnew=(Rold minus set(I)) union set(R). It also proves sum(Rnew)=-sum(V) using the physical zero-total source_cycle, and sum(V)+sum(R)=sum(W)+sum(I). Physical labels are never identified by equal numerical values.

MixedSuffixEnergy mass,G,H,U,J are reused unchanged, with J=(G,H,U). Exact additive Nat balances: A gives Gnew+1=Gold, Unew+1=Uold+|T1|+|T2|, Hnew+3^Z2=Hold+3^P+3^D. B gives Gnew+1=Gold, Unew+1=Uold+|T2|, Hnew=Hold+3^P. C gives Gnew=Gold, Unew=Uold, Hnew+3^r+3^Z2=Hold+3^P+3^D. A/B strictly lower G regardless of H or U. C strictly lowers H using the native energy estimate. The conclusion explicitly includes strict J descent.

The unused SMALL set is exactly the disjoint union of its old value and the SMALL part of R: set(T1++T2) in A, set(T2) in B, and empty in C. Thus unused SMALL support is enlarged only by the actual returned SMALL labels; in C it is unchanged. Numerical ties, nonunits, short numerical orbits, seams and zero SMALL steps require no exclusions. The construction handles Z2>D and Z2<=D without terminal dominance as a premise.

Full C3.1, universal favorable-path availability, and full historical population remain OPEN. No minimizer wrapper is supplied.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange.actualSource_twoOpposite_twoStep_full`
- Truth anchor: `D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange.actual_source_ne_q_sub_one`
- Truth anchor: `D5/S3/Combinatorics/Circle/TwoOppositeLargeExchange.native_geometry`
- Dependency: [D5/S3/Combinatorics/Circle/MixedSuffixEnergy](MixedSuffixEnergy.md)
- Dependency: [D5/S3/Combinatorics/Circle/SmallStepOrdering](SmallStepOrdering.md)
