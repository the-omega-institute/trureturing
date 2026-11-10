# Independent shorter orders transport through charged physical blocks

## Abstract

Independent shorter orders transport through charged physical blocks

**Theorem 1.1 (Independent shorter orders transport through charged physical blocks).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicShortening.periodic_shortening_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicShortening.periodic_shortening_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d>=2, 1<=w<=2^(d-1)-1 and m>=2, EVERY OriginalOrder(d,w,alpha) and independently EVERY OriginalOrder(d+1,w,beta) supply the specified full physical chargedWord at k=d*m+1 and U=w*G_m. It has integer total zero and every pair of natural prefix heights differs by at most D=C-(2^(d-1)-w)*G_(m-1)<C. An attained minimum ell<k gives a rotation that is a permutation of finRange(k), has total zero and has every natural take sum in the ORIGINAL interval [0,C], including overlength takes.

Early blocks use exponent r*d+i+1, with actual endpoint -w*G_(r+1). The final label map fixes zero and sends j>0 to (m-1)*d+j. On each beta-prefix the SAME surviving phases give Y=2A-E+w*epsilon and Q=A+w*epsilon-w. A may be negative: the proof uses only 0<=Y<=q-1, 0<=E<=w and epsilon in {0,1}. Integer rounding gives -w<=Q<=q/2-1. Thus all original heights lie in [-w*H,R*(q-1)+(q/2-1)*H]. Minimum rotation reuses ZeroSumWordCount.nonnegative_rotate_of_minimum; segment sums are reused from that same owner. Physical permutations retain repeated values as separate labels. The construction removes periodic shortenings in original length induction, since d and d+1 are both smaller than d*m+1. The general cyclic-primitive shortening branch of C3.1 remains open.

This is a repository derivation of the conditional periodic-shortening construction. The source problem is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, Conjecture 3.1. No literature novelty or solution of its general aperiodic case is asserted.

## Application: conditional joint repetition at the supplied cut

Write s_n(t,i)=actualSource(n,t,i) and M_n=2^n-1. OriginalOrder(n,t,l) means that l is a permutation of ALL physical labels 0,...,n-1, its integer source total is zero, and for EVERY h in the natural numbers the sum of s_n(t,i) over take(h,l) lies in [0,floor(M_n/2)]. RunFirstEarTransport.earWord(n,l,j) inserts the fresh label n after take(j,l), retaining every old label in order. Fix d>=2, 1<=w<=2^(d-1)-1, m>=2, ANY alpha and 0<=j<=d, with BOTH supplied witnesses OriginalOrder(d,w,alpha) and OriginalOrder(d+1,2w,earWord(d,alpha,j)). Put q=2^d, G=geom(d,m)=1+q+...+q^(m-1), K=d*m and U=w*G. Define tau by copying alpha in the physical block order m-1,0,...,m-2, replacing i in block r by the distinct label r*d+i.

The conditional consequence is OriginalOrder(K,U,tau) AND OriginalOrder(K+1,2U,earWord(K,tau,j)). Both use this exact tau and the identical NUMERIC cut j, including j=0 and j=d. Thus both source totals are zero and both original strips bound every prefix, including empty, complete and overlong takes. The map (r,i) to r*d+i is a bijection onto the K physical labels; equal source values never identify occurrences. The derivation below applies the existing prefix and scaling results.

For the old source, ThreeRowSource.multiplier_identity and repeated_source give M_K=G*(q-1), U<M_K and s_K(U,r*d+i)=G*s_d(w,i). ThreeRowSource.scaled_sum and scale_strip therefore give each copied alpha total zero and strip cap G*B<=floor(M_K/2), where B=q/2-1. TwoRunSource.concatenate_zero joins the blocks in the stated order; SourceWidth.inStrip_prefix includes every natural take-prefix. Reduction modulo d establishes the value identity only; the physical list still contains all K distinct labels.

For the new source, SourceWidth.centered_full_period gives s_n(2t,i)=s_n(t,rho_n(i)), where rho_n is cyclic successor WITHIN dimension n. Set beta=map(rho_(d+1),earWord(d,alpha,j)); the second supplied witness gives OriginalOrder(d+1,w,beta). Define L(0)=0 and L(t)=(m-1)*d+t for 1<=t<=d. The successor image map(rho_(K+1),earWord(K,tau,j)) is exactly tail++early, with tail=map(L,beta) and early the copies of alpha at labels r*d+i+1 for r=0,...,m-2. Indeed successor sends each old label r*d+i to r*d+i+1 and the fresh label K to 0; in the first block these are L(i+1) and L(0). Since alpha has length d and j<=d, the literal insertion stays inside that first block, including its two endpoints. No correspondence between different moduli is assumed.

Put H=geom(d,m-1), R=q^(m-1), V=R*(q-1)+B*H, D=V+w*H and C=(q-1)*G=2^K-1=floor(M_(K+1)/2). PeriodicShortening.beta_prefix_bound bounds every tail prefix in [0,D] after cancelling its -w*H translation. PeriodicShortening.early_blocks gives early total -w*H and InStrip cap D starting at w*H. The identities G=H+R, R=(q-1)*H+1 and 2B=q-2 give the exact margins D-(w*H+2*G*B)=R-B*H=(B+1)*H+1>0 and C-D=(B+1-w)*H>0. Thus V>=2*G*B and D<=C. PeriodicShortening.chargedWord_perm also makes tail++early a full physical permutation, so ZeroSumSubsets.source_cycle and the early total force tail total +w*H. PeriodicShortening.strip_of_prefix, SourceWidth.inStrip_append and inStrip_prefix join at that exact height and end at zero, bounding every new prefix by C. The within-dimension successor identity then returns the literal ear to seed 2U.

For TwoNegativeJointLift.actualSource_two_negative_joint_lift this application retains a,b>=2 and b<a, with d=a+b and w=1+2^a: m=2 gives cyclic gaps (a,b,a,b), and general m gives 2m occupied binary positions. Other supplied base joint witnesses can be repeated with all their hypotheses intact. This conditional consequence does not construct both base witnesses for arbitrary sources. Full Circle C3.1 and unrestricted four-gap physical J remain OPEN. No external novelty, finite-search completeness or official acceptance is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicShortening.periodic_shortening_transport`
- Dependency: [D5/S1/Words/Compositions/ZeroSumWordCount](../../../S1/Words/Compositions/ZeroSumWordCount.md)
- Dependency: [D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic](PeriodicShorteningArithmetic.md)
