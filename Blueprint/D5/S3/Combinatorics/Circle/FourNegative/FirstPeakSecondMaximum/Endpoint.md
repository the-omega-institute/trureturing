# All a>d>=max(b,c), with b,c at least two

## Abstract

First peak and second maximum: physical joint lift

**Theorem 1.1 (One physical order and one literal ear cut).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/Endpoint.actualSource_first_peak_second_maximum_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/Endpoint.actualSource_first_peak_second_maximum_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural a,b,c,d with b,c at least two, b and c at most d, and d strictly below a, put k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). A single permutation sigma of the physical Fin k labels and a single natural cut j at most k satisfy OriginalOrder(k,A,sigma) and OriginalOrder(k+1,2A,earWord(k,sigma,j)). Each order includes its literal permutation, total zero and the half-modulus bounds for every natural take-prefix, including empty and overlong prefixes. Equal values retain their distinct labels.

Set n=2^(a-d), y=2^b, z=2^c, t=2^d and D=yz+y+1. The positive heads are A=ntD+1, B=nt^2(y+1)+t+1, L=nzt^2+zt+z+1 and M=tyz+D. The four physical chains start at 0,d,d+c,d+c+b and have lengths d,c,b,a. Their new heads are 2A, Bn=2B-1, Ln=2L-z-1 and Mn=2M-D. The native chain identities give both terminal masses. The old total is zero, the new old-label total is -A, and the fresh label k contributes A.

When b<=c and the last three gaps are not all equal, complementary low-X masks p=n-r and q=r-1 partition precisely the first a-d X labels. A U-mask v and a V-mask w move whole physical occurrences. The terminal bank order is X,U,V,W. Its old seams are A-nM, B-rM-vA, L-rM-vA-wB,0. Its new seams are 2A-nMn, Bn-rMn-2vA, Ln-rMn-2vA-wBn,0. The successors in the two rows are A,B,L,M and A,Bn,Ln,Mn. The equal, twice and separated charts cover respectively c=b, c=b+1 and c>=b+2. Signed quotient and remainder bounds yield the masks and all seam and peak inequalities. For b=c=d the equal-last-three construction supplies the literal cut 3b; other charts use cut zero.

For the ascending allocation put delta=A-nM and H=rM+vA. The required joint inequalities are B+rD<=2H, H<=B, 2L+2rD-z<=4H+2(2B-1)w, and H+Bw<=L. They imply both rows of seam and peak gates together with the first seam identity. The discrete grid at cap Q is v=floor((Q-M)/A), r=min(n,floor((Q-vA)/M)); its remainder proves 0<=Q-H<M+delta and 1<=r<=n. The strict capacity 2L<tA bounds the U mask before conversion to a natural number.

On the equal chart z=y, the excluded last-three-equal face leaves t>=2y. Set Q=L and w=0; the positive margins B-L and 2L-B-nD-2(M+delta) give the four joint inequalities. On z=2y write f=t/z and use r=n,v=f-1,w=0. On z>=4y use Q=B and w=floor((L-H)/B). The margins B-nD-2(M+delta), L-2B-nD and L-B control the remainder, while zB>2L gives 2w<z. All these margins are exact polynomial identities in nonnegative shifted chart coordinates, followed by positivity; dyadic exponent exhaustion supplies the three charts.

When c<b, write E=nD. The reverse grid uses epsilon=A-RM, G=epsilon+M, C=floor((4B-2L+z-2E-2)/4), v=floor((C-epsilon)/A), and r=max(1,ceil(((v+1)A-C)/M)). The ceiling is signed: ceil(q/M)=-floor(-q/M). Euclidean division proves 0<=v, 1<=r<=R, 0<=C-((v+1)A-rM)<G and 2v<t before conversion to natural masks. The three grid cases are d>b with R=n, d=b and n=8 with R=7, and d=b with n>=16 and R=floor(L/M). Exact polynomial identities in nonnegative shifted coordinates establish their universal margins.

The descending grid hypotheses are the positive separation B-2L, nonnegative remainder L-RM, width condition L-E-2G>=0 and capacity tA-2B>0. For the large boundary R=floor(L/M), Euclidean division gives 1<=R<n and 0<=L-RM<M. The positive margin 3L-E-2A-4M supplies its width bound. Separate polynomial certificates establish these inequalities on n>=2,z>=4,y>=2z,t>=2y; on n=8,t=y; and on n>=16,t=y. Thus the choices of R follow from proven signed arithmetic across the entire unbounded chart.

The descending grid orders terminal banks X,V,U,W. Its old seams are A-nM, L-B+(v+1)A-rM, L-rM,0, and its new seams are 2A-nMn, Ln-Bn+2(v+1)A-rMn, Ln-rMn,0. The successors are A,L,B,M and A,Ln,Bn,Mn. The remaining unbounded cases d=b,n=2 and d=b,n=4 use u=2^(b-c-1), r=n-1, p=1 and q=n-2. A single nonterminal U bit u moves to V, and terminal banks are X,U,V,W. Their old seams are A-nM, B-rM-uA, L-rM,0 and new seams are 2A-nMn, Bn-rMn-2uA, Ln-rMn,0. Polynomial margins in z-4 and u-1 handle every b,c in these two cases.

Complementary bit partitions and interval concatenation give the complete physical inventory. Exact paired bank sums and native terminal identities give every seam and peak. Nonnegative terms within each bank and the four-strip lemma then give all prefix inequalities. The physical lift and marked-word identities retain the original seed, doubled seed and literal ear cut. The grid constructions are due to the caller and reuse the dyadic-mask, source-table and physical transport results. The unrestricted strict-saddle chamber, full four-gap joint lift and Circle C3.1 remain open.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/Endpoint.actualSource_first_peak_second_maximum_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/EqualLastThreeUpper/Endpoint](../EqualLastThreeUpper/Endpoint.md)
