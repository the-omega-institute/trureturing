# All c>=4, a>=c+2, d>=a+c+1, b>=d+1

## Abstract

Parity-tail four-bank joint orders

**Theorem 1.1 (One physical permutation and its literal ear at cut zero).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakParityTail/Endpoint.actualSource_second_peak_parity_tail_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakParityTail/Endpoint.actualSource_second_peak_parity_tail_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural a,b,c,d with c>=4, a>=c+2, d>=a+c+1 and b>=d+1, put k=a+b+c+d and A=1+2^a+2^(a+b)+2^(a+b+c). There exists one list sigma of Fin k labels satisfying OriginalOrder k A sigma and OriginalOrder (k+1) (2A) (earWord k sigma 0). Both words use the actual centered sources. For every pair of natural numbers m,n, the take-n prefix of m concatenated copies has sum in [0,floor((2^k-1)/2)] on the old side and [0,floor((2^(k+1)-1)/2)] on the new side. For every m both repeated words have exact sum zero. Empty, full and overlong prefixes and zero repetitions are included. The unrestricted four-gap problem and Circle J remain open.

Set u=2^(a-c), z=2^c, h=2^(d-a), t=2^(b-d-1), x=uz and q=ht. Then u>=4, z>=16, h>=2z and t>=1. The integer selector uses M=2u(z+1), A0=uz+1, D=(u^2-1)h, B=15uz/8 and J=2(u-1). It compares the two first points of the interlaced lattices KM-D+pA0, p=0,1, above B. Their smaller point has nonnegative excess less than M-A0. Rounding this excess in steps of J, with a minimum of one step, produces alpha,S,delta with 2<=S, 4S<=7z, 0<=delta<=J and M alpha=(u^2 z+1)h+(uz+1)S-B+delta. All divisions in this selection are integer Euclidean divisions; z is divisible by eight.

In chain order U,V,W,X, the four positive bank coefficient rows are (alpha,0,(x-u-2)q,0), (0,0,uq+(h-S)t,u(z/2-1)), (xh/2-1-alpha,0,0,0), and (0,z/2-1,2q-1-(h-S)t,u-1). The banks terminate in order U,X,W,V. PhysicalBanks realizes these coefficients by disjoint actual dyadic labels, proves complete nonterminal coverage and computes both actual masses. The final W subword is retained literally at the end of the last bank. All parameter boundaries, including b=d+1, remain in scope.

After substitution of the selector equality, multiply the three old lower seams and three new upper peaks by the positive scale 8u(z+1). At S=2 or 7z/4 and delta=0 or 2(u-1), all six margins are nonnegative polynomials in u-4, z-16, h-2z and t-1. An exact rectangular interpolation identity transfers the corner inequalities to the selected S and delta. PhysicalStrips connects these rational identities to the actual integer masses and native terminal values.

Positivity inside each bank and the exact final terminal bounds first give the old lower prefix bound. The matched charge chi(i)=2 oldValue(i)-newValue(i) is nonnegative and has total A, so A+newPrefix-2 oldPrefix is nonnegative. This gives the new lower bound. The three new upper peaks give A+newPrefix<=2^k-1, and hence oldPrefix<=floor((2^k-1)/2). The fresh ear label contributes A. Exact source totals extend both strips to every natural number of repetitions. The physical permutation is converted to Fin labels, and its literal ear is identified with the fresh label followed by the same permutation.

The Reg companion retains the complete eight-binder family and every prefix and total conclusion. Its two readouts are the actual old and enlarged OriginalOrder predicates. Whole-family variation and deletion sensitivity test each readout. Source-seed changes distinguish both observations at parameters in the stated domain. Continuation is unknown.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/SecondPeakParityTail/Endpoint.actualSource_second_peak_parity_tail_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/PacketNormalForm/Endpoint](../PacketNormalForm/Endpoint.md)
