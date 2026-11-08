# The original infinite family and its two source rows

## Abstract

Opposite first and third maximum: original physical joint construction

**Theorem 1.1 (Four original parameters, one original permutation, one literal ear).**

Lean statement: `D5/S3/Combinatorics/Circle/FourNegative/OppositeFirstThirdMaximum/Endpoint.actualSource_opposite_first_third_maximum_joint_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/FourNegative/OppositeFirstThirdMaximum/Endpoint.actualSource_opposite_first_third_maximum_joint_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original telescope is (a b c d : Nat), 2<=b, 2<=d, c=a, b<a, d<a, and b<d or d+2<=b. No finite-range or feasibility premise is added. Put k=a+b+c+d and seed=1+2^a+2^(a+b)+2^(a+b+c). The endpoint supplies one permutation sigma of all Fin k physical labels and a natural cut j<=k. It asserts OriginalOrder(k,seed,sigma) and OriginalOrder(k+1,2*seed,earWord(k,sigma,j)) for that same sigma and cut. Equality c=a is substituted only inside the proof; it is retained in the public statement and its seed.

actualSource(k,seed,i) is the centered residue of 2^i*seed modulo 2^k-1. Doubling modulo this odd modulus is invertible and generates a cyclic action; the labelled source is its sequence of occurrences. Values at different labels may coincide. This construction permutes physical occurrences and proves integer prefix bounds; it does not prove that every source orbit is free, has length k, or classifies arbitrary group actions. No orbit, rotation, seed replacement or reflection is used to alter the original target.

Write s=a=c, x=2^s, y=2^b, t=2^d, N=x*x*y*t-1, Q=2*N+1, F=x+1 and C=1+y*F. The four old heads are A=x*C+1, B=1+t*F+x*y*t, L=F*(1+x*t), K=C+x*y*t. Their enlarged shared heads are 2*A, SU=2*B-1, SV=2*L-F and SW=2*K-C. The canonical chain_values and actual_values lemmas identify these with the actual centered rows. Positivity and terminal bounds come from those source lemmas, rather than from an abstract mass assignment.

The original positive chains have offsets U=0, V=d, W=d+c, X=d+c+b and lengths d-1, c-1, b-1, a-1. The four terminal labels remain d-1, d+c-1, d+c+b-1 and k-1. The existing chamberLabels decoder lists the actual set-bit occurrences in increasing local exponent order. The stock_split lemma partitions a full all-ones mask into a selected mask and its XOR complement, proving exact occurrence inventory and disjointness. Below the full-mask capacity this XOR complement equals arithmetic subtraction. Empty masks and empty complementary banks are retained.

Let M=2^(s-1)-1 and n=2^(s-b-1). The n-mask is exactly one available V bit; b>=2 and b<s ensure its exponent is in the positive V range. Write Ufull and Wfull for all positive U and W labels, and X(m), V(n), Xcomp(m), Vcomp(n) for the decoded masks and their actual complements. Form P(m)=Ufull ++ X(m) ++ [k-1] ++ Xcomp(m) ++ [d-1], and T=Wfull ++ V(n) ++ [d+c-1] ++ Vcomp(n) ++ [d+c+b-1]. The Source module proves that each concatenation order exhausts precisely List.range k. Thus coincident scalar values never merge distinct occurrences.

When b<d, choose m=floor((2*A-B-1)/(2*K)) and use P(m) ++ T. When d+2<=b, put h=floor((2*A+B-1)/(2*K)), choose m=h-1 and use T ++ P(m). The actual natural mask is obtained only after proving nonnegativity of the integer quotient expression. In both cases 0<=m<=2^(s-d)-1<2^(s-1), so the decoder uses available X exponents. The cut is the length of the constructed prefix ending at the displayed occurrence k-1. It is d+popcount(m) in the first order and s+b+d+popcount(m) in the second. The Lean implementation uses the prefix length directly; it proves its legal bound from the full inventory and proves that insertion is literally take j sigma ++ [k] ++ drop j sigma in natural labels before applying the canonical Fin bridge.

The quotient proof uses integer remainder R, twice the rho of the supplied construction. In the first region R=2*A-B-1-2*m*K and 0<=R<2*K; the first old doubled head has upper slack R+1. The enlarged lower slack after terminal k-1 is (x-2*m)*C-2*R-2. The dyadic ratio g=x/t is 2, 4, or at least 8. The first two cases force m=1 and m=3, with explicit positive polynomial slacks. The g>=8 case uses m<=g-1 and the remainder bound. In the second region R=2*A+B-1-2*h*K, and the enlarged doubled slack is (x-2*h)*C-2*R. For t>=8 the bound h<=g suffices. At t=4, the positive identity 2*(g-1)*K-(2*A+B-1)=2*((7*y-92)+(33*y-11)*(g-8)+4*y*(g-8)^2) proves h<=g-2. No boundary tuple is discarded.

The six gates in each order are mixed bank margins. Before the fresh insertion they bound the old bank heads above and the enlarged endpoints after negative jumps below. After insertion they bound the old endpoints below and enlarged bank heads above. The remaining margins are the explicit positive expressions involving B-K, SW-B, (eta+2)*B-K-L and 2*SV+SW-1-(eta+2)*SU in the first region, or 2*L-K-eta*B, the first enlarged V endpoint, 2*B-K and SW-SU in the second, where eta=x/y=2^(s-b). Their positivity is proved for the infinite parameter family by polynomial decompositions, rather than by enumerating tuples.

For each shared original label the charge delta=2*oldValue-newValue is nonnegative. On U,V,W,X positive bits it equals respectively 0, 2^i, F*2^i and C*2^i. At the four old terminals its values are 1, x/2+1, 1+y*F/2 and (A+1)/2. The source proof handles the actual terminal formulas as well as the positive bits. The old total is independently zero; the enlarged shared total is independently -A, and the sole fresh value is A. These follow from source_totals and the proved occurrence permutation. Hence the total shared charge is A, and every partial shared charge lies between 0 and A. The private complete_checks lemma uses this accounting to recover both missing prefix inequalities from each mixed margin. Nonnegative banks then let four_strip control every intermediate physical prefix, including the fresh prefix inside its bank and all terminal boundaries.

The endpoint uses actual_nat_joint_iff from PacketNormalForm.Endpoint to obtain OriginalOrder on the original natural-label word and its literal earWord. It reuses the zero-period repeated_prefixes lemma from SecondPeakEqualTail.Endpoint. For every pair of natural numbers m,n, take n of flatten(replicate m sigma) has sum in [0,modulus(k)/2]. The corresponding enlarged repeated word has sum in [0,modulus(k)]. Both complete repeated-word sums are zero separately for every m. Zero repetitions, zero takes, exact period boundaries and overlong takes are all covered. The enlarged half-modulus is proved equal to modulus(k).

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/FourNegative/OppositeFirstThirdMaximum/Endpoint.actualSource_opposite_first_third_maximum_joint_lift`
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/OppositeFirstThirdMaximum/Physical](Physical.md)
- Dependency: [D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Endpoint](../SecondPeakEqualTail/Endpoint.md)
