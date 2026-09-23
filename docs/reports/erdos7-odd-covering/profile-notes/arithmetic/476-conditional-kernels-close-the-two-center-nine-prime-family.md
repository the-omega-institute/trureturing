# Conditional kernels close the two-center nine-prime family

Let P={3,5,7,11,13,17,19}. A finite family of classes c mod m with pairwise distinct odd numerical moduli m>1 cannot cover the integers under these hypotheses:

* Every support prime belongs to P union {23,29}.
* There are two ordinary integers a,b with a!=b mod3. For each p in P other than3, they agree modulo p^h_p, where h_p is the greatest p-exponent in any old cofactor of a class touching23 or29 (zero if absent).
* Write each later modulus as d·23^j·29^k, with d supported on P and j+k>0. Its original residue satisfies c=a mod d when j>0, including cross classes with k>0; when j=0 and k>0, it satisfies c=b mod d.

All finite heights are arbitrary. Old-only original residues and all new-coordinate original residues are arbitrary. Every original class and numerical modulus stays fixed. The actual full survivor set has Haar mass

    H(U9) >= delta/2079 >1/10395000,                (KD1)

where delta is the exact positive comparison margin below. No assumption about the presence or residue of an original mod3 class is needed.

There is also an unrestricted large-prime continuation: allow any finite number of additional primes, all greater than500000000, and impose the preceding two-center condition only on the head-only subfamily. Every tail-touching class may have arbitrary original phases, heights and joint prime support. The full family still cannot cover. The tail proof retains positive distorted-measure mass greater than1/75000000; this latter number is not a Haar-density bound.

This adds a two-center family alongside [report473's one-center family](473-a-finite-query-certificate-removes-the-coherent-cofactor-height-bound.md); the two hypotheses are not a containment chain. [Report475](475-two-center-density-and-query-bounds-lose-original-survivor-realizability.md) showed that the scalar query and density bounds admit a law supported entirely in the two-center bad event. Here the actual source conditional kernels and mandatory anchor exclusions give a stronger bound that excludes that event as the whole live support. These are ordinary mathematical deductions with exact rational arithmetic, not Lean certification or a settlement of unrestricted Erdős #7.

## One actual old-prime process and auxiliary reference paths

Apply the source completion only to the old-only original family. Use one fixed completed family and its actual charged seven-core process from [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md). On the product of the seven p-adic spaces its live, unnormalized measure nu satisfies

    nu(X)>=m7=7235955529/450000000000,
    nu<=(27/2)H.                                  (KD2)

It starts from unnormalized H restricted to the completed3,5 anchor A. At the five later coordinates its normalized kernels, defined for every entire earlier history, have pointwise Haar density caps

    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5).      (KD3)

The source completion contains one selected mod3 class and one selected mod5 class, so A avoids one fixed root at each of those primes. Further anchor exclusions remain part of the actual process. The completed covered set contains the original old covered set, even when some auxiliary selected residues move. Thus nu avoids every original old class. Completion is not applied to later classes, whose original residues remain unchanged in the fibre calculation.

The source is Michael Schroeder, *Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1: completion Lemma2.2, capped kernels and reverse integration Lemmas3.1--3.2, and the ordinary seven-core mass deduction retained in report467. The [library entry](../../../../../Library/Arith/schroeder2026nine.md) records source identity and verification scope. Haar-preserving coordinate normalizations in that proof can be pulled back; root labels here are relative to the original centers.

Extend each common nonternary prefix of a,b to one fixed p-adic path t_p. At3 use their two distinct fixed paths. These auxiliary references agree with every required original later residue. There is no assertion that two distinct ordinary integers agree at infinitely many depths of another prime. Beyond the finite original precisions, auxiliary path choice only supplies an upper bound on active old cofactors.

For a point x put v_p=v_p(x_p-t_p) at nonternary primes and C=product_(p in P,p>3)(v_p+1). In the ternary root of a let v=v3(x3-a)>=1. The complete path loads are

    (Qa,Qb)=((v+1)C,C)         in root a,
    (Qa,Qb)=(C,(v+1)C)         in root b,
    (Qa,Qb)=(C,C)              in the third root.   (KD4)

Each load includes the unit cofactor. It bounds the number of distinct active old cofactors of the respective category of original later classes. Equality with an auxiliary path has Haar measure zero, also under nu by KD2; it can be assigned to the bad set without changing any mass.

## The actual23/29 fibre retains positive mass off one increasing event

Define

    F(Qa,Qb)=(22-Qa)_+(28-Qb)_+-Qa,
    B={F<=0}.                                      (KD5)

At an original old survivor x, for every fixed pair of later exponents there is at most one original class per old cofactor, by numerical distinctness. The23-only union costs at most Qa/22 in Haar mass, and the29-only union costs at most Qb/28. Their complements form a product. Cross classes use center a and cost at most Qa/(22·28). Therefore

    H23,29(actual fibre survivors at x)>=F(Qa,Qb)_+/616. (KD6)

All sums are over fixed original labels; infinite geometric sums merely bound the finite inventories. No phases are reselected on different fibres. The map F is nonincreasing in either load, so B is increasing in every valuation in each of the three roots.

If C>=20, then F<=2·8-20<0. In root a, v>=21 is bad because Qa>=22; in root b, v>=27 is bad because Qb>=28. Every good profile is therefore in the finite region

    C<=19; 1<=v<=20 in root a; 1<=v<=26 in root b,
    C<=19 in the third root.                       (KD7)

In particular each nonternary valuation is at most18. The exact enumeration below gives minimum positive F equal to4 across all three roots. Hence every good actual fibre retains at least1/154 Haar mass.

## Conditional tail bounds dominate this increasing event

For p in {7,11,13,17,19}, the actual kernel cap gives, for every earlier history and e>=1,

    Pr(v_p>=e | entire past)<=C_p/p^e.             (KD8)

Define independent auxiliary comparison variables J_p by

    Pr(J_p=0)=1-C_p/p,
    Pr(J_p=j)=C_p(p-1)/p^(j+1), j>=1.              (KD9)

Their independence is a property of the comparison model, not of the actual source law. A probability satisfying KD8 is stochastically dominated by KD9: expand any bounded nondecreasing function as its value at0 plus nonnegative increments times indicators of the tails {v>=e}, then apply KD8 and monotone convergence.

Keep the actual normalized kernels, including their prescribed extensions to deleted histories, and first remove the deletion indicators to bound live bad mass from above. Integrate the final coordinate against its kernel. Since the bad indicator is increasing in that coordinate's valuation, KD8 replaces its integral by expectation against J19, uniformly in the entire remaining past. This new function is still increasing in the other later valuations. Continue backwards through17,13,11,7. The resulting upper bound retains Haar on the3,5 anchor and uses the independent variables KD9 elsewhere. It does not multiply unconditional marginal bounds or change the actual source law in KD2.

The nonnegative anchor integrand permits enlarging A to the complement of its selected mod3 root and mod5 root. This loses other exclusions only on the upper-bound side. Both selected roots exist even if the corresponding original labels were absent.

## The worst anchor exclusions are controlled exactly

For fixed nonternary valuations, the bad indicator in the third ternary root has loads(C,C). In either center root the loads are coordinatewise at least(C,C). The Haar mass of each root is1/3. Consequently the integrated bad mass of either center root is at least that of the third root, pointwise in the remaining coordinates. Removing the third root is therefore the worst choice of the selected mod3 class, including after any fixed mod5 exclusion.

Let rho be unnormalized Haar restricted to the two center roots at3, ordinary Haar at5, and the independent comparison variables KD9 at later primes. Its total mass is2/3. Write

    beta0=rho(B | v5=0),                           (KD10)

where only the5-coordinate is conditioned: the ternary factor remains of total mass2/3. Each noncentral mod5 root has v5=0 throughout and contributes exactly beta0/5 to rho(B). In the central root v5>=1, and monotonicity makes its bad contribution at least beta0/5. Deleting any one selected mod5 root therefore yields

    nu(B)<=rho(B)-beta0/5.                         (KD11)

The normalization distinction in KD10 is essential: beta0 is not a probability conditioned on the two-root ternary set as well.

## Finite complement arithmetic, with no omitted probability tail

Every good profile lies in KD7. Sum its exact mass using2/3^(v+1) for a depth-v center-root valuation,1/3 for the third root, ordinary Haar valuation probabilities at5, and KD9 elsewhere. Subtracting good mass from the full root mass gives the entire bad mass, including all arbitrarily high valuations.

The [exact verifier](../../frontier/cover-geometry/two_center_kernel_domination.py) obtains:

| Quantity | Exact count or displayed approximation |
| --- | ---: |
| Good profiles in roots a,b,third | 403,723,669 |
| Good profiles with v5=0 in roots a,b | 816 total |
| Minimum positive F in roots a,b,third | 4,4,8 |
| rho(B) | 0.017345430730161347... |
| beta0 | 0.007406057519969442... |
| rho(B)-beta0/5 | 0.01586421922616746... |
| m7 | 0.016079901175555557... |

Every calculation and comparison uses rational arithmetic; full fractions are in the [result data](../../frontier/cover-geometry/two_center_kernel_domination.json). An independent scalar convolution computes the distribution of C<=19 without enumerating valuation tuples; both methods agree exactly on all three root masses and on the v5=0 masses. The verifier also evaluates every possible excluded ternary root. Its worst case is the third root, in agreement with the monotonicity proof.

Define delta=m7-rho(B)+beta0/5. The exact result is

    delta=
    3755445884378962483813219728834516558385621016682535036625522444307126665443613875601601431
    /17411961895899990232372965510151523793025616448771503457695580547379781614067321738750000000000
    >1/5000.                                      (KD12)

Thus nu(B^c)>=delta. By KD2 the Haar mass of original old survivors outside B is at least delta/(27/2). Integrating KD6 with the minimum positive numerator4 gives

    H(U9)>=delta/[(27/2)·154]=delta/2079
          >1/10395000.                            (KD13)

The full original family is finite, so its survivor set is a union of residue classes on its original finite CRT period. Positive p-adic Haar mass supplies a surviving residue and hence an uncovered integer. Auxiliary reference depths and source completion do not change that implication.

## Arbitrary original classes on primes above500000000

For this extension apply KD13 only to the head-only original subfamily. Set R=P union {23,29}. Explicitly take a new head seed H_R restricted to its full original survivor set U9. Its mass is greater than1/10395000, and its joint density is at most1. Resolve the head coordinates through all exponents needed by the tail-touching original classes; the Haar lift preserves this mass. Do not project those tail classes into additional head forbidden classes, and do not transfer any source query bound to this new seed.

The Haar second-moment factor in [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md), SH6, is

    M2(R)=product_(p in R) p(p+1)/(p-1)^2
         =14003665/540672.                         (KD14)

Use Chapter33 SH11--SH13 with B=500000000, ell=18 and3^18=387420489<=B. Put

    c=(2ell^2+1)/(2ell^2-1),
    tau7=c^7/B ·[B/(B-3)]^2·sum_(j=0,...,7)7!/[(7-j)!ell^j].

The exact consumer verifies

    1/10395000-M2(R)tau7(B,18)>1/75000000>0.        (KD15)

Chapter33 assigns each original tail class to its last exposed outside prime, keeps its complete head and earlier-tail exponent labels and residue, and bounds the union loss under one actual final law. The number of outside primes, their finite heights and their joint occurrence in moduli are unrestricted. Only their being greater than B is required. Its analytic prime-product premise and source-verification boundary are inherited unchanged. KD15 is a distorted-measure mass reserve, not a Haar-density lower bound for the full family.

## Reproduction and remaining boundary

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_center_kernel_domination.py
```

The program reads the retained report467 source constants from common_law_mass_tail.json, with its data identity fixed, and does not rerun the source producer, its geometry or Lean. Optional `--source PATH` chooses that input location; `--output PATH` writes JSON. Explicit checks stay enabled under Python optimization. The analytic domination and original-family bridge above are ordinary proof inputs, not consequences of the finite arithmetic alone.

The new result does not allow independent old phases for every23/29 class, arbitrary assignment of both centers to every category, other intervening support primes up to the stated tail cutoff, or an arbitrary growing small-prime core. In particular report475's abstract-law obstruction remains valid: scalar density and query summaries still do not imply KD11. The proof succeeds by keeping the conditional source structure that those summaries omit. Removing the phase restriction while retaining one actual original survivor process remains unresolved.
