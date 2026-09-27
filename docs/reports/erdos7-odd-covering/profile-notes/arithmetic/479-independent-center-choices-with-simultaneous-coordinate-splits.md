# Simultaneous coordinate disagreements with independent original center choices

Every later original modulus may independently choose either of two old reference residues, while both references may differ simultaneously in all seven old coordinates after the common prefixes specified below. The resulting nine-prime family cannot cover the integers. This gives a different extension of [report478](478-independent-center-choices-with-one-varying-old-coordinate.md): it admits simultaneous disagreements, but requires shared initial digits in the later old coordinates. Neither scope contains the other.

These are ordinary mathematical deductions with exact integer and rational checks, using the attributed Schroeder source construction retained in [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md), not a new Lean certification. Arbitrary independent old residues and unrestricted Erdős #7 remain unresolved.

## Original scope and target

Let P={3,5,7,11,13,17,19}. An original finite family has pairwise distinct odd numerical moduli m>1 supported on P union{23,29}. For m=d23^j29^k with j+k>0, its old-coordinate residue is either a mod d or b mod d, chosen independently for each full numerical label m. Classes with the same old cofactor d may choose differently at different new exponent pairs. Old-only classes and all new-coordinate phases and finite exponents are arbitrary.

Assume a,b share their first digit at every p>=7 in P. At3 and5 impose either

    (h3>=2 and h5>=2), or (h3>=3 and h5>=1),

where hp denotes the shared prefix depth. Each coordinate may split at any later depth, independently of every other coordinate. All seven coordinates can differ simultaneously. Equivalently, for ordinary integer centers one sufficient condition is that a-b be divisible by either

    3^2*5^2*7*11*13*17*19,
    3^3*5*7*11*13*17*19.

The theorem stated here assumes this divisibility for the two integers. Its proof only reads the depths used by the finite original family: those finite prefixes can instead be extended to two fixed prime-adic reference paths satisfying the displayed depth conditions. Every continuation is fixed once for the whole original family. No original phase is reselected as x or a recursive branch changes.

The outcome is positive original Haar survivor density

    H(U)>148455529/467775000000000>1/3222450.

Any finite set of further support primes greater than150000000 may be added. The center conditions apply only to the head-only subfamily; all tail-touching original classes may have arbitrary phases, heights and joint support. The continuation below retains distorted mass greater than1/40000000, not an enlarged-family Haar-density bound.

## Preserve the union and intersection of original divisor labels

For an old point x define

    A=product_p(vp(x-a_p)+1),
    B=product_p(vp(x-b_p)+1),
    C=product_p(min(vp(x-a_p),vp(x-b_p))+1).

Outside a null set of reference coordinate paths these are finite positive integers. A and B count the exponent vectors of old numerical cofactors matched by each reference. C counts their intersection, so their union has exactly

    J=A+B-C.

This subtraction is necessary: an original numerical cofactor matching both references is still one label. At each fixed pair(j,k), distinctness of original d23^j29^k means at most J active old cofactors, regardless of their individually chosen centers. J is an upper bound on the chosen active inventory, not a recovery of the actual selector from its union.

For J<=19, the original23-only,29-only and cross inventories therefore give the same original two-axis fibre lower bound as report478:

    (1-19/22)(1-19/28)-19/(22*28)=1/77.

The actual new-coordinate phases stay fixed. Hence it suffices to retain positive mass on GOOD={J<=19} in the one actual old survivor process.

## A finite three-load comparison

Use exactly the charged source nu from reports467,477,478. Its normalized conditional kernel caps at7,11,13,17,19 are3/2,5/3,3/2,2,9/5, its joint Haar density is at most27/2, and its eight coarse-type mass bounds come from the same retained32 vertices and their concave interpolation within each fixed coarse source. The source completion changes only the old-only family; it enlarges its excluded set. All later original labels and phases remain fixed, and every point retained by nu avoids the original old-only classes.

The abstract GOOD load space is

    S={(A,B,C):1<=C<=min(A,B), A+B-C<=19}.

There are1330 such triples. Some need not arise from actual valuation products; admitting them only enlarges the dynamic envelope. Since J>=max(A,B), both A and B are at most19 in a GOOD state.

At one coordinate with local valuations i,j, the state multiplies componentwise by

    (i+1,j+1,min(i,j)+1).

BAD is absorbing. Every multiplier (u,v,w) has1<=w<=min(u,v), and maintains C<=A,B. For any such multiplier, J cannot decrease. More generally, after any further multiplier(alpha,beta,gamma), with gamma<=alpha,beta, the change in the final union load is

    A alpha(u-1)+B beta(v-1)-C gamma(w-1)>=0.

Indeed A alpha>=C gamma, u>=w and v>=1. Therefore the terminal BAD indicator is monotone under all such multipliers. Positive averaging and taking suprema over coordinate laws preserve this monotonicity. In particular the payoff of local pair(0,0) is minimal, which is exactly the condition needed for density-cap domination.

For two paths whose common prefix depth is h, the joint Haar atoms of(i,j) are

    (j,j), j<h:       (p-1)/p^(j+1),
    (h,h):           (p-2)/p^(h+1),
    (j,h),(h,j),j>h:  (p-1)/p^(j+1) each.

Coincident paths have the diagonal Haar valuation law. All admissible later h satisfy h>=1. Multiply every nonbaseline joint atom by Cp and place the remaining mass at(0,0). This gives a positive probability: its nonbaseline mass is Cp/p<1. For every admissible payoff f,

    E_actual f <= f(0,0)+Cp E_H[f-f(0,0)].

The actual complete earlier history is fixed when applying this bound. Drop actual deletion indicators only on the upper BAD side, and integrate the actual normalized kernels in reverse order.

Starting with Vafter19=1_BAD, the finite recursion is

    Vbeforep(A,B,C)=max_(h>=1) E_Jp,h Vafterp(A(i+1),B(j+1),C(min(i,j)+1)).

The maximizing h is allowed to depend on the current load triple. This is an upper relaxation of fixed global center paths; it does not give physical centers adaptive choices. The comparison variables are auxiliary, not assertions that the actual source coordinates are independent.

If a local valuation i or j is at least19, the corresponding new A or B is at least20 and the state is BAD. For h>=19, all locally GOOD atoms are exactly the same diagonal atoms j=0,...,18. Thus h=1,...,18,19, with19 also representing every larger/infinite depth, covers all separations exactly. No probability tail is discarded: all omitted mass is absorbing BAD.

The verifier uses common integer denominators in every transition, verifies all action upper inequalities, nonnegative probabilities, value ranges and multiplicative monotonicity. It computes the final five-coordinate upper payoff V7 on all1330 states.

## Seven source types: complete pure anchor

Since both centers have a common first digit at3 and5, the joint baseline Haar masses are2/3 and4/5. Completed pure3 and pure5 exclusions have total masses1/2 and1/4. Any excluded point has payoff at least the baseline payoff, so removing these total masses from the baseline atoms gives an upper bound on the actual restricted integral, regardless of the positions of the exclusions. The remaining comparison measures are positive. Drop mixed exclusions only on this upper side. Applying the same triple-state recurrence at5, then integrating3, gives the uniform upper bound

    nu(BAD)<=0.022200298829181918...<9/400.

This bound allows h3,h5>=1 independently, hence is valid for both stronger prefix boxes. Every coarse source except(2,4,1) has live mass at least5891133457/225000000000, so these seven types leave more than the claimed uniform GOOD margin.

## Worst source: joint reference positions in the actual six-cylinder anchor

Normalize the worst coarse source(2,4,1) simultaneously with both reference paths and every original query. As in report477, the mandatory exclusions become

    0 mod3,1 mod9,4 mod27,0 mod5,1 mod25,2 mod15.

The selected25 class requires a permutation of its second-digit children after the source's first-digit normalization. This is one common representation change. Prime-adic tree automorphisms preserve all shared prefix depths, joint valuation distributions, Haar mass and numerical exponent labels.

Let R1,R2,V5,W5 be the same regions as reports477,478. The enlarged source anchor is the disjoint union

    A0=(R1 times V5) union(R2 times W5),

with coordinate masses5/27,1/3,19/25,14/25. Integrate V7 against the exact joint valuation-pair distributions for both anchor coordinates, retaining the two load factors and their intersection factor. Additional source exclusions can be omitted because V7 is nonnegative.

Ternary prefixes are enumerated modulo27 and quinary prefixes modulo25. Distinct prefixes determine the separation depth. Equal prefixes enumerate every deeper h through19, with19 representing all later/infinite values. Filter the required h lower bound before signature deduplication. Within each allowed prefix cell, either both valuations are known, one has a geometric tail, or the two paths have the exact shifted split law above. Every residual tail is already BAD. Cell masses and all four region masses are checked exactly.

For(h3>=2,h5>=2), there are513 raw ternary cases and450 raw quinary cases. Exact signatures leave59*74=4366 joint checks. The maximum is

    0.015577146913228318...,

with representative ternary prefixes(2,11), separation2, and equal quinary prefixes3, separation2.

For(h3>=3,h5>=1), there are459 raw ternary cases and550 raw quinary cases, reduced to54*80=4320 joint checks. The maximum is

    0.015726249876144426...,

with equal ternary prefixes2, separation3, and quinary prefixes(3,8), separation1.

Both maxima are strictly below63/4000. The checker stores their full rational values; displayed decimals are not used as evidence.

## Uniform original-family conclusion

The same worst source has mass at least

    m7=7235955529/450000000000.

Thus both prefix boxes have

    nu(GOOD)>m7-63/4000
             =148455529/450000000000>1/3100.

For each of the other seven coarse types use its own mass lower bound minus9/400; the checker verifies every such gap is larger. The BAD estimates hold uniformly in the continuous pure5 budget, so the retained four-vertex minimum belongs to the same actual source throughout.

Divide by the density cap27/2 and integrate the original new-fibre mass1/77 to obtain

    H(U)>148455529/467775000000000>1/3222450.

The original finite CRT period therefore contains an uncovered integer. This handles two references which may disagree simultaneously at all seven old coordinates, with each original full numerical modulus selecting its reference independently.

## Unrestricted large-prime continuation

Switch to Haar restricted to the full original head survivor set, with mass greater than1/3222450 and density at most1. Resolve every head digit queried by later original classes without inserting the projections of those classes as head exclusions. Apply the [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md) continuation with

    M2=product_(p in P union{23,29}) p(p+1)/(p-1)^2=14003665/540672,
    B=150000000, ell=17, c=(2ell^2+1)/(2ell^2-1)=579/577,
    tau7=(c^7/B)(B/(B-3))^2 sum_(j=0,...,7) 7!/((7-j)!ell^j).

The inherited analytic bound requires B>=286, ell>=4 and3^ell<=B. Exact arithmetic verifies these premises and

    M2 tau7=0.0000002851486782398132...,
    1/3222450-M2 tau7>1/40000000.

Assign each original tail-touching class once to its last exposed outside prime, retaining its complete earlier cofactor and fixed original phase. The resulting positive distorted mass proves noncoverage with arbitrary further support primes above B. It is not a lower bound on the enlarged family's Haar density.

## Verification and remaining boundary

The [standalone verifier](../../frontier/cover-geometry/independent_center_multiple_coordinates.py) and [exact result data](../../frontier/cover-geometry/independent_center_multiple_coordinates.json) verify the positive local comparison laws, all1330 states and separation actions, multiplicative monotonicity, joint anchor distributions and masses, the two rational upper bounds, all32 source vertices, original fibre and Haar conversion, and large-prime tail arithmetic.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/independent_center_multiple_coordinates.py
```

Optional `--input-dir DIR` relocates the two hash-pinned source inputs; `--output PATH` writes JSON. Explicit checks remain active under optimization. Source construction, continuous-budget interpolation, simultaneous normalization and the analytic tail estimate are the ordinary proof inputs above; their producers and Lean are not rerun. Finite calculation certifies the comparison envelope, not an enumeration of every original family.

The first-digit restrictions at p>=7 and the stated ternary/quinary prefix alternatives remain hypotheses of this result. No necessity for noncoverage is asserted. Removing them or allowing arbitrary independent old phases requires a further argument; unrestricted Erdős #7 has not been settled.
