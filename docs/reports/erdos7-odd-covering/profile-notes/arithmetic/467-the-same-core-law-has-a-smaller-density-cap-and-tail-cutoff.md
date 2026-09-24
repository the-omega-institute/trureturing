# The same core law has a smaller density cap and a five-million tail cutoff

A finite family with pairwise distinct odd numerical moduli greater than one cannot cover the integers if at most seven of its support primes are below 43 and at most nine are at most 5000000. Original residues, finite prime-power heights, the number of larger primes and their joint occurrence in moduli are unrestricted.

This improves the cutoff 3000000000 in [report463](463-two-actual-prime-extensions-preserve-a-common-core-law.md) to 5000000. The underlying change is a stronger density bound for the **same** seven-core query law, not a replacement by a different favorable measure. For any fixed family and finite period supported on at most seven chosen odd core primes, resolving the family and its query depths, one probability satisfies

    supp(mu)=U,
    (1/5) H_K|U <= mu <= Lambda7 H_K,
    R_K(mu)=sum_(1<d|K) max_a mu(a mod d) <=70871/3375,
    Lambda7=6075000000000/7235955529 <840.

Here U is the full original survivor set. The prior upper bound 455625 and its deductions remain valid. The compatible all-depth law of [report466](466-randomized-completion-retains-full-original-survivor-support.md) can also be chosen with this smaller cap, for one fixed original finite family and one fixed set of at most seven primes.

The proof combines the already retained ordinary prefix mass with the refined query comparison on one charged source process. These are ordinary deductions from Michael Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, edition 1.0.1, as developed in [Chapter30](../../problem-details/30-six-prime-prefix-measures-close-all-six-vertex-blocks.md), [Chapter31](../../problem-details/31-seven-vertex-block-noncoverage-with-actual-prime-measures.md) and reports462--466. Source attribution, archive identity and the arbitrary-height verification boundary remain in the [library entry](../../../../../Library/Arith/schroeder2026nine.md). No new Lean certification or unrestricted Erdős #7 conclusion is claimed.

The same law also gives the [six-prime two-copy estimate](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#a-quantitative-common-law-for-six-prime-two-copy-families): arbitrary fixed residues with at most two classes per numerical modulus, on at most six odd primes excluding3, admit one full-support law with all-depth query bound33748/3375<10 and density below420. That deduction uses actual ternary comb families and their joint query partitions; it adds no hypothesis to the seven-prime result here.

Report348's separate [direct capped law with the actual pure-anchor masses retained](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md#retaining-the-actual-pure-anchor-masses) improves that two-copy interface to a query upper bound5.149795473527814... and density below88. Both improved bounds belong to the direct law; they are not additional estimates on the seven-prime law constructed here.

On P={3,5,7,11,13,17,19}, the uniform survivor-mass consequence
H(U)>=1/Lambda7 also gives a
[different supported law by legal phase resampling](530-one-supported-law-controls-unused-and-deep-occupied-labels.md): all unused numerical labels and all occupied labels above10^9 have combined query sum below6.737016. A Gibbs refinement and fixed mixture give this same law full actual survivor support and the density cap Lambda7; controlling the remaining shallow labels under that law remains open.

## The ordinary prefix mass bounds the charged process itself

Fix one completed source family on the reference primes 3,5,7,11,13,17,19 and one legal charged enlargement at 7, including the randomized choices used in report466. Initialize with unnormalized Haar on the actual completed anchor survivors and use the explicit normalized capped kernels with caps

    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5).

Stop after 19 and call the resulting live measure nu. This is the same process used for report466's refined final-stage query comparison.

The full selected completion contains pure powers and 15,21,35,45,63,75,105,165. It satisfies the weaker completion conditions of the basic anchor calculation. The basic anchor reserve includes the entire mixed 3--5 reciprocal inventory; inserting selected 45 or 75 does not require another charge outside that inventory. Its 15-credit remains valid. The 165-class ends at 11, where the ordinary inventory includes it once, releasing its projection in the upper comparison rather than changing its actual residue.

At a 7-anchor cell let s count the active selected projections of 21,35,63,105. Every one has current exponent one. If Z_rest is the remaining normalized raw 7-load, then

    Z7=Z_rest+(6/7)s.

Replacing their target union by any size-s superset of nonzero first digits costs s/7 in Haar mass. Including the pure 7-set of mass 1/6, the explicit cap-3/2 kernel has current loss at most

    (1/4)[Z_rest+(6/7)s-1]_+ = (1/4)[Z7-1]_+.

This is exactly the ordinary threshold-2 upper hinge. Thus the ordinary stage-7 estimate pays for the charged deletion, including added target digits. At every later stage the same normalized conditional caps permit the ordinary reverse-integration estimate. Ignoring the refined first-hit savings and releasing the fixed 165 projection can increase the comparison bound; it does not require a different physical process.

Chapter30 explicitly permits retaining the charged enlargement under the ordinary inventory bound. The source compatible-screening lemma provides the corresponding stagewise domination. Consequently the full set of 32 basic prefix inequalities applies to this nu, even when finer source screens are needed to control the hypothetical final query stage.

For each basic anchor vertex v, let R_basic(v) be the reserve and O_p(v) the already retained ordinary loss upper bounds, in 135-cell units. The existing prefix result is

    min_v [R_basic(v)-O7(v)-O11(v)-O13(v)-O17(v)-O19(v)]/135
      = m7=7235955529/450000000000 >2/125.

The minimum occurs at (a,b,c)=(2,4,1), j=1,3,4. The reserve is affine and the ordinary loss bounds are convex in the same pure-5 budget, so these 32 vertices control every permitted continuous anchor parameter. No interpolation of independently chosen laws is used. First-hit accounting therefore gives, for every completed family and every legal charged choice,

    m7 <= nu(1) <=3/8,
    nu <= (27/2) H.

This bound was already retained for the ordinary prefix in Chapter31 and the [report461 data](../../frontier/cover-geometry/query_stoploss_completion.json). Its use here is justified by the charged-process domination above. No geometry or old prefix producer needs to be regenerated.

## Keep the refined query bound, then normalize once

For this same nu, the relative terminal ledger of report466 gives simultaneously for every complete physical query L

    integral (L-1) dnu <= (70871/3375) nu(1).

The basic prefix ledger need not equal the refined denominator D7 in that proof. Both are valid estimates for the same physical measure: one lower-bounds its total mass, while the other supplies the query inequality. We do not substitute a basic reserve or loss into the refined relative-ledger ratio.

Average unnormalized measures over legal completion and charged choices as in report466, then over its finite random prefix injections to actual primes. Every summand has mass at least m7. Haar domination is applied before averaging. The same original queries are pulled back through each representation; no query chooses its law. One final normalization therefore preserves the query bound and gives

    mu <= [(27/2)/m7] H = Lambda7 H <840 H.

The lower density on all original survivors is unchanged: report466 uses its point-preservation probability and the upper mass 3/8, both of which still hold. Projection from padded unused primes preserves all bounds. Applying the finite-simplex compactness argument with this stronger cap also preserves them for one common law over every core depth. This is not a mixture of a high-mass ordinary law with a separate low-query law.

## A nine-prime head with a larger Haar reserve

Take seven old core primes and two distinct new primes q>=43 and r>=47, with arbitrary original phases and heights. Resolve also the old-coordinate depths of every class that will be processed later. Report463's fixed pure-conditioned product and original-label counting apply with the conservative A=21 and Lambda=840.

For the old law mu and new pure-conditioned probabilities rho_q,rho_r, delete all remaining original head classes from their one product. The union bound retains the d=1 old cofactor for classes involving both new primes. Its surviving mass is at least

    N21(q,r)/[(q-2)(r-2)],
    N21(q,r)=(q-23)(r-23)-463.

The product density is at most 840(q-1)(r-1)/[(q-2)(r-2)]. Hence the original head survivor set U9 has

    H(U9) >= N21(q,r)/[840(q-1)(r-1)]
           >=17/1622880 >1/100000.

The second inequality uses the same increasing rational expression as report463; its minimum on q>=43,r>=47 is at (43,47). There is no restriction on which original classes occur or on how their old phases agree. In particular, this is a bound for the actual original survivor set, not just for a favorable old fibre.

## Arbitrarily many primes beyond 5000000

Use H restricted to U9 as the unnormalized head seed. It has mass greater than 1/100000 and joint Haar density at most one. This change of seed is explicit: no query bound is transferred to normalized Haar on U9.

The head Haar second-moment factor is bounded by

    M2=product_(p=3,5,7,11,13,17,19,43,47) p(p+1)/(p-1)^2
      =1026827659/43877376.

Each factor decreases with p. Therefore it bounds any such nine-prime head, including a padded one. Apply [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md), (SH11)--(SH13), with

    B=5000000, ell=14, 3^14=4782969<=B,
    c_ell=(2ell^2+1)/(2ell^2-1)=393/391,
    tau7(B,ell)=c_ell^7/B * [B/(B-3)]^2
                 * sum_(j=0,...,7) 7!/[(7-j)! ell^j].

Exact rational arithmetic gives

    1/100000 - M2 tau7(5000000,14) >1/1000000 >0.

This is a lower bound for remaining mass in the distorted tail construction. It is not a Haar-density lower bound of that size. The analytic prime-product premise is inherited from Chapter33 and its cited source; the arithmetic consumer does not prove it.

The tail argument assigns each original tail-touching modulus to its last exposed outside prime. It retains all old exponents, the full set of earlier outside exponents and the original residue. The total number of outside primes and the number appearing together in one modulus are unrestricted. Positive final mass yields an avoiding residue on the full finite CRT carrier and hence an uncovered integer.

To obtain the opening statement, put every actual support prime at most B into the head. There are at most nine. Pad, if necessary, with unused odd primes between 43 and B, until there are nine. There remain at most seven head primes below 43, so the eighth and ninth are at least 43 and 47. The other original primes lie above B. Padding adds no forbidden class, and projection of the final witness removes the artificial coordinates.

## Exact consumer and scope

The [consumer](../../frontier/cover-geometry/common_law_mass_tail.py) reads the retained report461 prefix summary and report466 randomization summary with exact data identities. It consumes their already recorded mass and query bounds, computes the stronger common-law density cap, the nine-prime Haar reserve and the new all-prime tail margin, and writes [the result data](../../frontier/cover-geometry/common_law_mass_tail.json). The same-law deduction and the analytic tail premise remain ordinary mathematical inputs, not consequences of matching numbers.

Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/common_law_mass_tail.py \
  --prefix docs/reports/erdos7-odd-covering/frontier/cover-geometry/query_stoploss_completion.json \
  --randomized docs/reports/erdos7-odd-covering/frontier/cover-geometry/randomized_completion_support.json
```

The input files are required; optional `--output PATH` writes the computed JSON instead of sending it to stdout. The isolated optimized run passed. Checks use explicit exceptions and stay enabled with Python optimization. Source geometry, old producers and Lean are not rerun.

This result adds families with arbitrarily many primes above the smaller cutoff, under the stated head restrictions. It does not handle the first nine odd primes, supply induction through arbitrary small-prime cores, or settle unrestricted Erdős #7. The remaining two-axis problem still requires a positive joint fibre estimate for the original shared phases.
