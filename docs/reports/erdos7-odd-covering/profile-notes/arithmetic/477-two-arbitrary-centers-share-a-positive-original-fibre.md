# Two arbitrary centers share a positive original fibre

Let P={3,5,7,11,13,17,19}. Consider a finite original family of classes c mod m with pairwise distinct odd numerical moduli m>1, all supported on P union {23,29}. Suppose there are two fixed integers a,b such that, writing a later modulus as d·23^j·29^k with d supported on P:

* if j>0, its original residue satisfies c=a mod d, including cross classes with k>0;
* if j=0 and k>0, its original residue satisfies c=b mod d.

There is no condition on how a,b agree or differ at any prime, and a=b is allowed. Old-only original residues, all finite heights, and all23/29-coordinate residues are arbitrary. Then the full original survivor set U has normalized Haar mass

    H(U)>373455529/3742200000000000>1/10395000.     (AC1)

Thus the family cannot cover the integers. This contains both the single-center family of [report473](473-a-finite-query-certificate-removes-the-coherent-cofactor-height-bound.md) and the restricted two-center family of [report476](476-conditional-kernels-close-the-two-center-nine-prime-family.md). In particular it removes report476's requirements that the centers differ modulo3 and share all six nonternary prefixes.

The same conclusion extends to any finite set of further support primes all greater than500000000, with the two-center condition imposed only on the head-only subfamily. Every tail-touching original class may have arbitrary residues, heights and joint prime support. Report476's retained continuation then leaves distorted-measure mass greater than1/75000000. This is not a Haar-density lower bound for the enlarged family.

These are ordinary mathematical deductions with exact integer and rational checks. They use the pinned Schroeder source construction and the retained source bounds below, not a new Lean certification. The category rule remains essential to the statement: this does not allow every original class to choose independently between the two centers, let alone arbitrary independent old residues. Unrestricted Erdős #7 remains unresolved.

## A pair of path loads controls the original new-coordinate fibre

Use one fixed completed source family and the actual unnormalized seven-core process nu from [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md). Completion acts only on the old-only family. Its covered set contains the original old covered set; all later original classes remain fixed. The same process has

    nu<=D H,  D=27/2,
    nu(X)>=m7=7235955529/450000000000,             (AC2)

with the stronger coarse-anchor lower bounds used below. It starts from H restricted to the actual completed3,5 anchor A and has normalized conditional kernels, defined for every entire earlier history, with caps

    (C7,C11,C13,C17,C19)=(3/2,5/3,3/2,2,9/5).     (AC3)

At each prime view a,b as two fixed paths. More generally the proof permits any two p-adic paths extending the required finite original prefixes. Define

    Qa(x)=product_(p in P)(v_p(x_p-a_p)+1),
    Qb(x)=product_(p in P)(v_p(x_p-b_p)+1).         (AC4)

These loads include the unit cofactor and bound the respective active old-cofactor inventories. Path equality is Haar null and nu-null by AC2; assign it to the bad set. The original23-only union costs at most Qa/22 in its Haar coordinate, the29-only union at most Qb/28, and cross classes at most Qa/616 in the product. Numerical distinctness supplies at most one class for every complete exponent label. Consequently

    H23,29(fibre survivors at x)>=F(Qa,Qb)_+/616,
    F(u,v)=(22-u)_+(28-v)_+-u.                     (AC5)

The actual new-coordinate residues never change with x. Infinite geometric sums bound only the given finite inventories. F is nonincreasing in either argument. Let BAD={F<=0}. Every GOOD integer-load pair has F>=1, so every good fibre has Haar mass at least1/616. The stronger1/154 floor in report476 depended on its narrower pair geometry and is not used here.

## A positive comparator for two paths at one prime

Put h=v_p(a_p-b_p), allowing h=infinity, and let H_(p,h) be the Haar law of the local pair (v_p(x-a_p),v_p(x-b_p)). For finite h its atoms are

    (j,j), j<h:       (p-1)/p^(j+1),
    (h,h):           (p-2)/p^(h+1),
    (j,h),(h,j), j>h: (p-1)/p^(j+1) each.          (AC6)

For coincident paths only the diagonal geometric atoms remain. The baseline(0,0) has mass1-2/p if h=0 and1-1/p otherwise.

If a normalized actual kernel K has Haar density at most C, then every bounded coordinatewise nondecreasing payoff f satisfies

    integral f dK
      <=f(0,0)+C integral[f-f(0,0)]dH_(p,h)
      =integral f dJ_(p,h,C),                     (AC7)

where J scales every nonbaseline Haar atom by C and assigns all remaining probability to the baseline. The measure J is positive because C H(nonbaseline)<=2C/p<1 for all five caps in AC3. AC7 follows by integrating the nonnegative function f-f(0,0); it is not an inference from separate marginal bounds.

Drop the actual deletion indicators only on the upper-bound side, then integrate the actual normalized kernels backwards. AC7 applies uniformly in each complete earlier history. The comparison variables may be taken independent for a fixed list of path separations; this does not assert independence of the actual process.

## A finite upper envelope covers every separation depth

There are515 positive integer pairs (u,v) with F(u,v)>0; necessarily u<=21 and v<=27. Every other pair is absorbing BAD, since all later local factors are positive integers. If both local valuations are at least19, both accumulated loads are at least20 and

    F(u,v)<=(22-20)(28-20)-20=-4.

Thus every h>=19 has exactly the same GOOD contributions as h=infinity. Only h=0,...,18 and one coincident-path option are needed in later-coordinate transitions. This is an exact reduction, not a probability-tail truncation.

Start with V_after19(u,v)=1_BAD. Working backwards through19,17,13,11,7, define

    V_beforep(u,v)
      =max_h integral V_afterp(u(i+1),v(j+1)) dJ_(p,h,Cp)(i,j). (AC8)

On absorbing pairs V remains1. Every transition preserves monotonicity and the range[0,1]. Allowing the maximizing h to vary with the current load pair enlarges the class of fixed path pairs; it is used only as an upper bound. No original center is changed in the physical process.

The exact checker computes AC8 with common integer denominators and checks every transition inequality, range and adjacent-state monotonicity. Write V7 for its resulting upper payoff after integrating the five later coordinates. Then, for the same nu in AC2,

    nu(BAD)<=integral_A V7((v3,a+1)(v5,a+1),
                           (v3,b+1)(v5,b+1)) dH3 dH5. (AC9)

## A global bound using every completed pure3 and pure5 class

The completed pure p-power classes are pairwise disjoint, with total Haar mass1/(p-1). In particular the pure3 and pure5 exclusions have masses1/2 and1/4. Dropping all mixed anchor exclusions gives a product of their actual pure survivor sets.

At5 every increasing payoff is smallest at its joint baseline. This baseline has Haar mass at least3/5. Removing any set of mass1/4 therefore leaves an integral bounded above by the positive measure

    H_(5,h)- (1/4)delta_(0,0).                    (AC10)

Integrate against AC10 and maximize over the same finite set of separation types to obtain an increasing payoff g on the ternary load pair, of total mass at most3/4.

If h3>=1, the ternary baseline has mass2/3; subtracting(1/2)delta_(0,0) gives another positive upper comparator. If h3=0, the baseline has only mass1/3. Any removed pure3 set of mass1/2 therefore has at least1/6 outside it. Outside the baseline, the local load pair is at least(2,1) or(1,2), so the removed integral is at least

    (1/3)g(1,1)+(1/6)min(g(2,1),g(1,2)).          (AC11)

Equivalently the remaining upper bound is the maximum of the integrals against two positive measures: remove the baseline mass1/3, then mass1/6 from either local pair(2,1) or(1,2). Each such atom has Haar mass2/9. Positivity permits replacing the remaining payoff by its upper envelope; subtracting a credit after an unrelated upper bound would not suffice.

The exact maximum over all ternary separation types is

    0.01691017358748595... <17/1000.               (AC12)

Full fractions are retained in the result data. This estimate alone is slightly above m7. The source coarse-anchor information supplies the remaining distinction.

## Keep the source geometry attached to its own mass lower bound

Use the basic normalized anchor notation of the pinned Schroeder source, distinct from the center names a,b. Its eight coarse triples are(alpha,beta,gamma), where alpha=1 or2 is the selected15 residue, beta=2 or4 the selected27 residue, and gamma=1 or2 the first digit of the selected25 residue. Each triple has four vertices for the continuous pure5 tail budget.

The ordinary source reserve is affine and its loss bounds convex in that tail budget. Therefore the source live-mass lower bound is concave and bounded below by the smallest of its four vertex values. These are the retained32 rows in [report461](461-query-stop-loss-gives-a-common-law-six-core-completion-margin.md), applied to the same charged process by report467. The checker reads those rows; it does not regenerate their geometry.

For every coarse triple except(2,4,1), the retained mass lower bound is at least

    5891133457/225000000000=0.026182815364444...,

so AC12 leaves more than1/1250 good mass. At(2,4,1) the source minimum is m7. Here the actual anchor must avoid all six classes

    0 mod3, 1 mod9, 4 mod27,
    0 mod5, 1 mod25, 2 mod15.                     (AC13)

The source's gamma=1 specifies only the first digit of the selected25 class. Permute the five second-digit children inside that column so its second digit becomes0, giving1 mod25. This preserves the mod5 and15 anchors and all ternary data. Apply this permutation, together with the source's normalizations, to the entire family, both center paths and all original queries. These prime-adic tree automorphisms preserve Haar, all cylinder depths, path intersection depths and the original numerical exponent labels. This is a simultaneous change of representation, not a translation-only assumption or a fresh choice of original later residues.

Enlarge the actual anchor to the complement A0 of just AC13. Define

    R1={x3=1 mod3, x3!=1 mod9, x3!=4 mod27},
    R2={x3=2 mod3},
    V5={x5!=0 mod5, x5!=1 mod25},
    W5=V5 minus {x5=2 mod5}.

Then A0 is the disjoint union

    A0=(R1 times V5) union (R2 times W5),           (AC14)

with respective coordinate masses5/27,1/3,19/25,14/25. This keeps the15 exclusion in its actual joint position. Additional pure powers and mixed anchor classes can be dropped on the upper-bound side because the payoff is nonnegative.

## All arbitrary center positions in the six-cylinder anchor

Enumerate the ordered center prefixes modulo27 at3 and modulo25 at5. Distinct prefixes determine their separation depth. Equal prefixes require only finitely many deeper separations: the implementation enumerates through27, with all larger or infinite values having the same GOOD contribution. The stronger h>=19 reduction above already justifies this finite coverage.

For a retained prefix cell not containing either center, both valuations are known exactly. In a cell containing only one center, one valuation is fixed and the other has its exact Haar geometric tail. In a cell containing both centers, use the corresponding shifted version of AC6. Every omitted depth has an already-BAD local load and is placed at one absorbing atom. All root masses are checked with integer weights having common denominator p^28.

Equal distributions are deduplicated by exact integer signatures, retaining the root labels needed by the15 class. The resulting counts are

| Component | Count |
| --- | ---: |
| Raw ternary center/separation cases | 1377 |
| Raw quinary center/separation cases | 1250 |
| Distinct ternary distributions | 88 |
| Distinct quinary distributions | 108 |
| Joint distribution pairs checked | 9504 |

For every pair the checker integrates the same V7 using the positive decomposition AC14. The largest exact value is

    0.01521356135458516... <61/4000.                (AC15)

One representative has ternary prefixes(2,2), separation depth8, and quinary prefixes(3,4), separation depth0. The full rational maximum is in the data. No floating-point comparison or rounded signature is used by the verifier.

Combining AC15 with the matching source coarse mass gives

    nu(GOOD)>m7-61/4000
      =373455529/450000000000>1/1250.              (AC16)

The other seven coarse types have a larger gap using AC12. The bad bounds are uniform in the continuous pure5 tail budget, so taking the source minimum over its four vertices is legitimate; no favorable vertex is chosen independently for each query or history.

## Transfer to the original family and the unrestricted large-prime tail

The same measure nu avoids all original old-only classes and has density at most27/2. Hence AC16 gives an actual old survivor set of Haar mass greater than(373455529/450000000000)/(27/2) on which AC5 leaves new-coordinate Haar mass at least1/616. Integrating yields AC1. Since the original full family is finite, positive mass on its finite CRT period supplies an uncovered integer.

For the large-prime extension apply AC1 only to the head-only subfamily and explicitly switch to Haar restricted to its full original survivor set. This seed has density at most1 and mass greater than1/10395000. Uniformly extend its head coordinates to all depths needed by tail-touching originals; do not insert their head projections as forbidden classes.

This is precisely the seed threshold used by report476's retained [Chapter33](../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md) continuation. Its exact loss inequality at B=500000000, ell=18 is reused unchanged, including the analytic prime-product premise. Each original tail class retains its numerical label, fixed residue and complete earlier cofactor, assigned once to its last exposed outside prime. The resulting positive distorted mass is greater than1/75000000.

## Exact consumer and remaining restriction

The [standalone verifier](../../frontier/cover-geometry/arbitrary_two_center_kernel.py) uses only the Python standard library. It consumes the retained report467 mass/cap data, report461's32 source rows, and report476's tail constants by their exact data identities. It computes the new515-state upper envelope, the global pure bound and the9504 joint anchor inequalities, then checks all eight coarse source gaps and the original-fibre conversion. Its [result data](../../frontier/cover-geometry/arbitrary_two_center_kernel.json) contain exact rational outputs.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/arbitrary_two_center_kernel.py
```

Optional `--input-dir DIR` relocates the three retained inputs; `--output PATH` writes JSON. Checks use explicit exceptions and stay active under optimization. Source producers, their geometry and Lean are not rerun. The stochastic comparison, continuous source interpolation, normalization transport and original-family bridge remain the ordinary proof inputs stated above.

The proof now allows completely unrelated reference paths for the two categories. It still requires that every23-only or cross class share one old center and every29-only class share the other. With independently varying old residues, the actual inventories need not be the two products AC4, and the515-state comparison does not apply. Removing that category-wide coherence is the next unresolved phase restriction; a finite certificate for these two products does not settle arbitrary original layouts or unrestricted Erdős #7.
