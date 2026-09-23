# Two-center bad support passes the query and density bounds but is not an original survivor set

One actual probability law satisfies the seven-core all-depth query bound, both density bounds on its full support, and avoidance of the third ternary root, while the two-center 23/29 fibre union-bound certificate is zero throughout that support. The same support **cannot** be the full survivor set of any finite original family on these seven primes with pairwise distinct numerical moduli greater than one.

Thus the numerical query and density interface loses a genuine original-family realizability restriction. This is a counterexample to an implication about that interface, not an integer covering counterexample. The proof uses ordinary finite probability and CRT counting with an exact standard-library certificate; no Lean certification or unrestricted Erdős #7 settlement is asserted.

[Report473](473-a-finite-query-certificate-removes-the-coherent-cofactor-height-bound.md) retains one common old reference for every later class. This note tests the next relaxation: 23-only and 23/29-cross classes use old center a, while 29-only classes use center b; these centers agree at the six nonternary precisions and differ modulo3. If their active old-cofactor counts are bounded by Q_a,Q_b, the actual fibre has the sufficient lower bound

    [(22-Q_a)_+(28-Q_b)_+-Q_a]_+/616.

The product bounds the remaining two axes; the subtracted Q_a/616 bounds cross classes using their distinct original exponent labels. Failure of this lower bound does not imply that the actual fibre is empty. No later covering family is supplied here. Unlike [report474](474-arbitrary-fixed-phases-admit-high-load-below-the-query-cap.md), the present law satisfies both density inequalities; the failure event concerns a pair of coherent queries rather than one uniformly heavy fixed-phase query.

## Statement with two fixed ordinary integer centers

Let P=(3,5,7,11,13,17,19), h=(6,2,2,1,1,1,1), and

    M=product p_i^h_i=41247931725,
    a=0, b=30610605025.

Thus b=1 modulo3^6 and b=0 modulo every other prime-power factor of M. Define the two actual complete coherent finite queries

    Q_a(x)=sum_{d|M} 1_{x=a mod d},
    Q_b(x)=sum_{d|M} 1_{x=b mod d}.

Both sums include d=1. Let

    B_M={x:(22-Q_a(x))_+(28-Q_b(x))_+<=Q_a(x)}.

There exists one probability mu_M on Z/MZ, positive exactly on a set E, with

    E subset B_M,
    E intersect {x=2 mod3}=empty,
    (1/5)H_M|E <=mu_M<=Lambda H_M,
    Lambda=6075000000000/7235955529.

Extend it to the product of the seven p-adic coordinate spaces by uniform independent Haar tails conditional on its finite residue. For this one law mu, define

    m_e(mu)=max_z mu(x=z mod product p_i^e_i),
    R_infinity(mu)=sum_{e in N_0^7, e!=0} m_e(mu).

The exact value is

    R_infinity(mu)
      =1467018358219244540381743/76441190394266910720000
      =19.19146406083795... <70871/3375.

The same finite query event B_M has mu-probability one at every extension depth. The integer centers are only required to agree in the six coordinates at the finite precisions resolving Q_a,Q_b. No assertion that two different ordinary integers agree at all depths is used.

## Finite law and support

The certificate lists136 disjoint positive valuation orbits, each with a positive integer weight n_s; their sum is

    Z=999999999925.

For a listed branch c in {0,1} and valuation tuple v, the ternary part is

    min(v_3(x-c),6)=v_0,

where v_0>=1. The other coordinate conditions are

    min(v_(p_i)(x),h_i)=v_i, i>=1.

Let S_s be the resulting subset of Z/MZ and N_s its cardinality. The law is explicitly

    mu_M({x})=n_s/(Z N_s) for x in S_s,
    mu_M({x})=0 outside the union E.

The sets are pairwise disjoint. Their coordinate cardinalities are obtained by literally enumerating at most729 residues per coordinate in the verifier; equivalently, a capped valuation a has cardinality1 if a=h and(p-1)p^(h-a-1) otherwise. Thus this is a finite CRT probability, not an LP relaxation or a list of marginal moments.

At a branch0 state put C=product_{i>=1}(v_i+1). Then Q_a=(v_0+1)C and Q_b=C. At a branch1 state Q_a=C and Q_b=(v_0+1)C. These are exact finite divisor-query values even at saturated coordinates. The verifier checks the defining B_M inequality on every positive state. Branch2 never occurs, so the law also avoids the forbidden class2 mod3.

The exact Haar support mass and density extrema are

    H_M(E)=35805248/13749310575,
    min_E dmu_M/dH_M=3966795245413/11519999999136
                    =0.3443398650790373...>1/5,
    max_E dmu_M/dH_M=171827199999724269/204799999984640
                    =839.0000000615787...<Lambda.

These inequalities hold pointwise and persist under the Haar-tail extension. The lower bound concerns E, the exact support of this constructed law. Replacing E by a prescribed original survivor set U is not justified.

## Every query phase is accounted for

For each coordinate orbit and each0<=e_i<=h_i, project its literal finite residue list modulo p_i^e_i. Each resulting projected set has constant fiber cardinality; the verifier checks this using exact integer counts. At fixed i,e_i, projected sets belonging to different orbit types are either identical or disjoint; the verifier checks that assertion too.

Consequently, for one exponent tuple e<=h, a state contributes uniformly to exactly one product of these local projected sets. If this product has T_(s,e) actual query residues, its contribution to each such residue is n_s/(Z T_(s,e)). For each product phase class, sum these contributions over the states projecting to it. The greatest such sum is exactly m_e(mu_M). Residues outside the represented classes have mass zero.

This exhausts all actual query residues, not just the two coherent centers and not just those phases used to select the law. The136 states give48075 nonzero product phase classes across1008 distinct exponent tuples. Exact common integer denominators are used for every maximum. The optimization program is not invoked or trusted by verification.

## Exact all-depth tail sum

For any exponent tuple e in N_0^7, let f_i=min(e_i,h_i). Haar continuation makes every depth-e cylinder below one fixed depth-f residue have exactly the same conditional mass. Therefore

    m_e(mu)=m_f(mu_M) product_{i:e_i>h_i} p_i^(-(e_i-h_i)).

The equality holds for maxima as well: every finite maximizing f-residue has descendants, all with that same factor. Summing over the disjoint fibers of e -> min(e,h) gives the exact identity

    1+R_infinity(mu)
       =sum_{0<=f<=h} m_f(mu_M)
          product_{i:f_i=h_i} p_i/(p_i-1).

All terms are nonnegative. There is no truncated or unpaid tail and no assumption that separately selected maximizing phases are jointly compatible: R is itself the sum of individual maxima under one fixed law. Applying this formula to the exact finite maxima proves the rational value stated above. Its exact margin below the report467 budget is

    138156043093967379510737/76441190394266910720000>0.

## A zero-cylinder test proves that this support is not an original survivor set

Let T be the fixed CRT box

    x=0 mod3; x!=0 modp for p=5,7,11,13,17,19,

and let nu be normalized Haar restricted to T, with Haar tails. Every listed positive orbit is disjoint from T: a branch1 orbit has a different ternary root, and each branch0 orbit has at least one positive nonternary valuation. In particular nu(E)=0.

For a numerical P-supported modulus m, a class that could belong to an original family with survivor set E must have mu-mass zero. Write f_i=min(v_(p_i)(m),h_i), d_f=product p_i^f_i, and define

    z_f=max {nu(x=r mod d_f):mu(x=r mod d_f)=0},

with value zero when there is no zero-mass class. Both mu and nu have uniform tails. Thus the greatest nu-mass of a mu-zero class modulo m is exactly

    (d_f/m) z_f.

Indeed both probabilities acquire the same positive tail factor d_f/m, so zero mass is equivalent to zero mass at the projected finite cylinder. Summing over all numerical moduli, not just those dividing M, gives

    sum_(m>1, P-supported) max_(mu(C)=0, C mod m) nu(C)
      =sum_(0<=f<=h) z_f product_(i:f_i=h_i) p_i/(p_i-1)
      =11356324750837/37150418534400
      =0.3056849747283853... <1.                   (Z1)

The unit term vanishes since mu(1)=1. At each fixed finite label, all query residues meeting T have the same nu-mass. The verifier obtains their local phase types by literally projecting T in each coordinate. It detects whether at least one such product type is absent from the positive mu support, and hence computes z_f exactly. There are702 labels with positive z_f; all higher labels are paid for by the displayed geometric tail factors.

Now take any finite original family of distinct P-supported numerical moduli whose forbidden classes all avoid E. Its union has nu-mass at most the left side of Z1, because at most one class is available for each numerical modulus. Consequently its actual survivors within T have nu-mass at least

    25794093783563/37150418534400 >0.              (Z2)

Since T is disjoint from E, no such family has complete survivor set exactly E. This exclusion allows arbitrary original residues and arbitrary finite heights. It does not exclude a different support contained in the same two-center bad event.

This separates two boundary descriptions explicitly: the same constructed law passes the query maxima and density inequalities, but fails the zero-cylinder condition necessary for one original family to generate its support. Merely adding another depth to those already all-depth queries cannot repair this loss of original-family data.

## Which two-center original cases remain

Here take any finite family of pairwise distinct numerical moduli greater than one, all supported on P union {23,29}, satisfying the two-center hypothesis above. The centers may be any two integers distinct modulo3 and agreeing at every nonternary precision used by the original old cofactors; original heights and all remaining phases are arbitrary. Suppose its original old family has a class modulo3 with phase a or b. Its survivors exclude that center's root. The opposite center's coherent divisor load then bounds both active old-cofactor inventories: a cofactor using the excluded ternary root cannot be active, and every remaining cofactor has the common nonternary phase. Applying report473's finite query potential to the opposite center, using the same source theorem from [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md), produces positive source mass with both counts at most19. The 23/29 fibre there retains at least1/77 Haar mass, exactly as in report473's proof. Its full survivor Haar lower bound449287056937/6056623125000000000 remains valid.

If the original old family has no class modulo3, append the class a mod3. Its numerical label is unused, so the enlarged family remains admissible and falls under the preceding case. Invoke the source theorem for that enlarged family; do not transfer a source law from the old family. Its survivors are also survivors of the given family.

Hence the unresolved two-center case can be restricted to original families containing the class at the third ternary root. The constructed law already respects that zero cylinder. Passing this single original-class constraint still does not give a realization of its complete support, as Z1 shows. For arbitrary finite original heights the centers need agree only to the nonternary precisions used by those original cofactors, not at every infinite depth.

## Verification and scope

The [integer-weight certificate](../../frontier/cover-geometry/two_center_density_obstruction_weights.json) specifies136 actual disjoint orbits. The [standard-library verifier](../../frontier/cover-geometry/two_center_density_obstruction.py) reconstructs literal coordinate residues, their finite query maxima, exact full tails, density extrema, the two fixed integer centers, and the zero-cylinder test. Its [result data](../../frontier/cover-geometry/two_center_density_obstruction.json) contain the exact outputs. The ordinary arguments above justify Haar continuation and passage from Z1 to the original-family exclusion.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_center_density_obstruction.py
```

Optional positional input selects a certificate and `--output PATH` writes results. Explicit checks remain active under Python optimization. The verifier does not use a numerical optimizer or trust a claimed optimum, and it does not enumerate the full41247931725-point carrier.

The boundary that remains is concrete: a source-supported law must have its zero cylinders organized by one finite set of distinct original numerical labels and fixed original phases, with their union exactly the complement of the complete survivor set. The constructed E fails this requirement. The findings neither refute the source theorem nor establish noncoverage for every two-center original family, let alone unrestricted Erdős #7.
