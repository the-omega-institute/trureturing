# Deeper divisor queries force positive mass outside a load-twenty plateau

For any finite original family supported on the primes 3,5,7,11,13,17,19, with pairwise distinct odd numerical moduli greater than one and arbitrary phases and heights, its actual survivor set has positive Haar mass outside the following fixed set:

    E={x: x=0 mod81, and exactly two of 5,7,11,13,17,19 divide x}.

More precisely, the common law supplied by [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md) satisfies

    mu(E^c) >= 158401/10363825 > 0.015,
    H(U\E) >= 1146182591749129/62960236875000000000 > 1/55000.

Here U is the full original survivor set. All sets and measures are taken on one finite period resolving the original moduli and the query period 3^6·5·7·11·13·17·19. The Haar inequality concerns actual original survivors, not an abstract load distribution.

This follows from a finite deeper-query certificate, not from positive variance or a change of probability. At the smaller period 3^4·5·7·11·13·17·19, uniform(E) satisfies both the source density and common-query scalar bounds while an actual complete query is constantly twenty. At ternary depth six, however, **every** probability supported on the lift of E violates the common-query bound. The extra queries expose a restriction absent from the smaller interface.

These are ordinary deductions from the existing source-law theorem and elementary finite partitions, with an exact arithmetic checker. There is no new Lean certification or enlarged noncoverage range. A point outside E need not have positive 23/29 extension capacity; the unrestricted problem and that joint-capacity obligation remain unresolved.

## A fixed-period plateau passing every query at that period

Put P={5,7,11,13,17,19} and K=81 product_(p in P)p=130945815. Take the complete zero-phase query

    Q(x)=sum_(d|K) 1_(x=0 mod d).

At x in E there are five choices of the 3-exponent and two choices at each of the two other dividing primes. Consequently Q(x)=5·2^2=20. There are 320 distinct divisor labels, all with one fixed phase.

For a two-element C subset P, let E_C be the stratum with zero roots exactly at C. Its cardinality is product_(p in P\C)(p-1). Thus

    |E|=166464,
    H_K(E)=1088/855855,
    d uniform(E)/dH_K=855855/1088 on E.

The density is below Lambda7=6075000000000/7235955529. The lower inequality (1/5)H_K|E <= uniform(E) also holds.

It is possible to evaluate **all** query phases under this same uniform law. Let q_p=p-1, Z=166464 and e_j be the j-th elementary symmetric sum of the six numbers q_p. For a modulus with other-prime support T, fix a phase whose zero roots in T are A subset T. Every nonzero specified residue has the same probability, by multiplication by units in each prime coordinate. The exact number of E points in that cylinder is

    sum_(C subset P, |C|=2, C intersect T=A)
        product_(p in P\(C union T)) q_p.

The 3-coordinate either misses E or fixes a zero prefix already shared by all E, so the maximum is independent of its exponent 0,...,4. Summing the exact maxima over the 64 supports T gives

    sum_T max_phase mu(phase on T)
      =4+(e_0+e_1+e_2+e_3)/e_4
      =4+25127/166464.

For |T|=0,1,2 the respective sums are 1,2,1. For larger T the maximum uses two zero roots, giving the remaining elementary sums. One can verify that choice directly from the displayed finite formula; the checker exhausts all zero/nonzero phase types rather than assuming the aligned query maximizes them.

Therefore

    1+R_K(uniform(E))=3454915/166464,
    R_K(uniform(E))=3288451/166464 < 70871/3375.

Unlike [report470](470-an-actual-load-twenty-plateau-fails-the-common-query-bound.md), this example passes the full query maximum at its specified period. It does not identify E with an original complete survivor set, or claim that its law extends while preserving the same bound at greater depths.

## A lower bound for every law on E

Now let nu be any probability supported on E, without a uniformity assumption. Define w_C=nu(E_C), so the fifteen pair weights sum to one. For every T subset P write

    m_T=max_b nu(x=b mod product_(p in T)p).

For |T| at most two, using the zero phases gives

    sum_(|T|<=2) m_T >= 1+2+1=4.

For a triple T and a pair C subset T, put r=T\C. On E_C the two C-coordinates are zero and the r-coordinate is nonzero. Its mass w_C is split among r-1 possible nonzero r-residues, so

    m_T >= w_C/(r-1).

This inequality holds separately for each of the three pairs in T. Taking their average, then summing over triples, gives

    sum_(|T|=3) m_T
      >= (1/3) sum_C w_C sum_(r in P\C) 1/(r-1)
      >= (1/3)(1/10+1/12+1/16+1/18)
      =217/2160.

The minimum occurs at C={5,7}, which removes the two largest reciprocal terms. Higher-cardinality supports are nonnegative and may be discarded. Consequently every such nu satisfies

    sum_T m_T >= 8857/2160.                         (DQ1)

Each maximum refers to a different numerical divisor and can be selected independently in a complete query on the same law. No common query centre or independence between the prime coordinates is required.

## Two additional ternary digits exclude every supported law

Let K_h=3^(4+h) product_(p in P)p, and let nu be any probability supported on the inverse image of E in Z/K_h. Its projection supplies the m_T in DQ1.

For ternary exponents a=0,...,4 the maximal cylinder at modulus 3^a product(T) has mass m_T: every supported point already has the zero ternary prefix. For a=4+j, take a maximizing base T-cylinder. It is partitioned into 3^j possible descendants of the zero mod81 prefix, so some descendant has mass at least 3^(-j)m_T. Summing over all the distinct divisor labels yields

    1+R_(K_h)(nu)
      >= (5+sum_(j=1,...,h)3^(-j)) 8857/2160.       (DQ2)

This is a lower bound for arbitrary higher-digit distributions, not a computation restricted to independent uniform tails.

At h=2, DQ2 gives

    R_(K_2)(nu) >= 414553/19440,
    414553/19440 - 70871/3375 = 158401/486000 >0.   (DQ3)

Thus already at ternary depth six no supported law can have the source common-query bound. The displayed bound at h=1 is 8452/405, which does not exceed the source bound; no claim is made that h=2 is the optimal distinguishing depth.

## Quantitative escape for the actual source law

The lower bound is homogeneous in the measure. For any probability mu on K_2, put alpha=mu(E). If alpha>0, normalize mu restricted to E and apply DQ3. Every nonunit cylinder maximum for mu is at least the corresponding maximum of that restriction. Therefore

    R_(K_2)(mu) >= alpha (414553/19440).             (DQ4)

At alpha=0 the same inequality is immediate. Hence R_(K_2)(mu)<=70871/3375 forces

    mu(E^c) >= 1-(70871/3375)/(414553/19440)
             =158401/10363825.                    (DQ5)

For an arbitrary original family on these seven primes, choose one finite period resolving both its actual moduli and K_2. Report467 supplies one probability supported on U, with R bounded by 70871/3375 and density at most Lambda7. Projection to K_2 preserves its cylinder probabilities; the query sum there is bounded by the full-period sum. Applying DQ5 on this one projected law gives the same mass outside the inverse image of E. Since mu is supported on U and mu<=Lambda7 H,

    H(U\E) >= mu(E^c)/Lambda7
             >=1146182591749129/62960236875000000000.

No compactness step or selection of unrelated laws at different depths is needed: one sufficiently resolved finite-period law suffices. Translation of the query centres gives the corresponding translated-set conclusion, without changing any original residue.

## Direct original-label obstruction at the smaller period

There is also an elementary reason E cannot be the entire original survivor set for a family whose numerical moduli divide K. Any forbidden class must miss E. At ternary exponent zero, the projection of E onto any set of at most two other prime coordinates is full, so no class at such a label can miss E. All remaining labels together have reciprocal budget at most

    B=(sum_(a=1,...,4)3^(-a)) product_(p in P)(1+1/p)
       +sum_(T subset P, |T|>=3) 1/product(T)
     =133338/146965.

Distinct original labels allow each term at most once. Yet

    1-H_K(E)-B=1330577/14549535 >0.

Thus those labels cannot cover the entire complement of E. This budget argument concerns divisors of that exact K only. DQ5 instead uses the existing source law to force actual surviving mass outside E for arbitrary original heights on the same seven primes.

## Verification and remaining scope

The [standard-library checker](../../frontier/cover-geometry/deeper_query_plateau_escape.py) evaluates all 320 base labels by exact CRT phase types, checks the cylinder-maxima sum and density, and verifies the triple-support, deeper-query, escape-mass and original-label-budget constants. Its [result data](../../frontier/cover-geometry/deeper_query_plateau_escape.json) retain these finite inputs and exact outputs. General partition arguments and the source-law theorem remain ordinary proof inputs, not consequences of checking the constants.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/deeper_query_plateau_escape.py
```

Optional `--output PATH` writes JSON. Checks raise explicit exceptions and remain enabled under optimization. The program neither enumerates the full 130945815-point period nor reruns the source geometry or Lean.

The current seven-prime noncoverage theorem is reused, not strengthened to more prime supports. The additional result is a quantitative restriction on where its actual survivors can lie. It does not show that the escaped mass satisfies a positive two-prime joint-capacity inequality; controlling that set remains a separate obligation.
