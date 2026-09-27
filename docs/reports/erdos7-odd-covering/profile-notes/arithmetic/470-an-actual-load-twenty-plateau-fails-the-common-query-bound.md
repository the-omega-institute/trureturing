# An actual load-twenty plateau fits the density cap but fails the common-query bound

An actual complete divisor query can equal twenty on a set whose Haar mass exceeds the seven-core survivor-density lower bound of [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md). Thus arithmetic realizability of a single query and that density lower bound do not exclude a load-twenty plateau. However, another complete query equals twenty-four on the same set, so **every** probability supported there violates report467's common-query bound. The set is not identified with the complete survivor set of any original family.

This distinguishes three requirements that cannot be substituted for one another: an actual arithmetic query, an actual original survivor set, and one supported law controlling every query. It does not realize the constant-twenty obstruction under the full source hypotheses, supply a joint two-prime covering, or enlarge a noncoverage range. The argument and the CRT check below are ordinary mathematics, with no new Lean certification.

## One fixed arithmetic query

Let

    P={5,7,11,13,17,19},
    K=9 product_(p in P) p=14549535.

There is one fixed query residue b_d at every divisor d of K. Set b_1=0 and b_d=1 for all nonunit d, except

    b_9=0,
    b_(9pq)=0 for all distinct p,q in P.

The query load is

    Q(x)=sum_(d|K) 1_(x=b_d mod d).

These are normalized numerical residues and all 192 divisor labels are distinct. The sixteen changed labels are 9 and the fifteen labels 9pq. No phase depends on the sampled x.

Consider the set

    E={x mod K: x=1 mod9, and exactly three p in P satisfy x=1 mod p}.

For x in E write C for those three primes. The unchanged aligned query

    A(x)=sum_(d|K) 1_(x=1 mod d)

has three choices of the 3-exponent and two choices of the exponent at each prime in C. Hence A(x)=3*2^3=24. Among the sixteen changed labels, exactly 9 and the three labels 9pq with p,q in C were aligned hits. All new zero-phase classes miss x, because they require x=0 mod9. Therefore

    Q(x)=24-[1+binomial(3,2)]=20 for every x in E.

This is a pointwise identity on an actual finite CRT carrier, not an abstract load assignment. It does not assert that the query is constant outside E.

## Exact mass and the same-set alternate query

For each three-element C subset P, the corresponding CRT stratum contains

    product_(p in P\C) (p-1)

points: the mod9 residue and the three selected prime residues are fixed, and each remaining prime has p-1 choices. The twenty strata are disjoint, so

    |E|=sum_(|C|=3) product_(p in P\C)(p-1)=23320,
    H_K(E)=424/264537.

With Lambda7=6075000000000/7235955529 from report467, exact comparisons give

    H_K(E)>1/Lambda7,
    d uniform(E)/dH_K=264537/424 < Lambda7 on E.

Thus the available density cap alone admits a probability concentrated on a genuine load-twenty plateau. The lower density inequality (1/5) H_K|E <= uniform(E) also holds. This statement uses E in place of a survivor set only to test the numerical density conditions; it does not assume that replacement is valid for the source construction.

The common-query condition is much stronger. For every probability mu supported on E, the alternate query A satisfies E_mu A=24. Consequently

    R_K(mu)=sum_(1<d|K) max_a mu(a mod d)
           >=sum_(1<d|K) mu(1 mod d)
           =23 >70871/3375.

This excludes every such mu from report467's admissible source laws, regardless of how its mass is distributed within E. Uniformity is not used in this exclusion. Testing only Q would miss the violation: E_mu Q=20 for all the same laws.

Even the implication from density to a point with Q different from twenty is therefore false for arbitrary sets. What remains unresolved is whether a constant-twenty query can occur on an **actual complete original survivor set** carrying the source's simultaneous bounds. [Report469](469-full-survivor-support-does-not-force-query-variance.md) gives an actual survivor-set plateau at level two; the present construction does not raise that result to level twenty.

## Exact verification and scope

The [standard-library checker](../../frontier/cover-geometry/load_twenty_plateau.py) constructs all 192 numerical query labels and checks all twenty CRT strata. For each query it verifies that its indicator is constant throughout each stratum, using the allowed residues in every prime coordinate. It computes the exact stratum sizes, verifies Q=20 and A=24, and compares the rational density and common-query bounds. It does not enumerate the full 14549535-point carrier or search for an original forbidden family with survivor set E.

The [result data](../../frontier/cover-geometry/load_twenty_plateau.json) retain the query rule, changed labels, stratum counts and exact comparisons. Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/load_twenty_plateau.py
```

Optional `--output PATH` writes the JSON. Checks raise explicit exceptions, including under optimization. The source's all-height construction and Lean are not rerun.
