# Two query scalars do not determine a surviving extension

The query bound and Haar-density bound alone do not guarantee an extension of every fixed old survivor law through original 23 and 29 constraints. This is a specific boundary of [report463](463-two-actual-prime-extensions-preserve-a-common-core-law.md)'s interface. It applies the existing deleted-fibre obstruction of [report455](455-positive-mass-core-margins-give-height-independent-tail-cutoffs.md#5-why-arbitrary-fixed-core-marginals-cannot-have-this-cutoff) with the exact scalar thresholds from [report462](462-the-final-stage-ledger-gives-a-seven-core-common-law.md). It is an ordinary proof with exact finite verification, not a new general obstruction theorem or Lean certification.

## Exact conditional fibres

Fix one actual old survivor probability mu on Z/K and the actual pure-conditioned new-coordinate laws rho_q, rho_r. All heights and all original phases are fixed. At an old coordinate x, let B_q(x) be the union of the q-coordinate cylinders supplied by original q-only classes whose old cofactors match x; define B_r(x) similarly. Let C(x) be the union of the q/r rectangles supplied by the mixed original classes whose old cofactors match x. The mixed inventory includes old cofactor d=1.

Write

    alpha(x) = rho_q(B_q(x)),
    beta(x)  = rho_r(B_r(x)),
    gamma(x) = (rho_q x rho_r)(C(x) intersect (B_q(x)^c x B_r(x)^c)).

Then the same product law from report463 has exact live mass

    nu(U) = E_mu[(1-alpha)(1-beta)-gamma]
          = 1-E alpha-E beta+E(alpha beta)-E gamma.

The product alpha beta is exact because q and r are conditionally independent under the single fixed product law. The old x is shared, so its expectation cannot be replaced by a product of two means.

For the raw sums of individual-cylinder probabilities L_q(x), L_r(x), L_m(x), the exact union-bound gain is

    W = E[L_q-alpha] + E[L_r-beta]
        + E[alpha beta] + E[L_m-gamma] >= 0.

Thus nu(U)=1-E[L_q+L_r+L_m]+W. The four terms retain within-axis overlap, shared-core cross-axis overlap, and mixed deletion already accounted for elsewhere. Existing R and density upper bounds do not by themselves determine these joint quantities.

A paired original-phase example makes that information loss explicit. Let K=3, mu be uniform on {1,2}, and old original class be 0 mod 3. Take pure 0 mod q and 0 mod r, a q-only class with projections (1 mod 3,1 mod q), and an r-only class with projections (h mod 3,1 mod r). Both h=1 and h=2 have R=1/2, density cap 3/2, E alpha=1/[2(q-1)] and E beta=1/[2(r-1)]. For h=1 the shared overlap is 1/[2(q-1)(r-1)]; for h=2 it is zero. Numeric labels and all separate expected loads agree. This rules out recovering the overlap from those separate data; it does not rule out further uniform estimates using richer structural data.

## A rectangular trapping criterion with original labels

Let K be odd, coprime to distinct odd primes q,r, with t nonunit positive divisors. Put mu=delta_1 and use original old classes 0 mod d for every nonunit d|K. Then mu is an actual old survivor probability,

    R_K(mu)=t,       mu <= K H_K.

Use pure original classes 0 mod q and 0 mod r. For distinct nonunit old divisors, assign q-only classes with projections 1 mod d and successive nonzero residues modulo q, up to min(t,q-1). Do the same on r. On the old fibre x=1 these classes leave a rectangle of size

    (q-1-t)_+ (r-1-t)_+.

There are t+1 distinct mixed modulus labels dqr, d|K, including d=1. If

    (q-1-t)_+ (r-1-t)_+ <= t+1,

assign one such original label to each residual rectangle cell, with old phase 1 whenever d>1. All moduli are actual, odd and numerically distinct. The entire old fibre x=1 is now covered. Consequently every probability with old marginal delta_1 gives zero survivor mass. More strongly, no nonzero surviving measure can have old marginal dominated by any finite multiple of delta_1. Changing conditional kernels or permitting a dominated change of old marginal cannot repair this fixed support.

This is not an integer covering. The CRT point with old coordinate 2 and q,r coordinates both 1 avoids the complete original family: it avoids old zero classes and every nonunit-cofactor class; the unit mixed class, if used, lies in the residual rectangle and hence has no coordinate 1. This applies for t>=1, as in the concrete instance below.

## Exact report462 scalar thresholds at q=23,r=29

Choose

    K=3^6*5^2=18225,  t=20,  q=23,  r=29.

There are 21 positive divisors. The remaining 2-by-8 rectangle has 16 cells, so the criterion holds. The probability satisfies

    R_K(mu)=20 < 70874/3375,
    mu <= 18225 H_K <= 455625 H_K.

There are 78 original classes: 20 old, two pure new, 20 q-only, 20 r-only and 16 mixed. The actual pure-conditioned product has 616 equally weighted points. Exact counts are

    q-only union: 560,
    r-only union: 440,
    q/r overlap: 400,
    mixed residual: 16,
    survivors: 0.

In particular alpha=10/11, beta=5/7, E(alpha beta)=50/77, gamma=2/77, and (1-alpha)(1-beta)=gamma. Even retaining the exact large cross-axis overlap does not produce positive live mass in this instance. It is not merely a defect of the scalar union bound.

The full period is 12156075. The integer 5121227 is explicitly uncovered; its CRT coordinates are (2 mod K,1 mod 23,1 mod 29).

If exactly seven old prime directions are required, append actual pure old classes 0 mod p for p in {127,131,137,139,149}, and take the old law delta_1 on K times the independent uniform nonzero-coordinate laws on those primes. The original trapping classes still cover its entire support. With c=product p/(p-1),

    R_padded=21c-1=45039362339/2166577920 < 70874/3375,
    density cap=18225c=6372801934965/337023232 < 455625.

This padding is not the first-seven-prime support. It only shows that the scalar obstruction survives a seven-coordinate requirement. The old primes may exceed the two subsequently exposed primes, as allowed by report463's general interface.

## Conclusion and exact boundary

The falsified claim is: *every actual old survivor law satisfying report462's two scalar certificates necessarily admits a positive extension through original 23 and 29 classes by the report463 product-and-delete construction.* Indeed this actual old law has no surviving point above its support at all.

This does not refute existence of a different admissible old law, the particular source-selected law of report462, a theorem with additional information about that law, or a proof specialised to old support {3,5,7,11,13,17,19}. It is not a counterexample to Erdos #7. A successful general continuation must obtain extra information about the actual seed law, choose it with future phases in view under a valid common-law argument, or use another joint construction. Merely deriving a larger overlap correction from the two scalar certificates cannot guarantee positivity for arbitrary laws satisfying those certificates.

The [standalone program](../../frontier/cover-geometry/two_prime_scalar_countermodel.py) enumerates only 616 product cells, retains all 78 original CRT residues, verifies the separate full-period avoiding integer, and checks the exact rational thresholds. The [result data](../../frontier/cover-geometry/two_prime_scalar_countermodel.json) contains this actual class inventory and the finite controls. Its checks use explicit exceptions and remain enabled under optimized Python. Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/two_prime_scalar_countermodel.py
```

The program tests the finite countermodel and its stated scalar bounds; it does not inspect or replace the arbitrary-height source construction.
