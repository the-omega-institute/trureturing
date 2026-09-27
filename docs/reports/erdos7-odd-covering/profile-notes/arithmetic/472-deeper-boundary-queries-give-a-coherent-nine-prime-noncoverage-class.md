# Deeper boundary queries give a coherent nine-prime noncoverage class

Let C be a finite family of residue classes with pairwise distinct odd numerical moduli greater than one, all supported on

    {3,5,7,11,13,17,19,23,29}.

Put K=3^4·5·7·11·13·17·19=130945815. Suppose there is one integer a such that every original class c mod m touching 23 or 29 has

    m=d·23^j·29^k,   j+k>0,   d|K,   c=a mod d.       (CB1)

Then C does not cover the integers. Its actual full survivor set has normalized Haar mass at least

    193575624497669/71320120312500000000 >0.           (CB2)

Classes supported entirely on the first seven primes have arbitrary original residues and arbitrary finite heights. Heights at 23 and 29 and all original residues on those two coordinates are also arbitrary. CB1 concerns only the old cofactor and old residue of a class touching a new prime. Classes may be absent; no completion or replacement of their phases is assumed. There are no additional support primes in this statement.

The proof first forces positive old-survivor mass onto a set with at most sixteen active old cofactors. Every point in that set has a surviving 23/29 fibre of Haar mass at least 1/11, for the same fixed original family. These are ordinary deductions from the common law of [report467](467-the-same-core-law-has-a-smaller-density-cap-and-tail-cutoff.md) and finite residue partitions, accompanied by exact arithmetic checks. They are not new Lean certification or a solution of unrestricted Erdős #7.

## Refinement has a simultaneous query cost

For a probability mu on Z/K, write

    m_d(mu)=max_c mu(x=c mod d),
    R_K(mu)=sum_(1<d|K) m_d(mu).

For any K dividing K', the least complete query sum among all lifts nu with projection mu is exactly

    min_(pi_*nu=mu) [1+R_(K')(nu)]
      =sum_(e|K') [gcd(e,K)/e] m_(gcd(e,K))(mu).     (CB3)

Indeed, put d=gcd(e,K). A maximizing d-cylinder is partitioned into e/d residue classes modulo e. Thus m_e(nu)>=(d/e)m_d(mu) for every lift. The uniform lift on each reduction fibre attains every one of these lower bounds simultaneously: each compatible e-cylinder receives exactly d/e times the corresponding d-cylinder mass. This proves the minimum identity. No independence assumption is imposed on an arbitrary competing lift. Requiring a lift to avoid additional original classes can only restrict the feasible set.

For the K in CB1, expose one additional digit on every old prime:

    Kplus=3^5·5^2·7^2·11^2·13^2·17^2·19^2.

Set P=(3,5,7,11,13,17,19) and h=(4,1,1,1,1,1,1). Grouping e|Kplus by d=gcd(e,K) assigns the coarse label d the weight

    beta_d=product_(p: v_p(d)=h_p)(1+1/p).          (CB4)

This grouping includes the unit label. Each label and each cylinder maximum belongs to the same law.

## A pointwise certificate on the entire high-load region

For a coarse point x, let v_p=min(v_p(x-a),h_p), with v_p=h_p when x=a modulo p^h_p. Define the coherent query and its refinement payoff by

    Q_a(x)=sum_(d|K) 1_(x=a mod d)=product_p(v_p+1),
    Psi_a(x)=product_p[v_p+1+(1/p)1_(v_p=h_p)].      (CB5)

For any probability nu on Kplus, apply the lower bound in CB3 and bound each coarse maximum below by its phase a cylinder. Expanding CB4 gives

    1+R_(Kplus)(nu) >= integral Psi_a dnu.           (CB6)

The expansion is pointwise: summing beta_d over d dividing gcd(x-a,K) contributes v_p+1 from the available coarse exponents, with the additional 1/p precisely when the highest coarse exponent is available.

On the entire region B_a={Q_a>=20},

    Psi_a >= c=7280/323.                           (CB7)

Here is a short proof independent of profile enumeration. Let s count the zero roots among 5,7,11,13,17,19, and put t=v_3+1 in {1,2,3,4,5}. Then Q_a=t·2^s.

* If s<=1, Q_a cannot reach twenty.
* If s=2, Q_a>=20 forces t=5. The smallest two root factors are at 17 and 19, giving (5+1/3)(2+1/17)(2+1/19)=7280/323.
* If s=3, then t>=3, so Psi_a>=3·2^3=24>c.
* If s=4, then t>=2, so Psi_a>=32>c.
* If s>=5, then Psi_a>=32>c.

Equality in CB7 occurs at the truncated profile (4,0,0,0,0,1,1). There are 320 coarse profiles, of which 170 have Q_a>=20. In contrast to [report471](471-deeper-queries-force-mass-outside-a-load-twenty-plateau.md), CB7 covers the whole high-load region at this coarse period, not only the fifteen strata with ternary valuation four and exactly two other zero roots.

The low query values are exactly

    {Q_a<20} values = {1,2,3,4,5,6,8,10,12,16}.

In particular, Q_a<20 implies Q_a<=16. The gap between sixteen and twenty is used in the actual fibre estimate below.

## One source law must give the low-load set positive mass

For an arbitrary old-only original family, let U be its actual survivor set. Choose a single finite old-prime period M resolving all its original moduli and Kplus. The source law retained in report467 satisfies

    supp(mu)=U,
    mu<=Lambda7 H_M,   Lambda7=6075000000000/7235955529,
    R_M(mu)<=A,        A=70871/3375.                (CB8)

The corresponding lower density bound is available but not needed here. Query labels e|Kplus are a subset of those at M, so their nonunit sum is at most A. The source result applies to this sufficiently deep period even if the extra query digits occur in no old-only original modulus.

Put alpha=mu(B_a). The partition proof of CB6 applies homogeneously to the unnormalized restriction mu|B_a. Its complete query sum is at least c alpha, and its unit cylinder contributes alpha. Cylinder maxima of mu dominate those of the restriction. Therefore

    R_M(mu)>=(c-1)alpha,
    mu(Q_a<=16)>=1-A/(c-1)=588542/23479875=:eps.    (CB9)

The same argument handles alpha=0 without normalization. Since mu is supported on U and has the density cap in CB8,

    H_M(U intersect {Q_a<=16}) >= eps/Lambda7.      (CB10)

No laws at different depths are interchanged. Translation by a only changes the query centres, not an original forbidden residue. CB9 holds for every chosen centre; CB1 specifies the one used by the original later classes.

## The actual 23/29 continuation retains at least one eleventh

Fix any old survivor x counted by CB10. Let

    D_x={d|K: x=a mod d}.

It contains the unit cofactor and has |D_x|=Q_a(x)<=16. By CB1, every later original class active at x has its old cofactor in D_x. Fixing d and a pair of new exponents specifies the numerical modulus uniquely. Distinctness of the original moduli therefore gives at most one original class for each such triple; no fibre may choose new original residues.

At a fixed 23-exponent j>=1, at most sixteen 23-only classes are active. Their union, summed over every occurring exponent, has Haar mass at most

    16 sum_(j>=1)23^(-j)=16/22.

This includes pure 23-powers through d=1. Thus the set G23 avoiding all these axis classes has mass at least 6/22. Similarly the set G29 avoiding all 29-only classes has mass at least 12/28. The actual finite-height geometric sums are bounded by the displayed infinite sums; no infinite family is introduced.

Before deleting cross classes, the new-coordinate survivors are G23 times G29. For each j,k>=1, at most sixteen cross classes are active, each with Haar mass 23^(-j)29^(-k). Their union has mass at most

    16 sum_(j,k>=1)23^(-j)29^(-k)=16/616.

Subtracting this upper bound from the product of the two axis survivor masses gives the actual full fibre bound

    H(fibre survivors at x)
      >=(6/22)(12/28)-16/616
      =1/11.                                     (CB11)

Cross classes with unit old cofactor are included. Axis deletions factor because they concern separate new coordinates after x is fixed; no independence between cross deletions is used.

Integrate CB11 over the actual old Haar set in CB10. On a finite period resolving the whole original family, this yields

    H(full original survivors)
      >=eps/(11 Lambda7)
      =193575624497669/71320120312500000000.        (CB12)

Positive finite Haar mass gives an avoiding residue and hence an uncovered integer. This proves CB2 for the original family with all its fixed labels and residues.

## Exact checks, reuse and remaining boundary

The [standard-library checker](../../frontier/cover-geometry/coherent_boundary_two_prime_escape.py) groups all 4374 fine divisor labels into their 320 coarse labels and verifies the payoff expansion on all 320 truncated profiles. It checks the high-load minimum, the low-load spectrum, the source-bound arithmetic and the actual two-prime fibre margin with rational arithmetic. Its [result data](../../frontier/cover-geometry/coherent_boundary_two_prime_escape.json) retain the inputs and exact outputs.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/coherent_boundary_two_prime_escape.py
```

Optional `--output PATH` writes JSON. Checks use explicit exceptions and remain enabled under optimization. The computation does not enumerate the full CRT period or rerun source geometry or Lean. The arbitrary-height partition proof and CB8 are mathematical inputs, not conclusions established by checking finitely many constants.

The closest retained interfaces are [Chapter09](../../problem-details/09-quantitative-extension-of-the-old-prime-powers.md)'s uniform fibre lift, [report439](439-actual-residual-lifting-and-exact-free-coordinate-cost.md)'s free-coordinate second-moment cost, and reports467 and 471. The first-moment refinement cost above connects these interfaces to the actual joint 23/29 continuation. The unrestricted-phase nine-prime results in [report463](463-two-actual-prime-extensions-preserve-a-common-core-law.md) and report467 require larger eighth and ninth primes; they do not cover this first-nine-prime subclass. No direct dominating result for CB1 was found in the searched repository reports. No claim of literature novelty is made.

The restriction d|K is essential to the stated proof: with larger old cofactors, Q_a need not count all active later labels. The common centre is also essential to this certificate: with independent old residues, the later active-label count is not controlled by this coherent query. Neither restriction is imposed on the old-only family. Removing these two conditions while controlling the same original joint fibre remains unresolved, as does unrestricted Erdős #7.
