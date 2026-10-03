# Joint shallow deletion can change the sign of the higher-core certificate

The boundary beyond the [clipped singleton source](751-clipped-common-sources-release-core-and-outside-heights.md) is the **joint surviving measure**, together with how each actual deletion intersects its query cylinders. Retention, the complete old marginal, and every conditional single-coordinate marginal are insufficient even to determine whether the current higher-core certificate is positive.

This note gives an exact deletion-credit identity, a checkable sufficient condition and source-selection LP, and an actual distinct-modulus pair where the certificate has opposite signs despite all those summaries agreeing. The example uses a declared common weighted prior, not Haar conditioning on the entire shallow survivor set. All mathematics and arithmetic here are ordinary finite arguments, not Lean. A uniform theorem admitting arbitrary core-shallow multiple-outside originals remains unresolved.

## 1. The object whose positivity matters

Fix the reference core `315=3^2*5*7`, shallow outside exponents at most one, and a finite actual joint source on the shallow carrier. A numerical query slot is `(d,J)` with `d|315` and outside subset `J`. Write its phase cylinders as `C_(d,J,a,t)` and put

```text
Sat(d)={3:9|d} union {5:5|d} union {7:7|d},
kappa(d)=product_(p in Sat(d)) p/(p-1)-1,
Q_(d,J)(F)=max_(a,t) F(C_(d,J,a,t)),
R(F)=sum_(d,J) kappa(d)*Q_(d,J)(F),
J(F)=mass(F)-R(F).
```

The two zero-coefficient core slots are `d=1,3`; there are 320 nonzero slots for five outside axes. All maxima are computed on the **same** nonnegative measure `F`.

Uniformly extend `F` in the higher core digits. At a fixed positive core excess vector, original numerical distinctness gives distinct projected saturated slots, including all outside subsets. Summing those actual original masses and the complete positive geometric tails yields higher-core deletion mass at most `R(F)`. Therefore

```text
J(F)>0 and F<=D*Haar  ==>  Haar(actual higher-core survivors)>=J(F)/D>0.
```

This is the previous marked bound in homogeneous form. It applies to arbitrary actual joint `F`; it does not require conditional product fibres or a row-uniform ansatz. Actual higher-core phases remain globally fixed, and outside exponents are still at most one in this version.

## 2. Exact deletion credit records where the mass was removed

Let one actual event, or an actual finite union of events, remove `G=F restricted to E`, so `F'=F-G`. For a query slot `l`, define its old maximum and phase slack

```text
M_l=max_c F(C_l,c),
s_l(c)=M_l-F(C_l,c)>=0.
```

Then the reduction in that maximum is exactly

```text
credit_l(F,G)
 =M_l-max_c(F(C_l,c)-G(C_l,c))
 =min_c [s_l(c)+G(C_l,c)].                              (JC1)
```

Consequently the whole same-source margin obeys the exact identity

```text
J(F-G)=J(F)-mass(G)+sum_l kappa_l*credit_l(F,G).          (JC2)
```

The credit can exceed the lost mass after summing the relevant query coefficients, so deleting a concentrated part of a source can improve this certificate. The maximizing phase can switch after deletion; the minimum over *all* phases in (JC1) accounts for that switch. Tracking only the mass removed from one old maximizing phase does not suffice.

A usable sufficient condition is to choose numbers `eta_l>=0` and verify

```text
G(C_l,c) >= (eta_l-s_l(c))_+  for every phase c.         (JC3)
```

Only phases with `s_l(c)<eta_l` require a positive deletion-intersection bound. Then

```text
J(F-G)>=J(F)-mass(G)+sum_l kappa_l*eta_l.                (JC4)
```

These are common-source upper/lower statements. They do not assume that distinct phase maxima or credits are attained at a common query. For a sequence of actual deletions, apply (JC4) to the updated source at each step; its gains telescope. A next uniform theorem could establish a positive final lower bound for this total loss-minus-credit expression, without requiring every individual deletion to improve the margin.

## 3. Joint marginals supply the intersections in the credit

As in the [joint update interface](750-marked-boundaries-and-joint-deletion-updates.md),
at each old row retain the unnormalized joint marginals `F_x(K,s)`. For an original with old condition `x=a mod d` and outside condition `y_J=t`, the correct update is

```text
F'_x(K,s)=F_x(K,s)
 -1_(x=a mod d)*1_(s,t compatible on K intersect J)
                   F_x(K union J,s union t).           (JC5)
```

Aggregating over an old cylinder gives the deleted mass in each requested query cylinder. Thus the data needed by (JC1)--(JC3) are joint scopes `K union J`, along with the old phase slack. Single-coordinate marginals omit these intersections. One need not always store an entire joint table: a smaller family of scopes closed under the actual required unions, or certified bounds sufficient for (JC3), can suffice. Higher outside powers require compatible prefixes and their common refinement; they cannot be supplied by the shallow root-count shortcut.

## 4. A bounded-density joint source-selection LP

Let `rho` be a declared actual prior with `rho<=D*Haar`, and let `A` be the set surviving all actual shallow originals, including multioutside ones. Write `v=rho restricted to A`. Choose a submeasure `0<=F<=v`, and maximize `J(F)`. A finite LP is

```text
maximize  sum_x F_x - sum_l kappa_l V_l
subject to 0<=F_x<=v_x,
           V_l>=sum_(x in C_l,c) F_x  for every l,c.     (JC6)
```

Any exact feasible solution with positive objective immediately gives a higher-core Haar lower bound equal to that objective divided by `D`. The source is chosen jointly on actual cells; it need not be uniform on an outside fibre. Numerical optimization may propose a solution, but every cylinder inequality can be checked rationally. No optimizer is required for a positive certificate.

Finite minimax gives the equivalent dual value

```text
max_(0<=F<=v) J(F)
 =min_gamma sum_x v_x*(1-score_gamma(x))_+,
score_gamma(x)=sum_(l,c) gamma_(l,c)*1_(x in C_l,c),
gamma>=0,  sum_c gamma_(l,c)=kappa_l.                  (JC7)
```

Indeed `R(F)` is the maximum of these linear scores against `F`; exchange max/min over compact finite polytopes, then optimize each coordinate `F_x` independently. If `v` is positive on its declared support, a zero optimum is equivalent to a dual score at least one everywhere on that support. That excludes every source law on **that support** after rescaling, not all laws on a larger actual survivor set omitted by `rho`.

This is also the [existing RC1 construction](../../001-064/13-probability-capped-deletion-and-a-joint-observation-beyond-this-boundary.md) applied to the true joint-cylinder functional:

```text
max_(0<=F<=v) J(F)=mass(v)-R_cap(v).
```

It does not contradict the [full357 scalar obstruction](../700-749/749-an-actual-prefix-blocks-every-scalar-source-reweighting.md): that obstruction uses the specified `beta+theta*Q` scalar field family and a different support-function operator. No inclusion between these field families on their different supports and interfaces is asserted. The LP/duality identities are standard finite convex consequences; the substantive new issue is which actual joint support and cylinder data enter them.

## 5. An actual pair: equal retention and all singleton marginals, opposite signs

Use these eleven old originals:

```text
(3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
(21,0),(35,0),(63,0),(105,0),(315,0).
```

Their old315 survivor set `X` has 102 points and contains 2 and47. Add the pure originals `0 mod p` for `p=11,13,17,19,23`. The common prior on `(x,y11,y13)` has:

* weight one on every `x in X`, `y11 in {3,...,10}`, `y13 in {3,...,12}`: 8160 cells;
* weight 120 on each of the eight cells `x in {2,47}`, `y11,y13 in {1,2}`.

Its total mass is 9120. Extend it by independent uniform nonzero roots at17,19,23. It is an explicitly weighted supported prior, and is the same before either deletion family.

Now add the following four literal original classes. Each family then has twenty distinct odd numerical moduli on the same finite carrier.

| Modulus | Family A forbidden phase | Family B forbidden phase |
|---:|---:|---:|
| 1001=7*11*13 | 639 | 639 |
| 3003=21*11*13 | 2081 | 2081 |
| 5005=35*11*13 | 782 | 3862 |
| 9009=63*11*13 | 7229 | 5150 |

On the small part of the prior, the first two remove the off-diagonal pairs `(1,2),(2,1)` at old row2. At old row47, family A removes the off-diagonal pairs, and family B removes the diagonal pairs. The background roots are all at least3 and are untouched.

Both families remove exactly four weight-120 cells. The remaining mass is 8640, hence retention is `18/19` in each. At both special rows, the remaining total mass and the individual11 and13 root masses agree; the entire background agrees as well. Therefore their complete old marginal and **every conditional single-coordinate marginal** agree, including the extra three axes.

Nevertheless their joint11/13 cylinders differ. For old divisors `d=5,9,15,45`, rows2 and47 have the same old residue. Family A retains the same outside diagonal at both rows, so its largest `(d,{11,13})` cylinder has mass240. Family B retains opposite pairings, giving maximum120. These four slots are the only differing nonzero two-outside query maxima. Their coefficients sum to

```text
kappa(5)+kappa(9)+kappa(15)+kappa(45)
 =1/4+1/2+1/4+7/8=15/8.
```

The additional three independent live-root axes multiply the entire query debit by

```text
(17/16)*(19/18)*(23/22)=7429/6336.
```

Direct exact evaluation gives:

| Quantity on the declared source | Family A | Family B |
|---|---:|---:|
| Remaining mass | 8640 | 8640 |
| Prior retention | 18/19 | 18/19 |
| `J(F)` | -802469/38016 | 9226681/38016 |
| Normalized higher-core debit `R(F)/mass(F)` | 329260709/328458240 >1 | 319231559/328458240 <1 |
| Credit relative to the same prior | 3068177/792 | 26216941/6336 |

The common prior itself has `J=-129827285/38016`. Both actual restrictions improve the margin; only B crosses zero. Their difference comes entirely from the four joint slots, not from a difference in retention or the available singleton summaries.

The raw source has Haar cap `50702925/8`. Thus B's current source certifies, uniformly over any further finite family of distinct higher-core originals within these five shallow outside axes,

```text
Haar(survivors)>=9226681/240940299600>0.
```

Family A is **not** a covering or a failure of every source-selection method. The common background alone survives both families and has `J=3370981/1024>0`. Both therefore admit a different positive source. The example refutes the sufficiency of retention plus all conditional singleton marginals for evaluating the **current** joint source and its deletion credit; it does not refute feasibility of (JC6).

## 6. Exact verification and the next proof obligation

The [exact consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_deletion_credit.py)
reconstructs literal CRT residues, applies the actual numerical congruence
deletions, and builds every cylinder histogram by reduction modulo its
numerical query modulus. It verifies original labels, carrier and source
masses, complete old and conditional singleton equality, forty nonzero
two-outside query slots on each measure, their exact transport to five
outside axes, and every slack-plus-deletion credit. It also verifies the
positive common-background certificate, which prevents interpreting A as
a failure of every source on its actual survivors.

The [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_deletion_credit.json)
is compared with a complete replay. The program uses exact integer and
rational arithmetic and no optimization premise. An independent dense
integer-array enumeration over all45045 residues gives the same source
masses, all eighty nonzero query profiles for A/B, singleton marginals,
credits and signs. These are finite arithmetic checks, not Lean verification.

The next concrete uniform target has two sufficient directions: construct an actual joint source with a positive (JC6) certificate, or prove enough same-source intersection lower bounds (JC3) that the accumulated expression (JC4) stays positive after the actual shallow multioutside deletions. These construction routes have not been proved equivalent: the LP may choose an additional reweighting beyond the specified deletion sequence. Merely proving positive shallow retention does not settle that target. The example specifies exactly four joint query slots whose omitted relations already change its answer.
