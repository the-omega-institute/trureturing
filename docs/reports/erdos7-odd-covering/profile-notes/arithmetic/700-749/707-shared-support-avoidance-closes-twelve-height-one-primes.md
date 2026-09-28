# Whole support avoidance closes the twelve-prime height-one continuation

Every finite distinct odd nonunit congruence family on at most twelve
actual support primes, with every original satisfying v3(m)<=1, has
positive survivor Haar density; the exact bound below exceeds 1/450.
This is an ordinary mathematical deduction and exact arithmetic, not
new Lean verification. It combines one actual survivor source with the
complete scalar query and actual pure-outside continuation.

## 1. Existing support theorem and a small positivity interface

[Chapter21 KR8--KR12](../../../problem-details/21-coupled-first-root-profiles-and-an-exceptional-five-prime-block.md)
and [Chapter23 CK6--CK10](../../../problem-details/23-conditional-kernels-and-recursive-block-noncoverage.md) already give the support
intersection version of the Scott--Sokal/Shearer theorem, using
[Theorem4.1(a) of Scott--Sokal](https://arxiv.org/html/cond-mat/0309352v2). If support
events E_D live on independent full coordinates, their intersection
dependency graph has the avoidance polynomial

    Z_A(c) = sum_{F disjoint supports in A} (-1)^|F| product_{D in F} c_D.

All coordinate residuals positive suffice for the full strict Shearer
region (including every induced event subgraph), and actual avoidance
probability is at least Z_A(c). The direct coordinate recurrence is

    Z_A = Z_{A minus i} - sum_{D subset A, i in D} c_D Z_{A minus D}.

Here every support has at least two coordinates. This gives a useful
interface when |A|=8: it suffices for all coordinate residuals of size
at most6 to be positive, to conclude the unconditional numerical bound

    Pr(avoid every E_D) >= Z_A(c).                         (SS1)

If Z_A<=0, this is trivial. If Z_A>0, each displayed subtraction has
nonnegative terms, all involving residuals of size<=6. Consequently
every seven-coordinate residual is at least Z_A>0, and the strict
region follows. Positivity of all coordinate residuals extends to
every event-induced subgraph by reducing omitted event weights to zero:
the derivatives are -Z_{A minus D}, so induction on coordinate size
preserves positivity when any weights decrease. This explains the full
Shearer hypothesis, rather than checking only one top polynomial.

For Q=(5,7,11,13,17,19,23,29), the common cap box needed below is

    c_D <= 2 product_{q in D} 1/(q-3), |D|>=2.

At its maximum, the minimum residual for each coordinate cardinality
k=0,...,6 is respectively

    1, 1, 3/4, 17/32, 21/64, 789/4480, 3251/71680.

These are exact minima over all declared subsets, not merely over the
first k coordinates. All247 residuals of cardinality<=6 are positive.
They stay positive throughout the cap box, by the derivative induction.
There are three negative seven-coordinate residuals at the maximum and
the eight-coordinate value is -4635703/37273600; SS1 deliberately does
not assume these maximal seven/eight-dimensional values are positive.

## 2. One actual source and the complete shared numerical-label budget

Retain [Report528 FC3--FC6](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md)'s actual product source lambda. There are two
surviving ternary roots, each of weight1/2. On root r the star-survivor
submeasure is product_q eta_qr, with mass factors

    m_qr=1-beta_qr, beta_q1+beta_q2<=b_q=1/(q-2).

For a complete nonternary support D, put b_D=product_D b_q and let
theta_Dr be the sum of literal cylinder caps for original3d labels with
support D that target root r. Complete exponent vectors and one original
phase for every numerical label are retained. Distinctness gives

    theta_D1+theta_D2 <= b_D.

The original no3 labels d contribute at most b_D on either root. Under
the normalized star product on root r, the entire original group with
support D therefore has probability at most

    c_Dr=(b_D+theta_Dr)/product_{q in D}m_qr.

Complete theta once to sum b_D, writing theta_D1=x_D b_D and
theta_D2=(1-x_D)b_D. This completes a cap budget, not the actual family.
It cannot duplicate a3d label across roots. Since m_qr>=1-b_q,

    c_Dr <= 2 product_{q in D}1/(q-3).

Disjoint D depend on disjoint full prime coordinates under this same
root product. SS1 consequently supplies the unnormalized root lower
bound

    sum_{F disjoint, |D|>=2} (-1)^|F|
       b_{union F} g_r(union F) product_{D in F}(1+x_Dr),
    g_r(U)=product_{q outside U}m_qr,
    x_D1=x_D, x_D2=1-x_D.                              (SS2)

No global cover minimality or private-region forcing is used.

## 3. Joint root bounds and the correct concavity

For k disjoint supports with union U, the coefficient in the root sum
is

    g_1(U) product_D(1+x_D) + g_2(U) product_D(2-x_D).

It is affine in each x_D separately, so its extrema on the cube occur
at endpoints. With j assignments to root1 its value is

    2^j g_1(U) + 2^(k-j) g_2(U), 0<=j<=k.

For an even k term in SS2 use the minimum of these k+1 values; for an
odd k term use the maximum, since that term is subtracted. Let E_k
denote that minimum/maximum and let N(h,k) count set partitions of an
h-element set into k blocks, each of size at least2. Then one uniform
lower response is

    G(beta)=(g_1(empty)+g_2(empty))/2
       +(1/2) sum_{k=1}^4 (-1)^k
          sum_U N(|U|,k) b_U E_k(g_1(U),g_2(U)).        (SS3)

Here N(0,0)=1 and

    N(h,k)=k N(h-1,k)+(h-1)N(h-2,k-1).

Different termwise extrema need not be jointly attainable; the signs
make this a valid lower relaxation. In particular the k=1 part is
exactly FC6, preserving the shared root allocation already there.

Fix all beta entries except one pair(beta_q1,beta_q2). Each g_r(U) is
affine in that pair. For even k, E_k is a minimum of affine functions,
hence concave. For odd k, -E_k is a negative maximum of affine functions,
also concave. Thus the ENTIRE G is separately concave in each beta pair;
this does not inherit concavity merely from the old FC6 term.

The actual beta pair lies in the triangle with vertices(0,0),(b_q,0),
(0,b_q). Iterating the separate concavity therefore bounds G below by
its minimum over the3^8=6561 triangle vertices. No star-mask enlargement
or change of source is needed. Exact integer evaluation gives

    alpha_* = 4945117/39037950 = .12667460765742053... .  (SS4)

Only the saturated partition A={5}, B=Q minus{5}, and its root exchange
minimize this lower response. These minimizing comparison vertices are
not asserted to be attained by a finite original family. At this corner
the old FC6 value is32977687/429417450, and the new correction is

    61196/1226907 = .049878271132204804... .

Thus alpha=lambda(U_actual)>=alpha_*, and the single query source is

    mu=lambda restricted to U_actual / alpha.

The proof uses the signed root lower polynomials in SS2. Truncating each
root value to its positive part is a valid probability lower bound, but
would not preserve the concavity argument just given. The actual finite
periods, complete source tails and all original labels remain fixed.

## 4. The previously checked query and continuation now have a reserve

Use Report528 FC17--FC20's ternary-truncated query construction on the
nine-core3,5,7,11,13,17,19,23,29. Its auxiliary multiplier is
M=(1+B)product_q(1+J_q), with B Bernoulli(1/2) and the complete nonternary
run tails Pr(J_q>=j)=c_q q^-j for j>=1, where c_q=(q-1)/(q-2).
At t=8 the exact scalar hinge is

    H0 = 36645196186562338862630609094665977037308771636736172158282771192951
         /91259075188331710704228574683636183224582522412602232580056664218750.

The same source mu serves every query; its nonunit query sum is at most
7+H0/alpha_* =10.169942757947005..., below39481/3615. The pure-conditioned
outside primes31,37,41 have the retained constants

    Q=241/2639, s=3511/39585, A8=1+s-8Q=14176/39585.

The original-family continuation therefore leaves unnormalized mass

    J=A8 alpha_*-Q H0 = .00869348113553861... >0.

The full old-and-outside product source is dominated by
(524288/134589) times Haar, giving the precise Haar lower bound

    6281023587738184305721905053142973502097475572877610426248176504676427
    /2814472824255297408335211233160838072379407147685788194996044021760000000
    = .0022316874171276206... >1/450.                  (SS5)

This uses Report463 PE3--PE5 / Report464 FQ2--FQ4's actual pure-outside
conditioning. All original ternary heights are at most1, so the truncated
old-query inventory covers every continuation cofactor required here.

For arbitrary at most12 actual primes containing3, the existing finite
prefix transport of Reports460/462 fixes3 and injects benchmark prefixes
into actual-prime prefixes, pairing the other primes in increasing order.
Pull back the one actual family along these injections, preserving its
complete exponent vectors and phases, then average the unnormalized
survivor pushforwards. The ternary injection is the identity. SS5's Haar
bound is preserved. Padding benchmark primes does not change the
ternary-height restriction.

If3 is absent, use the existing empty-core pure-product instance on the
first12 nonternary primes5,...,43. Its product cap is2097152/788307, its
mixed-deletion reserve is1087844306/2731483755, and the Haar lower bound
is543922153/3633315840>.1497>1/450. Larger actual primes only improve this
bound. No arbitrary first-prime height is renamed as a ternary height.

## 5. Exact verification and remaining scope

The [standard-library checker](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_support_shearer.py)
reconstructs all256 maximal-cap residual polynomials and verifies the247
low-dimensional strict inequalities. It evaluates every one of the6561
actual beta-triangle vertices using a common integer denominator, then
reconstructs the complete query hinge from its first moment and the
small product atoms through8. The [compact result](../../../frontier/cover-geometry/fibre-credit-partition/fibre_credit_support_shearer.json)
contains the exact minima, minimizing vertices, continuation constants,
density bounds and a digest of the complete vertex numerator list.
Default execution checks this result; explicit output mode regenerates it.

Independent checks use set-partition coefficients for the low-dimensional
residuals and a separate rational computation of all128 saturated
partitions. A full triangle computation agrees with their minimum.
Normal, optimized and different-directory replay agree. The probability
argument, shared allocation and concavity above supply the theorem;
finite arithmetic alone is not asserted to prove those interfaces.

All exponents other than the stated ternary cap are arbitrary finite,
and the actual prime values need not be bounded. More than twelve actual
support primes, or a deeper ternary exponent in this whole-family
version, are not settled by this result. No restricted comparison vertex
is asserted to be an actual covering family.
