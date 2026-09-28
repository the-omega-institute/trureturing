# A two-root supported source passes a fixed fourteen-prime height-one profile

For the specified core singleton profile, the root weights19/50 and31/50 give
one actual-supported law whose full nonternary query bound is below51/4. Its
pure-conditioned continuation through41,43,47 retains full Haar survivor density
greater than3/4000. This is a conditional profile theorem, not uniform
noncoverage for arbitrary fourteen-prime families. It is ordinary mathematics
and exact rational verification, not new Lean verification.

## Actual family, target profile, and finite thinning

Let the core nonternary coordinates be

    Q=(5,7,11,13,17,19,23,29,31,37).

The core includes3, and the outside coordinates are41,43,47. Consider a finite
family of distinct odd nonunit numerical moduli on these primes. Every original,
INCLUDING those touching the outside coordinates, has v3<=1. Nonternary heights
are arbitrary finite. Choose the two roots left by the actual pure3 class; if
that numerical label is unused, append one avoidance class at3 before imposing
the conditional profile below. Name the retained roots0 and1 without changing
any actual residue.

Let lambda_q be Haar conditioned on avoidance of all actual pure q-power
originals. As in [Report528](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md), its cylinder bounds are

    c_q=(q-1)/(q-2), b_q=1/(q-2),
    lambda_q(a mod q^e)<=c_q q^(-e).

On root r, let A_qr avoid the projections of every source-live actual3q^e
original, with a_qr=lambda_q(A_qr). The target retained masses are

    m_5,0=2/3,       m_q,0=1 for q>5,
    m_5,1=1,         m_q,1=(q-3)/(q-2) for q>5.         (FP1)

Assume a_qr>=m_qr. This is an explicit condition on actual star masks; it is
not asserted for arbitrary families. On each actual coordinate define

    eta_qr=(m_qr/a_qr) lambda_q|A_qr.

It has the target mass, is supported on the actual star survivor and is dominated
by the same lambda_q. All masses are positive, so the denominators are valid,
including when a=1. This is finite measure thinning, with no atomlessness premise.
Take w0=19/50,w1=31/50 and form the one predeletion submeasure

    nu=sum_r w_r delta_r tensor product_q eta_qr.

After avoiding all remaining actual core originals, let U be the actual core
survivor, alpha=nu(U), and mu=nu|U/alpha. These same measures serve all queries
and the outside continuation.

## The fixed-profile probability bridge is sufficient in ten coordinates

On root r, grouped nonsingleton-support event caps are bounded by

    2 product_(q in D)(b_q/m_qr), |D|>=2.

For root0, all coordinate residuals on at most eight coordinates at these
maximum caps are positive; the minimum at size8 is

    888304/23856525.

Weight decrease preserves them. If a completed ten-coordinate top polynomial
is positive, the one-coordinate recurrence forces every nine-coordinate
residual positive, because the complementary support in each subtraction has
size at most8. Downward closure then supplies all induced event subgraphs
required by the Shearer probability theorem. If the top is nonpositive, its
signed avoidance lower bound is trivial. Thus the signed ten-coordinate
response is admissible on root0 without a false top-only assumption.

For root1, ALL1024 maximal-cap coordinate residuals are positive, including

    Z_full=59873459/5322670080.

This directly supplies the same conclusion throughout its cap box. The checker
independently computes both sets of residuals using signed nonsingleton-partition
coefficients and elementary symmetric polynomials, not the coordinate recurrence.
The previous thirteen-prime bad-seven bridge is not reused outside its domain.

## Shared label inventory and the changed root weights

For each nonternary support D, the numerical originals d and3d have separate
inventories. The one3d label chooses one actual ternary root; its summed inventory
is shared between the two roots. Completing the inventory for comparison does
not change actual labels or phases. In particular the completed root caps are

    c_Dr=(1+x_Dr)b_D / product_(q in D)m_qr,
    x_D0+x_D1=1, x_Dr>=0.

The no3 support inventory contributes b_D, and the shared3d inventory
contributes x_Dr b_D. Actual event probabilities are bounded above by
these caps; completion imposes no lower bound on actual events.

Let g_r(U)=product_(q outside U)m_qr, b_U=product_(q in U)b_q, and let N(h,k)
count partitions of h elements into k blocks of size at least2. For each disjoint
family of k supports with union U, the extrema of the root coefficient are among

    w0 g_0(U)2^j+w1 g_1(U)2^(k-j), j=0,...,k.

Choose the minimum for even k and the maximum for odd k. Multiplying by its
signed partition count gives a valid common-source lower bound G. It is not
assumed that different termwise extrema are attained together. Exact evaluation
at the changed weights gives

    alpha>=G=8712921199/128193738750>0.                 (FP2)

The same w is used in the query calculation; no old equal-root scalar query
cap is carried over unchanged.

## Root selection stays compatible with the full query tail

For any finite query layout with ternary exponents0,1 and all nonternary
exponents through an arbitrary finite horizon, the labelled ordered-increment
comparison on each root has unnormalized auxiliary masses

    J_q=0: m_qr-c_q/q,
    J_q=j>=1: c_q(q-1)/q^(j+1).

These are nonnegative; positive-depth masses agree across roots. For a fixed
positive-depth support E, let

    a_r=w_r product_(q outside E)(m_qr-c_q/q),
    M=product_q(1+J_q).

The unit nonternary divisor is included. There are M visible3d labels, each
assigned to at most one root. Convexity bounds the query hinge by placing them
all on root0 or all on root1 at this J, giving the integrand

    max(a0(2M-t)_+ +a1(M-t)_+,
        a0(M-t)_+ +a1(2M-t)_+).                       (FP3)

Its two alternatives differ by

    (a0-a1)[(2M-t)_+-(M-t)_+].

The bracket is nonnegative. Hence the maximizing root depends on E but not on
M within that E. Moving this particular two-way maximum through the M integral
is justified by that sign identity; no global max/integral exchange is assumed.

The independent checker instead leaves the maximum inside the integral and
uses the full linear first moment plus exact small-load corrections. For M>=t
the integrand is M(a0+a1+max(a0,a1))-t(a0+a1). The positive-depth mass and first
moment are products of c_q/q and b_q+c_q/q. Only finitely many exact atoms M<t
are needed to correct the linear formula; all infinite geometric tails remain.

At t=8, the exact hinge upper is

    H=1550736200437900822266258293503106585119613595102947530250177781833199805979455302174417150916
      /3979077992122914037545231244599972274732294360773588307186756841616694998995784567353759765625.

Thus the one supported source satisfies

    R(mu)<=7+H/alpha<=7+H/G
      =12.73401072831597... <51/4.                     (FP4)

## Same-law continuation and the corrected Haar density cap

Pure conditioning on41,43,47 gives

    Q_out=355/4797,
    s_out=1733/23985,
    R_target=(1+s_out)/Q_out-1=23943/1775.

It applies to the same mu and all original outside phases, with ternary depth
at most1 throughout the whole family. The source/query score is

    (R_target+1-8)G-H
      =.051315179755402285... >1/20.

Equivalently, with A8=1+s_out-8Q_out=886/1845, the unnormalized final reserve is

    reserve=A8 G-Q_out H=Q_out*score>0.                (FP5)

For a Haar density claim the changed root weights must also be reflected in
the domination cap. The ternary density cap is

    3 max(w0,w1)=93/50,

not3/2. Multiplying all thirteen nonternary pure-coordinate caps, including the
outside ones, gives

    D_Haar=(93/50) product_(q in Q union{41,43,47})(q-1)/(q-2)
          =1495269376/295615125.

The actual full-family Haar survivor mass is at least reserve/D_Haar, namely

    14497284272285229039969661893442238397915513357242350038012275306105248291740772722436029644339
    /19309674535779188927292165500652994443346883102254741632026087523011525719531837457711923200000000
    =.0007507782819137107... >3/4000.                  (FP6)

This is a Haar/natural-density bound in the complete finite CRT period, unlike
the distorted-law tail reserves of Report709. It is conditional on FP1 and the
whole-family height restriction. No no3 case or arbitrary-prime relabeling is
silently included in this fixed-profile statement.

## Exact artifact and unresolved interface

The [standalone exact verifier](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_height_one_fourteen_profile.py)
and [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_height_one_fourteen_profile.json)
count nonsingleton partitions by unordered block sizes with factorial
multiplicities, check all1024 residuals on each root, evaluate the complete
query at the fixed rational weights, and verify the continuation and density.
A coordinate-recurrence residual calculation, associated-partition recurrence,
and small-product convolution independently reproduce these exact values.
Default replay checks the retained result and explicit --output regenerates it.
Run from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_height_one_fourteen_profile.py
```

The unresolved uniform problem is whether arbitrary actual height-one masks
can be covered by such certified target profiles or by a quantified actual-source
transport. The positive certificate at this target does not solve that problem.
The deficit-loss transport of
[Report712](712-exact-deficit-transport-beyond-pointwise-star-bounds.md) can be applied only with an
explicit paid loss and rechecked margin; FP6 is not automatically retained after
such an additional loss.
