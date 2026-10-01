# The exact paired-source gap for an eleven-prime head

The existing eight-coordinate paired seed cannot certify a positive
survivor after the additional reference primes31,37,41 using [Chapter08's](../../../problem-details/08-arbitrary-head-transfer-by-the-joint-load-invariant.md)
scalar mass/Gamma recurrence, for ANY choices of the three constant
clipping thresholds. This is a continuous method obstruction, not a
failed finite grid. It concerns the stated comparison budget, not the
actual surviving measure, all possible source laws, or odd covering.

The same calculation gives an exact, reusable target for improving the
source: its mass-to-Gamma ratio must exceed

    Rcrit approximately0.00290038335747,

whereas the current certified ratio is

    R0=0.0024267850833266212237....

Both ratio values refer to paired bounds on ONE actual source. The exact
radical formula and certified rational enclosures appear below. No new
source with the required improved bounds has been constructed here.

The continuous scalar optimization is reused from [Report304](../../257-320/304-an-actual-star-blocks-a-universal-scalar-restart-at19.md),
especially(SC1). Its notation is f=G/M and its output capacity is C_q(H).
Here R=1/f and the backward map below is exactly
B_q(t)=1/C_q(1/t) for t>0, with its continuous limit at0. The formulas
are restated in the mass-to-Gamma orientation to expose the new source
obligation; no new generic scalar optimization theorem is claimed.
Report04's optimal scalar clipped certificate provides another example
of this method boundary, but it uses a different rectangle/profile
relaxation and is not substituted into the present recurrence.

## 1. General clipping on one actual source

Let a finite nonnegative old measure mu be supported on the actual
survivors and satisfy

    mu(X)>=M>0, Gamma(mu)<=G,
    Gamma(mu)=max_L integral L^2 dmu,

where L ranges over complete numerical-divisor layouts, including1.
At a new prime q, use the complete q^H-coordinate Haar law and the
actual current bad union, including pure q-powers. All original moduli
remain distinct complete numerical labels with globally fixed phases.
At every depth e the earlier forbidden conditions give a partial query
layout; Chapter08's completion and pair argument applies to all depths.

For a constant threshold0<delta<1 the normalized clipped kernel has
Haar density at most1/(1-delta), and its actual bad mass is bounded by

    G/[4delta(1-delta)(q-1)^2].

Although the displayed capped-deletion statement in Chapter08 is often
used at delta<=1/2, its proof extends to every0<delta<1: the same kernel
is normalized, and(t-delta)_+<=t^2/(4delta) is valid for every delta>0.
The complete exponent-pair sum is

    a=a(q)=(3q-1)/(q-1)^2.

Extend by this normalized kernel, then restrict to the actual bad-set
complement WITHOUT renormalizing. Restriction decreases every integral
of the nonnegative L^2. Thus one valid paired comparison update is

    M'=M-G/[4delta(1-delta)(q-1)^2],
    G'=G[1+a(q)/(1-delta)].                               (R1)

Both bounds describe the same actual restricted measure. They are
comparison numbers, not assertions that actual mass and actual Gamma
attain the displayed extrema. There is no division by the surviving mass.

Replacing delta>1/2 by1-delta leaves the debit unchanged and decreases
the Gamma multiplier. For positive certificates it therefore suffices
to consider0<delta<=1/2. This reflection does not assert equality of the
physical kernels or of their actual resulting measures.

## 2. Exact one-step optimal ratio

Set

    R=M/G, c=1/[4(q-1)^2].

Whenever the updated budget has positive mass, its ratio is

    Phi_q(R,delta)
      =[R(1-delta)-c/delta]/[1-delta+a].                  (R2)

A positive one-step budget is possible precisely when R>4c, since
max_delta delta(1-delta)=1/4. When R>4c, differentiation of(R2) gives

    sign(dPhi/ddelta)
      =sign[-Ra delta^2-2c delta+c(1+a)].

The polynomial on the right strictly decreases on delta>0. It is
positive at0 and negative at1/2 because its value there is a(c-R/4).
Thus there is one strict global maximizer on0<delta<=1/2:

    delta*(R,q)
      =(1+a)/[1+sqrt(1+Ra(1+a)/c)] in(0,1/2).             (R3)

The ratio there is

    V_q(R)
      =[R(1+a)-2c-2sqrt(c[c+Ra(1+a)])]/(1+a)^2.           (R4)

These are exact formulas, not numerical optimizer outputs. At the
boundary R=4c, the best mass is zero, achieved by delta=1/2. When
R<4c no threshold gives a positive budget, so a positive-certificate
iteration must stop; a negative formal ratio is not a survivor bound.

For each fixed delta,

    dPhi/dR=(1-delta)/(1-delta+a)>0.

The positive-domain optimum V_q is consequently strictly increasing.
It follows inductively that, for a fixed remaining prime sequence,
maximizing this comparison ratio at each step maximizes every later
comparison ratio. In particular it is horizon-optimal for the final
POSITIVE-BUDGET criterion. This does not assert optimal final mass,
minimal actual Gamma, or an optimal physical/source strategy. Those
objectives are different. No Pareto state enlargement or threshold grid
is needed for this scalar positivity task.

## 3. An exact backward threshold, without differentiation

For a desired final ratio t>=0, define

    B_q(t)=t+[sqrt(c)+sqrt(c+a t)]^2
          =(1+a)t+2c+2sqrt(c(c+a t)).                     (R5)

For a fixed delta, the condition Phi_q(R,delta)>t is exactly

    R>t+c/delta+(c+a t)/(1-delta).

The inequality

    u^2/delta+v^2/(1-delta)>=(u+v)^2,
    u=sqrt(c), v=sqrt(c+a t),

follows from

    [u(1-delta)-v delta]^2/[delta(1-delta)]>=0.

Equality occurs at delta=u/(u+v)<=1/2. Therefore

    exists delta with Phi_q(R,delta)>t
      if and only if R>B_q(t).                           (R6)

This criterion is strict: equality yields best final ratio t, not a
strictly positive excess. Since t>=0, satisfying(R6) also preserves
positive intermediate mass whenever the eventual target requires it.

For extra primes31,37,41 the exact initial threshold for positive
final mass is

    Rcrit=B_31(B_37(B_41(0))), B_41(0)=1/1600.             (R7)

More generally a subsequent tail whose charge is bounded by t times
the final Gamma uses the same composition with t in place of0. Thus the
backward map is also an explicit tool for connecting a finite head to a
later tail criterion. No tail theorem for the newly improved hypothetical
seed is claimed in the present calculation.

## 4. The current seed fails even continuous optimization

The [existing763 seed](763-a-joint-query-head-admits-an-unrestricted-prime-tail-above-1400.md) used in the [nine/ten-head continuation](766-nine-and-ten-prime-heads-with-a-missing-small-prime.md) is

    M0=10237584019/168750000000,
    G0=26010182627/1040449536,
    R0=237083545724928/97694496044921875.

Integer-square-root enclosures with outward rational rounding certify

    9063697992101/3125000000000000
      <=Rcrit<=1450191678736161/500000000000000000.

Numerically these endpoints are0.002900383357472320 and
0.002900383357472322, and R0 is strictly below the lower endpoint.
The exact continuous forward optima are enclosed as follows:

|step|optimal delta|largest next ratio|
|---|---:|---:|
|q=31|0.45760642649865967...|0.001100266711003520...|
|q=37|0.48540490849272163...|0.000281563149237973...|

The last ratio is strictly below1/1600=0.000625, the necessary and
sufficient one-step positivity threshold at41. All real threshold
choices within(R1) are covered, including choices depending on the
previous scalar bound. This is stronger than failure of half clipping
or any finite threshold grid.

There is also a shorter certificate requiring no square roots. For
all0<delta_i<1,

    4delta_i(1-delta_i)<=1,
    1+a(q_i)/(1-delta_i)>=1+a(q_i).

These give a lower bound on the cumulative DEBIT OF THE SCALAR BUDGET:

    G0[1/30^2+(1+a(31))/36^2
                 +(1+a(31))(1+a(37))/40^2]
      =228291372917179/3371056496640000.

Consequently its final mass lower-bound variable obeys

    M3<=-1857729195660261599/263363788800000000000<0.       (R8)

This is not a lower bound on the actual losses or on actual Gamma.
The negative result is about the sufficient bound(R1), whose upper
Gamma variables have deterministic multiplicative growth. The actual
measure may have substantially more survival and a smaller Gamma.

## 5. Actionable paired-source obligations

Keeping the current Gamma bound G0, the exact threshold requires mass
strictly greater than

    G0 Rcrit approximately0.0725066408374 .

Keeping the current mass lower bound M0, it requires Gamma strictly
less than

    M0/Rcrit approximately20.9169468583 .

These are alternative same-source targets. A mass bound on one measure
and a Gamma bound on another do not meet either target. Improving the
source ratio by any combination can be tested directly against(R7).

For concrete rational sufficient targets, either of the hypothetical
paired seeds

    (M0,209/10), or (73/1000,G0)

crosses the exact threshold. The rational thresholds

    (delta31,delta37,delta41)=(9/20,47/100,1/2)

already work, with no use of irrational optimal thresholds. Exact
iteration of(R1) gives positive final mass budgets respectively

    1055989934891/22699237500000000,
    45043276408211/91885368508416000.

The consumer verifies positive mass at every intermediate step and
records the paired Gamma bounds. These are CONDITIONAL sufficient
certificates. Neither improved actual source has been established here.

## 6. Scope of the obstruction and remaining routes

The reference tuple is31,37,41 after the transported eight-coordinate
source. Larger actual extra primes can have smaller charges and growth,
so this does not exclude positive certificates for selected larger
prime tuples. For the proposed uniform eleven-small-prime extension,
the minimal tuple is an admissible case, so mere scalar threshold
optimization of this unchanged seed cannot supply that uniform proof.

The obstruction applies to(R1) with one global constant threshold per
prime and its specified comparison coefficients. It does not rule out
source-specific quantitative Gamma decrease from actual bad-set deletion,
stronger joint transfer information, another source construction,
history-dependent fibrewise thresholds with separately proved bounds,
or an improved finite-height estimate. Neither the actual covering
problem nor all physical capped-kernel strategies are ruled out.

The original numerical labels, all finite original heights, fixed phases
and arbitrary support arities remain in Chapter08's recurrence. Their
role is not weakened by this optimization. The proof optimizes only
certified scalar transport, while the potential improved paired-source
bounds remain genuine open obligations.

## Exact consumer

The [consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_three_step_ratio_barrier.py)
and [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_three_step_ratio_barrier.json)
reproduce the continuous threshold and the conditional rational certificates:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_three_step_ratio_barrier.py
```

The consumer pins the inherited paired seed and imports304's capacity
and integer-square-root functions directly, without executing that report's
unrelated star calculation. It reconstructs Gamma from its joint pair
factors, encloses every radical, checks(R8), and verifies both conditional
rational witnesses. The default invocation compares a fresh recomputation
with the retained result. An independent rational-bisection implementation
confirms the critical interval and its separation from the current ratio.
No threshold grid or solver search is used. These are exact arithmetic
checks of the ordinary continuous argument, not new Lean verification or
a construction of either improved source.
