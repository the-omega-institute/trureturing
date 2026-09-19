[Index](../marked_head_profile.md) · [Adopted quadratic costs](113-quadratic-hinges-and-the-factorial-tail-share-one-head.md) · [Actual-source interface](131-ten-complete-quadratic-costs-share-their-actual-off-face-head.md) · [Uniform hinge operator](134-one-complete-cost-is-uniform-on-a-nonzero-k-neighborhood.md) · [Common portfolio and mass](137-eleven-original-costs-share-one-uniform-k-neighborhood.md) · [Uniform factorial head](138-the-complete-factorial-tail-is-uniform-on-a-source-neighborhood.md)

# Ten adopted quadratic costs share a uniform source neighborhood

On134's actual-source neighborhood

    qK>=1-sigma, sigma<=1/10000,
    rho<=1/100000, r<=1/520,

the ten original positive-expansion quadratic rows satisfy

    sum_(i in I) weight_i*Cost_i
      <=657441925477112732727911969427910963320838177034441
        /52125777872062494315118058344639991040000000000000
      =12.612606512860838... ,                    (QP1)
    I=(41,42,43,44,45,47,48,49,50,51).

The same portfolio on the face, with the controllers actually adopted
in113, is2111889246010484736362835017/167630845620786142795200000,
or12.598452499535751.... The uniform excess is0.014154013325086565....
Zero radius recovers that adopted portfolio exactly.

Nine rows use the common hinge/factorial head from113, transported
through134 and138. Row47, raw81 n=2, retains its stronger original
raw-source controller;113's weaker positive-expansion candidate is
not substituted. Every cost keeps its original independently labelled
test, all polynomial and geometric tails, both K orientations and
every feasible root1 beta distribution.

These are ordinary continuous-domain bounds with exact arithmetic.
They supply ten numerator components. Raw81 n=1, the square complement,
the remaining original rows, the signed mass and the full survival
denominator remain separate consumers. There is no new global K or
Lean claim.

## 1. Preserve the nine adopted positive expansions

For each of41,42,43,44,45,48,49,50,51 use its original113 identity

    f_i(v)=sum_t a_(i,t)*(v-t)_++theta_i*Phi5(v),
    a_(i,t)>=0, theta_i>0, f_i(1)=0.             (QP2)

131's original-tag reconstruction checks all finite transitions and
both coefficients of the complete eventual polynomial, including
the exact original AP cap parameters. No finite load cutoff is used
to infer(QP2). All ten rows in I have f_i(1)=0. Therefore this
portfolio has no mass constant requiring an upper or lower S bound;
137's mass bounds are still needed by the full signed consumer.

For the same original six-head layout ell and positive-seven head xi,
134 gives a uniform enlarged finite hinge bound, with the corrected
mean credit and the seven-coordinate shifted residual prices.138
gives the full factorial bound

    integral Phi5(A_i)dmu<=Jbar(ell)+Pbar.

Its original ell is retained. Define the modified finite objective by
adding theta_i*Jbar(ell) before maximizing over ell and xi. The
head-independent complete payment is theta_i*Pbar. This is131's
same-head formula with its inputs replaced by uniform source bounds,
not by separately maximized hinge and factorial totals.

The factorial envelope uses the fixed common radius rho0. It is
already valid at every actual q and residual vector in that radius.
Consequently theta_i*Jbar(ell) is a q-independent nonnegative addition
to134's fixed-head convex objective. Convexity on134's polygon is
preserved. This conservative use of the factorial radius does not
claim the sharper coordinate allocation retained for the hinge part.

## 2. One actual source, common q and common residual coordinate

Write F_(i,ell,j)(q) for134's complete fixed-support expression after
adding the two factorial terms. Its seven prices already include
the actual bounded-head union error, source-corrected mean prices
and every omitted old/positive-seven tail. All supports are fixed
before the q maximization.

For the same actual shifted vector y,

    sum_j y_j<=rho0-g*(q5+q15)=e(q), y_j>=0.

The portfolio upper is

    max_(q in vertices(P)) max_j
         sum_i weight_i*max_(ell,xi)F_(i,ell,j)(q). (QP3)

Different original costs have independent heads. The equality that
moves their finite maxima inside the weighted sum is precisely137's
independent-test argument. Every cost uses the same q and j in(QP3).
There is no independent choice of residual coordinate per cost.
The positive weighted sum and finite maxima preserve the convexity
needed for the polygon vertices.

For each row, the complete support candidates are(8,6,6,5),
(10,10,10,10) and(12,12,12,12). Each candidate is first maximized
completely; the selected fixed vector is then used in(QP3). Every
row selects(8,6,6,5). The remainder beyond each cut is its entire
geometric sum, including the original25/27/75/81 omission rules.
At zero radius the exact zero-error cap series is used directly,
so no artificial fixed-cut intercept prevents face recovery.

## 3. Row47 keeps the original raw81 controller

Row47's adopted face bound is

    1344356641/405168750=3.31801660666080... .

It comes from84's original source.square357(81/4,dat), with the
genuine convex raw-source function maximized over the three beta
vertices on each face. Its all-load majorant is the identity.
113's candidate3.332315550105... is larger and was not adopted.

The following explicit continuity estimate transports this original
controller. For two effective source records put

    N=||n-n*||1, E=||eta-eta*||1,
    F=||d-d*||infinity, s=sum n.

For the complete original raw357 function at81/4,

    |raw357(dat)-raw357(dat*)|
      <=(57/14)*N+(3153/280)*E+(5471/11340)*F.    (QP4)

106's projection gives N<=delta/2,E<=delta/9,F<=5*delta/4.
The projected beta is allowed anywhere in the full raw-controller
simplex: no first-beta triangle or common finite-LP witness is
required.84's convex face maximum therefore gives

    Cost47<=1344356641/405168750+(25207/6480)*delta.
                                                        (QP5)

At delta=1/10000 this is516293472151/155584800000. The controller
ignores the mixed-seven deletion, so no rho payment is needed.
Its weighted bound can be added as a constant in every q,j entry
of(QP3), retaining the same adopted controller at zero radius.

## 4. Reusable complete raw-source continuity prices

Here is the proof and reusable computation behind(QP4). Let f be
one of the pinned nonnegative increasing convex original costs,
with eventual polynomial a*v^k+b, k in{1,2}. The original ternary
baselines take values1,2,3. In verify_joint_frontier's zero5_raw,
the finite source part is a maximum of

    sum_l[n_l*f(B_l)+eta_l*C_f(B_l)]
                   +max_l Deep_f(B_l,d_l),     (QP6)

where C_f is zero5_centered_correction. Its N price is
max_(v=1,2,3)|f(v)|, and its E price is
max_(v=1,2,3)|C_f(v)|. Signed centered coefficients are bounded by
absolute values; no componentwise monotonicity is assumed.

The deep function is a positive weighted sum of running maxima of

    d*[f(v+j+1)-f(v+j)]+C_f(v+j+1)-C_f(v+j).

Changing d by at most F changes the jth running maximum by at most
F*[f(v+j+1)-f(v+j)], because convexity makes these f increments
nonnegative and nondecreasing. The exact summed price is therefore

    max_(v=1,2,3)sum_(j>=0)3^(-j-3)*[f(v+j+1)-f(v+j)],

computed by the existing zero5_convex_pure_deep. Its entire linear
or quadratic polynomial continuation is retained.

The separate positive-five expression is a sum of maxima affine
in eta, plus an eta-independent deep constant. Before its polynomial
entrance c, the largest eta coefficient is

    sum_(2<=n<c)4*(n-1)*5^-n*[f(3n)-f(n)]/n.

The complete remaining coefficient is

    a*(T_k-T_(k-1))*(3^k-1)+J_f,
    T_j=4*sum_(n>=c)n^j*5^-n,
    J_f=sum_(2<=n<c)4*5^-n*f(n)+a*T_k+b*T_0.

All coefficients in this positive-five expression are nonnegative.
Taking the largest baseline3 is legitimate. Adding this E price to
the absolute centered price proves a three-coordinate Lipschitz
bound for the complete raw35 operator.

Finally the exact zero7_raw formula is

    raw357_f=(E7_f-tau_f)*s
              +sum_(e=0..c-2)raw35_(seven_block(f,e))
              +tau_f*raw35_(v^k),               (QP7)

with tau_f>=0 and all count tails evaluated exactly. Add the finite
raw35 prices, their tau_f-weighted monomial price, and
|E7_f-tau_f| to the N price using|Delta s|<=N. This proves the
generic interface raw_source_lipschitz(source,tag,seven=True).
Setting seven=False supplies the raw35 prices. This argument applies
to both linear and quadratic original convex costs; it does not
infer continuity from successful finite samples.

For(QP4), the resulting prices are exactly57/14,3153/280 and
5471/11340. Their projection combination is25207/6480. The checker
evaluates every geometric moment through the existing complete
source functions and verifies the six original face vertex values.

## 5. Exact portfolio and verification

The nonzero-radius individual bounds, shown as decimal displays, are

| Index | Adopted controller | Uniform upper |
| --- | --- | ---: |
|41|Same hinge/factorial head|5.291541429504682|
|42|Same hinge/factorial head|1.4520780049810111|
|43|Same hinge/factorial head|0.17191455110472845|
|44|Same hinge/factorial head|1.6451991791656904|
|45|Same hinge/factorial head|0.2298441641345596|
|47|Original raw square357|3.318405603574385|
|48|Same hinge/factorial head|3.941300311442666|
|49|Same hinge/factorial head|4.3036642240889895|
|50|Same hinge/factorial head|4.50061733534678|
|51|Same hinge/factorial head|4.6206475126805175|

Every authoritative value, weight and coefficient is rational in
the certificate. The nonzero-radius computation includes
9*3*12500*10=3375000 original branches and108 independent rational
LP checks. The zero-radius recovery adds1125000 branches and36
rational checks. Every adopted face comparison is exact, including
row47's separately retained controller.

The common portfolio maximum is at q=(0,0), in the omega coordinate.
Here its value equals the sum of the individual weighted maxima;
the numerical gain from sharing is zero. This equality does not
remove the shared-budget obligation for the general interface.
No maximizing outer table or residual allocation is asserted to be
realized by an actual congruence family.

[uniform_quadratic_cost_portfolio.py](../frontier/uniform_quadratic_cost_portfolio.py)
and its [certificate](../certificates/source_norms/uniform_quadratic_cost_portfolio.json)
retain the complete component bounds and common maxima.

```sh
python3 -I -O docs/reports/erdos7-odd-covering/frontier/uniform_quadratic_cost_portfolio.py --check
```

The remaining full numerator and denominator must use their own
correctly directed mass terms and adopted controllers before a
source-uniform comparison or global replacement is claimed.
