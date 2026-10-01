# Six-direction continuation needs an aggregate hinge budget, not a bounded old query

The [six-direction pointwise inequality](738-full-convex-source-supports-six-fresh-prime-heights.md) remains valid without requiring the
support fields to satisfy `C_J<=384`. Extend the pair penalty linearly with
terminal slope640. Every argument at which the certificate evaluates its
conjugate is at most503.685, so the conjugate and the already verified gate
are unchanged.

This removes a range obstruction, not the old-height source obligation.
For one actual source, the sufficient obligation is that the **sum** of its
unary hinge costs, pair costs and higher-support mean costs is below19000.
It need not satisfy the shallow comparator separately in every field.
The same sufficient obligation has a stronger, explicit17-threshold
complete-query formulation. Neither budget has been proved uniformly for
arbitrary old heights. These are ordinary deductions from the existing
six-direction certificate, not new Lean verification.

## 1. The conjugate never reaches the terminal slope

Keep the six reference capacities and the fixed certificate coefficients:

    r=(28,30,36,40,42,46), m=r-1=(27,29,35,39,41,45),
    kappa=1/5000, target=19000.

Let

    T=(1,8,10,12,16,20,24,32,40,48,64,80,96,128,160,192,256,384).

On[1,384], let g interpolate `v^2` linearly at these knots. Define

    g_inf(c)=g(c)                                  if1<=c<=384,
             384^2+640(c-384)                      ifc>=384.       (OH1)

This is increasing and convex on[1,infinity), because its successive
secant slopes are the increasing numbers `v_j+v_(j+1)` and its last
secant is256+384=640. The extension is linear, and does **not** claim to
majorize `c^2` beyond384. No such quadratic majorization is needed.

For every0<=s<=640,

    sup_(c>=1)(s c-g_inf(c))
       =max_(v in T)(s v-v^2)=:g_star(s).                         (OH2)

On each finite interpolation interval the objective is affine; on the
terminal ray its slope is `s-640<=0`. Thus an endpoint attains its
supremum, including at s=640. This proves(OH2) on an unbounded domain.

For arbitrary real fields `C_J>=1`, set

    A_i=C_{i}, u_i=(r_i-A_i)_+, P=product_i u_i,
    b_J=product_(i outside J)u_i,
    Q2=sum_(|J|=2)b_J C_J,
    H=sum_(|J|>=3)b_J C_J,
    Hbar=sum_(|J|>=3)C_J product_(i outside J)m_i,
    W=(P-Q2-H)_+.

Since0<=u_i<=m_i, every pair argument used by the old certificate obeys

    0<=lambda b_J<=kappa*35*39*41*45
                 =100737/200=503.685<640, 0<=lambda<=kappa.     (OH3)

The strict slope slack is27263/200. Consequently the same finite
conjugate values apply to every unbounded pair field. Young's inequality,
`Hbar>=H` and `H+W>=(P-Q2)_+` give

    kappa W+sum_(|J|=2)g_inf(C_J)+kappa Hbar
       >=Psi(u),
    Psi(u)=max_(0<=lambda<=kappa)
             [lambda P-sum_(|J|=2)g_star(lambda b_J)].           (OH4)

The inherited complete-domain scalar certificate states

    sum_i f_i(A_i)+Psi(u)>=19000   for EVERY real A_i>=1,       (OH5)

where `f_i(a)=sum_t c_(i,t)(a-t)_+/100` and the nonzero coefficients are

| i / t | 8 | 10 | 12 | 16 | 20 | 24 | 32 |
|---|---:|---:|---:|---:|---:|---:|---:|
|1|12634|52898|34342|41801|0|0|0|
|2|15374|0|60271|58710|0|0|0|
|3|6885|0|24801|28063|34776|25472|0|
|4|6385|0|16214|19003|12339|49940|0|
|5|4735|0|15737|15922|7199|51748|0|
|6|0|5894|11911|11324|0|22024|52293|

Its interior exact enclosure and exterior unary argument already cover
all A_i>=1; neither is being inferred from new samples. Combining them
with(OH4) proves, for **all63 fields in[1,infinity)**,

    kappa W+F(C)>=19000,
    F(C)=sum_i f_i(C_{i})+sum_(|J|=2)g_inf(C_J)
                  +kappa sum_(|J|>=3)C_J product_(i outside J)m_i. (OH6)

The coefficients of the final sum add to934878. Its42 fields, the15
pair fields and the six unary fields all remain in this one inequality.

## 2. Actual fields at arbitrary old and fresh heights

Fix ONE finite original family with pairwise distinct odd numerical
moduli greater than1 and one globally fixed phase per original. Let

    P0={3,5,7,11,13,17,19,23},
    Q0=product_(p in P0)p^H_p,

where the old heights H_p are arbitrary nonnegative finite integers.
Every original divides

    Q0 product_(i=1)^6 q_i^E_i,

with six distinct fresh primes outside P0, sorted at least29,31,37,41,43,47,
and E_i arbitrary nonnegative finite integers. Missing coordinates may
have height0. Q0 must include the old exponents of **fresh-bearing**
originals as well as those of old-only originals.

Choose one nonnegative finite measure nu on `Z/Q0 Z` such that

    nu<=Haar_Q0, nu is supported outside every old-only original,
    rho=nu(1)>0.                                                   (OH7)

For nonempty fresh support J and positive exponent tuple e on J,
the originals with that exact tuple have old cofactors d|Q0. There is
at most one original per d: otherwise its full numerical label repeats.
Complete the partial old-cofactor query to one phase for every d|Q0,
retaining each original's old projection. Denote the completed load
by L_(J,e). Its unit term is1. Added query slots are analytic upper
bounds, not extra forbidden original classes.

Put

    alpha_(J,e)=product_(i in J)(q_i-1)/q_i^e_i,
    Omega_J=sum_(1<=e_i<=E_i)alpha_(J,e)
           =product_(i in J)(1-q_i^(-E_i)),
    C_J=(1-Omega_J)+sum_e alpha_(J,e)L_(J,e).                     (OH8)

If some E_i=0 in J the sum is empty and C_J=1. Every mixture is finite
and1<=C_J<=tau(Q0), but no uniform upper bound384 is asserted. All
fields are functions on the SAME old source and keep the actual
fixed phases and full numerical exponent tuples.

The existing unary carving proof works without any hard range bound.
At an old point x, the actual unary forbidden q_i-fibre has Haar mass
at most C_{i}(x)/(q_i-1). Restrict Haar to its actual unary survivor,
then fractionally thin to mass `(1-C_{i}(x)/(q_i-1))_+`. Its mass on
an actual depth-e cylinder is at most q_i^(-e). Tensor these SIX
dominated submeasures. Every mixed original is charged on its actual
fixed joint cylinder, retaining the other coordinate masses. Grouping
and applying(OH8) gives the familiar lower fibre response.

For larger actual fresh capacities than r, the **normalized** response
is nondecreasing. Where all u_i>0, it equals

    product_i(1-A_i/r_i)
      *[1-sum_(|J|>=2)C_J/product_(j in J)(r_j-A_j)]_+.          (OH9)

Both nonnegative factors increase coordinatewise with r. If some u_i=0,
the response is zero; continuity completes the boundary argument.
Holding the actual field values fixed therefore bounds the actual
fresh Haar survivor below by `W(x)/product_i r_i`, using the reference
capacities in(OH6). No phase or source is reselected for this comparison.

## 3. The sufficient source budget is one aggregate inequality

Define the absolute cost of the actual fields by

    B_nu=integral F(C(x)) dnu(x).

Integrating(OH6), using(OH7) and the actual carving construction gives

    Haar(full survivor)
      >=[19000 rho-B_nu]_+/(kappa product_i r_i).                (OH10)

In particular the strict gate is simply

    B_nu<19000 rho.                                              (OH11)

This allows costs on different supports to compensate. It imposes
neither independence among fields, individual copies of one comparator,
separate caps on each moment, nor a fieldwise improvement over the old
source. The source must be the same in every summand.

In normalized notation write nu=h mu, where mu is a probability and
**h mu<=Haar_Q0**. With `B_mu=E_mu F(C)`,(OH10) becomes

    Haar(full survivor)
      >=h[19000-B_mu]_+/(kappa product_i r_i).                    (OH12)

For example, mu may be uniform on one actual old survivor set of Haar
mass h. Merely knowing that some survivor set has mass h does not
give(OH12) for a different nonuniform mu. A known bound
`mu<=D Haar` instead permits h=1/D.

Under the shallow reference comparator Y, the previously certified cost is

    B_ref=2670385906653884932/151398428146875.

Consequently a new supported source and its actual fields pass whenever

    B_mu-B_ref
      <206184228136740068/151398428146875
       =1361.865051443705... .                                  (OH13)

The left side is the **signed aggregate excess**: a more expensive
component can be offset by a less expensive component. Requiring every
excess separately to be nonpositive is stronger than needed. This
comparison supplies no estimate for a new source by itself.

The source-existence obligation relevant to this fixed certificate is:
for every specified full family, construct ONE nu satisfying(OH7) and
(OH11). It is sufficient, not a necessary condition for noncoverage.
Allowing nu to depend on the full family is legitimate. A source chosen
from the old family alone and working for every fresh continuation is
a stronger uniform statement.

## 4. A stronger universal test uses only17 hinge levels

For one fixed measure nu as in(OH7), define

    S_nu(t)=max_L integral(L-t)_+ dnu,                            (OH14)

where L ranges over complete divisor queries on Q0 with one fixed phase
per numerical divisor. The maximum is finite for each finite Q0; its
maximizing layout may depend on t, but **nu never does**. This is an
upper bound on each query, not a claim that all maxima are simultaneously
attained by one query or one original family.

The piecewise-linear pair penalty has the exact representation

    g_inf(c)=1+sum_t a_t(c-t)_+, c>=1,

where a_1=9, and at every interior knot
`a_(v_j)=v_(j+1)-v_(j-1)`. The last nonzero coefficient is
a_256=192. There is no hinge at384: the final slope continues unchanged.

By Jensen on each finite mixture(OH8), every hinge reading of C_J is
at most S_nu(t). The constant padding contributes zero because t>=1.
Since C_J>=1, its mean is at most `rho+S_nu(1)`. Summing the six unary
penalties,15 pair penalties and42 higher-support charges therefore gives

    B_nu<=B_profile(nu)
      =(504939/2500)rho+sum_t d_t S_nu(t),                       (OH15)

with the following exact positive coefficients:

| t | d_t | t | d_t |
|---:|---:|---:|---:|
|1|804939/2500|8|59513/100|
|10|16198/25|12|43069/25|
|16|186823/100|20|33157/50|
|24|41796/25|32|76293/100|
|40|240|48|360|
|64|480|80|480|
|96|720|128|960|
|160|960|192|1440|
|256|2880|||

Thus `B_profile(nu)<19000 rho` is an explicit stronger sufficient
interface independent of which fresh query fields arise. It permits
positive probability above384 and does not require the entire ICX order
relative to Y. Only one weighted total of these17 hinge bounds is used.

For `S_nu(t)<=rho E(Y-t)_+`,(OH15) reproduces **exactly** rho B_ref.
The known h=104726/6084351 then recovers the previous shallow density

    2699106184481030045171/53817625874009626674318000>1/20000.

Seventeen objective levels are not seventeen source states. The old
query menu and actual prefix compatibility data can still grow with
the full old heights. Equation(OH15) does not supply a bounded-size
representation, an efficient optimizer, or a uniform-height bound.

The weakening is strict at the scalar-field level. On ONE abstract
probability space let every one of the63 fields equal the same variable C,
with law

    Law(C)=(1-epsilon)Law(Y)+epsilon delta_1000,
    epsilon=1/100000.

This is one joint law, with all fields completely correlated. It has

    E(C-384)_+=77/12500>0,

so it violates both C<=384 and `C<=_icx Y`. Nevertheless the fee when
all fields equal1000 is379470996/25, giving the exact aggregate budget

    E F(C)=3740749621838208374119/210275594648437500<19000,
    19000-E F(C)=254486676482104125881/210275594648437500>0.       (OH16)

Thus the new condition admits positive mass beyond the old comparator's
support. This example proves strict weakening of the scalar assumption;
it does **not** claim that these63 coincident fields arise from one
arithmetic congruence family or furnish the missing old-height source.

## 5. Existing old-height results and the remaining obligation

The attributed eight-prime theorem used in [Report734](734-seven-and-eight-full-height-heads-admit-quartic-prime-tails.md) supplies a genuine
positive source at arbitrary old heights: on the full old carrier,
Haar restricted to the actual old-only survivor has mass at least
1/1002375 and is dominated by Haar. This invokes Michael Schroeder's
*Nine Prime Divisors in Odd Distinct Covering Systems*, edition1.0.1,
`cor:uncovered-density`, at the repository's stated attribution and
local-replay boundary. It establishes(OH7), **not**(OH11) or(OH15).
No new local Lean replay of that theorem is claimed here.

[Chapter09](../../../problem-details/09-quantitative-extension-of-the-old-prime-powers.md) already gives ordinary arbitrary-height lifting conditional
on a suitable same-source query bound and a deletion debit below1.
Its displayed universal finite-base calibrations are explicitly false
by the recorded star construction. [Chapter14](../../../problem-details/14-a-shared-parameter-improvement-for-arbitrary-three-prime-heights.md) supplies useful
arbitrary-height three-prime source bounds; it does not supply the
eight-prime17-hinge budget above.

[Report726](726-the-exact-joint-moment-still-blocks-the-complete-scalar-gate.md) excludes the particular complete-debit criterion
`A(p)+Gamma_star(p)/19<1` for every probability on its75-row actual
head with independent Haar higher5/7 digits. [Report729](729-the-same-root-head-has-a-finite-joint-moment-obstruction.md) supplies another
exact obstruction on the85-row head at its stated coefficient. Neither
excludes a conditional higher-digit source, actual union credits, or
the field-dependent summed penalty in(OH11). Conversely, those
obstructions do not constitute evidence that(OH11) holds.

[Report689](../650-699/689-actual-pure-support-averaging-gives-a-finite-all-height-query-interface.md)'s surviving-prefix averaging retains actual pure holes and
reduces its declared normalized-cylinder **suprema** to finite menus,
provided the reference density is constant on each surviving conditioning
atom and the query menu is descendant-closed. It does not automatically
preserve the whole-query hinge integrals in(OH14), nor the phase-specific
fields in(OH8). A use here must prove that additional transfer. Prefix
probabilities or individual cylinder caps alone omit relevant data.

Actual prefix submeasures with tree consistency and fixed-phase cylinder
readings may support a direct estimate of(OH11). No uniformly positive
full old-core budget has been constructed here. A positive old survivor
mass, separately optimized source laws or unchanged shallow query slots
cannot replace this estimate.

The concrete missing proposition is therefore a **uniform same-source
bound for the weighted total in(OH11), or the stronger(OH15)**, with all
old original and query exponents included. Freeing the old heights while
silently retaining C_J<=384 is unnecessary and invalid; replacing it
by the proved linear penalty leaves this quantitative proposition explicit.
Even proving that proposition would settle this six-fresh-direction
family. It would not by itself prove arbitrary-support Erdős#7 or a
uniform further-tail moment invariant.

The640 continuation is specific to the six-direction numerical gate.
A different gate whose conjugate arguments exceed640 requires a steeper
extension or another penalty and budget. In particular, (OH3) is not a dimension-independent bound.

## 6. Exact arithmetic and proof scope

The [standard-library consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old_height_hinge_bridge.py)
reconstructs the support coefficients, conjugate-argument caps, terminal
slope, seventeen hinge coefficients, exact aggregate fee and strict
weakening example. Its [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_old_height_hinge_bridge.json)
binds the unchanged scalar certificate and comparator result by their
hashes. It verifies their fixed data but does not rerun the inherited
six-variable enclosure or the original source geometry.

An independent calculation reconstructed the hinge coefficients from
successive secant slopes, summed complementary support charges and
recomputed the budget, strict weakening example and density from the
canonical source law. Finite checks at knots and interval midpoints
support the arithmetic; the affine-ray proof in(OH2) supplies the
unbounded quantifier. Explicit checks remain active with Python -O.
The arbitrary-old-height source budget remains unproved, and no new
Lean verification is claimed.
