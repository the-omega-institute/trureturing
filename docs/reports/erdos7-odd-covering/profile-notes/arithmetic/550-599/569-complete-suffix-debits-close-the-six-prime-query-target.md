# Complete suffix debits close the six-prime two-copy query target

For every finite actual family with at most two residue classes per
nonunit numerical modulus supported on `Q={5,7,11,13,17,19}`, the
unchanged PA construction admits one probability supported on its
complete actual survivor set with

\[
R_Q\le B_*:=\frac{432040125182653876501}{86355045355449035400}
       =5.003067549838209\ldots<257/51.
\tag{SD1}
\]

Every original phase is arbitrary and globally fixed; every finite
original height and the complete all-height query inventory are
allowed. No prescribed old comb, first11 table, missing label,
occupied-root condition or current projection is assumed.

The decisive correction is already enough without a cap-slack estimate:
the complete query contains labels supported only on coordinates still
to be processed. When the comparison adds missing mass, those labels
give a compulsory nonnegative payoff. Keeping that payoff yields the
simpler bound

\[
R_Q\le B_0:=\frac{137303605308635558323}{27345764362558861210}
       =5.021019105124311\ldots<257/51.
\tag{SD2}
\]

A joint convex loss/cap estimate strengthens SD2 to SD1. These results
exclude the remaining NC1 all-supported-laws lower witness of
[Report348](../../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md).
They do not transfer automatically through an arbitrary ternary
prefix: different original powers of3 can create more than two
projected phases at the same numerical cofactor. A restricted
nine-prime consumer, with that multiplicity hypothesis explicit,
is given below. A weighted residual extension requires the two-phase
condition only through ternary exponent5, allowing arbitrary deeper
phases and arbitrary23/29 originals. A density bound restricts this
condition further to534 nonunit cofactors at most500000; that finite
window permits arbitrary additional support primes greater than1000000.
A22-original counterexample to the additive residual certificate
is repaired by retaining the actual cross-cofactor union under the
same law. For the direct seven-core source construction, the analogous
suffix correction is valid but cannot close its stronger query target
using the retained early-stage envelopes: one regenerated finest branch
fails even with maximally generous cap credits, at every real final
threshold from1 through12. Unrestricted Erdős #7 remains open.

## One actual law and its existing mass bounds

Use Report348's order, thresholds and caps:

| Current prime `q` | `t_q` | `C_q` | `a_q=2C_q/(q-1)` |
|---|---:|---|---|
|11|2|`5/3`|`1/3`|
|13|2|`3/2`|`1/4`|
|17|4|2|`1/4`|
|19|4|`9/5`|`1/5`|

The actual pure5/7 survivor Haar masses are `x in[1/2,1]`,
`y in[2/3,1]`. Let `sigma` be their unnormalized product restriction.
Delete the actual mixed5/7 forbidden union, of mass `m<=1/12` under
`sigma`, to obtain `lambda0`. Every later actual row has density

\[
k_q(h,z)=\kappa_q(h)\mathbf1_{G_q(h)}(z),\qquad
\kappa_q=\min(C_q,1/g_q),\quad g_q=H_q(G_q),
\]

with zero row at `g_q=0` and convention `kappa_q=C_q` there.
Its total mass is `s_q=min(1,C_q g_q)`. Write

\[
\Delta_q=\int(1-s_q)\,d\lambda_{<q},\qquad
K_q=\int(C_q-\kappa_q)\,d\lambda_{<q}.
\]

These all use their actual unnormalized prefixes. The existing
conditional comparison gives

\[
\Delta_q\le a_qF_q(x,y),\qquad
s:=\lambda_{\rm final}(1)=xy-m-\sum_q\Delta_q
\ge\alpha:=xy-\tfrac1{12}-\sum_q a_qF_q>0.
\tag{SD3}
\]

Here `F_q` is the full auxiliary old-load hinge at threshold `t_q`.
The raw5/7 auxiliary coordinate measures have total masses `x,y`,
means `x+1/4,y+1/6`, and atoms
`pi_p(1)=w_p-1/p`, `pi_p(n)=(p-1)/p^n` for `n>=2`.
The later coordinate probabilities have

\[
\Pr(N_q=1)=1-C_q/q,\qquad
\Pr(N_q=n)=C_q(q-1)/q^n\quad(n\ge2).
\]

All auxiliary product masses remain `xy`. Their full final hinge at3
is `Phi(x,y)`. Independence belongs to these comparison variables,
not to the actual survivor coordinates. The actual final measure
obeys `H_Q restricted to V <= lambda_final <=9H_Q`, so normalization
preserves exactly the actual survivor support. No intermediate
normalization is used.

## Complete-query suffixes charge every added comparison mass

For each later row, define

\[
\zeta_q=\mathbb E\left(\prod_{r>q}N_r-3\right)_+,
\qquad
\zeta_0=\mathbb E\left(N_{11}N_{13}N_{17}N_{19}-3\right)_+.
\]

The empty suffix has product one, hence `zeta19=0`. Exact values are

| Boundary | Suffix hinge |
|---|---|
|Before11|`zeta0=208872886945/1638469417728`|
|After11|`zeta11=554975819/11284224640`|
|After13|`zeta13=120619/8346320`|
|After17|`zeta17=1/3610`|
|After19|`zeta19=0`|

For every finite fixed query layout, including its unit once,

\[
H:=\int(L-3)_+\,d\lambda_{\rm final}
\le\Phi-\zeta_0m-\sum_q\zeta_q\Delta_q.
\tag{SD4}
\]

To prove this, first fix a complete finite exponent box and all its
query phases. Apply the same conditional convex comparison as
Report348, beginning with the last coordinate. At the current row
`q`, all strictly later coordinates in the remaining main term have
been replaced by independent nested auxiliary uniforms. For every
actual earlier history and every current point, the labels whose
earlier and current exponents are zero contribute exactly the product
of the later truncated auxiliary counts. Consequently the current
payoff, averaged over those later uniforms, is at least `zeta_(q,H)`.
These are query labels, whether or not any original uses them.

Complete the actual row by

\[
\widetilde k_q=k_q+(1-s_q)\frac{C_q-k_q}{C_q-s_q}.
\]

This adds a nonnegative measure of mass `1-s_q`; the denominator is
positive since `C_q>1` and `s_q<=1`. The completed row has mass one
and density at most `C_q`. Its added payoff is at least
`zeta_(q,H)(1-s_q)`. Subtract that amount before comparing the
completed row. Integrate against the actual prefix and extract the
scalar `zeta_(q,H) Delta_q`. Keep it outside all subsequent backward
comparisons. Thus a later-row debit is never recomputed on an earlier
auxiliary source.

After all four rows, the main old-coordinate envelope is at least
`zeta_(0,H)` everywhere. Since `sigma-lambda0` is a positive measure
of mass `m`, replacing `lambda0` by `sigma` adds at least
`zeta_(0,H)m`. Subtract this amount and apply the existing raw-anchor
comparison to the remaining nonnegative full envelope. This proves
the finite-box version of SD4.

Complete any prescribed finite query by arbitrary fixed phases in
larger boxes. Its hinge cannot decrease. The auxiliary `Phi_H` and
each `zeta_(q,H)` converge separately to their full values; their
finite first moments ensure finiteness. Taking those limits proves
SD4. No monotonicity of the difference is assumed. The argument
neither selects phases at individual histories nor duplicates the
unit term.

The same proof also keeps the cap-slack debit of
[Report559 Section9](559-pure-union-savings-control-all-four-later-rows.md):

\[
H\le\Phi-\zeta_0m-\sum_q
                    (\zeta_q\Delta_q+\eta_qK_q).
\tag{SD5}
\]

On a row where `kappa_q<C_q`, its mass is one and the deletion debit
is zero; its cap-envelope slope supplies `eta_q(C_q-kappa_q)`.
Otherwise cap slack is zero and the completion argument applies.
Thus both credits belong to one conditional inequality. The
coefficients are

\[
(\eta_{11},\eta_{13},\eta_{17},\eta_{19})=
\left(\frac{641451990131}{13653911814400},
\frac{130632977}{5642112320},\frac{118307}{16692640},\frac1{6498}\right).
\]

They obey `zeta_previous=zeta_q+C_q eta_q`. This is also obtained
directly by adding the current factor in the auxiliary suffix hinge.

## Deletion alone already crosses the target

For any `Lambda>=zeta0`, SD3--SD4 give

\[
\begin{aligned}
\Lambda s-H
&\ge\Lambda xy-\Phi-(\Lambda-\zeta_0)m
                        -\sum_q(\Lambda-\zeta_q)\Delta_q\\
&\ge\Lambda\alpha-\Phi+D_0(x,y),\\
D_0(x,y)&:=\zeta_0/12+\sum_q\zeta_q a_qF_q(x,y).
\end{aligned}
\tag{SD6}
\]

All coefficients multiplying the upper mass-loss bounds are
nonnegative. In particular the old mixed deletion supplies
`zeta0/12` in this combined inequality even when its actual mass is
smaller: then the retained-mass credit pays the difference.

The quantities `alpha`, `Phi` and `D0` are bilinear in `x,y`.
At `x=1/2,y=2/3`, with `Lambda=155/51`, the old deficit was
`-0.011361818958024154...`; now

\[
D_0=\frac{51786591556298429}{3913893821597760000},\qquad
\Lambda\alpha-\Phi+D_0
=\frac{25377570437213856497}{13573383773301031680000}>0.
\]

The other three corners are positive as well. More precisely the
maximum corner value of `2+(Phi-D0)/alpha` is `B0` in SD2.
Choose `Lambda=B0-2>=zeta0`. The four nonnegative corner values of
SD6's right side interpolate nonnegatively throughout the rectangle.
Thus `H<=Lambda s`. Since `L-1<=2+(L-3)_+`, simultaneous phase
maximization for each finite inventory under this one law and then
exhaustion prove SD2.

## A joint convex penalty strengthens the bound

Retain the actual prefix mass `M_q=lambda_<q(1)` and its existing
lower bound

\[
A_q=xy-\tfrac1{12}-\sum_{r<q}a_rF_r.
\]

Let `mu_q` be the raw auxiliary old-load measure of mass `xy`.
For integers `1<=n<t_q`, define

\[
d_q(n)=\eta_q\left(C_q-\frac{q-1}{q-1-2n}\right),\qquad
J_q=\sum_{n<t_q}d_q(n)\mu_q\{n\}
                       -d_q(1)(xy-A_q).
\tag{SD7}
\]

All `d_q(n)` are positive. For any `w_q>=eta_q C_q`, the function

\[
\psi_q(u)=
\begin{cases}
\eta_q[(q-1)/(q-1-2u)-C_q],&0\le u<t_q,\\
w_qa_q(u-t_q),&u\ge t_q
\end{cases}
\tag{SD8}
\]

is increasing and convex. The two branches meet at zero. The left
derivative there is `eta_q C_q a_q`, at most the right derivative.
For `u=(q-1)(1-g_q)/2`, it equals exactly
`w_q(1-s_q)-eta_q(C_q-kappa_q)`. The upper linear branch remains
an upper envelope when an original union bound exceeds one.

Split actual originals at every current exponent into two globally
fixed slots. Complete each slot to an old query `L_i` including the
unit. With weights `beta_(e,j)=(q-1)/(2q^e)`, their sum is one and
the actual union satisfies `u<=sum_i beta_i L_i`. Monotonicity and
Jensen therefore bound the actual penalty by `sum_i beta_i psi_q(L_i)`.
All phases remain attached to their original full numerical labels.

The function has a negative value at1, so applying subprobability
domination to it directly would be invalid. Instead apply the
existing comparison to the nonnegative increasing convex function
`psi_q(max(u,1))-psi_q(1)`. Every actual and auxiliary load contains
the unit and is at least one. Restoring its constant gives

\[
w_q\Delta_q-\eta_qK_q
\le w_qa_qF_q-\sum_{n<t_q}d_q(n)\mu_q\{n\}
                       +d_q(1)(xy-M_q)
\le w_qa_qF_q-J_q.
\tag{SD9}
\]

The complete first moment makes the infinite slot and query
completions integrable. No nonconvex clipped comparison or signed
domination has been used.

Choose `w_q=Lambda-zeta_q`. The suffix identity ensures
`w_q>=eta_q C_q` whenever `Lambda>=zeta0`. Combining SD5 and SD9,

\[
\Lambda s-H\ge\Lambda\alpha-\Phi+D_0+\sum_qJ_q.
\tag{SD10}
\]

Each `J_q` is bilinear and has positive values at all four corners.
At the worst corner their sum is
`29453940047709845861/15968686792118860800000`.
The exact four-corner quotient comparisons are

| `(x,y)` | `2+(Phi-D0)/alpha` | `2+(Phi-D0-sum J)/alpha` |
|---|---:|---:|
|`(1/2,2/3)`|5.021019105124311…|5.003067549838209…|
|`(1/2,1)`|3.650603189896209…|3.629732273772383…|
|`(1,2/3)`|3.017532302733528…|2.992824752176305…|
|`(1,1)`|2.737719897521626…|2.711772100478736…|

The data retain exact fractions for every entry. The maximum is `B*`
at the first corner. Taking `Lambda=B*-2>=zeta0` makes all four
SD10 corner values nonnegative. Bilinear interpolation and the same
fixed-law query maximization prove SD1. At the target `155/51`, the
worst corner has strict margin

\[
\frac{53066757345018132083}{14287772392948454400000}>0.
\]

## Scope and a restricted original-modulus consumer

Report348 NC2 already supplies a smaller query bound for every other
declared carrier of at most six odd primes excluding3. Together with
SD1 this excludes NC1 for all those carriers. The old necessary
pure-label and phase conditions do not leave an exceptional NC1
family after this estimate.

For an original family of pairwise-distinct nonunit moduli supported on the
first nine odd primes, put `P={3,5,7,11,13,17,19}`. Impose the
following restriction only on its `P`-supported originals:

> After removing powers of3, every nonunit numerical `Q` cofactor
> has at most two distinct projected residues across all its original
> occurrences, including originals not divisible by3.

Collect those projections as one actual two-copy `Q` family and use
SD1's law `nu_Q` to avoid all of them. Independently use normalized
Haar on the actual pure3 survivor. Its mass is at least `1/2`, its
density at most2 and its complete query norm at most1, because the
original numerical pure3 moduli are distinct. Their product is one
law on the actual `P`-only survivor with

\[
R_P\le1+2B_*
=\frac{475217647860378394201}{43177522677724517700}
<565/51.
\tag{SD11}
\]

Every other original may touch23 or29 with arbitrary residues and
finite heights. Under the product of this law with free23/29 Haar,
numerical distinctness and the complete query sum bound its entire
forbidden union by

\[
(1+R_P)\sum_{j+k>0}23^{-j}29^{-k}
\le(2+2B_*)\frac{51}{616}
=\frac{8812717899147749502317}{8865784656492767634400}<1.
\tag{SD12}
\]

The unit old cofactor is included. The unchanged PA density bound
`9/min alpha`, multiplied by the pure3 factor2, converts the positive
remaining mass to actual Haar survivor mass at least

\[
\frac{53066757345018132083}{1553164904833455513600000}
>1/30000.
\tag{SD13}
\]

This is a noncoverage result for the stated projected-phase class,
with arbitrary23/29 originals. The product and final-union arguments
reuse [Report463](../450-499/463-two-actual-prime-extensions-preserve-a-common-core-law.md).
The projection restriction is not automatic for arbitrary ternary
histories. No assertion about unrestricted first-nine-prime families,
arbitrary larger prime supports or unrestricted Erdős #7 follows.

## Weighted projection residuals allow arbitrary deeper phases

The two-phase hypothesis can be replaced by a weighted condition on
the actual original ternary cylinders. This is a further consumer of
SD1 and Report463's pure-coordinate conditioning, not a new independent
construction of the six-prime law.

For each nonunit numerical `Q` cofactor `d`, choose a fixed set `A_d`
of at most two projected residues. Apply SD1 to these classes to obtain
one probability `nu_Q`. Let `nu3` be normalized Haar on the actual
pure3 survivor, and set `rho=nu3 times nu_Q`. For every residue `r`
modulo `d`, let `U_(d,r)` be the union of the actual ternary cylinders
of those `P`-only originals `3^e d` whose `Q` projection is `r`.
An exponent-zero cylinder is the whole ternary space. All these sets
are fixed by the original family, before any query is chosen.

Put `p_d=max_r nu_Q(r mod d)`. The selected phases have zero
`nu_Q` mass. The remaining original union therefore has `rho` mass
at most

\[
\begin{aligned}
\delta_{\rm phase}
 &=\sum_{d>1}\sum_{r\notin A_d}
       \nu_3(U_{d,r})\nu_Q(r\bmod d)\\
 &\le\sum_{d>1}p_d\rho_d
 \le B_*\max_{d>1}\rho_d,
 \qquad
 \rho_d:=\sum_{r\notin A_d}\nu_3(U_{d,r}).
\end{aligned}
\tag{SD14}
\]

Only cofactors actually occurring in the original family enter these
sums; an empty inventory has residual zero. For a fixed `d`, distinct
residues have disjoint `Q` events, so its inner sum is its exact
remaining forbidden mass. Across different `d` the displayed sum is
an upper bound. Combining cylinders with the same projected residue
retains their actual overlap. One may select the two largest values
of `nu3(U_(d,r))` for each `d` to minimize `rho_d`; this uses only the
original family and the already fixed pure3 law. SD1 then produces
one `nu_Q` for the entire selected family. No law or original residue
is reselected for individual queries.

Let `delta<1` bound the actual remaining original union, for example
by any of the estimates in SD14, and restrict `rho` to
the actual `P`-only survivor, obtaining the unnormalized measure
`sigma`. It has mass `s>=1-delta`, density at most `18/alpha_min`,
and complete nonunit query sum at most `A=1+2B*`. Deletion only
decreases this nonnegative sum; it is not divided by `s` yet.

Independently condition23 and29 Haar on their actual pure-power
survivors. The density factors are at most `22/21` and `28/27`,
and their positive-exponent query sums are at most `1/21` and
`1/27`. Original labels touching exactly one of these primes have
total remaining charge at most `A/21+A/27`. Those touching both
have charge at most `(A+s)/(21*27)`: the old unit cofactor carries
mass `s`, not one. This is Report463's counting argument applied
before normalization. Thus the same product submeasure retains
mass at least

\[
M(\delta):=\frac{566(1-\delta)-49A}{567}.
\tag{SD15}
\]

In particular `delta<1-49A/566` suffices for noncoverage, and the
actual Haar survivor mass is at least

\[
M(\delta)\frac{\alpha_{\min}}{18}
                  \frac{21}{22}\frac{27}{28},
\qquad
\alpha_{\min}=\frac{7575003978548161}{73724315753088000}.
\tag{SD16}
\]

All original moduli touching23 or29 remain arbitrary. Retaining the
unit's actual mass improves the simpler direct-union reserve by
`delta/567`. Neither argument independently optimizes different
queries or assumes independence within `sigma`.

An explicit all-height class follows. Assume only that, for each
nonunit `d`, the originals with ternary exponent `0<=e<=h` have at
most two distinct `Q` projections. Choose those phases as `A_d`.
At every later exponent there is at most one original with modulus
`3^e d`; since `nu3` has density at most2,

\[
\rho_d\le2\sum_{e>h}3^{-e}=3^{-h},
\qquad \delta\le B_*3^{-h}.
\tag{SD17}
\]

For `h=5`, SD15--SD17 give the uniform actual Haar bound

\[
H(U)\ge
\frac{15786622554865812862151}{113225721562358906941440000}
>\frac1{8000}.
\tag{SD18}
\]

Thus only exponents0 through5 need the two-phase restriction; every
original at exponent6 or higher can have an arbitrary new projected
residue. There is no bound on their finite heights or total projection
multiplicity as the cofactors vary. Arbitrarily many distinct phases
at one cofactor are permitted by taking that cofactor sufficiently
large and using distinct later exponents. The `h=4` uniform scalar
reserve is negative; this fails to certify that larger class and
does not exhibit a covering. Actual weighted data in SD14 can still
certify families outside the stated five-level class.

The unrestricted problem requires control of arbitrary low-level
projections as well. SD14 does not prove that its residual threshold
always holds, and the new consumer does not close that missing bridge.

## A finite cofactor window suffices

The same law's density bound makes it unnecessary to restrict the
shallow phases at every possible cofactor. Put

\[
\Lambda_Q=9/\alpha_{\min},\qquad
T_Q(D)=\sum_{\substack{d>D\\d\ Q\text{-smooth}}}\frac1d
=\frac{157435}{165888}
 -\sum_{\substack{1<d\le D\\d\ Q\text{-smooth}}}\frac1d.
\tag{SD19}
\]

Suppose only that, for each nonunit numerical `d<=D`, its original
projections at `e=0,...,5` have at most two phases. Select these
phases for such `d`. For `d>D`, select just the phases at `e=0,1`,
if present. Every other phase at every height is unrestricted.

The corresponding shadow costs satisfy `rho_d<=1/243` on the
small cofactors and `rho_d<=1/3` on the large ones. Both
`sum p_d<=B*` and `p_d<=Lambda_Q/d` hold for the same selected
`nu_Q`. Thus, separating the two inventories without changing the
law, SD14 gives

\[
\delta\le\delta_D:=\frac{B_*}{243}
              +\frac{80\Lambda_Q}{243}T_Q(D).
\tag{SD20}
\]

The residual cannot be evaluated by choosing a different maximizing
source for each cofactor; the two displayed caps concern its one
actual query vector. The reciprocal series is exact at all heights,
since it is the product of six convergent geometric series. Only
its finite complement is enumerated.

| Cofactor cutoff `D` | Nonunit `Q`-smooth cofactors at most `D` | `delta_D` | Actual nine-head Haar survivor lower bound |
|---|---:|---:|---:|
|200000|399|0.045794994205...|`>1/150000`|
|500000|534|0.033201344500...|`>1/14000`|

For the second row the exact Haar bound from SD16 is

\[
h_{\rm win}=
\frac{65309357447174553501464811666318913123}
 {891295583254235091928801373698690560000000}.
\tag{SD21}
\]

Consequently only a finite set of full original labels is restricted:
`3^e d` with `0<=e<=5`, nonunit `Q`-smooth `d<=500000`.
The condition concerns the actual projections grouped by `d`; it
does not prescribe their values or require these labels to occur.
Every `P`-only original outside this window, and every original
touching23 or29, is arbitrary. No phase multiplicity bound is imposed
at large cofactors or at higher ternary exponents.

## Arbitrarily many sufficiently large prime coordinates

Let every support prime belong to
`P9={3,5,7,11,13,17,19,23,29}` or be strictly greater than1000000.
Impose the finite-window condition of SD21 only on the `P`-supported
originals. All tail-touching originals have arbitrary phases, heights
and support sizes; their old projections are not restricted by the
window condition.

Resolve the nine head coordinates to every exponent occurring in the
complete original family, including classes touching tail primes.
The actual head-only survivor `U` has Haar mass at least `h_win`.
Use the new unnormalized seed `H_P9 restricted to U`, with joint
density at most one. Its complete query second moment is bounded by

\[
M_2=\prod_{p\in P9}\frac{p(p+1)}{(p-1)^2}
    =\frac{14003665}{540672}.
\]

This uses Haar domination, not an unproved transfer of the old PA
query bound to the changed seed. Apply the existing homogeneous
joint-load transfer of [Chapter33, SH5--SH13](../../../problem-details/33-seven-small-primes-with-an-unrestricted-large-prime-tail.md).
For `B=1000000`, `ell=12`, its full prime-tail charge is at most

\[
\begin{aligned}
M_2\tau_7(B,\ell),\qquad
\tau_7(B,\ell)
 &=\frac{c_\ell^7}{B}\left(\frac B{B-3}\right)^2
   \sum_{j=0}^7\frac{7!}{(7-j)!\ell^j},\\
c_\ell&=\frac{2\ell^2+1}{2\ell^2-1}=\frac{289}{287}.
\end{aligned}
\tag{SD22}
\]

The applicable prime-product estimate is the literature premise
specified in Chapter33 SH11 and Chapter32 JR20. Its original
Rosser--Schoenfeld Theorem8 inequalities have been read directly;
the rational producer does not prove that analytic theorem. Its required
`3^12<=1000000` and the remaining parameter inequalities hold.
Exact arithmetic gives

\[
M_2\tau_7
=\frac{18784226696570844907670807127734375}
       {337155933270740130462847785506306260992},\qquad
h_{\rm win}-M_2\tau_7>\frac1{60000}>0.
\tag{SD23}
\]

Assign each tail original once to its largest tail prime, retaining
all earlier head and tail exponents and the original phases. The
normalized current kernels preserve the entire previous joint
measure; all tail bad sets are removed together at the end. Hence
the positive margin is mass on one actual complete survivor law,
and supplies an uncovered integer by finite CRT. It is **not** a
final Haar-density lower bound: the tail kernels change the density.

The stronger all-cofactor five-level assumption of SD18 gives a
larger head mass and final distorted mass `>1/12000` at the same
cutoff. The finite-window version above already allows arbitrarily
many tail primes. It still excludes extra support primes from31
through1000000 and retains its explicit finite head condition.
Neither restriction is removed by this continuation.

## A shared original cylinder defeats the additive certificate

The cross-cofactor sum in SD14 can fail even when the actual union
under the same law passes SD15. Take the four pure3 originals
`(modulus,residue)=(3,2),(9,4),(27,19),(81,37)`. For each `p in Q`,
take exactly the following three further originals, with their full
residue fixed by CRT:

| Original modulus | Ternary condition | `Q` condition |
|---|---|---|
|`p`|none|`x_p=0 mod p`|
|`3p`|`x_3=0 mod3`|`x_p=1 mod p`|
|`27p`|`x_3=1 mod27`|`x_p=2 mod p`|

These22 original moduli are distinct and odd. The pure3 cylinders
are disjoint and avoid both displayed ternary cylinders. Their
survivor Haar mass is `41/81`; normalized Haar on it gives the three
phase weights `1,27/41,3/41` at every cofactor `p`. Its complete
positive-depth query norm is `81/82`, since root0 is untouched.

The family is irredundant. A private point for a pure3 original has
its displayed3-residue and every `Q` root equal to3. A private point
for the chosen `p`, `3p` or `27p` original uses respectively
`(x_3,x_p)=(0,0),(0,1),(1,2)` and every other `Q` root3.
CRT joins these coordinates. Each point hits only its named class;
the exact producer supplies all22 integer witnesses.

Consider any selector of at most two phases per cofactor and any
one `Q` probability avoiding those phases. If `k` roots are selected
at `p`, its maximum root mass is at least `1/(p-k)`. Selecting
outside the three actual phases cannot decrease the residual.
For `k=0,1,2` the best local lower bounds for `rho_p p_p` are
respectively `71/(41p)`, `30/(41(p-1))`, `3/(41(p-2))`.
The last is strictly smallest for every `p>=5`. Hence

\[
\sum_p\rho_p p_p\ge\frac3{41}\sum_{p\in Q}\frac1{p-2}
=\frac{7244}{115005}=0.0629885657145\ldots
>\delta_*:=1-\frac{49(1+2B_*)}{566}.
\tag{SD24}
\]

This fails SD14's weighted-maximum sufficient certificate even
after replacing the coarse ternary norm1 by `81/82`: the resulting
threshold is only `0.0535098569215...`. It does not lower-bound the
actual union or the phase-resolved sum for an arbitrary supported law.

Select phases0 and1 at every `p`. One product law uniform on roots
`2,...,p-1` attains all six lower bounds in SD24 simultaneously.
Its complete query norm is

\[
R_Q=\prod_{p\in Q}\left(1+\frac{p}{(p-1)(p-2)}\right)-1
=\frac{214267985}{147806208}<B_*.
\tag{SD25}
\]

This is also the actual PA law for these selected pure-prime
inputs: there is no mixed5/7 deletion, and every later pure-root
row has normalized density `p/(p-2)` below its PA cap. Thus the
minimum in SD24 is attained by one admissible actual law.

All unselected originals share the single ternary cylinder1mod27.
Under this very law their joint remaining union has exact mass

\[
\delta_{\rm joint}
=\frac3{41}\left[1-\prod_{p\in Q}\left(1-\frac1{p-2}\right)\right]
=\frac{47063}{1035045}
=0.0454695206488\ldots<\delta_*.
\tag{SD26}
\]

No phase, source or law changed between SD24 and SD26. The additive
account counted overlapping events more than once. Using SD26 in
SD15 with the unchanged conservative budget `A=1+2B*` yields positive
mass. The actual source density here is `1729/205`, giving

\[
H(U_9)\ge
M(\delta_{\rm joint})\frac{205}{1729}\frac{21}{22}\frac{27}{28}
=\frac{220847911852866873499201}{1190705023034810768709876960}
>\frac1{5500}.
\tag{SD27}
\]

Thus this fixed22-class head admits arbitrary additional distinct
original moduli supported on `P9` and touching23 or29. It lies
outside SD18's two-phase condition already at ternary exponent3.
The example refutes automatic success of the specified additive
certificate and identifies a sufficient joint-union repair; it
neither supplies a covering nor proves the repair works for every
head. It does not require improving the universal query budget.

## Direct seven-core suffix debits and the charged baseline

Use the actual seven-core measure of
[Report462](../450-499/462-the-final-stage-ledger-gives-a-seven-core-common-law.md),
with its fixed source completion, charged first7 row and physical165
projection. All quantities below use the same unnormalized actual
prefixes and135 comparison units per Haar unit. Write

\[
d_q=135\int(1-s_q)\,d\nu_{<q},\qquad
k_q=135\int(C_q-\kappa_q)\,d\nu_{<q}
\quad(q=11,13,17,19).
\]

The ordinary caps are `(5/3,3/2,2,9/5)`. At7 the source's comparison
row mass is `S_s=(1,1,6/7,9/14,3/7)`, where `s` is its charged
projection count; denote the actual surviving row mass by `r_7<=S_s`.
Define

\[
B_7=135\int(1-S_s)\,d\nu_{<7},\qquad
E_7=135\int(S_s-r_7)\,d\nu_{<7},\qquad d_7=B_7+E_7.
\]

Report462's final comparison already replaces the ordinary zero7 atom
by `S_s-3/14=(11,11,9,6,3)/14`. It has therefore already paid `B_7`.
Only `E_7` is available for a new suffix debit.

Let `zeta_q=E[(prod_{r>q} N_r-12)_+]` under the ordinary auxiliary
laws at11,13,17,19, and put
`eta_q=(zeta_previous-zeta_q)/C_q`. For every complete finite query
layout `L`, the refined comparison is

\[
H:=135\int(L-12)_+\,d\mu_7
\le10L_{23}-\zeta_7E_7
 -\sum_{q=11,13,17,19}(\zeta_qd_q+\eta_qk_q).
\tag{SD28}
\]

For an ordinary row, labels supported only on later coordinates give
the completed row a compulsory payoff at least `zeta_q`. Its missing
mass and its unused cap are handled by the same conditional convex
comparison used above. Each integrated debit is retained as a scalar
before the next earlier comparison.

At7, write the ordered-increment majorant as a constant plus
nonnegative cylinder increments. Its constant costs the actual mass
`r_7`; the increments retain the source's depth caps. Replacing `r_7`
by `S_s` adds at least `zeta_7(S_s-r_7)` to this majorant. This remains
valid when `r_7<3/14`; no negative actual zero atom is introduced.
The remaining main comparison is exactly Report462's matched positive
component functional. Finite query boxes increase to the complete
inventory, with convergent first moments for each coefficient and
each main expectation. This proves SD28 on one law, without choosing
the completion or prefixes in response to the query.

Write `m=135 mu_7(1)` and `D_7=R-L_7-L_11-L_13-L_17-L_19`, using
the retained source reserve and stage upper bounds. For
`lambda>=zeta_7`, substitution of `E_7=d_7-B_7`, the actual mass
identity, and the bounds `d_q<=L_q` give

\[
\lambda m-H\ge G:=\lambda D_7-10L_{23}
 +\zeta_7(L_7-B_7)+\zeta_{11}L_{11}
 +\zeta_{13}L_{13}+\zeta_{17}L_{17}
 +\sum_q\eta_qk_q.
\tag{SD29}
\]

The coefficients of the actual losses before substitution are
`lambda-zeta_q>=0`, which fixes the inequality direction. Since
`L-1<=11+(L-12)_+`, positivity of `G` at `lambda=27/49` would
give the desired same-law query norm strictly below `566/49`.
It is a sufficient certificate, not an evaluation of the actual norm.

The suffix values are
`zeta_7=0.002242588487415791...`,
`zeta_11=0.00016597487039070558...`,
`zeta_13=0.0000011483205094759597...`,
`zeta_17=1/1164902588982190`, and `zeta_19=0`.
In particular `eta_19=1/2096824660167942`.

## One finest branch rules out the retained threshold12 certificate

In the pinned edition1.0.1 source verifier, take
`node=(2,4,1,8,1,2,1,0,13)`, charged projection `(1,4,7,14)`,
and the physical165 phase14. This is its finest `A1` branch.
Regeneration gives `R=135/4` and the following stage bounds:

| Stage | Upper bound in135-cell units |
|---|---:|
|7|10.4062667005|
|11|5.2980442211|
|13|6.175771329875369...|
|17|3.9061873394797946...|
|19|4.365028233373036...|
|23|3.5862096296263943...|

The fixed165 cost and its available budget agree exactly with the
source's retained `closing.json`. Thus `D_7=3.5987021756718...`,
and the old surplus `D_7-L_23=0.0124925460454...` remains positive.

Every actual prefix has mass at most one, so `k_q<=135C_q`. Even
granting `B_7=0` and all four cap slacks their independent generous
maxima, the additional cap credit is at most

\[
\sum_q\eta_qk_q\le135\sum_q\eta_qC_q
=135\zeta_7=0.3027494458011\ldots.
\tag{SD30}
\]

The base of SD29 is `-33.8791379545672...`; all suffix deletion
credits with `B_7=0` add only `0.0242234078673...`. Consequently
even this optimistic value is

\[
G_{\rm opt}=
-\frac{479429892642015605297432820666392256166724042026707948688449009645876336499}
 {14289089577386851154058862090334325976908866877949621298761228800000000000}
<-33.
\tag{SD31}
\]

No simultaneous attainability of these generous credits is assumed.
The upper bound is deliberately favorable to the proposed certificate.
This one comparison branch already refutes uniform positivity of this
fixed certificate, so its full28001-branch traversal is unnecessary.

## Every real final threshold from1 through12 also fails

Keep all five actual early stages fixed. Change only the dummy query
threshold to `t in[1,12]`, so its conversion factor is `22-t`, its
dummy cap is `22/(22-t)`, and
`lambda_t=566/49-(t-1)`. No23 kernel is added to the actual law.
Let `Hbar(t)` be the unrounded source upper numerator, recomputing
the ordinary expectation and both matched zero7 components at that
same `t`. Keep the source's finite anchor rectangle `u<12,v<9`
and its full-linear omitted-height bounds. Define `zeta_q(t)` and
`eta_q(t)` by replacing12 with `t` in the suffix formulas.

The analogous candidate is at most

\[
G_{\rm opt}(t)=\lambda_tD_7-\overline H(t)
 +\sum_{q=7,11,13,17,19}\zeta_q(t)L_q+135\zeta_7(t).
\tag{SD32}
\]

The `lambda_t>=zeta_7(t)` condition holds throughout: the suffix
hinge is1-Lipschitz, and `lambda_12>zeta_7(12)`. All12 integer
values are negative. Their largest is `G_opt(1)=-31.2004179162...`.
The unrounded numerator is smaller than the rounded source numerator,
so this test only makes the proposed certificate more favorable.

To cover intervening real thresholds, first express the source
comparison as positive7-depth components and the nonnegative spatial
zero component. For `k<t<=k+1`, its split of integer multipliers
`m<t` is fixed. Each low-multiplier term `m F(t/m)` and each high
term `mW-tM` is nonincreasing on this half-open interval. Hence
`Hbar(t)>=Hbar(k+1)`. The nonnegative suffix credits are also
nonincreasing. Therefore

\[
G_{\rm opt}(t)\le V_k:=\lambda_kD_7-\overline H(k+1)
 +\sum_q\zeta_q(k)L_q+135\zeta_7(k)
\le V_1=-1.7715974684507994\ldots<-7/4
\tag{SD33}
\]

for `k=1,...,11`, as checked exactly. Together with the separate
`t=1` value this covers all real `t in[1,12]`. Global monotonicity
of `Hbar` is not asserted: crossing an integer changes its multiplier
split and can introduce an upward jump from the omitted-tail majorant.

This stops the retained early-stage ledger, current geometry/tail
envelope and these suffix/cap corrections for this threshold range.
It does not stop changed early kernels, tighter joint geometry,
additional credits or other laws. In particular it is not an actual
query lower bound, an actual family attaining the upper envelopes,
or a covering counterexample. Any future positive finite certificate
using SD29 must also construct a same-source computable upper bound
for the actual integral `B_7` and compatible interpolation/screening;
the old branch fields do not automatically determine it. That missing
interface is immaterial to the negative result, which granted `B_7=0`.

## The maximum-weight selector hides the first private-hull reservation

The two-largest-weight choice in SD14 need not preserve the regions
that a private-hull argument would charge. For the first reservation
forced by [Report528 FC943](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md#private-hull-descendants-reserve-entire-parent-phases),
the following local conditions force its entire parent cylinder to
have zero mass under that choice of source.

Fix a nonunit Q-smooth cofactor d. Its actual rows3^e d have at most
one original at each exponent. Suppose d and3d occur, with distinct
cofactor phases r0,r1 modulo d, and let b be the first ternary digit
of the3d original. If an actual pure3 original occurs, suppose its
digit differs from b. All deeper pure and same-cofactor originals
have arbitrary phases and finite heights, with at most one per depth.
Whole coverage and private-hull assumptions are not needed for this
local statement.

Choose H>=1 resolving those ternary depths. On the finite ternary
carrier let lambda be uniform, V the actual pure survivor, S=lambda(V),
and W_r=lambda(V intersect U_(d,r)). These are the actual UNION events
from SD14. Put

    T_H=sum_(j=2..H)3^(-j)=(1-3^(1-H))/6<1/6.

The exponent-zero row gives W_r0=S. The pure3 cylinder misses the
b-root; all deeper pure deletions cost at most T_H, so

    S>=2/3-T_H>1/2,
    W_r1>=lambda(V intersect[b]_3)>=1/3-T_H.

For every r outside{r0,r1}, only exponent-at-least-two rows contribute,
giving W_r<=T_H. The pure tail and the same-cofactor tail are different
event families, bounded separately on the same lambda. No independence
or disjointness of their unions is used. Thus

    W_r1-W_r>=1/3-2T_H=3^(-H)>0,
    W_r0>W_r.                                          (SD34)

Dividing by the same positive S preserves the rankings. Both dominant
weights are positive, so the UNIQUE at-most-two-phase set minimizing
the SD14 residual sum is{r0,r1}. Missing depths only strengthen the
bounds. Pure3 may be absent; coincident low cofactor phases or a3d
root deleted by pure3 are outside the stated conditions. The strict
gap need not stay bounded away from zero as H grows.

The chosen Q source therefore satisfies nu_Q([r1]_d)=0. Consequently
rho=nu3 times nu_Q gives zero mass to the ENTIRE parent cylinder
R={all ternary states} times[r1]_d and every subregion of R, including
its intersection with any query phase. This is stronger than merely
avoiding the original3d class, which fixes a ternary digit as well.

In the globally count-then-modulus-sum minimal whole cover considered
by FC943, its explicit crossing and proper-multiple premises supply
the actual hull descendant3d. Comparable disjointness supplies the
two local phase conditions above. Hence its forced reservation
R_(3d) is null under the SD14 maximum-weight source. FC942's geometric
payment inequality remains valid, but this particular reservation
has zero demand under that law. This establishes a specific instance
of FC942's existing zero-source warning; it does not invalidate the
private-hull theorem.

An arbitrary selector need not choose these phases. A different source,
or a deeper reservation outside the selected cylinders, may retain
positive mass, but its full loss and query bounds must be established
together. No decrease of the actual continuation margin, impossibility
of another supported law, or covering counterexample follows.

A scoped Lean application verifies the actual finite prefix-union
ranking, positivity of S, and the exact normalized residual-minimizer
conclusion, allowing arbitrary missing depths. It also verifies the
parent nullity for a GIVEN Q law satisfying the selected-support
contract, and any ternary probability joined to it. The standard axiom
closure is unchanged. The application reuses prefix counts, finite
union bounds, geometric estimates and finite selection identities;
no canonical specialization is added. It proves the strict ordering
needed by the selector, not the displayed closed-form gap3^(-H).
The numerical cofactor interpretation and the FC943 whole-cover
consumer above remain ordinary applications of their stated results;
this check does not reconstruct the two-phase Q source or formalize
whole-cover minimality.

## Verification

The [standard-library producer](../../../frontier/cover-geometry/no-mod3-through2/pa_complete_suffix_debits.py)
and [exact data](../../../frontier/cover-geometry/no-mod3-through2/pa_complete_suffix_debits.json)
reconstruct full moments, suffix hinges, cap slopes, prefix mass
bounds, signed-penalty corrections, all four corners and the restricted
nine-prime consumers, finite cofactor windows, large-prime continuation
and the22-original shared-cylinder example.
All225 checks pass with Python optimizations
enabled. Independent arithmetic reconstructs the four corners and
both bounds without importing the producer. The finite-box and
all-height arguments above supply the arbitrary-family proof; finite
checks do not replace it. No Lean statements were added for these results.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/no-mod3-through2/pa_complete_suffix_debits.py
```

The separate [seven-core producer](../../../frontier/cover-geometry/seven-core-suffix-branch/seven_core_suffix_branch.py)
and [exact results](../../../frontier/cover-geometry/seven-core-suffix-branch/seven_core_suffix_branch.json)
hash-pin the source manuscript, verifier, C++ enumerator and two
certificate inputs. It copies the unchanged verifier and enumerator
into temporary storage, compiles the enumerator and extends only the
runtime threshold-ratio set from15 to45. It regenerates24 geometry
batches with10152 integer queries, reconstructs the original branch
and all12 threshold numerators, and checks all11 interval bounds.
All107 producer checks pass. Independent exact arithmetic checks the
suffix coefficients and all11 interval bounds; the ordinary interval
argument above supplies the passage from endpoints to real thresholds.
The source verification material is copyright2026 Michael Schroeder,
MIT licensed; its license is retained with the temporary copies.
Source identity and attribution are also recorded in
[the existing library entry](../../../../../../Library/Arith/schroeder2026nine.md).
The source's general comparison theorem remains an attributed premise;
this bounded replay does not reverify its entire proof or certificate.

Run without `-O`, since the unchanged external verifier uses assertions:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/seven-core-suffix-branch/seven_core_suffix_branch.py --source-root /path/to/nine-prime-support
```

## A common source controls one-slot changes, but cannot restore excluded support

Suppose two finite selected Q libraries share every forbidden class
except one optional or differing second phase at the same numerical
cofactor d. First apply the existing two-copy supplier to their COMMON
library, obtaining one probability mu. Write B0 and B1 for the two
additional phases; an absent phase is the empty event. Distinct phases
at the same cofactor are disjoint. Put

\[
b_i=\mu(B_i),\qquad \delta=\max(b_0,b_1)<1,\qquad
\nu_i=\mu(\,\cdot\mid B_i^c).
\tag{SD35}
\]

These are two explicit laws derived from one source. Both preserve every
common forbidden class as a null event and avoid their own additional
phase. For a finite nonunit query inventory M, let
`q_m(eta)=max_a eta([a]_m)` and `R_M(eta)=sum_(m in M)q_m(eta)`.
The ordinary conditioning bound holds for every phase before taking
maxima, so

\[
\sum_{m\in M}\max\{q_m(\nu_0),q_m(\nu_1)\}
\le \frac{R_M(\mu)}{1-\delta}.
\tag{SD36}
\]

Thus two separately constructed source bounds need not be added.
The same denominator works for every finite window; exhaustion gives
the corresponding complete-query bound when the common source has one.
The unit query is excluded here. Including it requires the common-source
budget `1+R_Q(mu)`.

For the SD1 source, `mu<=Lambda Haar_Q`, where
`Lambda=9/alpha_min` uses SD16's unchanged density constant. Consequently
`b_i<=Lambda/d`; if `d>Lambda`, SD36 is at most
`B_*/(1-Lambda/d)`. This is a sufficient one-slot estimate, not a uniform
small-cofactor bound or a new noncoverage class.

Disjointness also gives the exact retained masses

\[
\nu_0(B_1)=\frac{\mu(B_1)}{1-b_0},\qquad
\nu_1(B_0)=\frac{\mu(B_0)}{1-b_1}.
\tag{SD37}
\]

In particular, positive retained mass is equivalent to positive mass
under the common source. SD36 does not supply that positivity. The
existing PA construction has full support on the actual common-library
survivor V: its raw measure satisfies
`Haar_Q restricted to V<=lambda_final<=9 Haar_Q`, with total mass at
most one. Hence `mu(E)>=Haar_Q(E intersect V)`. On a resolving finite
CRT carrier, `mu(E)>0` holds exactly when `E intersect V` is nonempty.
The missing condition is therefore actual surviving support.

### An inactive parent can be excluded by another cofactor

The following finite family demonstrates the distinction while keeping
actual original labels, their crossing, and their complete private
region. All entries and private points are modulo105.

| Original modulus | Original residue | A private point |
|---:|---:|---:|
|3|0|3|
|5|2|7|
|7|2|16|
|15|10|10|
|21|1|1|
|35|0|35|
|105|50|50|

The labels are exactly the nonunit divisors of105. They are distinct
odd integers, all twelve comparable pairs of classes are disjoint,
and the private points prove irredundancy. The COMPLETE private region
of the35 class is `{35}` modulo105, so its congruence hull is105.
Moreover, `A_15 intersect A_35={70}`. Thus the crossing and private-hull
data used for the35-parent reservation are present in this example.
It is a NONCOVER:4 avoids every listed class. No claim of global
count-then-sum minimality is made.

The105 class has ternary root2 and parent

\[
R_{105}=[15]_{35}=\{15,50,85\}\pmod {105}.
\tag{SD38}
\]

The first point is pure3-deleted, the second is the105 original, and
the third lies in the15 original. In particular, the entire parent
on inactive ternary root1 is already covered by an actual lower original.

On root1, the exact Q library obtained from the active originals is

\[
5:\{2,0\},\qquad 7:\{2,1\},\qquad 35:\{0\}.
\tag{SD39}
\]

It has15 surviving points modulo35, but none in `[15]_35`: the common
forbidden class `[0]_5` already contains that target. Adding the optional
second phase15 at cofactor35 therefore leaves its survivor unchanged.
Both libraries have at most two phases per numerical cofactor. The same
probability on their common survivor serves both, so on every query
window their joint envelope equals its ordinary single-law envelope.
Its extra joint cost is zero, while every supported law gives the target
zero mass.

This one-slot comparison is SD39 with and without the extra35 phase.
It is not the pair of natural root1 and root2 libraries: the latter
root has `5:{2}, 7:{2}, 35:{0,15}`, changing three secondary choices.
The example therefore isolates retained support without attributing a
one-slot relation to those two actual roots.

FC941 excludes other35-multiples from the parent;15 is a complementary
label, which FC942 expressly allows to cover its reserved hole. Thus
divisor closure, comparable disjointness, irredundancy and the displayed
private-hull crossing do not force positive inactive-root parent mass.
A whole-minimal-cover argument would need an additional consequence of
its global hypotheses; this finite noncover does not refute such an
argument.

If an old selected phase is contained in the union of the UNCHANGED
common forbidden classes, removing that redundant slot preserves all
old avoidance requirements. Within the same cofactor's remaining
two-phase allowance, one may then select a fixed further actual phase,
construct the new source, and check its joint budget. Being null only
under the old law does not justify this replacement after a source
change. The set-containment argument reuses
[Report528 FC455--FC457](../500-549/528-surviving-fibre-credits-control-arbitrary-phases-at-ternary-height-one.md)
and [Report626](../600-649/626-free-square-roots-admit-one-complete-boundary-gate.md),
not a new source theorem. Neither skipping a redundant phase nor SD36
supplies a uniformly useful reservation. The remaining task is to find
an actual target escaping the ENTIRE common library, quantify its mass,
and apply the existing all-competitive-phase debit and complementary-tail
payment on that same source.

### A deep original supplies support on its own root

There is a useful positive statement when the original has ternary
depth at least two. Let `m=3^e d` be one actual original, with `e>=2`,
`d>1` and d supported on Q. Assume it has a COMPLETE original private
integer w: w lies in its class and in no other original class. Whole
coverage is not required for this support statement.

Put `b=w mod3`. For each nonunit Q-smooth c, select exactly the Q
phases of every actual original c and every actual original3c whose
first ternary root is b.
Call this library L_b. Numerical distinctness gives at most two phases
per numerical cofactor. No deeper or inactive-root phase is added.
Let N_Q resolve d and every selected Q cofactor, and let V_b be the
complete survivor of L_b modulo N_Q. Then

\[
x_0=w\bmod N_Q\ \in\ V_b\cap[a_m]_d.
\tag{SD40}
\]

Indeed, a selected phase containing x_0 would, together with the fixed
root b when needed, put w in a different actual original. This contradicts
privacy. The argument uses the same w for all selected constraints.
It gives no assertion about a different root or a selector that inserts
extra deeper phases.

Choose finite H resolving m and every actual pure3 original. Let
`tau_H` be uniform ternary Haar, T_b the pure-surviving part of root b,
and C_m the original m's ternary prefix. An actual pure3 class at depth1
cannot occupy b, by privacy of w. At most one pure class occurs at each
larger depth. Thus

\[
\tau_H(T_b)\ge \frac13-\sum_{k=2}^{H}3^{-k}>\frac16,
\qquad \tau_H(C_m)=3^{-e}\le\frac19,
\]

and consequently

\[
\tau_H(T_b\setminus C_m)>\frac1{18}.
\tag{SD41}
\]

This changes only the ternary tail, keeping root b and the complete Q
point x_0. The resulting configurations avoid every selected low original,
every pure3 original, and the original m itself; they remain in its
mod-d parent. Other deep mixed originals may still cover them.

Apply the existing PA supplier once to L_b, with its original raw
support bound and total mass at most one. Its normalized law nu_b has
`nu_b({x_0})>=1/N_Q`. For the UNNORMALIZED root measure

\[
\eta_b=(\tau_H|_{T_b})\otimes\nu_b
\]

it follows that

\[
\eta_b\bigl([a_m]_d\setminus A_m\bigr)
>\frac1{18N_Q}>0.
\tag{SD42}
\]

Here the parent cylinder includes the whole ternary coordinate; the
product of `T_b minus C_m` with the singleton x_0 already supplies the
bound. Missing pure depths are permitted. The constant depends on the
actual finite Q resolution and is not a uniform bound over all original
heights.

This reuses actual private-point projection and the root-capacity
calculation of Report528 FC704--FC712; its FC1066--FC1068 already
separates positive private-head support from a sufficient continuation
budget. The present application specifies a parent HOLE by leaving the
deep original while keeping its first root. At depth1 that operation
cannot stay on the same root, which is precisely the obstruction in
SD38--SD39.

To use FC942's complementary-label payment, one additionally needs the
actual parent d and `m in H_d`, including `m | Gamma_d` for the COMPLETE
d-private region, under FC942's whole-minimal-cover hypotheses. First
extend eta_b uniformly on the fibres of a common CRT period resolving
ALL original moduli. This preserves its existing marginal and SD42;
every complementary original is evaluated on that single extension.
The smaller period used for SD40--SD42 need not resolve every remaining
deep mixed or outside-prime original. Positivity in SD42 does not prove
the required hull membership.
FC943 automatically supplies3d in its crossing case, whose depth1 is
outside SD40--SD42. Nor does this one-root law inherit the query budget
of a different selected source. Existence of a useful deep hull pair,
a quantitatively sufficient same-source query debit, and payment of the
remaining original tail all remain unresolved.

### A fixed mixture supplies all deep private holes before deletion

The fixed-mixture argument of
[Report530 GD4](../500-549/530-one-supported-law-controls-unused-and-deep-occupied-labels.md)
applies to SD40--SD42 with the following actual source choices. Keep
`P={3,5,7,11,13,17,19}` and `Q=P minus {3}`. Fix one finite family of
distinct odd original moduli and one common finite CRT resolution of
all its originals. Each chosen deep mixed original
`m=3^e d`, with `e>=2`, `d>1` and d Q-smooth, is assumed to have a
COMPLETE private point. Count minimality of a hypothetical whole cover
supplies that premise. No selected phase or probability below depends
on the subsequent query.
All laws have uniform Haar tails beyond the finite coordinate heights;
outside-P CRT coordinates are extended uniformly before whole-family
tests. The query norms below include those complete tails.

Let `L_all` contain the Q projections of every actual original c and
3c, for nonunit Q-smooth c. It has at most two phases per complete
cofactor. SD1's PA construction supplies one law `nu_all` avoiding
this library, with complete nonunit query norm at most

\[
B=B_*=
\frac{432040125182653876501}{86355045355449035400}.
\]

Let u be normalized Haar on the complement of ALL actual pure-three
classes. Their finite total Haar mass is less than `1/2`, so u has
density at most2 and complete ternary query norm at most1. Consequently
`rho_0=u tensor nu_all` avoids every pure-three original and every
actual P-only original of ternary depth zero or one, and

\[
R_P(\rho_0)\le A_0=1+2B.
\tag{SD43}
\]

This law need not give a deep parent hole positive mass: its library
also includes projected phases from inactive first roots.

For each first root b containing a chosen deep original, instead
apply PA to its OWN-root library `L_b` of SD40. This library depends
only on b and the fixed original family. It therefore supplies one
law `nu_b` usable for ALL chosen deep originals in that root. Take
one common Q resolution `N_Q` resolving these originals and the low
libraries; extra digits receive the usual uniform extension. The PA
survivor lower bound gives every relevant private Q point mass at
least `1/N_Q` under this same `nu_b`.

Write `a_b=tau(T_b)`, where `T_b` is the pure-surviving part of b, and
set `rho_b=(tau restricted to T_b)/a_b tensor nu_b`. SD41 gives
`1/6<a_b<=1/3`. SD42, divided by a_b, yields for every chosen m in b,
with `R_m=[a_m]_d`,

\[
\rho_b(R_m\setminus A_m)>\frac1{6N_Q}.
\tag{SD44}
\]

This normalized law also avoids ALL actual low P-only originals:
other-root rows cannot meet its ternary support, and the active rows
were included in `L_b`.

For the complete ternary query norm of normalized root Haar, the
depth-one contribution is1 and the remaining absolute cylinder
maxima sum to at most `sum_(k>=2)3^-k=1/6`. Thus
`r_b<=1+1/(6a_b)<2`. The product identity, including the unit query in
each factor, gives

\[
R_P(\rho_b)=r_b+(1+r_b)R_Q(\nu_b)<2+3B.
\]

This is the root law's own budget. Indeed every law supported on one
first root has `r_b>=3/2`; such a bare product could itself satisfy
`R_P<566/49` only if `R_Q(nu_b)<197/49`. Inserting the upper bound B
does not certify that condition and does not prove its failure.

For a nonempty choice of deep originals, fix nonnegative root weights
theta summing to1, positive on every
chosen root. There are at most three such roots; if pure3 is present
there are at most two. Set

\[
\rho_+=(\sum_b\theta_b\rho_b),\qquad
\rho_\varepsilon=(1-\varepsilon)\rho_0+
\varepsilon\rho_+,
\qquad 0<\varepsilon\le1.
\]

All these components avoid the same actual low originals. Convexity
of each literal query maximum and then the nonnegative query sum
give, on this ONE fixed mixed law,

\[
\begin{aligned}
R_P(\rho_\varepsilon)&\le1+2B+\varepsilon(1+B),\\
\rho_\varepsilon(R_m\setminus A_m)&>
\frac{\varepsilon\theta_b}{6N_Q}
\quad(m\text{ in root }b).
\end{aligned}
\tag{SD45}
\]

Finite query inventories suffice for convexity; the complete sum
follows by monotone passage through them. No separate optimizer is
chosen for a different modulus or phase. If the PA density cap is
`Lambda=9/min alpha`, rho_0 and rho_b have density at most `2 Lambda`
and `6 Lambda`, respectively. The same mixture therefore has density
at most `(2+4 epsilon)Lambda` relative to the common CRT Haar law.

Choose `epsilon=1/20` and uniform weights on the nonempty set of
chosen roots. Every chosen deep parent hole then has mass greater
than `1/(360N_Q)`, while

\[
\begin{aligned}
R_P(\rho_{1/20})&\le A_\varepsilon=
\frac{19527101084953238679941}{1727100907108980708000}
<\frac{566}{49},\\
K_\varepsilon=566-49A_\varepsilon&=
\frac{20711160260974385410891}{1727100907108980708000}>0.
\end{aligned}
\tag{SD46}
\]

For one chosen root the hole bound is `1/(120N_Q)`. With no chosen
deep originals, use rho_0 and make no hole assertion. Neither the
resolution-dependent lower bound nor convex support restoration
supplies private-hull membership for a chosen pair.

### The remaining loss must be measured on this mixture

Let D be the union of ALL remaining actual P-only originals, including
the deep mixed ones, and restrict this SAME rho to `D`'s complement
to obtain sigma. For every complete nonunit query modulus q write
`M_q=max_a rho([a]_q)` and

\[
c_q=\min_a\bigl(M_q-\rho([a]_q)+
\rho(D\cap[a]_q)\bigr).
\]

The exact deletion identity of
[Report571 JB7--JB9](571-joint-residual-laws-retain-conditional-and-query-incidence.md)
and its weighted form in
[Report752 JC1--JC4](../750-799/752-joint-deletion-credit-distinguishes-equal-marginal-sources.md)
then give the sufficient test

\[
566\delta-49\sum_q t_q<K_\varepsilon,
\qquad
\delta\ge\rho_{1/20}(D),\quad 0\le t_q\le c_q.
\tag{SD47}
\]

Without certified query credit this requires
`delta<20711160260974385410891/977539113423683080728000`, approximately
0.02118704. Support restoration consumes part of the old preliminary
margin; it does not automatically improve the deletion estimate.
The actual D mass and all competitive phase intersections remain to
be bounded. Positive mass in one parent hole is not a lower bound on
every query credit. In particular SD46 concerns a law avoiding the
low library, whereas the continuation gate requires sigma to avoid
ALL actual P-only originals. This distinction remains even when a
chosen deep original belongs to a supplied private hull.

### Private-hull reservations restrict the entire tail phase menu

There is a stronger use of a supplied private-hull reservation than
concentrating the source on one parent hole. Keep one actual family,
one preliminary law rho from SD43, its remaining P-only union D, and
sigma=rho restricted to D-complement. Write s=sigma(1). This subsection
assumes the ENTIRE original prime support lies in P union {23,29}.
Any further outside primes require their own continuation payment.

Choose a finite set H of actual pairs (d,m), with d>1, d|m, m>d,
and BOTH d,m supported on P, for which FC941 holds:

    R_m=[a_m]_d,
    n!=m and d|n ==> A_n intersect R_m=empty.

Under the hypothetical whole-minimal-cover premises, this follows
when d is an original parent and m|Gamma_d. The numerical labels,
complete private hulls and phases all belong to the SAME family.
A private point of m alone does not establish this hypothesis.

For every nonunit P-smooth query label k, define the finite menu

\[
\mathcal A_k=\{a\bmod k:
  a\not\equiv a_m\pmod d\text{ for every }(d,m)\in\mathcal H
  \text{ with }d\mid k\}.
\]

Every actual23/29-touching original whose old cofactor is k has its
actual phase in this menu. Such an original is different from each
P-only m, and d|k implies d divides its full numerical modulus, so
FC941 excludes the entire R_m. No phase or source is reselected.

Define maxima with a zero option, including when the menu is empty:

\[
q_k^{\mathcal H}(\sigma)=
\max\bigl(\{0\}\cup\{\sigma([a]_k):a\in\mathcal A_k\}\bigr),
\qquad R_{\mathcal H}(\sigma)=\sum_{k>1}q_k^{\mathcal H}(\sigma).
\]

Condition23 and29 Haar on their actual pure-power survivors, exactly
as in SD15. The old nonunit costs are now R_H/21 and R_H/27. Originals
touching both primes cost at most(R_H+s)/567. The old unit is still
present in the last expression: no parent d>1 divides1. Consequently
this SAME product submeasure has full survivor mass at least

\[
\frac{566s-49R_{\mathcal H}(\sigma)}{567}.
\tag{SD48}
\]

Thus positivity contradicts whole coverage. This reuses SD15's
original-label count with the smaller justified phase menus. Since
R_H<=R_P, it never weakens the old certificate on the fixed sigma.
Strict improvement requires actual phase information.

### Pay the remaining competitors once

Let M_k=max_a rho([a]_k), and let
s_(k,a)=M_k-rho([a]_k) be the old phase slack. The exact total reduction
from the old unrestricted query to the new tail menu is

\[
\begin{aligned}
h_k&=M_k-q_k^{\mathcal H}(\sigma)\\
&=\min\left(\{M_k\}\cup
 \{s_{k,a}+\rho(D\cap[a]_k):a\in\mathcal A_k\}\right).
\end{aligned}
\tag{SD49}
\]

This is Report571 JB7 / Report752 JC1 applied to the restricted menu.
The extra M_k represents the zero option. With an empty menu h_k=M_k,
and no actual tail original may use that old cofactor. Otherwise
EVERY remaining competitive phase is included. Removing one old
maximizer is insufficient if an uncharged competitor remains.

All series converge by the finite bound SD46 on R_P(rho); each term
is nonnegative and bounded by its unrestricted counterpart. Menu
inclusion and the unchanged law give

\[
h_k\ge c_k\ge0,\qquad
R_{\mathcal H}(\sigma)=R_P(\rho)-\sum_{k>1}h_k.
\tag{SD50}
\]

Here h_k already contains both deletion and phase restriction. It
must not be added to the old c_k as a second saving. Overlapping
reservations are combined in A_k before taking the maximum.

For a finite query test set J, same-source bounds
0<=t_k<=h_k and delta>=rho(D) therefore give the sufficient gate

\[
566\delta-49\sum_{k\in J}t_k<K_\varepsilon.
\tag{SD51}
\]

A useful simpler bound is h_k>=M_k-max({0} union
{rho([a]_k):a in A_k}). It is positive exactly when M_k>0 and every
old maximizing phase is excluded. SD49 can additionally charge
actual D-intersections in the surviving near-maximal phases.

Choose K0 resolving rho, D and all selected d,m, with every prime
height positive; retain Haar tails. For g=gcd(k,K0), d|k iff d|g,
and A_k is the inverse image of A_g. The exact finite reduction is

\[
R_{\mathcal H}(\sigma)=
\sum_{\substack{g\mid K_0\\g>1}}\gamma_g q_g^{\mathcal H}(\sigma),
\qquad
\gamma_g=\prod_{\substack{p\in P\\v_p(g)=v_p(K_0)}}\frac p{p-1}.
\tag{SD52}
\]

This reuses JB5, with maxima over the declared menus. It retains all
higher query exponents. Actual finite phase histograms and reservation
congruences suffice; separate query-dependent source laws do not.

### Saturated parent phases remove a complete numerical cone

For one actual parent d define its literal divisor-survivor residues

\[
S_d=\{z\bmod d:\ z\not\equiv a_e\pmod e
     \text{ for every actual original }e>1\text{ with }e\mid d\}.
\]

This definition INCLUDES the original d itself. Because sigma avoids
all P-only originals, its mod-d support lies in S_d. Comparable
original disjointness puts every selected descendant's mod-d phase
in S_d, and FC941 makes those phases pairwise distinct.

Suppose the selected P-only descendants of d occupy every residue
of S_d. Equivalently their number equals |S_d|. Then every k divisible
by d has qH_k(sigma)=0: each phase meeting sigma is forbidden to the
tail. This deletes the entire numerical cone, uniformly in the actual
weights of sigma and in all query heights.

For every k, the partition into k phases gives q_k(sigma)>=s/k.
Put C_P=product_(p in P)p/(p-1)=323323/110592. Therefore

\[
R_P(\sigma)-R_{\mathcal H}(\sigma)
\ge\sum_{d\mid k}q_k(\sigma)\ge\frac{C_P}{d}s.
\tag{SD53}
\]

With R_P(sigma)<=A_epsilon and s>=1-delta, a uniform sufficient
condition under this ACTUAL saturation premise is

\[
(566+49C_P/d)(1-\delta)>49A_\varepsilon.
\tag{SD54}
\]

For SD46's A_epsilon this allows respectively

| Saturated parent d | Sufficient delta upper threshold |
|---:|---:|
|5|0.06834734010495902...|
|7|0.05534316295050326...|
|35|0.028214444129245873...|

The thresholds mean strict inequality. The previous bound without
certified query saving is0.021187039962459072.... These are conditional
certificate improvements; no saturation occurrence is asserted.
For several saturated parents, replace C_P/d by C_P times the finite
inclusion-exclusion sum of reciprocal lcms. This counts each removed
numerical query once, even when its label lies in several cones.

Divisor closure provides an explicit sufficient route to saturation.
If m=d r lies in H_d, every d t with t|r and t>1 is another such child.
Thus tau(r)-1 distinct phases lie in S_d. If

    tau(r)-1=|S_d|,

saturation follows. In particular for prime d=p, |S_p|=p-1, so the
condition tau(r)=p suffices. For m=3^e d the forced child count is e.
These are conditions on an actual hull descendant, not a claim that
whole minimality supplies equality. A smaller child count leaves
unreserved phases which must still be paid in SD49.

The general unresolved input is now precise: force enough of these
actual reservations to eliminate near-maximal tail phases, or bound
D-intersections on every competitor that remains, while simultaneously
bounding the TOTAL D loss on the same rho. Saturation gives one uniform
sufficient branch, but existence of deep hull pairs, saturation or
adequate nonsaturated joint incidence has not been proved for every
hypothetical whole cover. All-height menu reduction and the ordinary
proofs above are not new Lean verification or an Erdős #7 solution.

### Whole-cover inventory excludes small saturated prime parents

The numerical gain in SD54 requires an actual saturation configuration.
Existing whole-cover structure excludes several prime-parent examples.
Keep the ONE EB1 family, minimizing first class count and then modulus
sum. Let Pmax be its largest support prime and N_p the number of ALL
original labels divisible by a prime parent p. The selected reservations
are still P-only, but N_p includes originals touching23 or29 or any other
support prime.

For a prime parent, S_p consists of the p-1 roots different from the
original p-root. If the selected reservations fill ALL of S_p, FC941
makes each such root contain exactly its one reserving original child.
Comparable-original disjointness leaves only the original p in its own
root. Thus

\[
N_p=p,\qquad H_p=1.
\tag{SD55}
\]

The height assertion reuses
[Report364 SI1--SI4](../../321-384/364-singleton-cofactor-ideal-and-forced-colors.md):
a singleton p-root must cover every p-tail over the same nonempty R_p,
so its original has p-exponent one. An original of higher p-height
would require a nonsingleton root. No conclusion here follows merely
from occupying every root currently carrying positive sigma-mass;
SD55 requires the complete arithmetic set S_p.

For Pmax>p, apply
[Report385 §56 NF66](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#56-the-original-cover-needs-enough-small-prime-labels-to-block-compression)
to the SAME original family. It gives N_p>=Pmax-p+2 without an exponent
bound. With SD55 this implies

\[
\text{a saturated prime parent }p
\quad\Longrightarrow\quad P_{\max}\le2p-2.
\tag{SD56}
\]

For Pmax=p the displayed conclusion is automatic since p>=3. If29 is
an ACTUAL support prime, no parent in {3,5,7,11,13} can be saturated.
Merely allowing29 in an ambient window does not establish its presence.
Alternatively, Report385 NF68 obtains Pmax>=29 by directly invoking
Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*,
edition1.0.1, Theorem1.1; the
[source entry](../../../../../../Library/Arith/schroeder2026nine.md)
records its verification boundary. This use of the attributed ordinary
source theorem does not assert a local kernel replay of its full
arbitrary-height proof.

If Pmax>=37, every prime parent at most19 is excluded. This structural
restriction does not extend SD48's separate support hypothesis; any
additional primes still require their continuation payment. For the exact
nine-prime support ending at29, only17 and19 remain as prime-parent
saturation possibilities among the seven head primes. Neither is
asserted to exist. SD54's d=5 and d=7 scalar implications remain valid,
but their full-saturation premises are empty in this EB1 domain with
Pmax>=29, so they supply no available credit there. Composite parent35
is not excluded by this prime-root count. Nor does SD56 exclude a
reservation menu covering only the support of sigma: unreserved roots
may have zero mass, which would require its own same-source proof.

### Crowding bounds the complete small-prime hull

If Pmax>2p-2, NF66 instead gives N_p>p. Among the p-1 non-own roots
there must be a root containing at least two original p-bearing labels.
The existing crowded-parent result, Report385 DR4, now forces EVERY
nonunit divisor of the complete private hull Gamma_p to be an original
label. In particular Gamma_p itself is original. Its formal encloser
interface is
[PrivateRegionRephasing](../../../../../../D5/S3/Arith/Covering/PrivateRegionRephasing.lean),
`crowded_descendants_force_private_encloser`.

Put g_p=Gamma_p/p. Report364's complete prime-private product
P_p={a_p modp} times all p-tails times R_p shows p does not divide g_p.
For any prime ell>p dividing g_p, R_p would have a singleton mod-ell
projection, contradicting
[Report374 EP4](../350-399/374-extremal-prime-projections-and-cardinality-descent.md#2-too-small-a-projection-gives-a-strictly-smaller-cover).
Thus all prime factors of g_p are strictly smaller than p.

Since every divisor is present, the actual hull descendants of p are
EXACTLY p*t for t|g_p, t>1. FC941 reserves a different non-own root for
each. None can occupy the crowded root, by DR5. Consequently

\[
\begin{gathered}
P_{\max}>2p-2\quad\Longrightarrow\quad
\Gamma_p=p g_p\in D,\qquad p\nmid g_p,\\
\ell\mid g_p\text{ prime}\Longrightarrow\ell<p,
\qquad \tau(g_p)\le p-1.
\end{gathered}
\tag{SD57}
\]

In particular, when Pmax>=29,

\[
\Gamma_5\in\{5,15,45,135\},\qquad
\Gamma_7=7\cdot3^a5^b,\quad(a+1)(b+1)\le6.
\]

This gives a finite numerical list of complete private hulls for each
fixed small prime, independently of the full period's exponent heights.
It does not assert that all listed choices are jointly realizable,
bound the period's3- or5-heights, force g_p>1, supply rho-mass on a
desired phase, or bound the total deletion loss. The possible trivial
hull g_p=1 is retained.

### A saturated single chain forces original ladders at the other primes

SD54's specialized test tau(r)=p on an actual hull child p*r makes
r=ell^(p-1) for one prime ell. Its p-1 divisor children fill S_p;
SD55 rules out ell=p, and Report374 EP4 gives ell<p. Hence the ENTIRE
p-bearing inventory is

    p*ell^j, 0<=j<=p-1.

For every other actual support prime q, q!=p,ell, this branch forces

\[
q\ell^{|p-q|+1}\in D.
\tag{SD58}
\]

To see this, reuse the complete collision-root test in Report385 §56,
with L=max(p,q), s=min(p,q). Its T consists of the actual first-L roots
of originals L*u for which s*u is also original and gcd(u,L*s)=1.
The pure-prime pair contributes root0 after the common EB3 translation.
No original has both p and q as factors, since that would lie outside
the stipulated complete p-chain. Thus all the mixed blocking sets F_b
in that test are empty.

If |T|<=L-s+1, at least s-1 first-L roots remain outside T. Matching
them to the nonzero first-s roots satisfies the existing CRT transport
test. It keeps the original s class on the untransported zero-root,
preserves all other original events through one witness, avoids every
numerical collision, and deletes the original L class. This contradicts
minimum cardinality. Therefore

    |T|>=L-s+2=|p-q|+2.

Each root in T arises from a pair p*u,q*u, and the complete p-chain
forces u=ell^j with 0<=j<=p-1. Different T roots require different j.
Thus at least |p-q|+2 distinct exponents have q*ell^j original. The
largest such j is at least |p-q|+1, and divisor closure proves SD58.
The same count gives |p-q|+2<=p; for q>p it recovers SD56.

For the p=17,ell=3 chain on the full support through29, the forced
labels at q=5,7,11,13,19,23,29 have ternary exponents respectively
13,11,7,5,3,7,13. For p=19,ell=3, the exponents at
q=5,7,11,13,17,23,29 are15,13,9,7,3,5,11. If ell!=3, the q=3
instance forces original3*ell^(p-2). These are simultaneous numerical
requirements in one family, with the ACTUAL original phases retained.
They supply no aligned ell-prefixes or common private-source weights.
The17/19 chains and the nonsaturated same-source payoff remain unresolved.

These deductions reuse the existing inventory, projection, private-hull
and CRT transport results; they are not additional generic matching or
repair theorems. Numerical restrictions do not assert that at most one
prime can saturate: the needed product of two saturated primes is not
forced by divisor closure. No unrestricted noncoverage conclusion or
new literature-priority claim follows.

A scoped Lean check verifies the finite original-slot pigeonhole argument,
its application to the frozen crowded-private-encloser theorem, and the
reservation capacity and small-prime contradictions with NF66's lower
bound as an EXPLICIT premise. Its axiom closure uses only propext,
Classical.choice and Quot.sound. It does not supply NF66's geometric
transport, FC941's reservation hypotheses, EP4's projection theorem, the
single-chain transport in SD58, or the attributed nine-prime theorem.
Those parts remain the ordinary proofs and source applications identified
above; no new canonical Lean declaration is claimed for this reuse.
