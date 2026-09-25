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
[Report348](../321-384/348-fresh-prime-root-transport-and-two-copy-reduction.md).
They do not transfer automatically through an arbitrary ternary
prefix: different original powers of3 can create more than two
projected phases at the same numerical cofactor. A restricted
nine-prime consumer, with that multiplicity hypothesis explicit,
is given below. Unrestricted Erdős #7 remains open.

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
reuse [Report463](463-two-actual-prime-extensions-preserve-a-common-core-law.md).
The projection restriction is not automatic for arbitrary ternary
histories. No assertion about unrestricted first-nine-prime families,
arbitrary larger prime supports or unrestricted Erdős #7 follows.

## Verification

The [standard-library producer](../../frontier/cover-geometry/pa_complete_suffix_debits.py)
and [exact data](../../frontier/cover-geometry/pa_complete_suffix_debits.json)
reconstruct full moments, suffix hinges, cap slopes, prefix mass
bounds, signed-penalty corrections, all four corners and the restricted
nine-prime consumer. All150 checks pass with Python optimizations
enabled. Independent arithmetic reconstructs the four corners and
both bounds without importing the producer. The finite-box and
all-height arguments above supply the arbitrary-family proof; finite
checks do not replace it. No Lean was added or run.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/pa_complete_suffix_debits.py
```
