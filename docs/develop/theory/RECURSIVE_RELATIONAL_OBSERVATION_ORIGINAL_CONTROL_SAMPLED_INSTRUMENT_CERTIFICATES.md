# Recursive relational observation: sampled original-control instrument certificates

> **Machine contract.** This is a `generic-v1` reference volume. Locators are
> determined from this file's bytes by `GenericAtomizer`, without a genre
> registry. Merged bytes are append-only: corrections and extensions go after
> the terminal append anchor, with existing sections and anchors preserved.

## 1. Mathematical scope and the acquisition consumer

**Convention 1.1 (reference input).** This volume contains
ordinary mathematical definitions and proofs, without new Lean verification,
physical implementation or a completion claim. Lean declarations remain the
repository's mathematical source of truth.

All repository suppliers here are read at immutable revision
`5094da88f161741b61de3b6b16dbc3a115a83d63`. The four credited volumes are
[Instrument Boundaries](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md),
[Instrument Stability](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md),
[Quantum Carrier Minimum](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md)
and [Record Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md).
Their classification, sharp canonical survival, signed-loss image, phase-order
and winding witnesses, stability boundaries, exact qutrit correspondence,
coding minimum and area/winding acquisition certificates are reused.

The concrete consumer is Instrument Stability §5: certifying the complete
terminal operation requires time/mode loss-density error and terminal Kraus
error. Area/winding accuracy alone does not supply the first datum. Here a
finite simultaneous timed height/relative-phase record, together with an
externally justified bound on variation of height velocity, supplies both.
Theorem 7.1 gives a complete exact-time, five-mode certificate. Theorem 9.4
gives the deterministic sample/noise order for predicting this complete
instrument in one actual positive zero-phase source subclass.

A coordinate sampler is an added service. Its existence, lawful delivery,
calibration, disturbance and joint law are not consequences of transport.
Section 3 distinguishes a programme-source recorder continuing through
specimen failure from a recorder available only while the specimen is live.
Section 8 states an extra joint-kernel premise before making a joint-output
claim. A pointwise accurate table by itself establishes no such premise.

## 2. Original source, restricted controls and the complete metric

**Definition 2.1 (positive double-wall source).** Fix

$$
0<Z<1,\qquad r=1-Z=2c,\qquad b=(c,c,Z),\qquad
0<\eta<c/2,\qquad a\in[\eta,c-\eta].
\tag{SC.1}
$$

Modes are ordered $(0,1,2,3,13)$, with index $4$ denoting mode $13$.
The supplied probabilities and signed weights are

$$
p(k)=(k,c-k,Z,c-k,k),\qquad
w(k)=\tfrac12(1,0,0,0,1)-\frac{k}{r}(1,1,0,1,1).
\tag{SC.2}
$$

Fix the same positive preparation and calibrated reference where actually
supplied. An original control has finite $T\geq0$, continuous real $k,\chi$,
strict $0<k<c$, finite variation of $\chi$, and either absolute continuity of
both coordinates or the original finite-piecewise-$C^1$ alternative with
continuous derivative rates on its closed pieces. The latter also implies
absolute continuity by the supplied finite fundamental-theorem argument.
Put $\xi(t)=\chi(t)-\chi(0)$. The real lift is kept before any phase reduction.

For the certificate impose the additional source promises

$$
\begin{gathered}
k(0)=k(T)=a,\qquad \eta\leq k(t)\leq c-\eta,\qquad
|k'|\leq L\quad\text{a.e.},\\
\operatorname{TV}(\chi)\leq V,\qquad
v=k'\text{ a.e. for a BV representative }v,\qquad
\operatorname{TV}(v)\leq W,
\end{gathered}
\tag{SC.3}
$$

where $L,V,W$ are finite nonnegative supplied upper bounds. BV variation may
equivalently be bounded by the distributional variation on the open interval;
no artificial jumps from zero outside $[0,T]$ are charged. Values of $v$ at
individual partition points do not affect any integral. One may choose the
regulated representative with endpoint traces. These promises restrict both
original regularity alternatives; they do not replace the original class.
There is no bound on $\chi'$ and no exclusion of either sign of winding.
The current-loop variant adds $\xi(T)=2\pi m$, $m\in\mathbb Z$. A fixed $V$
contains only its compatible sectors; the union over finite $V$ contains all
signed integers. Unknown preinitial phase and winding are not inputs.

The exact return height is a source/generator guarantee, not an inference
from noisy endpoint readings. It supplies the actual matching guard for
later controls based at $a$.

**Definition 2.2 (credited canonical complete instrument).** For the
prescribed original control set

$$
\begin{aligned}
\lambda&=\frac{(k')_+}{k}+\frac{(-k')_+}{c-k},&
S(t)&=\exp\left(-\int_0^t\lambda\right),\\
H_i(t)&=\int_0^t w_i(k)\chi',&
g_i&=\lambda-(\log p_i(k))',\\
G_i(t)&=\int_0^t g_i,&
u_i(t)&=e^{-G_i(t)},\qquad m_i(t)=g_i(t)u_i(t).
\end{aligned}
\tag{SC.4}
$$

The rates $g_i$ are nonnegative and integrable by the canonical construction.
The credited no-failure operator can be written

$$
K_t=\operatorname{diag}_i(e^{-G_i(t)/2-iH_i(t)}),\qquad
e^{-G_i(t)}=\frac{S(t)p_i(k(t))}{p_i(a)}.
\tag{SC.5}
$$

This rewriting retains the initial normalization. With arbitrary unchanged
quantum reference $R$, the failure density in mode $i$ on a joint input is

$$
|f\rangle\langle f|\otimes m_i(t)\rho^R_{ii},\qquad
\rho^R_{ii}=\langle i|\rho_{LR}|i\rangle.
\tag{SC.6}
$$

The output includes success with unnormalized state $K_T\rho K_T^*$, or
exact first failure time $t\in(0,T]$, original mode $i$, and absorbing $f$.
Every Borel time event and each of the five mode names remain available.
On the supplied six-dimensional extension the no-new-failure operator is
$K_T\oplus1_f$ and jumps annihilate $f$. Existing stopped status is retained;
it is not a new successful trial. No reset, reverse execution, fresh specimen,
post-failure original trial, hidden Kraus-index access or environment port is
added. Calibrated Kraus operations, blank ancillas, prescribed waveform
execution and exact time/mode recording are conditional ideal services.

**Definition 2.3 (exact-time operational error).** For two instruments on
this same record space, use precisely Instrument Stability (IS.7):

$$
\begin{aligned}
d_{\rm op}(\mathcal I,\widetilde{\mathcal I})
=\sup_{R,\rho}\frac12\bigg(&
\|(K_T\otimes I_R)\rho(K_T^*\otimes I_R)
 -(\widetilde K_T\otimes I_R)\rho(\widetilde K_T^*\otimes I_R)\|_1\\
&+\sum_{i=0}^4\int_0^T
 \|(m_i(t)-\widetilde m_i(t))\rho^R_{ii}\|_1\,dt\bigg).
\end{aligned}
\tag{SC.7}
$$

The supremum is over common normalized inputs and arbitrary normal quantum
references, including infinite-dimensional ones. There is no time binning,
mode merging, postselected normalization, or restriction to classical source
probabilities. The same definition with $K_T\oplus1_f$ covers the stopped
extension. Complete normalized outputs have distance at most one. For the
minimax task below it also defines distance to any complete predicted
instrument on the same output space, by the corresponding output trace norm.

## 3. What an acquired table means

**Definition 3.1 (simultaneous timed values).** For $T>0$, let $n\geq1$,
$h=T/n$ and $t_j=jh$. An added acquisition service supplies ordered actual
times and numerical readings with one simultaneous certificate:

$$
\begin{gathered}
0=s_0<\cdots<s_n=T,\qquad |s_j-t_j|\leq\tau,\\
|y_j^{\rm raw}-k(s_j)|\leq d_k,\qquad
|x_j^{\rm raw}-\xi(s_j)|\leq d_x.
\end{gathered}
\tag{SC.8}
$$

All values refer to the same source/epoch, preparation, programme and clock.
Height and unwrapped relative-phase readings in each row are simultaneous.
The phase anchor is the actual initial event, not a guessed past lift.
Sensor error includes gain, bias, drift and quantization. A statistical
certificate must specify one joint event; separate marginal coverage
probabilities do not imply (SC.8) simultaneously. Asynchronous readings
need an additional phase modulus or a proved simultaneous-error contract:
total phase variation alone does not control a compressed intervening pulse.

Clip heights to $[\eta,c-\eta]$ and set $y_0=y_n=a$, keeping raw fields.
Let $x_j=x_j^{\rm raw}-x_0^{\rm raw}$. Form the affine interpolants
$\widetilde k,\widetilde\xi$ through $(t_j,y_j)$ and $(t_j,x_j)$.
Their initial relative phase is zero and their height returns exactly to $a$.
The actual surrogate phase is $\chi(0)+\widetilde\xi$; its execution would
require its own relative-command actuator, without learning $\chi(0)$.
Both interpolated coordinates have finite-piecewise-$C^1$ regularity and
finite variation. Their transported lift is the original integral lift.
When both coordinates change on a cell this lift need not be affine; no
claim of an affine chart for the full lifted state is needed.

The surrogate is an actual mathematical original control. It need not obey
the true source's speed or BV-velocity bounds. Those bounds are used to
certify its error, not silently imposed on interpolated noise. Its finite
description is not permission to execute it in place of the requested
programme and is not a reconstruction of the unknown quantum input.

**Definition 3.2 (two distinct delivery contracts).** Under the
programme-source recording contract, a classical command source actually
continues generating and recording its waveform through $T$, even when the
specimen has failed. Its full output supplies (SC.8). The data are generated
by that continuing command source; a failed specimen does not execute its
unvisited live tail. This is an additional service beyond the canonical
stopped instrument, with its own permission, calibration, work and storage.

Under the specimen-only contract, the recorder supplies only rows actually
obtained while live, then the actual failure time/mode and absorbing
successor. Failure before a complete table returns an incomplete
whole-programme certificate. No missing suffix is filled from a law, a
guessed programme or a retry. Surviving through the known return checkpoint
and receiving all rows can yield the pointwise certificate below. Neither
contract automatically supplies a joint nondisturbing sensor; §8 adds its
explicit premise for a joint-output comparison.

An illegal sensor or control request returns its visible unexecuted rejection
and no executed successor. A legal sensor failure retains its partial values,
clock/calibration flags, reason and declared successor. Missing permission,
source identity or calibration, ambiguous winding, arithmetic overflow or
exhausted precision yields an inconclusive acquisition result. Unflagged
violation of a promised sensor or regularity inequality is outside the
theorem; no universal violation detector is constructed.

## 4. Recovering strong height error from finite values

**Lemma 4.1 (BV interpolation constants).** Suppose $k$ is absolutely
continuous and $k'=v$ a.e. with $\operatorname{TV}(v)\leq W$. Let $k^0$ be
its exact-value affine interpolant on the uniform mesh. Then

$$
\|(k^0)'-k'\|_{L^1}\leq Wh/2,\qquad
\|k^0-k\|_\infty\leq Wh/4.
\tag{SC.9}
$$

If $|k'|\leq L$, independently $\|k^0-k\|_\infty\leq Lh/2$.
The single-cell constants $1/2$ and $1/4$ are attained by a velocity with
one jump at the midpoint.

Proof. On $I=[l,l+h]$, the interpolant slope is the mean
$\bar v=h^{-1}\int_Iv$. Jensen and the variation measure give

$$
\begin{aligned}
\int_I|v-\bar v|
&\leq\frac1h\int_I\int_I|v(t)-v(s)|\,ds\,dt\\
&\leq\frac2h\int_{(l,l+h)}(u-l)(l+h-u)\,d|Dv|(u)
\leq\frac h2|Dv|((l,l+h)).
\end{aligned}
\tag{SC.10}
$$

The middle inequality follows by integrating the variation between $s,t$;
the set $s<u<t$ has area $(u-l)(l+h-u)$, and the other order contributes
the same amount. All integrands are nonnegative. A mesh-point jump has no
effect on either adjacent cell's a.e. values, so the open-cell variation
measures sum to at most $W$ without double counting. This proves the first
bound. The cell residual $k-k^0$ starts and ends at zero. Its derivative
$v-\bar v$ has integral zero; each positive or negative part has integral
half its $L^1$ norm. Any primitive value is bounded by that half, giving
the second bound after (SC.10). For the Lipschitz bound write
$t=l+uh$ and use

$$
|k(t)-(1-u)k(l)-uk(l+h)|\leq 2Lu(1-u)h\leq Lh/2.
$$

For a midpoint jump of size $q$, direct integration gives derivative error
$hq/2$ and maximum height error $hq/4$. This also verifies the stated
constants for jumps. $\square$

**Proposition 4.2 (timed noisy height certificate).** Under (SC.3) and
(SC.8), define

$$
\begin{aligned}
\delta&=d_k+L\tau,&
\Delta&=\min(Lh/2,Wh/4)+\delta,\\
E&=Wh/2+2n\delta,&
M&=LT+2nd_k,\\
B&=E/\eta+M\Delta/\eta^2,& h_*&=h+2\tau.
\end{aligned}
\tag{SC.11}
$$

Then both heights lie in the same positive band and

$$
\|k-\widetilde k\|_\infty\leq\Delta,\qquad
\|k'-\widetilde k'\|_{L^1}\leq E,\qquad
\operatorname{TV}(\widetilde k)\leq M.
\tag{SC.12}
$$

Proof. Before clipping, every nominal nodal error is at most
$d_k+L\tau$. Projection to the known interval is nonexpansive relative to
a true height in that interval. The endpoint replacement is exact at both
actual and nominal endpoints. Thus the interpolated nodal errors have
supremum at most $\delta$. Their derivative has $L^1$ norm
$\sum_j|e_{j+1}-e_j|\leq2n\delta$. Add Lemma 4.1 to get the first two
claims. For the variation use ordered actual times, not nominal times:

$$
\sum_j|y_{j+1}-y_j|
\leq\sum_j|k(s_{j+1})-k(s_j)|+2nd_k\leq LT+2nd_k.
$$

Linear interpolation stays in the convex band and has exactly this nodal
variation. $\square$

Timing affects the derivative estimate through $2nL\tau$. Only the
phase-area calculation below is invariant under changing individual cell
durations. The exact-time loss measure is not reparameterized; its error is
compared on the nominal physical clock using (SC.12).

## 5. Terminal phase and paid current signed winding

**Proposition 5.1 (phase-area certificate without a phase-speed bound).**
For the general interpolant of Definition 3.1 set

$$
\begin{aligned}
\mathcal A&=\int_0^T k\chi',&
\widetilde{\mathcal A}
 &=\sum_{j=0}^{n-1}b_j(x_{j+1}^{\rm raw}-x_j^{\rm raw}),\qquad
b_j=(y_j+y_{j+1})/2,\\
E_A&=(Lh_*/2+d_k)V+d_x(2c+M),&
P&=d_x+E_A/r.
\end{aligned}
\tag{SC.13}
$$

Then $|\mathcal A-\widetilde{\mathcal A}|\leq E_A$. The real terminal
phases of true and surrogate controls satisfy
$\max_i|H_i(T)-\widetilde H_i(T)|\leq P$; in particular their character
errors are at most $\min(2,P)$.

Proof. On a cell with endpoints $s_j,s_{j+1}$,

$$
\left|k(t)-\frac{k(s_j)+k(s_{j+1})}{2}\right|
\leq\frac L2(s_{j+1}-s_j)\leq Lh_*/2.
$$

Replacing the two heights by $y_j,y_{j+1}$ adds at most $d_k$.
Integration against $|\chi'|$ over all cells costs at most the first term
in $E_A$. Write $e_j=x_j^{\rm raw}-\xi(s_j)$, so $|e_j|\leq d_x$.
The remaining error is exactly

$$
\sum_j b_j(e_{j+1}-e_j)
=b_{n-1}e_n-b_0e_0
 +\sum_{j=1}^{n-1}(b_{j-1}-b_j)e_j.
\tag{SC.14}
$$

Both endpoint coefficients are bounded by $c$. Moreover
$\sum_{j=1}^{n-1}|b_j-b_{j-1}|\leq\sum_j|y_{j+1}-y_j|\leq M$:
each difference of averages is half the sum of two adjacent increments,
and every interior increment is charged at most once. This proves $E_A$.

The displayed trapezoid sum is exactly the integral
$\int\widetilde k\,d\widetilde\xi$ of the simultaneous affine
interpolants. It depends on vertices, not cell durations; centering every
phase vertex by the same $x_0^{\rm raw}$ changes no increment. The original
signed weights give, as real numbers,

$$
H_+=\xi(T)/2-\mathcal A/r,\qquad H_-=-\mathcal A/r,\qquad H_2=0.
\tag{SC.15}
$$

The surrogate endpoint differs from $\xi(T)$ by at most $2d_x$.
Substitution gives $P$, and $|e^{iu}-e^{iv}|\leq\min(2,|u-v|)$ gives
the character bound. No phase derivative reconstruction is used. $\square$

**Proposition 5.2 (exact current signed sector with paid arithmetic).**
Suppose in addition the current executed/generator control is promised to
have $\xi(T)=2\pi m$, $m\in\mathbb Z$. The credited Record Acquisition
Theorem 7.3 certifies this signed $m$ from the endpoint readings: with exact
$\pi$ the sufficient condition is $d_x<\pi/2$. With rational arithmetic
choose an integer $M_\pi\geq V/6$, a positive rational $\pi_*$ and a
certified $|\pi_*-\pi|\leq\varepsilon_\pi$, and require

$$
2d_x+2M_\pi\varepsilon_\pi<\pi_*.
\tag{SC.16}
$$

Retain an inconclusive result if the separated-cell test fails. Once $m$
is certified, build a phase polygon with endpoints $0,2\pi m$ and the
unmodified internal $x_j^{\rm raw}$. The height polygon is unchanged. It
has exactly the current signed winding $m$, and its phase bound can use

$$
E_A^{\rm loop}=(Lh_*/2+d_k)V+d_xM,\qquad
P_{\rm loop}=E_A^{\rm loop}/r.
\tag{SC.17}
$$

Proof. The credited rounding argument uses
$|x_n^{\rm raw}-x_0^{\rm raw}-2\pi m|\leq2d_x$ and
$2\pi|m|\leq V$, hence $|m|\leq M_\pi$ because $\pi>3$.
(SC.16) keeps the measured difference strictly inside its unique rational
nearest-integer cell. Negative integers obey the identical separation test.
This uses the integer-loop promise; it does not infer that promise from
samples. The new endpoint errors in (SC.14) are exactly zero. Internal
errors remain at most $d_x$, leaving only $d_xM$. The endpoint real phase
increments now agree, so (SC.15) gives (SC.17). The new phase polygon is an
original control, with finite variation and a finite symbolic description
of its $2\pi m$ endpoint. $\square$

This certifies a current loop, not winding before the initial event. Its
surrogate does not overwrite the actual programme label or a permission
field. Exact mathematical $\pi$ in a programme description does not supply
an exact gate. For numerical bounds, use certified interval evaluation.
An arithmetic area error $\rho_A$ adds $\rho_A/r$ to $P$; an additional
phase-evaluation error $\rho_H$ adds $\rho_H$. Rational rounding in (SC.16)
and transcendental evaluation have separately charged precision.

## 6. Direct comparison of nonnegative loss rates

**Lemma 6.1 (first-loss density comparison).** Let $g,\widetilde g$ be
nonnegative integrable rates on $[0,T]$, let
$u(t)=\exp(-\int_0^t g)$ and $\widetilde u$ be defined likewise, and set
$e=\|g-\widetilde g\|_{L^1}$. Then

$$
\|gu-\widetilde g\widetilde u\|_{L^1}\leq2e,\qquad
|\sqrt{u(T)}-\sqrt{\widetilde u(T)}|\leq e/2.
\tag{SC.18}
$$

Proof. For $z=u-\widetilde u$, variation of constants in the absolutely
continuous scalar equation gives

$$
z(t)=-\int_0^t
 e^{-\int_s^t\widetilde g}(g(s)-\widetilde g(s))u(s)\,ds.
$$

Multiply the absolute-value bound by $\widetilde g(t)$ and integrate.
Tonelli and the scalar fundamental theorem give

$$
\begin{aligned}
\int_0^T\widetilde g(t)|z(t)|\,dt
&\leq\int_0^T|g-\widetilde g|(s)u(s)
 \left(1-e^{-\int_s^T\widetilde g}\right)\,ds\leq e.
\end{aligned}
$$

Adding $\int|g-\widetilde g|u\leq e$ proves the first claim. The function
$x\mapsto e^{-x/2}$ is $1/2$-Lipschitz for $x\geq0$; its arguments differ
by at most $e$, proving the second claim. No lower survival bound is used.
$\square$

**Lemma 6.2 (acquired height errors control every rate).** With the true
and reconstructed heights in (SC.12),

$$
\|\lambda-\widetilde\lambda\|_1\leq B,\qquad
e_i:=\|g_i-\widetilde g_i\|_1\leq2B,\qquad e_2\leq B.
\tag{SC.19}
$$

Proof. At fixed height the hazard is piecewise linear in velocity, with
slopes of modulus at most $1/\eta$. At fixed velocity $\widetilde k'$,
changing the height by at most $\Delta$ costs at most
$|\widetilde k'|\Delta/\eta^2$. Integrating gives the first bound,
which is the credited estimate (IS.26) with now-acquired error data.
Each of $k'/k$ and $-k'/(c-k)$ has the same $B$ difference bound, by the
same denominator calculation. Subtract these logarithmic derivatives from
the hazard for the plus and minus modes; the middle logarithmic derivative
is zero. The triangle inequality proves (SC.19). $\square$

## 7. Complete finite-record instrument certificate

**Theorem 7.1 (finite coordinate values to the complete operation).**
For every control satisfying (SC.1)–(SC.3), every $T>0,n\geq1$ and every
complete table satisfying (SC.8), the polygon of Definition 3.1 is a
strictly positive original control with exact return height $a$, and

$$
d_{\rm op}(\mathcal I_{k,\chi},\mathcal I_{\widetilde k,\widetilde\chi})
\leq\min(1,3B+P),
\tag{SC.20}
$$

where $B$ is (SC.11) and $P$ is (SC.13). With Proposition 5.2's paid
current-sector certificate and endpoint replacements, use $P_{\rm loop}$
instead. The bound holds on arbitrary five-dimensional live inputs with
arbitrary unchanged quantum references, and on the supplied stopped
extension. It therefore applies to the credited qutrit representation with
every actual correlated archive retained. For $T=0$ both instruments are
the identity, the table can be empty, and the error is zero.

Proof. Proposition 4.2 and finite polygon regularity establish the first
claim. For each original mode apply Lemma 6.1 to the nonnegative rates in
Lemma 6.2. Thus

$$
\|m_i-\widetilde m_i\|_1\leq2e_i\leq4B.
\tag{SC.21}
$$

By (SC.5), Lemma 6.1 and Proposition 5.1, each terminal diagonal difference
has modulus at most $e_i/2+P$, using attenuation at most one. Hence

$$
\|K_T-\widetilde K_T\|_{\rm op}\leq B+P.
\tag{SC.22}
$$

This also holds after adjoining the identical stopped entry. For any joint
input the blocks $\rho^R_{ii}$ are positive and their traces sum to at most
one. Therefore (SC.6) and (SC.21) bound the entire integrated failure
difference norm by $4B$. For the success map, contractions $K,L$ obey

$$
\|K\rho K^*-L\rho L^*\|_1\leq2\|K-L\|_{\rm op},
$$

also with an identity on $R$: add and subtract $L\rho K^*$ and apply the
trace-class ideal inequality. These arguments require no dimension bound
on $R$. The half-sum in (SC.7) is at most $(B+P)+2B=3B+P$.
Normalized complete outputs supply the cap one. For the current-loop
polygon use Proposition 5.2 in (SC.22). $\square$

The argument uses the initial-mode attenuation $u_i$, rather than first
bounding source-family loss densities and then dividing by $p_i(a)$ or a
terminal survival floor. The only denominators in the certificate are the
actual support margin and the fixed source parameter $r$. This improves a
sufficient bound for this acquisition consumer; it is not an inverse
stability result and does not remove the supplier's low-survival inverse
obstruction. The nonnegative-rate lemma is elementary mature calculus; its
combination with actual sampled source controls is the application here.

## 8. Joint sensor laws, causal use and complete boundary updates

**Definition 8.1 (an explicit sufficient extra joint service).** Let
$\omega$ index a classical source/generator programme and let $M_0$ contain
all actual classical source/epoch, permission, calibration, clock, controller,
pending-programme and selection/update fields. They can be correlated with
an arbitrary quantum input/reference/archive state $\rho_{\omega,M_0}$.
The label $\omega$ can be latent; using it in a mixture is not delivering it
to a controller. Suppose the programme-source recorder supplies a measurable
kernel $Q(dy\mid\omega,M_0)$ such that its full joint operation is

$$
\mathcal J_{\omega,M_0}(dy,do)(\rho)
 =Q(dy\mid\omega,M_0)\,
   (\mathcal I_{\omega}(do)\otimes\operatorname{id}_R)(\rho).
\tag{SC.23}
$$

Here $y$ contains every actual sensor/calibration/failure payload and $o$
the canonical quantum outcome, with exact failure time/mode. The source
programme is fixed over this stage. Sensor randomness is independent of
the canonical quantum process conditional on $(\omega,M_0)$, and the
sampler does not read or disturb the quantum archive. The promise includes
causal delivery of row $j$ only at/after its actual acquisition event. It is
a strong, explicit passive command-sensor premise; equal sensor marginals
or a table error bound cannot prove it. A sensor coupled to a live quantum
read must supply its own appropriate full joint operation instead.

**Proposition 8.2 (what the joint premise contributes).** Under (SC.23),
keep the same actual joint distribution of $(\omega,M_0,y)$ and the same
conditional input/reference states in the true and predicted models.
Replace only $\mathcal I_\omega$ by the polygon instrument computed from
$y$. Fix one total measurable predictor: use the stated polygon on reported
complete tables and a declared normalized default instrument on reported
incomplete results. The predictor does not inspect a latent good/bad event.
If $\varepsilon(y)$ bounds (SC.20) on every good pair $(\omega,y)$,
then the complete joint-output distance is at most

$$
\int_{\rm good}\varepsilon(y)\,d\Pr(\omega,M_0,y)
   +\Pr(\mathrm{bad}).
\tag{SC.24}
$$

In particular a uniform certificate $\varepsilon$ on a joint event of
probability at least $1-\alpha$ gives at most $\min(1,\varepsilon+\alpha)$.
This is unconditional and includes specimen and sensor failure branches.

Proof. Conditional on $(\omega,M_0,y)$, (SC.23) leaves exactly the
canonical instrument on its actual joint quantum input. Theorem 7.1 applies
to every such input, including its reference and archives. Integrate the
trace-norm inequality over the same classical measure on both sides.
On bad pairs the same record-defined predictor still outputs a normalized
instrument, so complete-output distance there is at most one. Retain every
actually reported failure label, but add no label for an unflagged statistical
error event.
The triangle inequality gives (SC.24). Discarding a latent analytical label
is contractive and does not grant its value to the controller. $\square$

**Convention 8.3 (failure and availability).** Under the specimen-only
contract a complete table is available only if the specimen survives and
the sampler actually finishes. The full-programme joint theorem cannot be
asserted from those censored data alone. For a source-family input the
canonical survival is $S(T)\geq e^{-LT/\eta}$. If the actual prefix sensor
leaves this canonical specimen marginal unchanged and has a joint
good-event probability at least $1-\alpha$, the intersection of
survival and good sensing has probability at least
$\max(0,e^{-LT/\eta}-\alpha)$, by the union bound. This lower bound is
specific to the source-family survival calculation, not every arbitrary
input in (SC.7). It is not guaranteed acquisition, a conditional-on-survival
error theorem, or permission to repeat. On failure retain the actual prefix
and $f$ with an incomplete whole-programme result. Under the extra
programme-source recorder, full command records may instead continue after
failure; their generation and storage are paid even on that branch.

**Proposition 8.4 (lawful finite use of a delivered certificate).** At the
terminal checkpoint keep every branch. On each completed live return branch
retain the actual specimen, full joint archives/reference, source and epoch,
time/reference calibration,
permissions, controller, pending programme, all raw sensor values, selectors,
and external update inputs. The exact common height is $a$ by (SC.3).
Allow every separately permitted prescribed original tail at this same base
with matching current height, either original regularity alternative, any
finite nonnegative duration including zero, and every signed sector allowed
by its explicit promise. Its relative real phase is joined by
`concatenate_original`; the unknown old lift is not a controller input.
Failed branches retain the original exact time/mode and absorbing $f$ with
only the declared stopped continuation. Illegal requests retain their
unexecuted rejection. Under these matched conditions any common finite
downstream CP protocol preserves a complete joint-output error bound such
as (SC.24), without conditioning on a successful live return.

Proof. The supplied chronological theorem keeps the old prefix and gives
the exact translated relative tail, with matching height and added original
weighted integrals. Thus the same permitted downstream operation has the
same domain in both comparisons. Treat all acquired classical fields as
retained controls and all quantum archives as reference inputs. A fixed
record-based policy and its complete update kernel are one common CPTP
operation on that full boundary. Trace distance contracts under it.
Iteration proves the finite claim; absorbing branches and rejections use
their same declared kernels. $\square$

The numerical summary does not replace the actual archive. A selector or
guard reading an omitted history field invalidates the matching premise.
An estimated terminal height cannot prove an exact matching guard; this is
why the return-height promise is used. Policies may use a certificate only
after its required values and arithmetic exist. A completed-stage table is
not a causal control input to an earlier action in that stage. An online
within-stage controller requires its own causal joint acquisition/actuator
proof, which (SC.23) for a fixed programme does not supply.

For a separately supplied sequence of at most $J$ adaptive components, if
each replacement has a uniform complete joint error $\varepsilon_j$ on
every reachable common boundary and the necessary certificate is available
at the point of use, the finite hybrid argument gives error at most
$\sum_{j=1}^J\varepsilon_j$. Replace one component at a time; common earlier
and later CP maps contract its uniform error, and the triangle inequality
adds the $J$ differences. Statistical bad-event exposures must also be
included. This mature composition rule supplies no unbounded horizon,
unsummable-error guarantee, unknown guard, free actuator or acquired overlap.

## 9. Sharp sample/noise order in a fixed original-control subclass

**Definition 9.1 (deterministic sample-only prediction).** Fix

$$
Z=1/2,\qquad c=1/4,\qquad a=1/8,\qquad\eta=1/16,\qquad
T>0,\quad L>0,\quad W>0.
\tag{SC.25}
$$

Let $\mathcal K$ be the original controls with constant real phase,
$k(0)=k(T)=a$, $\eta\leq k\leq c-\eta$, $|k'|\leq L$ a.e. and
$\operatorname{TV}(k')\leq W$ in Definition 2.1's sense. Both original
regularity alternatives are allowed. An estimator gets exact endpoint
heights, these common upper promises and at most $N$ adaptive interior
height queries. A query at an exact chosen time returns a value with
bounded adversarial error $\delta\geq0$. Its only source dependence is the
whole query transcript and matched metadata. Unlimited computation and
exact-real storage are allowed. It outputs one complete instrument on the
same exact-time, five-mode space. Numerical minimax loss requires an output
on every transcript; an abstention is an incomplete acquisition, not uniform
successful prediction.

Write $R_N(\delta)$ for the infimum over deterministic estimators of their
worst $d_{\rm op}$ error over $\mathcal K$ and all permitted errors. This
queries the waveform source, not the quantum specimen. There is no
uncounted programme log, generator state, quantum read, emitted stop record,
derivative sample, exact resource total, probability-law oracle, source
dependent seed or extra port. Retrospective query access is allowed, making
the lower stronger than for a causal logger. This is not a minimax claim
about every observer or about independent random noise.

**Lemma 9.2 (actual triangular loops and complete distance).** At the
source (SC.25), an affine up/down excursion from $a$ to $a+\alpha$ and
back, $0<\alpha<a$, with constant phase, has survival

$$
q(\alpha)=\frac{a-\alpha}{a+\alpha}.
\tag{SC.26}
$$

For a finite sequence of such excursions, possibly of different amplitudes
and durations, followed by or separated by waits, put
$S=\prod_jq(\alpha_j)$. Its complete instrument has distance exactly
$1-S$ from waiting, on every normalized live input with arbitrary unchanged
reference. All excursions are genuine original finite-piecewise-affine
controls from the same preparation, with zero phase, winding, area and
terminal normalized-state change.

Proof. Integrate the original hazard on the upward leg to get survival
$a/(a+\alpha)$; on the downward leg it is
$(c-a-\alpha)/(c-a)=(a-\alpha)/a$. Their product is (SC.26).
Chronological composition multiplies them. The final height and real
transport phases are unchanged, hence $K_T=\sqrt S I_5$. Completeness
gives total failure effect $(1-S)I_5$. Against waiting, the success
difference has norm $1-S$ and the positive failure blocks together have
trace $1-S$ on every normalized joint input. Their half-sum is $1-S$;
the failure event alone also attains it. All time/mode labels remain in the
comparison. $\square$

**Proposition 9.3 (two sample-only lower bounds).** Put $M_N=N+1$ and
suppose

$$
M_N\geq\max\{1,W/(4L),WT/(4a)\}.
\tag{SC.27}
$$

For every $\delta\geq0$,

$$
R_N(\delta)\geq\frac{WT}{16aM_N}.
\tag{SC.28}
$$

If $0<\delta\leq\delta_0$, where

$$
\delta_0=\min\left\{\frac14,\frac a2,\frac{WT}{32},
 \frac{2L^2T}{W},\frac{2a^2}{WT}\right\},
\tag{SC.29}
$$

then also

$$
R_N(\delta)\geq\frac{\sqrt{WT\delta}}{8\sqrt2\,a}.
\tag{SC.30}
$$

The second lower remains valid with any number of point queries.

Proof of (SC.28). Run a deterministic strategy on the exact constant replies
$a$, with the common upper promises. This is a realizable waiting source.
Its distinct query times and endpoints partition $[0,T]$ into $J\leq M_N$
positive gaps of lengths $\ell_j$ summing to $T$. Set
$v=W/(4M_N)$. In each gap insert a triangular excursion with slope $+v$
on its first half and $-v$ on its second half. Its excess is
$\alpha_j=v\ell_j/2$. The resulting single fixed actual path agrees with
waiting at every queried time. Induction over adaptive queries gives the
same times, replies and stopping decision: each next decision sees the
same prefix. Constructing this path after specifying the deterministic
strategy defines a worst-case fixed source, not a source changed mid-query.

Its speed is $v\leq L$ by (SC.27). Its BV derivative has one $2v$ jump at
each peak and one $2v$ jump at each join between consecutive gaps, so its
variation is $2v(2J-1)\leq W$. Endpoints do not add artificial exterior
jumps. Its largest excess is at most $vT/2\leq a/2$, which keeps it in
$[\eta,c-\eta]$. It is an actual original control with finitely many
affine legs and fixed preparation. By Lemma 9.2 its distance from waiting
is $1-S$, and

$$
-\log S\geq\sum_j2\alpha_j/a=vT/a=:x,\qquad 0<x\leq1.
$$

Here $-\log((1-z)/(1+z))\geq2z$ follows by integrating
$2/(1-z^2)\geq2$ from zero. Also $1-e^{-x}\geq x/2$ on $[0,1]$,
for instance by $e^{-x}\leq1-x+x^2/2$. Therefore
$1-S\geq WT/(8aM_N)$. The common-transcript estimate is at distance
at least half this from one of the two instruments, by the triangle
inequality. This proves (SC.28) for exact replies, which are permitted at
every noise budget. No exact variation total is supplied to the estimator.

Proof of (SC.30). Let
$n=\lfloor\sqrt{WT/(8\delta)}\rfloor\geq2$. Use $n$ equal triangular
excursions of excess $\delta$ over $[0,T]$. Their speed is
$u=2n\delta/T$, and

$$
\operatorname{TV}(k')=2u(2n-1)\leq8n^2\delta/T\leq W,\qquad
u\leq\sqrt{W\delta/(2T)}\leq L.
$$

The band holds because $\delta\leq a/2$. This path and waiting can return
the same value $a$ at every time, even under unlimited point access: choose
the fixed error function $a-k(t)$ on the triangular path and zero on
waiting. Both have sup error at most $\delta$ and exact endpoints. Thus
all deterministic adaptive transcripts match, irrespective of the query
count. They have common calibration promises and constant phase.

Now $S=q(\delta)^n$ and $x=2n\delta/a\leq1$ by (SC.29). As above,
$1-S\geq1-e^{-x}\geq n\delta/a$. Since
$n\geq\tfrac12\sqrt{WT/(8\delta)}$, the instrument separation is at
least $\sqrt{WT\delta}/(4\sqrt2 a)$. Halving for the common estimate
proves (SC.30). These are deterministic bounded-error functions, not
stochastic or independently sampled noise. $\square$

**Theorem 9.4 (sharp deterministic order with explicit regimes).** With
the fixed class (SC.25), for every $N$ satisfying (SC.27) and
$0\leq\delta\leq\delta_0$, there are positive constants depending only
on $T,L,W,a,\eta$ such that

$$
C_-\left(\frac1{N+1}+\sqrt\delta\right)
\leq R_N(\delta)\leq
C_+\left(\frac1{N+1}+\sqrt\delta\right).
\tag{SC.31}
$$

One may take

$$
\begin{aligned}
C_-&=\frac12\min\left\{\frac{WT}{16a},
                         \frac{\sqrt{WT}}{8\sqrt2 a}\right\},\\
C_1&=\frac{WT}{2\eta}+\frac{(LT+1)WT}{4\eta^2},\qquad
C_2=\frac2\eta+\frac{LT+1}{\eta^2},\qquad
C_+=6C_1+3C_2.
\end{aligned}
\tag{SC.32}
$$

Constants are explicit sufficient ones, not claimed minimax optimal.

Proof. For $\delta=0$ take $n=N+1$ cells; otherwise take
$n=\min(N+1,\lfloor\delta^{-1/2}\rfloor)$. Since $\delta\leq1/4$,
$n\geq1$, $n-1\leq N$, $n\delta\leq\sqrt\delta$ and
$1/n\leq2((N+1)^{-1}+\sqrt\delta)$. Use $n-1$ equally spaced
interior queries, exact endpoints and the known zero phase. Clip the
height values and output their polygon's canonical instrument. This is an
allowed complete-instrument prediction even if its polygon is outside
the original $L,W$ promise class. Set $\tau=d_x=V=0$ in Theorem 7.1.
Then $P=0$,

$$
E=WT/(2n)+2n\delta,\qquad
\Delta\leq WT/(4n)+\delta,\qquad
M\leq LT+2\sqrt\delta\leq LT+1.
$$

Consequently $B\leq C_1/n+C_2n\delta$, using $\delta\leq n\delta$.
Theorem 7.1 gives
$R_N(\delta)\leq3B\leq C_+((N+1)^{-1}+\sqrt\delta)$.
For the lower combine (SC.28) and (SC.30): the maximum of their two
right sides is at least half their sum after taking the smaller
coefficient. At $\delta=0$ only (SC.28) is needed. This proves (SC.31).
$\square$

The credited Record Acquisition lower bounds target area-derived coherence
responses under different regularity promises. The present witnesses have
identically zero phase, area, winding and normalized terminal-state change;
their target distinction is the canonical complete failure instrument.
The added BV-velocity promise yields the sample/noise tradeoff rather than
the supplier's fixed-variation floor. All witnesses lie in one fixed
positive original source. No action/law/resource correspondence to the
stationary $\alpha/\beta$ or fixed-Hamiltonian minimax model is inferred.

## 10. Finite record, clock, programme and arithmetic resources

**Proposition 10.1 (one sufficient allocation).** For fixed effectively
described $T,L,W,V,\eta,c$, taking $n\to\infty$ with
$d_k,\tau=O(n^{-2})$ and $d_x=O(n^{-1})$ gives
$\Delta,E,B,E_A,P=O(n^{-1})$ and hence a complete-operation certificate
$O(n^{-1})$. If finite arithmetic is used, require its additional phase
budget to be $O(n^{-1})$ as well.

Proof. In (SC.11), $h=T/n$, $n\delta=O(n^{-1})$ and
$M=LT+O(n^{-1})$. Substitute these into (SC.13), then (SC.20).
The loop version has the same order. $\square$

This is a sufficient finite-horizon allocation, not a physical price law.
In the minimax task, optimizing the sample count against a fixed $\delta$
instead uses $n$ of order $\min(N+1,\delta^{-1/2})$. Oversampling raw noise
without this balance need not improve the complete instrument.

**Definition 10.2 (charged digital boundary).** A finite implementation
needs finite effective descriptions or enclosing certificates for public
parameters, duration, support, $L,V,W$, the clock and phase reference.
On rational numerical grids the $n+1$ rows have bounded height range and
relative-phase range within $[-V-d_x,V+d_x]$. Height resolution of order
$n^{-2}$ and phase resolution of order $n^{-1}$ require $O(\log n)$ bits
per value for fixed ranges. Nominal mesh indices and uncertainty tags also
take $O(\log n)$ bits under the stated allocation. Thus one sufficient
table storage is $O(n\log n)$ bits, plus actual raw sensor payloads and
all metadata. This table estimate excludes any extra exact measured
timestamps and the original canonical exact failure time, which remains an
ideal real-valued record without a claimed finite-bit encoding.

Retain source/preparation/epoch identity, actual archives, calibration and
units, clock/reference certificates, permission data, generator/recorder
and pending-programme state, selectors, updates and all failure payloads.
The table is neither the whole archive nor the quantum state. Use the
credited fixed calibrated $M_3$ live carrier and absorbing sector only
when their actual encoding/decoding and operations are supplied. Its upper
correspondence preserves correlated archives; its unassisted dimension lower
does not apply to a code given such archives. No new quantum minimum or
minimum total observer memory is asserted.

For rational height/phase grids the trapezoid sum in (SC.13) can be
accumulated exactly with common denominator $2D_kD_x$, using $n$
multiplications and linearly many additions/subtractions at charged bit
widths. Retaining input values and a proved accumulator bound avoids
unreported overflow. The certificate itself uses rational bounds when the
public bounds are rational. The signed-loop version also uses an integer
of bounded magnitude and a finite symbolic $\pi$ description; certified
interval arithmetic evaluates its irrational quantities to paid precision.
Transcendental gate synthesis and waveform actuation are different costs.
Actual sampler calls, source preparation, simultaneous calibration,
unwrapping, programme generation, computing and storing certificates are
all separate resources. Continuing the command source after specimen
failure is charged through $T$ without executing a new positive specimen.

The source-side regularity promise is substantive. Finite values cannot
certify it on the full original class: in any unqueried interval of length
$\ell$, put $p$ small triangular excursions at fixed speed below $L$.
Their excess is proportional to $\ell/p$, while derivative variation grows
proportionally to $p$. For sufficiently large finite $p$ they stay in the
positive band, agree with waiting at all queried times and exceed any
proposed $W$. The record must therefore obtain its $W$ justification from
a generator constraint or a separate trusted certificate, rather than
estimate a universal bound from the same samples.

## 11. Suppliers, mature overlap, exact checks and open bridges

**Convention 11.1 (immutable source map).** The following suppliers all
refer to `5094da88f161741b61de3b6b16dbc3a115a83d63`. Paths identify
reused statements, not a compilation claim for this volume.

| Supplier | Actual contribution and boundary |
| --- | --- |
| [FiniteRectangleTransport Lean](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean), `ValidBase`, `probability`, `phaseWeight`, `weight_compatible`, `finite_rectangles_realize`, and its [Scribe](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/Blueprint/D5/S3/Quantum/Fibers/FiniteRectangleTransport.scribe.cs) | The exact positive signed source and all-sector original controls. Its double-wall weight gives (SC.2), hence the real phases (SC.15). No physical waveform sampler or actuator follows. The Scribe's all-sector applications are distinct from the scope of the rectangle declaration alone. |
| [OriginalControlComposition Lean](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/D5/S3/Quantum/Fibers/OriginalControlComposition.lean), `OriginalControl`, `FiniteC1Control`, `concatenate_original`, and its [Scribe](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.scribe.cs) | Both original regularity alternatives, zero and arbitrary finite durations, literal unchanged prefix, matching heights, translated relative tail and added weighted integrals. Used in polygon admissibility and lawful continuation, without revealing old lifts. |
| Instrument Boundaries §§4–5.2, 9–15 | The specified canonical optimal stopped instrument, signed source family, nonnegative rates, exact first time/mode output, classification, actual witnesses and joint finite continuation are credited. Lemma 9.2 applies its existing survival factors. No optimum or classification is redelivered. |
| Instrument Stability §§1, 3–5, especially IS.7 and IS.26–29 | Supplies the target complete metric, oscillation and low-survival boundaries and sufficient strong-data route. The acquired-record map supplies those data; direct mode-rate comparison gives (SC.20) without an artificial inverse-survival factor. |
| Quantum Carrier Minimum §§2–4, 6 | Reuse of the exact five-labelled live qutrit plus absorbing sector, preserving supplied joint archives. Its unassisted coding minimum has different inputs from its archive-preserving upper. Neither is a waveform sensor or a finite archive bound. |
| Record Acquisition §§2, 5–9, 11–12 | Credited query restrictions, conditional simultaneous samples, paid area/winding certificate, arithmetic and failure conventions. Proposition 5.2 reuses its signed rounding theorem; §9 here concerns a different complete-instrument target with a new BV-velocity promise. |
| Transport-Memory Completion §§2.9–2.12, 2.18 | Same coherent source, actual common port, aligned stable readings, known nonzero amplitudes and known nonzero record overlap remain required. Numerical control quadrature constructs none of these and cannot divide out an unknown overlap. |
| Process Geometry §34, especially PG.3400b-full and PG.3400c; Atlas Stable Core Holonomy §§1–3 | The actual joint source image, reachable domains, routes, permissions, complete rejections/failures, references, selector and update inputs remain separate obligations. Section 8 retains them as joint fields; it does not construct their actual acquisition or full closure. |
| `D5/S3/ObserverMemory/Dynamics/TwoClockKrylovClosure.lean`, `two_clock_span_eq_krylov` | Its exact finite-dimensional mixed-power span identity is not used as a sampler, conditioning estimate or acquired-record map. No cross-model theorem is transferred. |

**Literature statement 11.2 (precise attribution).** Averaging in BV,
piecewise-linear interpolation, summation by parts, nonnegative scalar
hazard equations, trace-class ideal inequalities, two-point minimax arguments
and finite CP composition are mature mathematics. The source-specific
finite timed-record certificate in Theorem 7.1 and the realized
sample/noise comparison in Theorem 9.4 are `repo-derived` ordinary deductions.
No worldwide originality or exhaustive literature-search claim is made.
Bounded searches of the pinned original-control/fiber sources did not find
this BV-velocity-to-complete-instrument certificate or its noise lower.

| Accessible primary text | Verified scope and use |
| --- | --- |
| N. S. Hoang and A. G. Ramm, [*On stable numerical differentiation*, arXiv:0711.4403v3](https://arxiv.org/html/0711.4403v3), §1 and §2.1, Eqs. (1), (3)–(5), Theorem 1 | `literature-attested`: differentiation of noisy values is ill-posed; their Volterra regularization uses $\alpha(\delta)\to0$ and $\delta/\alpha(\delta)\to0$ for the stated convergence. This credits the resolution/noise issue. No BV constant, source-specific instrument rate or sampler premise is imported; those are proved here. |
| L. Bouten, R. van Handel and M. R. James, [*A discrete invitation to quantum filtering and feedback control*, arXiv:math/0606118v2](https://arxiv.org/html/math/0606118v2), §§7.2–7.3, especially Lemma 7.66 and the controlled-filter construction | `literature-attested`: feedback is adapted to actual past observations with specified controlled coefficients; self-nondemolition/nondemolition is required for the conditional-state interpretation. No field-measurement channel or filter is supplied for the present absorbing source by citing it. This supports the boundary distinction in §8, not an imported acquisition theorem. |

The DOI texts for the Kuramochi erratum `10.1063/1.4961516`,
Ramm–Smirnova `10.1090/S0025-5718-01-01307-2` and Chartrand
`10.5402/2011/164564` were unavailable in the supplied primary-access
boundary. They are bibliographic leads only; no unseen theorem from them
supplies a premise. The elementary arguments above stand independently.

**Example 11.3 (finite exact arithmetic).** At
$c=2/5$, $Z=1/5$, $r=4/5$, $a=1/5$, $\eta=1/10$, $T=1$,
$L=1/5$, $W=V=1$, take $n=4096$, $d_k=\tau=n^{-2}$ and $d_x=n^{-1}$.
These are conditional sensor specifications, not laboratory readings.
The exact rational general-phase budgets are

$$
\begin{aligned}
E&=29/40960,&\Delta&=1027/41943040,&M&=2053/10240,\\
B&=32517135/4294967296,&E_A&=1409/5242880,&
P&=2433/4194304,\\
3B+P&=100042797/4294967296<1/40.
\end{aligned}
\tag{SC.33}
$$

**Open boundary 11.4 (what this bridge does not deliver).** The finite
table supplies strong derivative and terminal-character data for a restricted
canonical instrument. Actual sensor existence, calibration, unwrapping,
regularity certification, lawful availability and its full joint quantum
kernel remain extra premises. Programme recording through specimen failure
is a separate enlargement. A specimen-only failed run supplies an actual
partial archive and absorbing successor, not a completed waveform record.

Exact common-port acquisition and unknown record overlaps, arbitrary hidden
permission guards, a fully acquired closed selector/update boundary and
both directions of space/time/boundary/memory mutual recovery remain
unresolved. The full original class has no common $\eta,L,V,W$ or finite
effective waveform description; this volume does not replace it with the
restricted class. The native stationary $\alpha/\beta$ rate/cofinality task,
the separate fixed-Hamiltonian quantum minimax task, AURIC C114 mixed-state
source and twisted-ground lattice representation have no supplied
source/action/observation/resource correspondence to these estimates.
Finite-horizon numerical prediction is neither a forever finite-state
predictor nor physical construction, new Lean evidence or completion of the
continuing programme.

## 追加锚（本行以下为增补区）
