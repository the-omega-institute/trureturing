# Recursive relational observation: acquisition of original-control records

This volume gives an acquisition boundary for an unknown actual control of the
positive five-mode source. Finite control samples can hide a transported area,
even when aggregate resource totals agree. Specified rate bounds permit
quantitative approximation. A separately supplied, calibrated acquisition
interface permits a finite-precision area and signed-winding certificate.
These are ordinary mathematical results with explicit proofs, not kernel
certification, a constructed sensor, or completion of mutual recovery.

The mathematical notation uses GitHub dollar-delimited formulas. This is a
`generic-v1` reference volume. Its merged text is append-only; additions and
corrections belong after its append anchor and preserve existing source bytes.

## 1. One source, its supplied transport, and its complete declared response

**Definition 1.1 (original source).** Use mode order $(0,1,2,3,13)$, with Lean
index $4$ denoting mode $13$. For $b=(X,Y,Z)$ put $r=1-Z$ and

$$
\begin{aligned}
\operatorname{ValidBase}(b)&\iff 0<Z<1,\quad 0<X<r,\quad 0<Y<r,\\
J(b)&=(\max(0,X+Y-r),\min(X,Y)),\\
p(b,k)&=(r-X-Y+k,X-k,Z,Y-k,k),\\
d&=(1,-1,0,-1,1),\\
I_b(k)&=p_0^{-1}+p_1^{-1}+p_3^{-1}+p_{13}^{-1},\qquad
w_i(k)=\frac{d_i}{p_i(b,k)I_b(k)}.
\end{aligned}
$$

An original control has a finite duration $T\geq0$, continuous real controls
$k,\chi$ on $[0,T]$, $k(t)\in J(b)$, finite total variation of $\chi$, and
either absolute continuity of both controls or a finite piecewise $C^1$
partition with continuous derivative rates on its closed pieces. This is the
`OriginalControl` definition of the committed supplier. A based loop also has
$k(0)=k(T)=k_0$ and $\chi(T)-\chi(0)=2\pi m$, $m\in\mathbb Z$.

Fix one positive preparation $p(b,k_0)$ and one real phase vector $\theta$
with $\theta_2=0$. Set $\chi_0=d^{\mathsf T}\theta$. The actual lift is

$$
v_i(t)=\theta_i+\int_0^t w_i(k(s))\chi'(s)\,ds,
\qquad h=v(T)-\theta.
\tag{1.1}
$$

The finite piecewise $C^1$ alternative also gives absolute continuity on this
compact interval: apply the fundamental theorem on each piece and telescope.
Consequently all integrals here are ordinary absolutely continuous integrals;
finite variation alone is not being substituted for that regularity. The
supplied identities $w_2=0$ and $d^{\mathsf T}w=1$ give
$v_2(t)=0$ and $d^{\mathsf T}v(t)=\chi(t)$. The state convention is
$\psi_i(t)=\sqrt{p_i(b,k(t))}\exp(-iv_i(t))$.

**Convention 1.2 (double-wall specialization and credited identities).** The
acquisition theorems use the specific source class

$$
X=Y=r/2,\quad 0<Z<1,\quad 0<k_0<r/2,
\qquad e_+=(1,0,0,0,1),\quad b_0=(1,1,0,1,1).
$$

Thus $J(b)=(0,r/2)$ and

$$
p(k)=(k,r/2-k,Z,r/2-k,k),\qquad
w(k)=\tfrac12e_+-\frac{k}{r}b_0.
\tag{1.2}
$$

For every original based loop, including every signed integer winding,

$$
A(H)=\int_0^T k(t)\chi'(t)\,dt,\qquad
h(H)=\pi m e_+-\frac{A(H)}r b_0,\qquad
\beta(H)=h_0=\pi m-A(H)/r.
\tag{1.3}
$$

Equations (1.2)--(1.3), actual rectangle synthesis, fixed-preparation lifts,
reachable character domains and the coherence decoder are credited to
`FiniteRectangleTransport` and its owning Blueprint, not new classifications
in this volume. In particular, normalizing four reciprocal probabilities
without the signs in $d$ would give the wrong law.

**Definition 1.3 (complete fixed-base coherence response).** For the oriented
edge list

$$
\mathcal E=((0,1),(0,2),(0,3),(1,13),(3,13))
$$

write $a_{ij}=2\sqrt{p_i(k_0)p_j(k_0)}>0$ and
$\delta_{ij}=\theta_i-\theta_j$. The five complex responses, identified with
ten real responses in Euclidean norm, are

$$
C_{ij}(H)=a_{ij}\exp\bigl(i(\delta_{ij}+h_i-h_j)\bigr).
\tag{1.4}
$$

The positive sign in (1.4) follows from
$\overline\psi_i\psi_j$ and the negative sign in the state convention.
On the four bottom edges the residual character is $(-1)^m$; on edge $02$
it is $\exp(i\beta)$. In particular $a_{02}=2\sqrt{k_0Z}$.
These are ideal expectation coordinates. They are not acquired detector
outcomes, an expectation oracle, or a finite-shot discrimination claim.

**Definition 1.4 (future tests and actual legality).** A future command is a
public prescribed original based loop at this same $b,k_0$, described by its
actual real controls, duration and relative phase increment. A test is any
finite chronological sequence of these commands, with the full ten responses
queried at any declared completed prefix. The empty sequence is allowed.
Every integer winding of each command is retained. A fixed permission menu
may restrict these commands; it is fixed independently of the unknown past.
The mathematical over-menu consists of all such original loops. It is not
permission to execute, reverse, repeat, copy, reset, or prepare a source.

In this conditional action contract a command is enabled exactly when it is
in the permission menu and satisfies the original-control and endpoint
conditions. These conditions use the same source and its actual controls.
They do not inspect an unknown residual phase. The relative future $\chi$
is translated by the past terminal $\chi$; no absolute lift is erased.
The supplied `concatenate_original` keeps the entire chronological prefix,
has precisely that shifted tail, and adds every continuous scalar weighted
integral. Therefore it supplies the actual joined history, not just an
addition rule for invented endpoint labels.

For the same enabled command, its duration and any declared waveform costs
are identical for the histories compared here. Those costs concern the
additional prescribed waveform; they are not a reconstruction of past costs.
This source/action contract has no extra history-dependent guards or
execution-failure mechanism. An operational enlargement with such fields
must retain their actual values and prove their dependence separately. The
claims below do not drop executed failures or postselect a physical process.
Section 9 specifies how acquisition failures are retained.

## 2. What the sampled record contains

**Definition 2.1 (ideal finite point interface).** On an unknown actual past
of known duration $T>0$, a deterministic strategy makes at most $N$ interior
point queries. A query at $t$ returns the exact real pair $(k(t),\chi(t))$
with its timestamp. Endpoints, preparation, public parameters and explicitly
stated side information are also available. Later queries and stopping may
depend on the whole previous transcript. Retrospective queries are allowed,
so this is stronger than a causal logger. Repeated queries count toward the
budget and supply no new time.

All retained source-dependent observer state is a deterministic function of
this complete transcript and side information. A hidden clock, cache,
history pointer, waveform description, control generator state, coherence
measurement or archive entry is not an uncounted input. Unlimited
computation and exact-real storage are allowed in the lower bounds. The
interface is itself a conditional sensor promise, not supplied hardware.

Numerical lower bounds concern estimators returning values in the stated
real or complex target space on every allowed history. An abstention is
retained as a failed acquisition, not assigned an invented numerical value
or removed by conditioning on success. Such an interface may abstain, but
then it has not delivered uniform successful acquisition on this class.

An unknown actual waveform is different from a public prescribed waveform.
A valid description of the latter may permit exact integration or an
independent numerical certificate. The lower bounds quantify over unknown
histories whose only acquired dependence is Definition 2.1.

**Convention 2.2 (distinct resource promises).** The following classes are
separate. Constants established for one are not transferred to another.

| Class | Additional promise on the actual past | Access used |
| --- | --- | --- |
| Fixed variation | Fixed total variations, without a common speed bound | Ideal finite samples |
| Two bounded speeds | $|k'|\leq v_k$, $|\chi'|\leq v_\chi$ almost everywhere | Ideal finite samples, even with exact aggregate costs |
| One rate and variation | $\operatorname{Lip}(k)\leq L$, $\operatorname{TV}(\chi)\leq V$ | Ideal finite samples |
| Certified finite precision | The preceding rate/variation promises, plus simultaneous, calibrated unwrapped samples and finite arithmetic | The explicit contract in Section 7 |

Total variation means ordinary real total variation on $[0,T]$. When used,
the added identity-metric length and quadratic energy are

$$
\mathcal L=\int_0^T\sqrt{k'(t)^2+\chi'(t)^2}\,dt,
\qquad
\mathcal Q=\int_0^T(k'(t)^2+\chi'(t)^2)\,dt.
\tag{2.1}
$$

These are defined mathematical costs in chosen units. The source law does
not identify $\mathcal Q$ with physical energy. Sample count, elapsed time,
variation, these costs, acquired bits and arithmetic work are different
resources.

## 3. Actual rectangles hidden from finite acquired records

**Lemma 3.1 (one pulse, including its real lift).** Fix $\delta,a>0$ with
$k_0+\delta<r/2$. In an open interval of length $\ell>0$, traverse the four
affine legs

$$
(k_0,\chi_0)\longrightarrow(k_0+\delta,\chi_0)
\longrightarrow(k_0+\delta,\chi_0\pm a)
\longrightarrow(k_0,\chi_0\pm a)
\longrightarrow(k_0,\chi_0),
\tag{3.1}
$$

using four equal positive leg durations, and idle outside. This is a strictly
positive, zero-real-winding original history. Its signed area, residual and
variations are

$$
A_\pm=\pm a\delta,\quad
h_\pm=\mp S b_0,\quad S=a\delta/r,\quad
\operatorname{TV}(k)=2\delta,\quad
\operatorname{TV}(\chi)=2a.
\tag{3.2}
$$

Both orientations have $\mathcal L=2(\delta+a)$ and
$\mathcal Q=8(\delta^2+a^2)/\ell$.

Proof. The entire height interval is compactly inside $J(b)$; all five
probabilities are strictly positive. Finitely many affine legs with constant
extensions meet continuously, are absolutely continuous and have finite
phase variation. On the two height legs $\chi'=0$, so the lift is constant.
On a phase leg $k$ is constant, so (1.1) is affine and obeys the actual law.
The two phase-leg integrals are $\pm a(k_0+\delta)$ and $\mp ak_0$.
Their sum is (3.2), with exactly zero total real phase increment. Each moving
coordinate travels out and back; this gives the variations and length.
Each height leg contributes $\delta^2/(\ell/4)$ to quadratic energy and
each phase leg contributes $a^2/(\ell/4)$. The argument also proves directly
that affine time compression preserves area and variation. No unstated
time-reparameterization theorem or control permission is required. $\square$

**Theorem 3.2 (finite deterministic indistinguishability and fixed-variation
floor).** Fix $T>0$, $\delta,a>0$ as in Lemma 3.1, and
$0<S=a\delta/r\leq\pi/4$. For every deterministic strategy with any finite
budget $N$, there are two fixed actual histories of duration $T$ having
identical complete sampled transcripts, endpoints, preparations and the
exact variation totals in (3.2). Their complete ten-response vectors after
every common permitted prescribed future sequence have separation

$$
4\sqrt{k_0Z}\sin S.
\tag{3.3}
$$

Every transcript-only numerical predictor therefore has worst-case response
error at least $2\sqrt{k_0Z}\sin S$, independently of $N$. The same claim
holds for any $0<S\leq\pi/2$ if that larger parameter range is chosen.

Proof. Follow the strategy's constant-value replies $(k_0,\chi_0)$, with
the declared variation side information. Its finite set of distinct query
times leaves an open interval. Insert the two pulses (3.1) there. Both are
fixed functions after the strategy is specified; neither changes while it
is being queried. Induction over the adaptive queries gives the same replies,
times and stopping decision for both histories. Every finite prefix of this
constant-value transcript is realizable by such a pulse, so the use of
nonzero variation side information does not rely on an invalid oracle input.

All four bottom characters agree. The $02$ characters are
$\exp(i(\delta_{02}-S))$ and $\exp(i(\delta_{02}+S))$, so their chord has
length $2\sin S$. Multiplication by $a_{02}$ proves (3.3). Composition with
any common prescribed future loop adds the same actual residual to both
histories. Its edge characters are unit rotations, preserving that distance;
induction handles every finite sequence and every queried prefix. Legality
and additional costs coincide by Definition 1.4. The triangle inequality
gives half the separation for any common estimate. $\square$

The witnesses each have finite speed and finite $\mathcal Q$. As the hidden
interval shrinks their required speeds and quadratic energies grow. Theorem
3.2 asserts no common bound on these quantities. Equal fixed variation and
length cannot be silently strengthened to uniformly bounded energy.

**Example 3.3 (a fixed-visibility rational source).** Take

$$
b=(2/5,2/5,1/5),\quad r=4/5,\quad k_0=1/10,
\quad k\in[1/10,1/5].
\tag{3.4}
$$

At the two heights the probabilities and weights are

$$
\begin{aligned}
p(1/10)&=(1,3,2,3,1)/10,
&w(1/10)&=(3,-1,0,-1,3)/8,\\
p(1/5)&=(1,1,1,1,1)/5,
&w(1/5)&=(1,-1,0,-1,1)/4.
\end{aligned}
$$

Every probability throughout the band is at least $1/10$. A pulse with
$\delta=1/10$ and signed phase height $-8\pi$ has
$A=-4\pi/5$, $h=\pi b_0$, $\operatorname{TV}(\chi)=16\pi$ and
$\operatorname{TV}(k)=1/5$. Against the constant history its normalized
$02$ character is an antipode. Thus on the variation-upper-bound class
$\operatorname{TV}(\chi)\leq16\pi$ every finite deterministic sampler
has worst-case normalized-character error at least one, or unnormalized
response error at least $a_{02}=\sqrt2/5$. Constant and pulse do not have
equal variation totals; this example uses upper bounds, whereas Theorem
3.2 uses equal totals.

The same antipodal conclusion covers a strategy with no uniform query cap
that terminates on the constant history: its particular constant-history
query set is finite, and the pulse fits in a gap of that set. No termination
claim on an unrealizable constant transcript is used for this extension.

## 4. Source-independent random seeds

**Theorem 4.1 (bounded random query budget).** Fix the pulse parameters of
Lemma 3.1 with $0<S\leq\pi/2$. Let a measurable randomized strategy use at
most $q$ point queries, with its seed independent of the unknown source
history. It may know the exact fixed variations $2\delta,2a$. For every
integer $M>q$, two fixed histories can be selected before the seed is drawn
so that the transcript laws, even including the seed and all retained state,
have total variation distance at most $q/M$. Every character estimator has
maximum expected absolute error on these two histories at least

$$
\sin S\,(1-q/M).
\tag{4.1}
$$

For complete responses multiply (4.1) by $a_{02}$. The conclusion is
unchanged at any common prescribed future test of Definition 1.4.

Proof. Choose $M$ pairwise disjoint open candidate intervals inside $(0,T)$.
Run the strategy with constant-value replies and the fixed side information.
For each seed at most $q$ intervals contain a queried time. If $P_j$ is the
probability of hitting interval $j$, then $\sum_jP_j\leq q$. Select an
interval with $P_j\leq q/M$ using this distribution, not the realized seed.
Put the plus and minus pulses in that interval. For each seed that does not
hit it on the constant-reply run, induction gives exactly the same complete
run on both fixed sources. The same-seed coupling thus has probability at
least $1-q/M$ of identical transcripts. Its disagreement probability bounds
their total variation distance.

On the no-hit event the two estimates are the same, while their targets
have distance $2\sin S$. Their two absolute losses sum to at least that
distance. Integrating over this common event shows that the two risks sum
to at least $2\sin S(1-q/M)$; one is at least (4.1). Future rotation preserves
the target distance. The selection rule chose the source before the seed,
and did not assume independence of any model or repository priors. $\square$

**Corollary 4.2 (exact randomized minimax floor on a specified class).** In
the source (3.4), fix $\delta=1/10$, $a=4\pi$ and hence $S=\pi/2$.
On the zero-winding class with exactly
$\operatorname{TV}(k)=1/5$, $\operatorname{TV}(\chi)=8\pi$, and no common
speed bound, the normalized-character minimax expected absolute error is
one for every finite uniform query budget. Indeed, for each $M$ Theorem
4.1 gives risk at least $1-q/M$, so the supremum over fixed histories is
at least one. The constant estimator zero gives the matching upper bound.
This is a supremum statement; it need not be attained by one pair of
histories for all seeds. It is not a randomized $1/N$ theorem for a bounded
speed class, and it does not cover source-dependent seeds or fresh
source-dependent side inputs.

## 5. Equal aggregate totals under two common speed bounds

**Theorem 5.1 (resource-matched adaptive lower bound).** Fix $v_k,v_\chi,T>0$
with

$$
k_0+v_kT/4<r/2,\qquad
C=\frac{v_kv_\chi T^2}{16r}\leq\pi/4.
\tag{5.1}
$$

Consider zero-winding original based loops with
$|k'|\leq v_k$, $|\chi'|\leq v_\chi$ almost everywhere. For every
deterministic strategy using at most $N$ interior samples there are two
actual histories with the same complete transcript and exactly the same
resource tuple

$$
\begin{aligned}
\operatorname{TV}(k)&=v_kT/2,&
\operatorname{TV}(\chi)&=v_\chi T/2,\\
\mathcal L&=(v_k+v_\chi)T/2,&
\mathcal Q&=(v_k^2+v_\chi^2)T/2.
\end{aligned}
\tag{5.2}
$$

Even if (5.2) is supplied exactly before sampling, every numerical
predictor has worst-case complete-response error at least

$$
2\sqrt{k_0Z}\sin\!\left(\frac{C}{N+1}\right)
\tag{5.3}
$$

at every common prescribed future test.

Proof. Follow constant-value sample replies, supplying the tuple (5.2).
Sort the distinct query times and adjoin $0,T$. The positive gaps have
lengths $\ell_1,\ldots,\ell_J$, with $J\leq N+1$ and sum $T$. In gap $j$
use Lemma 3.1 with four equal leg times and

$$
\delta_j=v_k\ell_j/4,\qquad a_j=v_\chi\ell_j/4.
$$

Use the same orientation in all gaps. The controls return to the baseline
at every queried time, so both fixed histories give the prescribed adaptive
transcript. On height legs the slope magnitude is exactly $v_k$ and the
phase slope is zero; on phase legs it is exactly $v_\chi$ and the height
slope is zero. Condition (5.1) keeps every height strictly inside the
positive fiber. Summing the actual leg variations, lengths and quadratic
energies gives (5.2), independent of the gaps and orientation. The same
construction on every finite query prefix justifies the side-information
transcript, including its stopping rule.

The signed areas and residuals are

$$
A_\pm=\pm\frac{v_kv_\chi}{16}\sum_j\ell_j^2,
\qquad h_\pm=\mp S b_0,\qquad
S=\frac{v_kv_\chi}{16r}\sum_j\ell_j^2.
$$

Cauchy--Schwarz gives $\sum_j\ell_j^2\geq T^2/J\geq T^2/(N+1)$;
positivity and $\sum_j\ell_j=T$ give $\sum_j\ell_j^2\leq T^2$.
Thus $C/(N+1)\leq S\leq C\leq\pi/4$. Theorem 3.2's chord argument and
monotonicity of sine on this interval give (5.3), including the whole future
family and common legality. $\square$

**Theorem 5.2 (matching deterministic upper order).** On the same two-speed
class, let $n=N+1$, $t_j=jT/n$, and use the $N$ interior samples and known
endpoints. Then

$$
\widehat A=\sum_{j=0}^{n-1}k(t_j)(\chi(t_{j+1})-\chi(t_j)),\qquad
|A-\widehat A|\leq\frac{v_kv_\chi T^2}{2n}.
\tag{5.4}
$$

The decoder with $\widehat h=-(\widehat A/r)b_0$ has complete-response
error at most

$$
\frac{\sqrt{k_0Z}\,v_kv_\chi T^2}{rn},
\tag{5.5}
$$

uniformly after every common exact prescribed future sequence. For fixed
positive parameters satisfying (5.1), the deterministic point-query
minimax order is $\Theta(1/(N+1))$; constants are not asserted sharp.

Proof. The error on one cell of length $\ell=T/n$ is
$\int_{t_j}^{t_{j+1}}(k(t)-k(t_j))\chi'(t)\,dt$. Its absolute value is at
most $v_kv_\chi\ell^2/2$. Summing proves (5.4). Only the $02$ pair varies
when winding is zero. Use
$|\exp(ix)-\exp(iy)|\leq|x-y|$ and $a_{02}=2\sqrt{k_0Z}$ to get (5.5).
The common exact future action is an isometry on each edge pair. Finally
$\sin x\geq2x/\pi$ on $[0,\pi/2]$ makes (5.3) a positive constant times
$1/n$. This is classical quadrature and indistinguishability reasoning
applied to these actual histories; it is not a new quadrature principle.
$\square$

## 6. A distinct one-rate, bounded-variation class

**Theorem 6.1 (a rate/variation comparison without a phase-speed cap).** On
the fixed source (3.4), assume $\operatorname{Lip}(k)\leq L$,
$\operatorname{TV}(\chi)\leq V$, with $L,V,T>0$, and restrict to
zero-winding based loops in the same band. For at most $q$ interior ideal
samples, put

$$
s=1/10,\qquad
b_q=\min\left(\pi,\frac{V}{2r}
                 \min\left(s,\frac{LT}{8(q+1)}\right)\right).
\tag{6.1}
$$

Every deterministic strategy has worst-case normalized $02$ character
error at least $\sin(b_q/2)$. Conversely, $n$ equal time cells and their
$n+1$ samples give character error at most

$$
\min\left(2,\frac{LVT}{rn}\right).
\tag{6.2}
$$

The resulting deterministic asymptotic order is again $1/n$, but these
constants and promises differ from Section 5.

Proof. The constant-history run leaves a gap $\Delta\geq T/(q+1)$.
Place a pulse of total duration $\Delta/2$ strictly inside it. Its four leg
durations are $\Delta/8$. Choose

$$
\delta=\min(s,L\Delta/8),\qquad
a=\min(V/2,\pi r/\delta)
$$

and use the negative orientation. The height speed is $8\delta/\Delta\leq L$,
and its phase variation is $2a\leq V$. Its residual is
$\beta=a\delta/r=\min(V\delta/(2r),\pi)\in[b_q,\pi]$.
The constant history and this actual pulse give the same transcript. Their
character distance is $2\sin(\beta/2)$, proving the lower bound. This
comparison uses variation upper bounds, not equal exact totals.

For the upper bound the same left sum as (5.4) satisfies
$|A-\widehat A|\leq L(T/n)\int_0^T|\chi'|\leq LTV/n$.
For sufficiently large $q$, (6.1) is $VLT/(16r(q+1))$; elementary sine
bounds and (6.2) give the stated order. No bound on $\chi'$ was used in
this upper proof. $\square$

## 7. A conditional finite-precision area and signed-winding certificate

**Definition 7.1 (actual acquisition promise).** Use the exact source (3.4),
an original based loop, $\operatorname{Lip}(k)\leq L$ and
$\operatorname{TV}(\chi)\leq V$. Every signed winding compatible with
these promises is included. A separate acquisition service must provide
the following for the same executed history:

1. Ordered actual sample times $0=s_0<\cdots<s_n=T$, with simultaneous
   height and phase samples at each time. For nominal grid $t_j=jT/n$,
   a calibrated clock certifies $|s_j-t_j|\leq\varepsilon_t$ and the endpoint
   samples really are the initial and terminal events. Hence every actual
   cell is at most $h_*=T/n+2\varepsilon_t$ long.
2. Samples $\widehat k_j$ and $\widehat x_j$ of
   $k(s_j)$ and $x(s_j)=\chi(s_j)-\chi_0$, with simultaneous deterministic
   bounds $|\widehat k_j-k(s_j)|\leq d_k$ and
   $|\widehat x_j-x(s_j)|\leq d_c$. Height samples are clipped to the known
   band $[1/10,1/5]$. They can also be quantized there with the quantization
   error included in $d_k$. Real phase-lift samples, not circle samples,
   are required. Centering at $\chi_0$ does not discard a winding.
3. Source/preparation identity, units, initial lift/reference alignment,
   clock and sensor calibration, justification of $L,V$, permission fields,
   timestamps, ordered samples and all acquisition events belong to the
   actual record. The service must justify nondisturbance, or justify that
   the measured actual control and its lift still obey (1.1).

This promise includes access to the unwrapped phase and is stronger than
finite-shot quantum readout. Neither this service nor its calibration,
clock, phase reference, record copying or storage is supplied by the
transport or composition declarations. A statistical implementation may
instead certify these inequalities on one declared joint event of
probability at least $1-\alpha$; all conclusions then hold on that event.
Separate marginal confidence claims cannot replace the joint event.

**Theorem 7.2 (area certificate).** Under Definition 7.1, let
$K_{\max}=1/5$ and compute

$$
\widetilde A=\sum_{j=0}^{n-1}\widehat k_j
                     (\widehat x_{j+1}-\widehat x_j)
\tag{7.1}
$$

with an additional certified absolute arithmetic error at most $\rho_A$.
Then $|\widetilde A-A|\leq E_A$, where

$$
E_A=(Lh_*+d_k)V
  +d_c\bigl(2K_{\max}+LT+2(n-1)d_k\bigr)+\rho_A.
\tag{7.2}
$$

Proof. First compare $A$ with
$\sum_j\widehat k_j(x(s_{j+1})-x(s_j))$. On cell $j$ the height discrepancy
is at most $Lh_*+d_k$. Integration against $|\chi'|$ gives the first term.
Put $e_j=\widehat x_j-x(s_j)$. The remaining sensor contribution has the
exact summation-by-parts identity

$$
\sum_{j=0}^{n-1}\widehat k_j(e_{j+1}-e_j)
=\widehat k_{n-1}e_n-\widehat k_0e_0
 +\sum_{j=1}^{n-1}(\widehat k_{j-1}-\widehat k_j)e_j.
\tag{7.3}
$$

Its modulus is bounded by $d_c$ times the sum of the two endpoint height
magnitudes and the sampled height variation. Clipping bounds the first two
by $2K_{\max}$. The actual sampled height variation is at most $LT$;
the $n-1$ internal differences introduce at most $2(n-1)d_k$. Add the
arithmetic error. This proves (7.2) without a phase-speed bound. $\square$

**Theorem 7.3 (signed winding with finite arithmetic).** The original loop
promise is essential. With exact $\pi$, if $d_c<\pi/2$, nearest-integer
rounding of $(\widehat x_n-\widehat x_0)/(2\pi)$ gives the exact signed
integer $m$. For a finite implementation, let $M$ be a certified integer
upper bound for $V/6$, so $|m|\leq M$ because $\pi>3$. Let a rational
$\widetilde\pi$ satisfy $|\widetilde\pi-\pi|\leq\varepsilon_\pi$ and put

$$
R=2d_c+2M\varepsilon_\pi<\widetilde\pi.
\tag{7.4}
$$

Then the nearest integer to
$(\widehat x_n-\widehat x_0)/(2\widetilde\pi)$ is exactly $m$, and this
can be checked using rational arithmetic. All negative, zero and positive
integers in $[-M,M]$ are treated alike.

Proof. The measured endpoint difference differs from $2\pi m$ by at most
$2d_c$, and from $2\widetilde\pi m$ by at most $R$. The centers
$2\widetilde\pi j$ of different integer candidates are spaced
$2\widetilde\pi$ apart. Condition (7.4) puts the measured difference
strictly inside the true center's nearest-integer cell, excluding ties and
other integers. The exact-$\pi$ case is the same argument with radius
$2d_c<\pi$. $\square$

If the promised integer loop is not known, these data give an interval for
the real endpoint increment, not a proof that it is an integer multiple of
$2\pi$. Likewise, a band or variation promise cannot supply an unwrapping
sensor. A fixed $V$ excludes windings with $2\pi|m|>V$; the union of the
certificates over finite $V$ retains every signed winding, without asserting
arbitrarily large winding in one fixed resource class.

**Corollary 7.4 (complete response and calibration budget).** Recover $m$ by
Theorem 7.3 and form

$$
\widetilde\beta=\widetilde\pi m-\widetilde A/r,
\qquad \widetilde\epsilon=(-1)^m,\qquad
B_0=E_A/r+M\varepsilon_\pi+\rho_\beta,
\tag{7.5}
$$

where $\rho_\beta$ bounds additional phase arithmetic error. With the exact
supplied decoder the full ten-response error is at most

$$
a_{02}\min(2,B_0).
\tag{7.6}
$$

For a calibrated decoder let $G_e=a_e\exp(i\delta_e)$ and suppose the
stored calibration obeys $|\widehat G_e-G_e|\leq\gamma_e$ simultaneously.
With certified output-evaluation error $\rho_C$ in Euclidean norm, the bound
becomes

$$
\|\gamma\|_2+a_{02}\min(2,B_0)+\rho_C.
\tag{7.7}
$$

Proof. Formula (1.3) gives phase error at most $B_0$ on $02$ and exact
parity on all bottom edges. The unit-circle chord bound proves (7.6).
For each calibrated complex gain, insert $G_e$ times the predicted unit
character; its gain error is at most $\gamma_e$. Minkowski's inequality
and the additional output budget give (7.7). For example certified
$|\widehat a_e-a_e|\leq\eta_{a,e}$ and
$|\widehat\delta_e-\delta_e|\leq\eta_{\delta,e}$ permit
$\gamma_e=\eta_{a,e}+a_e\min(2,\eta_{\delta,e})$. $\square$

Clock error appears in $h_*$, sensor gain/bias/drift and digitization must
appear in $d_k,d_c$, and preparation/reference calibration appears in
$\gamma$. These are different budgets. In particular, a small timestamp
error between a height reading and a phase reading cannot be converted to
a small phase error using only total variation: a compressed phase pulse
can fit between those readings. Asynchronous acquisition needs an added
phase modulus or an independently justified simultaneous-error certificate.
Uncertified departures from the exact symmetric source law, or unknown
environmental overlap, are not covered by (7.2) or (7.7).

## 8. Finite storage and executable arithmetic obligations

**Proposition 8.1 (one sufficient finite allocation).** Let $u>0$ be an area
error budget. For positive $L,V,T$, one sufficient choice in Theorem 7.2 is

$$
\begin{aligned}
n&\geq\max(1,4LTV/u),\\
\varepsilon_t&\leq\min\left(T/(4n),\frac{u}{16\max(LV,1)}\right),\\
d_k&\leq\min\left(\frac1{2n},\frac{u}{8\max(V,1)}\right),\\
d_c&\leq\min\left(\frac18,
             \frac{u}{8(2K_{\max}+LT+1)}\right),\qquad
\rho_A\leq u/8.
\end{aligned}
\tag{8.1}
$$

These choices give $E_A\leq3u/4\leq u$. If
$\widetilde\pi\geq3$ and
$\varepsilon_\pi\leq1/(8\max(M,1))$, they also imply (7.4).

Proof. The five contributions $LTV/n$, $2L\varepsilon_tV$, $d_kV$,
the phase-sensor term and $\rho_A$ are bounded respectively by
$u/4,u/8,u/8,u/8,u/8$. Here
$2(n-1)d_k\leq1$. Also $2d_c+2M\varepsilon_\pi\leq1/2<3$.
These are sufficient allocations, not optimal constants. $\square$

**Definition 8.2 (charged digital realization of the certificate).** A finite
implementation requires finite descriptions of public parameters and
calibration bounds. For the rational source (3.4), one sufficient setting
has a rationally specified duration $T$, rational upper bounds for $L,V$
and errors, a rational grid controller, and certified interval algorithms
for $\pi$, square roots and trigonometric evaluation. A nonrational duration
instead needs an effective clock/mesh certificate sufficient for (7.2).
An arbitrary exact real parameter is not a free finite-bit input.

For example choose integers $D_k,D_c$ with $10\mid D_k$. Store height
values on the grid $j/D_k$ in $[1/10,1/5]$ and centered lift values on a
rational grid of step $1/D_c$ in $[-V_*,V_*]$, where
$V_*=\lceil VD_c\rceil/D_c$. Both grid endpoints are encoded grid values
and $[-V,V]\subseteq[-V_*,V_*]$. Clipping to the respective grid interval
is nonexpansive relative to the true value. Rounding contributes at most
half a grid step; add these contributions to the actual sensor errors to
obtain $d_k,d_c$. The required value widths can be bounded by

$$
b_k=\left\lceil\log_2(\lceil D_k/10\rceil+2)\right\rceil,
\qquad
b_c=\left\lceil\log_2(\lceil2VD_c\rceil+3)\right\rceil.
\tag{8.2}
$$

A stored row also charges its encoded timestamp, status and event fields.
Writing their widths as $b_t,b_e$, keeping the whole acquired record uses
at most

$$
(n+1)(b_k+b_c+b_t+b_e)+B_{\rm meta}+B_{\rm failure}
\tag{8.3}
$$

bits for the declared bounded encodings, in addition to numerical workspace
and programme storage. $B_{\rm meta}$ includes source, preparation,
reference, units, permissions, grid/controller description and calibration
certificates. $B_{\rm failure}$ charges all additional retained failure
payloads; it is not silently set to zero for a failed attempt. Grid indices
may encode nominal timestamps together with the certified actual-time
uncertainty. An actual measured timestamp, when supplied, is separately
encoded and paid for. No minimum-storage claim is made.

On these rational grids, (7.1) can be accumulated exactly with common
denominator $D_kD_c$, so $\rho_A=0$ is possible for the arithmetic part.
If $V$ is a grid endpoint, the signed numerator magnitude is at most
$2nD_kD_cK_{\max}V$; otherwise replace $V$ here by $V+1/D_c$.
Thus one sign bit plus
$\lceil\log_2(1+2nD_kD_cK_{\max}(V+1/D_c))\rceil$ bits suffices for that
accumulator. There are $n$ multiplications and a linear number of
subtractions/additions, at these charged widths. If a different fixed
precision arithmetic is used, its proved roundoff bound is $\rho_A$.
Winding rounding, evaluation of (7.5) and the decoder each have their
own certified arithmetic budgets. Sensor-pair count is $n+1$; it is not
a shot count, a wall-clock cost, or the price of validating $L,V$.

## 9. Retained failure records and later-loop errors

**Definition 9.1 (certificate result, without discarded failures).** An
acquisition attempt returns either a certified record meeting Section 7 or
an executed-failure record containing its reason, actual partial samples,
timestamps, calibration flags and any declared successor/stop state.
Missing permission or an illegal request is a distinct unexecuted rejection.
A failed sensor, missing lift calibration, violated rate/variation promise,
unknown source identity, ambiguous winding test, overflow or exhausted
error budget cannot yield a certified answer by omitting the failed data.
Its result is retained as inconclusive for the claimed precision. Further
attempts, if authorized, have their own acquisition and storage costs.

The deterministic sensor inequalities are promises, not tests that can in
general be proved solely from the same noisy data. Unflagged violation of
such a promise lies outside the certificate theorem; no failure detector
for all model violations has been constructed. With a joint statistical
certificate the complementary event of probability at most $\alpha$
remains an explicit failure exposure. These distinctions retain the
illegal/success/executed-failure separation of Process Geometry §34.

**Theorem 9.2 (same-source continuation and cumulative error).** Suppose a
certified past record has phase budget $B_0$ and exact parity as in (7.5).
For every finite common permitted future sequence whose actual residual
increments and signed windings are known exactly, the full family of
responses at all completed prefixes satisfies the same bounds (7.6)--(7.7).
Enabledness, declared additional durations and waveform costs agree
exactly with the actual same-source action of Definition 1.4.

If instead future increment $j$ has a certified $02$ phase error $e_j$, its
signed winding/parity is certified exactly, and its update arithmetic adds
phase error at most $r_j$, then at prefix $J$ replace $B_0$ by

$$
B_J=B_0+\sum_{j=1}^J(e_j+r_j).
\tag{9.1}
$$

Use that prefix's certified decoder calibration and output budgets in
(7.7). If a future control is unknown, it requires its own acquisition
certificate; calling its increment an input does not acquire it.

Proof. Apply `concatenate_original` successively to the actual past and
prescribed actual controls. It preserves the original prefix and adds their
real residuals and signed windings. Hence exact common updates preserve the
initial $02$ phase difference and bottom parity. For approximate updates,
the triangle inequality on the real phase errors gives (9.1); exact integer
addition preserves parity for negative and positive windings alike.
The edge-circle chord bound gives the response estimate at each prefix.
Legality follows from the common fixed endpoint, actual control conditions
and matched permissions, rather than an inference from noisy phase values.
$\square$

For example an output budget can assign $E_A/r\leq\eta/4$,
$M\varepsilon_\pi+\rho_\beta\leq\eta/4$,
$\sum_{j\leq J}(e_j+r_j)\leq\eta/2$, and
$\|\gamma\|_2+\rho_C\leq\zeta$. The resulting complete-response error is
at most $a_{02}\eta+\zeta$. Every resource in this allocation is conditional
on a certificate for the same actual history and future controls.

Exact future rotations are mathematical resources. An indefinitely long
sequence with positive per-step error does not have a summable budget by
default. Fixed finite bits also do not implement exact rotation forever.
Transport--Memory Completion §2.8 already gives the eventual-periodicity
obstruction for a closed finite-state predictor of an infinite-order
rotation. The present stable-initial-error estimate does not evade it.
No integer winding is replaced by parity in the retained actual lift or
control record; parity is only the bottom-edge prediction coordinate.

## 10. Exact finite arithmetic certificates

**Example 10.1 (speed and resource arithmetic).** Use $r=4/5$, $Z=1/5$,
$k_0=1/5$, $v_k=1/5$, $v_\chi=2$, $T=1$. This preparation differs from
(3.4); it is an instance of Section 5, not its finite-precision band.
For query gaps determined by $0,1/7,3/5,1$, the actual four-leg construction
gives

$$
\begin{aligned}
A_\pm&=\pm477/49000,&
h_\pm&=\mp(477/39200)b_0,\\
\operatorname{TV}(k)&=1/10,&
\operatorname{TV}(\chi)&=1,\\
\mathcal L&=11/10,&\mathcal Q&=101/50.
\end{aligned}
$$

All heights lie strictly between $0$ and $2/5$. These fractions follow by
summing $v_kv_\chi\ell_j^2/16$ and the leg costs in Lemma 3.1.

**Example 10.2 (a finite-precision budget including timing).** In source
(3.4), set $L=1/5$, $V=20$, $T=1$, $n=512$ and

$$
d_k=2^{-18},\quad d_c=\varepsilon_t=\rho_A=2^{-20},\quad
\varepsilon_\pi=2^{-24},\quad M=4,\quad\rho_\beta=0.
$$

Then the rational expressions in (7.2) and (7.5) are

$$
E_A=\frac{5427431931}{687194767360},\qquad
B_0=\frac{5427563003}{549755813888}<\frac1{64}.
$$

For any certified $\widetilde\pi\geq3$ with this approximation error,
$2d_c+2M\varepsilon_\pi<3$ proves (7.4). Every signed winding actually
consistent with $V=20$ is therefore recovered exactly; the candidate list
includes both signs and zero, and candidates excluded by the promise are
not declared realizable. With exact decoder calibration the response error
is at most $(\sqrt2/5)/64$. Additional decoder or future-loop errors use
(7.7) and (9.1), without being absorbed into this number.

Bounded exact in-memory rational checks verify the weight identities at
$k=1/10,1/5,3/20,7/25$, Example 10.1, Example 10.2 and (7.3) on 360
finite error-sign cases with $1\leq n\leq4$. These checks verify the
displayed finite arithmetic. The universal statements rest on their
ordinary proofs. No experiment files or computational certification are
needed for these examples.

Rational alternating-series bounds in Machin's identity
$\pi=16\arctan(1/5)-4\arctan(1/239)$ also certify the stated precision
of the rational value $3141592653589793/10^{15}$. The winding-cell inclusion
is checked for all 65 signed integers in $[-32,32]$ with
$d_c=2^{-12}$ and $\varepsilon_\pi=2^{-24}$. Finite rational checks of
(8.1) cover 81 positive parameter allocations; 60 rational lift-grid cases
check the value-count bound in (8.2). These are bounded certificate examples,
not substitutes for the all-parameter proofs.

## 11. What is recovered, and which boundary remains

**Proposition 11.1 (preserving signed sectors without a false fixed-budget
claim).** Let an original common prefix end at $k_0$ with signed winding
$m$. Follow it by either zero-winding pulse or either resource-matched
history above, translating its initial real phase as in the composition
supplier. The prefix is identical, the total winding remains exactly $m$,
and the two suffix-induced future coherence separations remain those
proved above. Thus the obstruction is not caused by deleting nonzero or
negative sectors. This construction uses the concatenated duration and
resources; it does not assert arbitrary $|m|$ at fixed $T$, fixed phase
speed or fixed $V$.

Proof. Composition preserves the full prefix and its lift, adds the zero
real increment of the suffix, and adds its signed area residual. The
common prefix only rotates the differing $02$ pair. $\square$

Both witness histories have the same positive endpoint probability support,
the same supplied preparation, the same elapsed duration and the same
declared reference and permissions. Their sampled records coincide while
their area and future coherence responses differ. On Section 5's witnesses
even the stated past resource totals coincide. Thus finite record equality
fails the record-to-response implication on this actual joint domain;
no new generic quotient or kernel theorem is needed to establish that fact.

The positive certificate recovers signed winding under the integer-loop
promise and approximates an area-derived endpoint phase. Its complete
response bound covers the declared fixed-base future menu, including the
actual legality relation specified for that same source. It does not recover
the continuous chronological waveform, the order of all past events, a
spatial embedding/metric, or past elapsed time from an endpoint. Duration
here comes from an independently charged clock contract. The actual record
and calibration remain in memory; their numerical response summary is not
a replacement for the archive.

Transport--Memory Completion §§2.9--2.12 and 2.18 additionally require a
same-source coherent common-port experiment, aligned times and records,
known nonzero amplitudes, known nonzero record overlap and actual acquired
readings. Control quadrature constructs none of these. If the overlap is
unknown, the measured cross term is a product with that unknown overlap;
it cannot be divided out. Process Geometry §34 and the atlas-compatible
stable core also retain actual domains, failure events, references,
permissions, selectors and update inputs. If any such field depends on
the unknown past, Definition 1.4's simpler enabledness contract no longer
applies. One must model that field in the same joint source and recheck
the complete response; the present estimate is not a full RRO minimum
memory theorem.

Remaining obligations are actual acquisition hardware or a proved
operational service with these calibration and disturbance guarantees;
the coherent common-port/reference/record-overlap interface; a lawful
joint archive and closed policy/update implementation; and both directions
of any proposed all-view recovery correspondence. Native stationary
$\alpha/\beta$ late-target cofinality and the separate QMB fixed-Hamiltonian
all-history optimum remain unresolved. Their five-dimensional terminology
provides no source, action, observation, joint-law or resource transfer.

## 12. Credited suppliers, classical principles and limits of transfer

All repository supplier links below select the public committed snapshot
`df12d01189bdf8196457773d7f9e8eda168cb3cc`. They identify the statements
used, not a new compilation or a certification of this volume.

| Supplier | Used result and retained boundary |
| --- | --- |
| [FiniteRectangleTransport Lean](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean), [owning Blueprint](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/Blueprint/D5/S3/Quantum/Fibers/FiniteRectangleTransport.md) | Exact positive source, signed weights, `finite_rectangles_realize`, `weight_compatible`, original all-sector lifts, reachable domains and full fixed-base coherence decoder. Source synthesis and these classifications remain credited suppliers. |
| [OriginalControlComposition](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/D5/S3/Quantum/Fibers/OriginalControlComposition.lean), `OriginalControl`, `concatenate_original` | Actual chronological prefix and shifted tail; real increments and every continuous scalar weighted integral add. No sensor, waveform acquisition or execution permission is inferred. |
| [Original probability/phase transport theory](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/docs/develop/theory/AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md), §§3.1, 3.12 and 4 | Original admissibility, signed winding and ideal readout convention. Public prescribed controls and unknown actual inputs remain different interfaces. |
| [Transport--Memory Completion](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §§1--2 | Future-menu minimality, inverse permissions, closed predictor, common-port acquisition and overlap conditions; these are not discharged by the certificate. |
| [Process Geometry](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §34; [atlas-compatible stable cores](https://github.com/the-omega-institute/trureturing/blob/df12d01189bdf8196457773d7f9e8eda168cb3cc/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md), §§1--3 | Actual joint source and routes, legality versus executed failure, complete records, forward closure and selector/update fields. No duplicate generic factorization theorem is offered. |

**Literature statement 12.1.** The quadrature, total-variation estimate,
finite-information indistinguishability argument, coupling inequality and
unit-circle chord bound are mature principles. The proved source-specific
content is the scheduling of actual lawful loops inside adaptive query
gaps, resource-matched instances, their full declared continued responses,
and the conditional calibrated record certificate. These are `repo-derived`
ordinary constructions. No worldwide originality claim is made.

| Primary source | Precise comparison |
| --- | --- |
| M. W. Alomari, [Two-Point Quadrature Rules for Riemann--Stieltjes Integrals with $L^p$-error estimates](https://arxiv.org/html/1901.01147v2), Theorem 1 | `literature-attested`: Hölder integrands and bounded-variation integrators provide classical quadrature estimates. Here the elementary ordinary-variation case is proved directly with $k$ as Lipschitz integrand and $\chi$ as absolutely continuous integrator. No generalized $p$-variation sharpness assertion is needed. |
| B. Hambly and T. Lyons, [Uniqueness for the Signature of a Path of Bounded Variation and the Reduced Path Group](https://arxiv.org/html/math/0507536v2) | `literature-attested`: complete signatures of bounded-variation paths determine tree-like equivalence classes. For a based loop, the first-level phase coordinate is $\Delta\chi=\chi(T)-\chi(0)=2\pi m$ with arbitrary signed $m\in\mathbb Z$, while the centered second-level coefficient is $S^{k,\chi}=\int_0^T(k-k_0)\,d\chi$. The transported area in (1.3) is the uncentered quantity $A=\int_0^T k\,d\chi=S^{k,\chi}+k_0\Delta\chi=S^{k,\chi}+2\pi m k_0$; hence $A=S^{k,\chi}$ only for $m=0$. Complete signature access is substantially stronger than finitely many point samples and does not acquire an archive. |
| C. Liu and S. Wang, [Signature inversion of $C^1$-axial linear curves](https://arxiv.org/html/2603.14904v1), Theorems 1.2 and 1.8 | The inverse uses a linear coordinate and signature coefficients of unbounded order; quantitative inverse stability also assumes derivative/Hölder control and signature precision. These are absent from the point interface. Time augmentation is not acquisition of these coefficients. |
| [Signature Reconstruction from Randomized Signatures](https://arxiv.org/html/2502.03163v1), §4 | Families over initial conditions and iterated-field independence are different access promises. The scaling step discussed below is excluded as a supplier. No reconstruction claim from this paper is used. |

**Counterevidence 12.2 (an excluded scaling identity).** In §4.1 of the
last cited version, the displayed assertion
$Y_t^{\eta,\lambda}=\lambda Y_t^{\eta/\lambda}$ is made for the equation
$dY=\lambda V(Y)\,dX$. It is false for general vector fields. For
$V(y)=y$, $X(t)=t$, the two sides are $\eta e^{\lambda t}$ and
$\eta e^t$; at $\eta=1$, $\lambda=2$, $t=1$ they are $e^2$ and $e$.
Even a bounded smooth field does not fix the general identity: for
$V(y)=\sin y$, $\eta=\pi/2$, $\lambda=2$, the derivatives at zero are
$2$ and $2\sin(\pi/4)=\sqrt2$. This is counterevidence to that displayed
proof step, not a proof that the paper's full reconstruction theorem is
false. It supplies no acquisition bridge here.

The bounded primary-source comparisons separate quadrature and signature
data from acquired control samples. They neither establish an exhaustive
literature search nor convert a different observability interface into this
one. There is no new physical law, physical realization, global recovery,
Lean certification, or completion of the continuing programme in these
ordinary results.

## 追加锚（本行以下为增补区）
