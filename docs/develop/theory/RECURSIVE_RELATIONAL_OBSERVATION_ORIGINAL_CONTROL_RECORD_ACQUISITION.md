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

## 13. An additional producer phase port and its original-source response

Sections 13–17 give a conditional acquisition interface for a binary current
height. The extra input is a producer-bound coherent port, not a recorded
height label. One actual probe read then selects a lawful original request
or its unexecuted rejection, while calibration leaves the old specimen and
all its joint records unchanged. Constructing and certifying this port from
the original producer remains unresolved. The existing original menu alone
is not asserted to provide this acquisition.

**Definition 13.1 (source and public binary promise).** Retain Definition
1.1's positive source, common preparation, real lifts and both original
regularity alternatives. Restrict to its calibrated double wall
$0<Z<1$, $r=1-Z$, $c=r/2$ and $0<k<c$. Fix public exact numbers
$0<x<y<c$. At an actual live cut of one unknown original past the current
height $K$ belongs to $\{x,y\}$. Its real phase, signed winding, waveform
and retained correlations are not observer inputs. The public catalogue
and calibrated preparation reference are extra supplied information.

Use the orthonormal preparation directions

$$
U_+=(e^{-i\theta_0}e_0+e^{-i\theta_4}e_4)/\sqrt2,\qquad
U_-=(e^{-i\theta_1}e_1+e^{-i\theta_3}e_3)/\sqrt2,\qquad
V=\operatorname{span}\{U_+,U_-,e_2\}.
\tag{RA.13}
$$

Here index $4$ denotes original mode $13$, and $\theta_2=0$.
The actual family used for the lower bound is

$$
\psi_{k,\beta,m}=\sqrt Z e_2+e^{-i\beta}
 \bigl(\sqrt{2k}U_++(-1)^m\sqrt{2(c-k)}U_-\bigr),
\qquad \beta\in\mathbb R,\quad m\in\mathbb Z.
\tag{RA.14}
$$

Its real residual is $(\beta,\beta-\pi m,0,\beta-\pi m,\beta)$.
Quantum Carrier Minimum Proposition 7.2 supplies these endpoints from one
common positive preparation: fix $a_0,q\in(0,c)$, $q\ne a_0$; use a
unit phase leg $2\pi m$ at $a_0$, a four-unit rectangle at $q$ of height

$$
B_{\beta,m}=\frac{r(\pi m-\beta)-2\pi m a_0}{q-a_0},
\tag{RA.15}
$$

then a unit zero-phase arrival at $k$. Indeed
$w(q)-w(a_0)=-(q-a_0)(1,1,0,1,1)/r$, so the two phase contributions
give exactly the displayed residual. The rectangle's real phase increment
is zero and the arrival transports no phase. All six legs are continuous
affine original controls in both regularity classes. For the two endpoint
heights their probability margin is at least
$\min\{a_0,q,x,c-a_0,c-q,c-y,Z\}>0$.
Their phase variation $2\pi|m|+2|B_{\beta,m}|$ is finite separately for
each history, with no common bound over all signed $m$ or real $\beta$.
Canonical survival is positive because the compact height bands make the
finite horizontal charges finite. These are actual live-branch witnesses;
no unsuccessful preparation is retried or erased.

**Definition 13.2 (additional joint port service).** The producer retains
its actual classical setting $K$ throughout a declared finite calibration
interval. The native branch makes a constant-height, zero-relative-phase
hold. A separate two-level probe $Q$ has a calibrated basis $|0\rangle,
|1\rangle$ and, for permitted real phase action $a$, receives

$$
R_k(a)=|0\rangle\langle0|+e^{ika/r}|1\rangle\langle1|.
\tag{RA.16}
$$

The port is bound to this same producer, source and epoch. It reads neither
an unrelated setting nor an estimated setting. Conditional on every actual
classical history $h$ with current height $k$, its full operation is
$\operatorname{id}_{SAR}\otimes\operatorname{Ad}_{R_k(a)}$ on the old
specimen $S$, archive $A$, quantum reference $R$ and the probe. All old
classical boundary fields are also retained. In particular, the coupling
does not change $k$, the old real phase lift, source identity, permissions
or controller inputs. Clock advancement and the appended calibration event
are explicit updates; old clock/archive entries are not overwritten.
The same statement holds for every conditional joint density $\rho^h_{SAR}$,
including entanglement, and every actual mixture of these histories.
The producer setting is classical here; no promise is made for a coherent
superposition of different settings.

This is a joint channel premise, stronger than a probe marginal or a claimed
nondisturbance of separate old marginals. Stable setting, source/epoch
authentication, coupling gain $1/r$, blank probe, coherent preparation,
phase reference, action calibration, clock, readout and permissions are all
additional services/resources. Port permission and hold permission must
actually be present. Calibration by this ideal service has no inconclusive
or executed-failure branch on its promised domain. A known missing
permission or known interface mismatch returns an unexecuted rejection
with its actual reason and no height certificate. Unflagged violation of
the service premise is outside the theorem; this definition supplies no
universal detector for such violations. An already stopped specimen keeps
its old first failure and absorbing successor, without a live calibration
attempt.

**Proposition 13.3 (functional correspondence, without a free route).**
The phase response (RA.16) is the restriction of the original constant-height
phase-leg unitary to $\operatorname{span}\{e_2,U_-\}$. Specifically, an
original phase increment $a$ at fixed height $k$ has $k'=0$, so its
canonical survival charge and all failure densities vanish. Its live map is

$$
U_k(a)=\operatorname{diag}_{(U_+,U_-,e_2)}
 \bigl(e^{-ia/2+ika/r},e^{ika/r},1\bigr).
\tag{RA.17}
$$

For the fixed isometry $J|0\rangle=e_2$, $J|1\rangle=U_-$ one has
$U_k(a)J=JR_k(a)$.

Proof. Insert the signed weights (1.2) into the actual negative state-phase
convention. At fixed height their integrals are $a w_i(k)$; the canonical
no-failure attenuation is one. Equal paired weights preserve $U_+,U_-$,
giving (RA.17) and the isometry identity. $\square$

This identity verifies the response function only. Executing the original
phase leg on the specimen would change its phase. Definition 13.2 instead
asks for a separate blank-probe route while the native phase is held fixed.
That route, its actual source binding and its identity action on the old
joint state are extra premises. Probe action $a$ is not an unrecorded
increment of the original relation phase $\chi$.

## 14. Sharp paid action with the full unknown original orbit present

**Definition 14.1 (the lower-bound access and cost contract).** During
calibration the only additional dependence on the unknown height is the
port of Definition 13.2. The input old specimen may be any member of
(RA.14). All other accessible assistance is one common state independent
of $k,\beta,m$, jointly, not merely in its separate marginals. Thus a
source-sensitive installed programme, readable archive, clock side channel,
receiver share, setting label or extra coupling is not an uncounted input.
Actual history-correlated spectator archives may remain untouched but
cannot be read by this lower-bound protocol. The upper protocol below
preserves arbitrary such correlations and does not require their
independence.

Allow finite-dimensional ancillas, arbitrary common known controls,
measurements, retained records and finite adaptive feedback. All outcomes
are kept. As in FIB Atom Whitebox SIC Time Acquisition §2.4, dilate
instruments with their outcome registers and environments and extend common
isometries to common unitaries with extra blanks. The access contract
requires that the outcome-retaining implementation have, between finitely
many common instantaneous operations, the Hamiltonian

$$
H_k(t)=H_0(t)-\frac{k}{r}G(t),\qquad
\mathcal A=\int_0^{T_c}\operatorname{diam}(\operatorname{spec}G(t))\,dt.
\tag{RA.18}
$$

Here $\hbar=1$, $T_c<\infty$ is a common terminal time, and $H_0,G$
are known common bounded self-adjoint operators, measurable in operator
norm with integrable norms on each piece. The common Hilbert space may
include enlarged outcome/environment registers; finite-dimensional
implementations are included. Spectral diameter means supremum minus
infimum of the bounded spectrum. The operators include routing and
coherently retained feedback registers. The paid action is the displayed
spectral diameter on this full coherent implementation. For one scalar drive
$G(t)=u(t)|1\rangle\langle1|$ it is $\int|u(t)|\,dt$ and
$a=\int u(t)\,dt$. Extra parallel couplings or coherent choices of forward
and inverse coupling must pay their full spectral width; they are not
unit-price extensions of a scalar call. The inaccessible producer label is
not included as an already distinguishable input in this discriminator.

Early decisions can be latched and padded to $T_c$ with the port off on
those branches. The action bound applies to the whole padded coherent
implementation, not its expected cost or a chosen successful branch.
The protocol must terminate with the correct label $x$ or $y$ with
probability one for every $\beta,m$ at each candidate height. A discarded,
inconclusive or failed branch does not meet this task. The lower bound even
allows disturbance of the old specimen by the common controls. Unknown
height-dependent native processors are not additional available queries
during this calibration; supplying them changes the access contract.

**Theorem 14.2 (binary producer-port acquisition frontier).** For every
$0<Z<1$ and public $0<x<y<c$, under Definitions 13.2 and 14.1 the minimum
paid action for exact total binary calibration on the whole original
family (RA.14) is

$$
\mathcal A_{\min}=\frac{\pi r}{y-x}.
\tag{RA.19}
$$

One independent probe attains it, leaves the old specimen and all supplied
joint archives/reference unchanged, and appends one actually acquired
classical height bit. The attaining preservation statement holds for every
conditional joint input $\rho^h_{SAR}$ of Definition 13.2. The minimum
claim uses the lower-bound assistance restriction; arbitrary readable
height-bearing archives are not subject to that lower bound.

Proof. First remove a possible shortcut through the old specimen using
actual source states. For each fixed $k$, the four states with
$\beta\in\{0,\pi\}$ and $m\in\{0,1\}$ span $V$: their sums give
$2\sqrt Z e_2$, and their differences give the two vectors
$2(\sqrt{2k}U_+\pm\sqrt{2(c-k)}U_-)$. All three coefficients are
nonzero by strict positivity. Section 13's common-preparation construction
realizes every one of these witnesses.

Fix the proposed protocol and a candidate $k$. With its common ancillary
input absorbed, let $E^{(k)}_{\rm bad}\geq0$ be the induced effect on the
old specimen for an incorrect or inconclusive output. Correctness says
$\langle\psi,E^{(k)}_{\rm bad}\psi\rangle=0$ on the four actual
witnesses. Since this equals $\|\sqrt{E^{(k)}_{\rm bad}}\psi\|^2$,
the positive effect annihilates their entire span. Completeness therefore
forces output $k$ with probability one for every unit vector of $V$.
This is a consequence of one fixed protocol's correctness, not permission
to prepare further original specimens. In particular the same protocol
must distinguish the two ports starting from a single identical unit vector
$v\in V$ and the same source-independent ancillary state.

Purify that common ancillary state. Let $W_x(t),W_y(t)$ be the dilated
unitaries, including every outcome and known feedback operation. Write
$V_{\rm rel}(t)=W_x(t)^\dagger W_y(t)$. Between the common operations,

$$
i\dot V_{\rm rel}(t)=L(t)V_{\rm rel}(t),\qquad
L(t)=-\frac{y-x}{r}\,W_x(t)^\dagger G(t)W_x(t).
\tag{RA.20}
$$

Common instantaneous unitaries cancel in $V_{\rm rel}$. Its generator
therefore has diameter $(y-x)\operatorname{diam}(\operatorname{spec}G)/r$.
Apply the projective-angle accumulation argument of the cited FIB §2.4
to the ray $V_{\rm rel}(t)|v,\mathrm{anc}\rangle$. Its continuous
version has speed $\sqrt{\langle L^2\rangle-\langle L\rangle^2}$:
subtract the component of $-iLz$ parallel to a unit vector $z$ and take
its norm. If the spectrum lies in $[a,b]$, positivity of
$(L-aI)(bI-L)$ gives variance at most
$(b-\langle L\rangle)(\langle L\rangle-a)\leq(b-a)^2/4$.
The projective angle obeys the triangle inequality used in FIB §2.4.
For completeness its path-length bound also follows without a smoothness
assumption on the controls: multiply the absolutely continuous vector
path by the phase $\exp(i\int\langle L\rangle)$, giving a unit path
$w$ with $w'=-i(L-\langle L\rangle)w$ and speed equal to that variance
square root. Regard it as a path on the real Hilbert unit sphere. If
$b(t)=\operatorname{Re}\langle w(0),w(t)\rangle$, tangency and
Cauchy–Schwarz give $|b'|\leq\sqrt{1-b^2}\,\|w'\|$.
Integrating the derivative of $\arccos b$, with limiting truncations at
$b=\pm1$, bounds spherical endpoint distance by $\int\|w'\|$.
Projective endpoint angle is no larger, since the absolute inner product
is at least its real part. Consequently

$$
\arccos\left|\langle v,\mathrm{anc}|
 W_x(T_c)^\dagger W_y(T_c)|v,\mathrm{anc}\rangle\right|
 \leq\frac{(y-x)\mathcal A}{2r}.
\tag{RA.21}
$$

The final records have different deterministic labels, hence the two
purifications lie in orthogonal output sectors. The left side is $\pi/2$,
proving the lower bound. Dilation retained all outcomes, so feedback and
postselection have not supplied a free exception. Source-independent
randomized choices also obey it: each of the finitely many spanning
witnesses is correct almost surely, giving one common conull set of seeds
on which this same argument applies under the common action bound.

For attainment prepare $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$ once
and drive the port with positive action $a_*:=\pi r/(y-x)$. Its two possible
states are

$$
q_k=\frac{|0\rangle+e^{ika_*/r}|1\rangle}{\sqrt2},\qquad
\langle q_x,q_y\rangle
 =\frac{1+e^{i(y-x)a_*/r}}2=0.
\tag{RA.22}
$$

One calibrated measurement in this known orthonormal basis returns $Y=k$
with certainty. The scalar drive has action $a_*$. Most importantly, the
joint port premise gives, conditional on each actual history $h$,

$$
\rho^h_{SAR}\longmapsto
 \rho^h_{SAR}\otimes|k(h)\rangle\langle k(h)|_Y.
\tag{RA.23}
$$

The measured probe may also be retained in its known state $q_{k(h)}$;
discarding that probe does not change (RA.23). Integrating this equation
against the actual history distribution preserves its old quantum and
classical correlations, and appends the correct correlated bit. This
joint identity follows from the supplied coupling, not from equal sensor
marginals. The native hold has zero survival charge and phase increment.
There is one probe preparation, no specimen copy, reset or retry. $\square$

**Corollary 14.3 (rate and continuum boundaries).** If the full spectral
width in (RA.18) is at most $v>0$ almost everywhere, every such protocol has
$T_c\geq\pi r/(v(y-x))$. A constant scalar drive $u=v$ attains this
interrogation duration with the attaining protocol's endpoint preparation
and measurement treated as instantaneous ideal operations. Nonzero
preparation/readout overhead is an additional duration, not included in
that equality. Under this same assistance/access contract no common finite
action budget calibrates every height in a nonempty open interval exactly;
nor does a common finite horizon do so at bounded spectral rate.

Proof. Integrating the width bound gives $\mathcal A\leq vT_c$; use
(RA.19). The constant drive gives equality. For an open interval and any
finite budget, choose two distinct heights in it with gap less than
$\pi r$ divided by that budget; the binary lower bound contradicts that
budget. A zero budget is already excluded by any distinct pair. This
does not rule on approximate estimation or pointwise unbounded stopping.
$\square$

## 15. An acquired legal-versus-illegal guard on the same live branch

**Example 15.1 (actual preparations and calibration).** Fix

$$
Z=r=1/2,\quad c=1/4,\quad a_0=1/8,\quad q=x=1/16,\quad y=3/16.
\tag{RA.24}
$$

For every real $\beta$ and signed integer $m$, use (RA.15) with
$B=8\beta-4\pi m$ and arrive at either $x$ or $y$. The six-unit
preparations share a strict probability margin $1/16$. Their common
first five legs survive with probability
$(2/3)(1/2)=1/3$: the down-leg factor is
$(c-a_0)/(c-q)=2/3$, the up-leg factor is $q/a_0=1/2$, and the phase
legs have factor one. The final arrival has factor $2/3$ in either case,
namely $(c-a_0)/(c-x)$ or $a_0/y$. Both actual live probabilities are
therefore $2/9$. All prior failures keep their actual first time/mode and
absorbing $f$; these are not repeat-until-success preparations.

The port cost is $a_*=4\pi$. The two output probes are
$(|0\rangle+i|1\rangle)/\sqrt2$ and
$(|0\rangle-i|1\rangle)/\sqrt2$. At spectral rate $v$, the ideal
interrogation lasts $4\pi/v$. During it the native source holds its actual
height and real phase. The old source prefix remains literally unchanged;
the clock advances and records this hold, action and observed bit.

**Proposition 15.2 (total handler and its complete quantum output).**
Assume this port, its calibration and the following original canonical
processor are supplied and permitted. After acquiring $Y$, consider the
public unit relative request

$$
\Delta k(t)=t/8,\qquad \Delta\chi(t)=0,\qquad 0\leq t\leq1.
\tag{RA.25}
$$

Its actual domain is $(0,c-1/8)=(0,1/8)$. The handler uses only the
actually acquired $Y$ and retained permission fields. At $Y=x$ it
reports executed and applies the matching canonical processor. At $Y=y$
it reports unexecuted domain rejection, keeps the specimen and old joint
state unchanged, and records no fictitious execution time or failure.
Known permission denials likewise return unexecuted rejection.

For the legal branch, let $\rho_{VR}$ denote the actual joint input,
including quantum archives in $R$, and let
$\rho^R_{aa}=\langle a|\rho_{VR}|a\rangle$ for
$a\in\{+,-,2\}$ in (RA.13). Its success operator at time $t$ is

$$
K_t=\operatorname{diag}_{(+,-,2)}
 \left(1,\sqrt{\frac{3-2t}{3(1+2t)}},\frac1{\sqrt{1+2t}}\right).
\tag{RA.26}
$$

The terminal output consists of success with
$(K_1\otimes I_R)\rho_{VR}(K_1^\dagger\otimes I_R)$, or the following
exact first-failure CP densities, each with absorbing specimen $f$:

$$
\begin{aligned}
\omega_2(t)&=\frac{2}{(1+2t)^2}|f\rangle\langle f|\otimes\rho^R_{22},\\
\omega_1(t)&=\omega_3(t)
 =\frac{4}{3(1+2t)^2}|f\rangle\langle f|\otimes\rho^R_{--},\\
\omega_0(t)&=\omega_{13}(t)=0,\qquad 0<t\leq1.
\end{aligned}
\tag{RA.27}
$$

The labels $1$ and $3$ remain distinct actual outcomes despite equal
densities. Exact event times are translated to the actual clock after
calibration. On every source-family input at $x$, the complete outcome
masses are success $1/3$, mode $2$ failure $1/3$, mode $1$ failure $1/6$,
mode $3$ failure $1/6$, and zero in the other two modes. Failure is absorbing,
with no original retry. With request permission present, each live branch
has working height $y$: by execution on legal survival, and by identity on
domain rejection at $y$. A permission denial instead retains its actual
current height.
The old calibration bit remains an archived event, not an overwritten
working-height register.

Proof. The partial-action domain follows by requiring
$0<k+t/8<c$ for every $t$. Thus $x$ is legal and $y$ is illegal
(its proposed endpoint would be $5/16>c$). The acquired bit is exactly
the actual $K$, so the handler implements this total distinction without
guessing a guard from a law. On the legal path
$k(t)=(1+2t)/16$ the canonical law gives
$\lambda=k'/k$ and $S(t)=x/k(t)=1/(1+2t)$.
Insert this into (OC.19), or the credited horizontal maps (OC.57), to
obtain (RA.26). The middle attenuation squared has negative derivative
$2/(1+2t)^2$, while the minus attenuation squared has negative derivative
$8/(3(1+2t)^2)$. The two original minus-mode jumps each have half that
strength. This proves the full-reference CP densities (RA.27), rather
than inferring them from a specimen marginal or an unrelated waveform.

For completeness, $K_1=\operatorname{diag}(1,1/3,1/\sqrt3)$, the
integrated middle failure effect is $2/3$, and the two integrated minus
effects are $4/9$ each. Their sum with $K_1^\dagger K_1$ is $I_V$.
For an actual source input the diagonal in this basis is
$(1/8,3/8,1/2)$; substituting it gives the stated outcome masses and,
more fully, failure densities $1/(1+2t)^2$ in mode $2$ and
$1/(2(1+2t)^2)$ in each of modes $1,3$. No phase or signed winding has
been supplied to the handler. Applying $K_1$ to (RA.14) gives
$\sqrt{1/3}\,\psi_{y,\beta,m}$, with the old real lift preserved.

Equation (RA.23) followed by these branch CP maps, tensored with identity
on all old registers, proves the asserted joint implementation. The
relative phase joins to the old actual lift through
`concatenate_original`; zero-relative-phase requests do not require its
numerical value. Old executed failures are never passed to a live
processor. On a new failure the complete old archive, acquired bit,
request, exact time/mode and stopped status remain. On rejection execution
does not occur and its current time is retained. The two live branches can
therefore have different current clocks; any later selector uses their
actual clocks, permissions and records. $\square$

After legal survival or domain rejection at $y$, every separately supplied
and permitted original tail based at $y$ can be joined with its actual
relative real phase. This includes
either original regularity alternative, arbitrary finite durations including
the zero-duration identity, and all signed sectors allowed by that tail's
explicit promises. For finite feedback, choose only from actual retained
records and the declared controller/external inputs and retain each full
update. The credited joint-continuation theorem of Instrument Boundaries
§14 then applies branchwise. This is not an assertion that missing future
processors, source-sensitive permissions or controller inputs have been
acquired. Calibration preserves the old specimen; the subsequent legal
original operation has its genuine nonzero failure probability.

## 16. Ownership of the port, information and resources

**Resource statement 16.1 (separate upper and lower accounts).** The
attaining calibration uses one live active qutrit and one independent probe
qubit, active tensor dimension six before readout, excluding all old
archives and references. Keeping the full five-mode realization instead
uses a ten-dimensional live specimen/probe tensor product. Readout appends
one classical bit; it can consume the probe, or the known conditional probe
state can also be retained and counted. The post-read active live component
with just that bit is $M_3\oplus M_3$, not a dimension-three complete
observer. Stopped status, the request/status fields and every old or newly
appended event are additional retained resources.

The producer-side carrier retains a two-valued classical setting, coupled
through the extra port. It is a source-bearing resource even though it is
not directly delivered as an accessible label. If a larger physical or
mathematical carrier implements it, its size is not bounded by this
two-valued description. Port ownership and access permission belong to the
producer/service contract. The observer owns the prepared probe and its
actual acquired bit; neither owns an extra original specimen.

The public catalogue, $Z$, preparation basis, coupling scale, known probe
amplitudes, orthogonal readout basis, action programme, calibration and
authentication, clock/reference stability, controller, request description,
permissions and all selection/update inputs require their actual supplied
representations. General exact real parameters need not have finite
effective descriptions. In Example 15.1 the catalogue is rational, the
basis read is the algebraic $\pm i$ basis, and $4\pi$ has a finite
symbolic description; exact execution still consumes ideal action and
timing/reference calibration, not a finite-noise guarantee.

Paid port action is $4\pi$ in that example, with interrogation time
$4\pi/v$ at the stated rate and any additional control/readout overhead
charged separately. The six-unit witness preparation, its $2/9$ live
probability, old waveform/lift information retained elsewhere, original
hold and tail permissions, and supplied canonical processor are separate
resources. Neither action nor live dimension prices their construction or
certification. Exact canonical failure time is an ideal continuous record;
no finite-bit archive bound is claimed. All source-bearing assistance must
be counted jointly when accessible, including a returned environment,
receiver share, source-sensitive clock or installed programme.

The sharp lower bound denies such extra readable assistance; it permits
the actual height-dependent old specimen and arbitrary common controls on
it. The upper joint identity permits arbitrary old correlations and simply
does not read them. A pre-existing readable height bit can reduce the
required port action to zero, so those two assistance contracts cannot be
conflated. No minimum physical hardware, classical archive size or total
observer resource follows from (RA.19).

## 17. Suppliers, mature attribution and remaining acquisition obligations

All repository suppliers for §§13–17 are inspected at the immutable public
snapshot `1f58736f50945c7cfeca93ce160eb9b46a3a7e7e`. The claims here have
ordinary proofs and no new Lean/kernel certification.

| Supplier | Exact use and boundary |
| --- | --- |
| `D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean` and its owning Scribe, `ValidBase`, `probability`, signed `phaseWeight`, `weight_compatible`, `finite_rectangles_realize` | Strict positive original source and actual rectangle paths. The all-signed-sector Scribe application supplies the winding leg and its real lift; the rectangle declaration alone is not credited with that entire application. |
| `D5/S3/Quantum/Fibers/OriginalControlComposition.lean` and its owning Scribe, `OriginalControl`, `FiniteC1Control`, `concatenate_original` | Both regularities, finite and zero durations, unchanged original prefix, matching height, translated real phase and additive transport. No port, actuator or old lift read is inferred. |
| [Instrument Boundaries](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md), §§4–5, 14, 17, 21–23; [Quantum Carrier Minimum](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md), §§1, 3, 6–10 | Actual full original orbit, complete stopped CP instrument, horizontal density formulas, common-preparation multi-height witnesses, matched joint continuation, known-anchor generated labels and received-command capacity remain credited. The exact total guard is an added consumer specification; a partial-action domain alone is not a height detector. |
| [FIB Atom Whitebox SIC Time Acquisition](FIB_ATOM_WHITEBOX_SIC_TIME_ACQUISITION.md), §2.4 and Citation 3.1 | Mature adaptive query-angle accumulation, outcome-retaining dilation and common-isometry invariance are reused in (RA.20)–(RA.21). Its tensor-sign device, archived scores, query count and legal-word service do not supply an original producer port or its price. |
| This volume §§1–12; [Instrument Stability](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md); [Sampled Instrument Certificates](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_SAMPLED_INSTRUMENT_CERTIFICATES.md), §§2–3, 7–8 | Existing point-query obstructions, area/winding certificates, complete-instrument error data and the extra joint sampler kernel keep their own promises. A height bit acquires none of their unknown waveform samples, derivative/loss densities or full marked laws. |
| [Event Memory and Coarse Aliasing](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_EVENT_MEMORY_AND_COARSE_ALIASING.md), §§2, 4–6; [Parity Record Transport](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_PARITY_RECORD_TRANSPORT.md), §§3, 9, 12–16; [Reanchoring Boundaries](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_REANCHORING_BOUNDARIES.md), §§2, 7–8 | Same-event memory, supplied-helper and live/failure-calibration results, and uncertain-height reanchoring remain distinct contracts. The present port is extra height-dependent access, not an acquired parity helper, unchanged return on failure, marginal event resampling or an unaugmented reanchoring construction. |
| [Probability/Phase Transport](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md), §9.1; [Transport–Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §§2.9–2.12, 2.18 | Actual relative-command domains are used for (RA.25). Same-source coherent common-port interference, aligned acquired readings and known nonzero amplitudes/record overlap remain unsupplied. The additional phase query has a different interface from those intensity readings. |
| [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §34; [Atlas Stable Core Holonomy](RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md), Theorem 6.3 | Actual joint source/epoch image, complete rejections/failures, archives, references, permissions and selection/update routes must coexist. A binary calibrated guard does not establish individual sufficiency of the four views. |

**Literature statement 17.1 (mature mechanism and precise transfer).**
Positivity of effects, actual-source spanning, unitary discrimination,
Stinespring dilation and projective-angle geometry are mature mathematics.
The source-specific synthesis here is `repo-derived`: the response
correspondence (RA.17), original-orbit reduction despite the old
height-dependent specimen, explicitly paid extra-port interface, joint
preservation (RA.23) and complete legal-versus-illegal original consumer.
The query-angle principle is reused, not presented as a new general
discrimination theorem. No worldwide priority claim is made.

| Primary text | Verified scope and use |
| --- | --- |
| A. Acín, [*Statistical distinguishability between unitary operations*, quant-ph/0102064v1](https://arxiv.org/html/quant-ph/0102064v1), Eqs. (18)–(21) | The relative-spectrum convex-hull criterion and multiple-use orthogonalization concern supplied unitary calls and prepared probes. This is mature discrimination context, not construction of our source-bound port. |
| R. Duan, Y. Feng and M. Ying, [*Entanglement Is Not Necessary for Perfect Discrimination between Unitary Operations*, quant-ph/0601150v2](https://arxiv.org/html/quant-ph/0601150v2), Theorem 1 and the numerical-range criterion preceding it | Known candidate unitaries, actual uses and common known intervening controls permit exact discrimination at the shortest-arc threshold. The continuous spectral-action specialization is justified in (RA.20)–(RA.22); neither a source setting nor a query route is obtained from that theorem. |
| S. Manna, S. Suresh, A. Das Bhowmik and D. Saha, [*Global vs. Local Discrimination of Locally Implementable Multipartite Unitaries*, 2509.10430v1](https://arxiv.org/html/2509.10430v1), probing protocols and Theorem 1 | Its local/global and adaptive/restricted comparisons presuppose supplied candidate operations, chosen probes and allowed measurements. Its bipartite-qubit equality of adaptive/restricted local discrimination supplies no producer coupling, acquisition law or resource transfer for this original source. |

These bounded primary comparisons supply method attribution and check the
access premises; none of the inspected texts constructs the missing joint
original-source port. This is not an exhaustive literature search, an
impossibility statement or evidence of worldwide originality.

**Open boundary 17.2 (the unconstructed source-to-port bridge).** The
original transport path and calibrated canonical Kraus formula do not
provide an executable route that couples a blank probe to the producer's
unknown actual current setting while preserving the old specimen,
reference and records jointly. A construction must establish the retained
producer carrier, stable setting, actual source/epoch authentication,
permissions, nondisturbing coupling, gain/reference/timing calibration,
probe preparation/readout, complete service failure behavior and their
costs. Invoking (RA.16) without that contract would install the missing
access by fiat. Existence and physical realization of this additional
service remain unresolved.

Unknown continuous catalogues, changing height during interrogation,
uncalibrated gain or phase reference, general phase/history-dependent
assistance, approximate/noisy acquisition and unbounded future accuracy
are not settled by the binary exact theorem. The current bit recovers
neither old winding nor waveform, unrecorded preparation data, unknown
record overlap or a whole probability law. The full original class retains
its other bases, arbitrary finite durations, both regularities and signed
sectors; the double-wall binary promise does not replace that class.

The complete common-port/overlap interface, actual compatible full observer
archive and closed selection/update acquisition, individual four-view
recovery, native stationary $\alpha/\beta$ memory-rate/cofinality and the
independent fixed-Hamiltonian quantum minimax keep their original unresolved
obligations. No source/action/observation/resource bridge from the static
arithmetic, preparer/reader, C114 mixed-state, twisted-ground or two-clock
span models is claimed. This conditional acquisition result does not close
the original unaugmented menu or the continuing programme.

## 追加锚（本行以下为增补区）

## 18. Signed numerical commands and an actual execution interface

**Definition 18.1 (the signed source and its nominal issued record).**
Let QP denote [Quantitative native long-time phase paths and terminal
heights](FIB_NATIVE_LONG_TIME_PHASE_QUANTITATIVE_BOUNDS.md), G denote
[Native two-control Green stability](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md),
D denote [Native long-time phase diffusion](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md),
and N denote [Auric FIB atom probability, phase transport and
holonomy](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md).
Use QP Definitions 69.1, 69.3 and all the calibration, finite-service,
permission, fairness and resource premises of its Assumption 69.2.
Only its exact scalar-execution premise is replaced by Definition 18.2.
In particular fix its original signed nonzero $\kappa$ in the nonzero
collar, $\varepsilon>0$, $0<Z<1$, $H=(1-Z)/2$, and deterministic immutable
INITIAL $=(k_0,y_0)$ with $k_0\in I=(l,u)$ and
$[l,u]\Subset\mathcal J_\kappa=(\max(0,2\kappa),H+\kappa)$.
All preparation phases and the negative amplitude convention remain fixed.

On the real lift write $y=(\theta,v,D)$ and
$c(k)=\widehat c_\kappa(k)=(A_\kappa(k),B_\kappa(k),\kappa b_\kappa(k))$.
These are exactly G (25.4):

$$
\begin{aligned}
s_\kappa&=H+\kappa,& a_\kappa&=\kappa+\kappa^2/H,\\
A_\kappa(k)&=\frac{(k-2\kappa)(s_\kappa-k)}{2H(k-a_\kappa)},&
B_\kappa(k)&=-\frac{k(k-2\kappa)}{2H(k-a_\kappa)},&
b_\kappa(k)&=\frac{s_\kappa-k}{H(k-a_\kappa)}.
\end{aligned}
\tag{18.1}
$$

The notation $a_\kappa$ here names G's $\alpha_\kappa$, not a control.
The fields are $P=\partial_k$ and $Q_\kappa=c(k)\cdot\partial_y$,
and the probabilities remain
$(k-2\kappa,H+\kappa-k,Z,H+\kappa-k,k)$.
The actual phase torus is $(\mathbb R/2\pi\mathbb Z)^3$.
For path comparisons use the Euclidean norm on the original three
lift coordinates and its uniform path metric. In particular $D$ is
never replaced by $D/\kappa$.

Choose exactly QP (69.2)--(69.5): $h,N,j_0,a,d,k_j$, the certified
dyadic transition rows, $B$, $\delta,z,e,\alpha$, and the independent
fair table and sign bits. Write $J_0=j_0$, $1\le J_i<N$ for its generated
height tape and $\xi_i\in\{-1,1\}$ for its phase signs, $1\le i\le m$.
Put $A_i=h(J_i-J_{i-1})$, $B_i=z\xi_i$ and $d_0=\delta/2$.
The issued schedule is precisely QP (70.1): installation hold $\iota$,
then, for each $i$, P for $d_0$, hold $d_*/2$, Q for $d_0$, hold
$d_*/2$, and terminal hold $r_*$. Its elapsed time is
$\tau=\iota+m(\delta+d_*)+r_*$, including every hold.
All stage quotas and $d_*/2\ge\ell$ remain requirements.

Let $R$ be the finite issued record: source and INITIAL identities,
calibration and guard certificates, granted permission identifiers,
all fair bits, $J_i,\xi_i$, the rational displacements and full timed
schedule. The phase reference $y_0$ is retained by identity/alignment;
no numerical polling of its phases is implicit. Execution status at a
declared completed delimiter is a separate finite event field.
The nominal path $(\bar K,\bar Y)$ is the exact ODE image of this same
issued record, so that
$\bar K_i=k_{J_i}$ and
$\bar Y_i-y_0=\sum_{j\le i}B_jc(k_{J_j})$.
It is the QP numerical path as a mathematical comparison, not an
additional execution, a reset, or a sensor.

**Definition 18.2 (covered errors, holds and common realization).**
Choose deterministic nonnegative rational displacement caps
$p_i,q_i$, $1\le i\le m$, recorded with $R$. On the P interval of cell
$i$ the actual velocity is $(A_i/d_0+u_i(t))P$; on its Q interval it
is $(B_i/d_0+v_i(t))Q_\kappa$, with

$$
u_i,v_i:[0,d_0]\to\mathbb R\ \hbox{Lebesgue measurable},\qquad
|u_i(t)|\le p_i/d_0,\quad |v_i(t)|\le q_i/d_0
\quad\hbox{almost everywhere}.
\tag{18.2}
$$

Here the argument is local elapsed time within the respective piece.
Thus the primitive error on any partial interval has absolute value
at most its elapsed fraction times $p_i$ or $q_i$, and its total
variation is at most $p_i$ or $q_i$. In particular the signed completed
displacement errors $e_i=\int u_i\,dt$ and $f_i=\int v_i\,dt$ lie in
$[-p_i,p_i]$ and $[-q_i,q_i]$. Every point of these intervals is allowed,
realized by the corresponding constant error speed. Endpoint-error
bounds alone, with uncontrolled intermediate excursions, are not this
interface.

Switching times, durations and all installation, latency and terminal
holds are exact; on holds both actual velocities are zero. Only the
active scalar speed is erroneous. There is no wrong-field component,
height leakage during Q, autonomous drift, timing slip, calibration
error, changed five-mode probability formula or extra error-correction control.
The source follows the original ODE for these actual velocities from
the same INITIAL. The original whole-command extrema guard, its
refusal, and Stop followed by a hold are retained for the *actual*
relative command. A speed-reversal within an active piece is allowed.
This is a conditional actuator specification, not a claim that it
has been installed or tested.

At the pathwise level all error profiles satisfying (18.2) are covered.
For probabilistic statements take any joint probability space carrying
the prescribed fair record with its original law and these error
profiles, for which the integrals and resulting paths are measurable
and the bounds hold almost surely. Their joint conditional law may
depend on the entire precomputed, already retained $R$, including
future phase signs, and on an unobserved auxiliary variable. No
independence, centering, temporal decorrelation or causal ignorance of
that tape is imposed. No actual-error value is a readable input.
The auxiliary variable describes execution uncertainty; it grants no
additional usable sampler. Any extra service actually used to produce
that uncertainty has its own finite-service charges in §22.
A missing command, a non-held source, lost record or failed service
does not satisfy this specification; if an interface supplies such
failure events they must be retained, and the successful-execution
conclusion is not asserted on them.

## 19. All-prefix lawfulness, discrepancies and original-time charges

**Theorem 19.1 (uniform certificate for every covered execution).**
For Definition 18.2 set

$$
P_i=\sum_{j=1}^i p_j,\quad P_0=0,\quad
P_\Sigma=P_m,\qquad Q_\Sigma=\sum_{i=1}^m q_i,\qquad
g=\min\{a+h-l,\ u-d+h\}.
\tag{19.1}
$$

Let $C>0$ and $L\ge0$ bound respectively $\sup_{[l,u]}|c|$ and
$\sup_{[l,u]}|c'|$. QP (69.2) gives $2h<g<4h$.
If $P_\Sigma<g$, every actual prefix, including partial active pieces,
is an original lawful native history and stays in $I$. Moreover

$$
\begin{aligned}
\sup_{t\le\tau}|K^*(t)-\bar K(t)|&\le P_\Sigma,\\
\sup_{t\le\tau}|Y^*(t)-\bar Y(t)|
 &\le \mathcal E:=C Q_\Sigma+Lz\sum_{i=1}^m P_i.
\end{aligned}
\tag{19.2}
$$

Here star denotes the actual execution. With $F=cc^{\mathsf T}$,
$T=\tau/b$ and any fixed $b>0$, its full-clock occupation also satisfies

$$
\sup_{0\le s\le b}\left\|
 \frac1T\int_0^{Ts}\{F(K^*(t))-F(\bar K(t))\}\,dt
 \right\|\le 2bCLP_\Sigma .
\tag{19.3}
$$

These are deterministic, simultaneous certificates over the entire
issued-record and error domain; they neither read errors nor replace
the original extrema domain by an endpoint test.

Proof. The nominal height range is $[a+h,d-h]$. At a partial P piece,
the height offset is the sum of completed P errors plus the integral
of the current $u_i$. Its modulus is at most $P_i$; at Q and holds it
is the completed sum $E_i=\sum_{j\le i}e_j$. Therefore the whole actual
height path lies in
$[a+h-P_\Sigma,d-h+P_\Sigma]\Subset I$.
It is absolutely continuous with integrable derivative. The relative
phase control is likewise absolutely continuous, with finite variation.
N Theorem 9.2 and Proposition 10.2 identify this actual horizontal
history with an original control, and give its exact extrema guard
and partial-action composition. This checks positivity for every
prefix, not just for the completed lattice points.

On Q piece $i$ the actual height is the constant $k_{J_i}+E_i$.
For a partial duration $s\in[0,d_0]$, subtract the nominal phase
increment from the actual one:

$$
 \frac{B_i s}{d_0}\{c(k_{J_i}+E_i)-c(k_{J_i})\}
       +c(k_{J_i}+E_i)\int_0^s v_i(t)\,dt .
\tag{19.4}
$$

Its norm is at most $LzP_i+Cq_i$.
Summing completed pieces and, when present, the current partial Q
piece proves (19.2). P pieces and holds add no phase discrepancy.
The segment between the two heights lies in $[l,u]$, so the derivative
bound is applicable. Finally
$\|F(k)-F(k')\|\le2CL|k-k'|$ by expanding the difference of the two
outer products. Integrating for the actual duration $Ts$, rather than
active time alone, proves (19.3). Stop truncates the same argument and
adds a held state; it supplies no full-horizon limit for an interrupted
run. $\square$

**Corollary 19.2 (explicit sufficient per-command scales).**
For $T=\tau/b>0$, choose a desired normalized discrepancy $r>0$.
It is sufficient that, for every $i$,

$$
q_i\le\frac{r\sqrt T}{2Cm},\qquad
p_i\le
 \min\left\{\frac hm,\,
 \frac{r\sqrt T}{(L+1)z\,m(m+1)}\right\}.
\tag{19.5}
$$

Then $P_\Sigma\le h<g$ and $\mathcal E/\sqrt T\le r$.
Equivalently the sufficient absolute speed-error caps on each active
piece are $2p_i/\delta$ and $2q_i/\delta$.
These are requested mathematical accuracy scales, not an accuracy,
throughput or energy theorem about a device.

Proof. One has
$\sum_iP_i\le m(m+1)\max_i p_i/2$ and
$Q_\Sigma\le m\max_i q_i$.
The two terms in (19.2), divided by $\sqrt T$, are at most
$rL/(2(L+1))$ and $r/2$ respectively. The height statement follows
from (19.1). $\square$

**Theorem 19.3 (native variation, length and energy on the same clock).**
Under Theorem 19.1 every covered execution has

$$
\begin{aligned}
 V^{a,*}&\le mh+P_\Sigma,&
 V^{b,*}&\le mz+Q_\Sigma,\\
 \mathsf L_A^*&\le (mh+P_\Sigma)/\varepsilon+mz+Q_\Sigma,\\
 \mathsf E_A^*&\le
 \frac2\delta\sum_{i=1}^m
  \left\{\frac{(|A_i|+p_i)^2}{\varepsilon^2}
                   +(z+q_i)^2\right\}.
\end{aligned}
\tag{19.6}
$$

The covariance/norm convention remains
$A=\operatorname{diag}(\varepsilon^2,1)$.
In particular the lifted state variation is at most
$mh+P_\Sigma+C(mz+Q_\Sigma)$.
All preparation and holds have their full original elapsed-time and
maintenance charges, although their horizontal energy is zero.

Proof. On a P piece the speed has modulus at most
$(|A_i|+p_i)/d_0$, and on a Q piece it is at most $(z+q_i)/d_0$.
Integrate the speed, or its square with the stated covariance weight,
over its duration $d_0$ and sum. The phase variation is at most $C$
times the scalar Q variation. No regularity or probability assumption
on the error beyond (18.2) was used. $\square$

## 20. Transfer of the unchanged joint transport consumer

**Theorem 20.1 (actual execution tolerance in the full joint regime).**
At every stage use the same fixed signed source and INITIAL of
Definition 18.1, with all the finite prerequisites of QP Theorem 70.1,
except for the replaced exact scalar-execution premise.
Assume its quotas, its latency/hold conditions, and the entire joint
regime

$$
\begin{gathered}
 h_n\longrightarrow0,\quad e_n\longrightarrow0,\quad
 \alpha_n\longrightarrow0,\quad T_n=\tau_n/b\longrightarrow\infty,\\
 m_n2^{-B_n}\longrightarrow0,\qquad
 \frac{\iota_n+m_nd_{*,n}+r_{*,n}+\delta_n}{T_n}\longrightarrow0 .
\end{gathered}
\tag{20.1}
$$

In addition assume $P_{\Sigma,n}<g_n$ and the proved discrepancy
bound satisfies $\mathcal E_n/\sqrt{T_n}\to0$.
For *every* sequence of joint actual error laws in Definition 18.2,

$$
 X_n^*(s)=\frac{Y^{*,n}(T_ns)-y_0}{\sqrt{T_n}}
 \ \Longrightarrow\ \widehat{\mathcal W}_{\kappa,b}
 \quad\hbox{in }C_0([0,b],\mathbb R^3),
\tag{20.2}
$$

and its endpoint covariance converges to $2b\widehat M_\kappa$, where

$$
 \widehat M_\kappa=\int_l^u c(k)c(k)^{\mathsf T}\phi(k)^2\,dk,\qquad
 \phi(k)=\sqrt{\frac2{u-l}}\sin\frac{\pi(k-l)}{u-l}.
\tag{20.3}
$$

The centering in (20.2) is exactly $y_0$, not an error-dependent mean.
The actual finite-stage mean need not vanish; its normalized modulus
is at most $\mathcal E_n/\sqrt{T_n}$.
Since $P_{\Sigma,n}<g_n<4h_n\to0$, (19.3) also transfers QP's full-clock
occupation certificate. Conditions (19.5) with $r_n\to0$ ensure all these additional
conditions. No optimal P-error threshold is asserted.

Proof. On the actual joint probability space construct the nominal
path as the stated deterministic function of the same $R_n$. Its
marginal distribution is exactly the QP numerical distribution:
adding an arbitrary conditional error law does not alter that
prescribed fair-record marginal. QP Theorem 72.1, with (20.1) and
all its original source/service hypotheses, gives its full joint
centered limit and endpoint covariance, including the signed cross
entries. By (19.2),

$$
 \|X_n^*-\bar X_n\|_\infty
             \le d_n:=\mathcal E_n/\sqrt{T_n}\longrightarrow0.
\tag{20.4}
$$

For every bounded Lipschitz function on this continuous-path space the
expectation difference is bounded by its Lipschitz constant times
$d_n$. Such functions determine weak convergence on this separable
metric space, proving (20.2). This is a comparison of the actual joint
law with the nominal joint law on one realization. It does not apply
a martingale theorem to the actual errors.

For the second-moment assertion put $U_n=\bar X_n(b)$ and
$V_n=X_n^*(b)-U_n$. The nominal vector has mean zero and uniformly
bounded second moment by QP Theorem 72.1. Since $|V_n|\le d_n$,
Cauchy--Schwarz gives

$$
 \|\operatorname{Cov}(U_n+V_n)-\operatorname{Cov}(U_n)\|
 \le 2(\mathbb E|U_n|^2)^{1/2}d_n+d_n^2 .
\tag{20.5}
$$

Also $|\mathbb E(U_n+V_n)|\le d_n$. This proves covariance and mean
convergence without assuming uniform integrability from weak
convergence or subtracting an unknown actual mean. Formula (19.3)
proves the occupation assertion. $\square$

**Corollary 20.2 (the selection consumer and a symbolic sufficient scale).**
Under all the hypotheses of QP Corollary 72.2, including that the
analytic selection is Q in the stated survival-selection class, add
Theorem 20.1's actuator and vanishing-discrepancy conditions.
Then the actual numerical executions approach that same correlated
rank-three Q transport endpoint. Their ensemble endpoint covariance
is positive definite eventually. This transfers that transport
consumer, not the native entropy-rate selection criterion.

In the specific simultaneous scaling QP (70.7), it is sufficient to
request $p_{i,n}\le n^{-7}$ and $q_{i,n}\le n^{-4}$, uniformly in $i$.
They give $P_{\Sigma,n}=O(n^{-3})$,
$\mathcal E_n/\sqrt{T_n}=O(n^{-1})$, and speed-error caps of orders
$n^{-5}$ and $n^{-2}$. This is a conditional symbolic scaling.

Proof. The limit matrix in (20.3) is positive definite for the fixed
nonzero signed collar by D Theorems 36.1, 39.1. Matrix convergence
therefore gives eventual positivity, exactly as in QP Corollary 72.2.
For the scaling, $m=n^4$, $z\asymp n^{-1}$,
$\delta\asymp n^{-2}$ and $\sqrt T\asymp n$. Substitute in (19.2)
and (18.2); $g>2h\asymp n^{-1}$ gives the guard. This calculation
does not establish the availability or price of the requested
accuracy. The same fixed holds must still accommodate every service
used, including those in §22 when that readable consumer is claimed.
$\square$

## 21. The exact scalar retained-record interval and its sharp threshold

**Theorem 21.1 (attained compatibility interval and scalar minimax).**
Let $\lambda=(2,-2,1)$, of Euclidean norm $3$, and let
$\chi^*(t)=\lambda\cdot(Y^*(t)-y_0)$ be its *lifted increment*.
For a completed issued record $R$, put
$\beta_R=z\sum_{i=1}^m\xi_i$.
On the exact-P subdomain $p_i=0$, the set of compatible terminal
lifted increments, over all covered Q-error profiles, is exactly

$$
 \{\chi^*(\tau)\mid R\}
       =[\beta_R-Q_\Sigma,\ \beta_R+Q_\Sigma].
\tag{21.1}
$$

Both endpoints and every intermediate value are attained on that
same record. Consequently

$$
 \inf_{a\in\mathbb R}\quad
 \sup_{\text{covered errors at }R}|\chi^*(\tau)-a|
       =Q_\Sigma,
\tag{21.2}
$$

attained by the record predictor $a=\beta_R$; it is the unique
minimizer, also when $Q_\Sigma=0$. Independent randomization of the
predictor cannot lower the worst-case expected absolute loss.
The same minimax radius holds for predicting the entire scalar
lifted-increment path in uniform norm, using its nominal path.

The notation in (21.1) is a set of realizations compatible with the
record and interface. It is not a conditional probability-support
assertion for every joint error law: a particular law can put mass
on a strict subset of this interval.

Proof. The exact supplied primitive identity is

$$
 \lambda\cdot c(k)=2A_\kappa(k)-2B_\kappa(k)+\kappa b_\kappa(k)=1.
\tag{21.3}
$$

This is D Theorem 50.1's original character, with both signs of
$\kappa$ unchanged. Thus $\chi^*$ is the actual accumulated scalar
Q displacement; neither height nor P motion enters it. At the
terminal hold it equals $\beta_R+\sum_i f_i$. The Minkowski sum
of the intervals $[-q_i,q_i]$ is $[-Q_\Sigma,Q_\Sigma]$.
Explicitly, if $Q_\Sigma>0$, any $s$ in this last interval is
realized by $f_i=sq_i/Q_\Sigma$, with constant speed
$v_i=f_i/d_0$. If $Q_\Sigma=0$, all $f_i=0$.
The exact-P history is lawful regardless of these Q errors because
height remains nominal. Indeed the scalar identity and interval
also hold with any of Theorem 19.1's guard-certified P errors;
exact P is imposed here for the vector comparison below.

For any predictor $a$, the larger of its losses at the two endpoints
is $Q_\Sigma+|a-\beta_R|$. This proves (21.2).
For a randomized output $A$, the sum of its expected losses at the
two endpoints is at least $2Q_\Sigma$, by the triangle inequality.
For paths the accumulated absolute Q error at every prefix is at
most $Q_\Sigma$, so the nominal path gives that upper radius.
The terminal two endpoints give the matching lower radius.
No winding has been reduced modulo a period in these statements.
$\square$

**Proposition 21.2 (vector bounds are different from the scalar equality).**
On the exact-P subdomain, write $c_i=c(k_{J_i})$.
The compatible full terminal vector increments form the attained set

$$
 \sum_i B_ic_i+
 \left\{\sum_i f_ic_i:\ -q_i\le f_i\le q_i\right\}.
\tag{21.4}
$$

Its Euclidean minimax radius $\mathfrak r_R$ satisfies

$$
 Q_\Sigma/3\le\mathfrak r_R\le C Q_\Sigma.
\tag{21.5}
$$

In particular the scalar radius $Q_\Sigma$ in (21.2) is not a
Euclidean vector-radius formula.

Proof. Integrate Q at its fixed height, and realize every $f_i$
by the constant speed from Theorem 21.1. The second set in (21.4)
is compact and centrally symmetric. If $w$ belongs to it, so does
$-w$, and any proposed vector center has maximum distance to that
pair at least $|w|$. The nominal center achieves maximum radius
$\max|w|$, so it is a minimax center. The triangle inequality gives
$|w|\le\sum_i q_i|c_i|\le C Q_\Sigma$. Taking all $f_i=q_i$ gives
$\lambda\cdot w=Q_\Sigma$ by (21.3), hence $|w|\ge Q_\Sigma/3$.
These are lower and upper bounds; no equality between them is claimed.
$\square$

**Theorem 21.3 (necessary and sufficient worst-case Q-error scale).**
Assume the complete nominal hypotheses and joint regime of
Theorem 20.1 and exact P. The deterministic caps $q_{i,n}$ may be
unequal. The following are equivalent:

1. $Q_{\Sigma,n}/\sqrt{T_n}\to0$.
2. For every sequence of allowed joint Q-error laws, with unrestricted
   dependence on the retained tape as in Definition 18.2, the actual
   paths have exactly the centered joint limit (20.2) and the endpoint
   covariance limit stated there.

The equivalence concerns uniform protection against the declared
full error domain. It is not a necessary condition for one particular
benign error law. For equal caps $q_n$, it is exactly
$m_nq_n=o(\sqrt{T_n})$, or, for a common absolute Q speed-error cap
$s_n=2q_n/\delta_n$, exactly
$m_n\delta_ns_n=o(\sqrt{T_n})$.

Proof. Sufficiency is Theorem 20.1 with
$\mathcal E_n=CQ_{\Sigma,n}$ and $P_{\Sigma,n}=0$.
For necessity choose the admissible constant speeds
$v_{i,n}=q_{i,n}/d_{0,n}$ for every record.
Then the normalized endpoint primitive increment is exactly

$$
 \lambda\cdot X_n^*(b)=
 \lambda\cdot\bar X_n(b)+Q_{\Sigma,n}/\sqrt{T_n}.
\tag{21.6}
$$

The nominal scalar converges to the centered normal of variance $2b$,
because $\lambda^{\mathsf T}\widehat M_\kappa\lambda
=\int_I1\,\phi^2=1$.
If the nonnegative shifts in (21.6) do not tend to zero, some
subsequence has a further subsequence tending either to a finite
positive value or to $+\infty$. In the first case its limiting
normal has that positive mean and is not the target scalar law.
In the second case tightness fails: a tight nominal variable shifted
to $+\infty$ leaves every fixed compact interval with probability
tending to one. Either case contradicts (20.2), since endpoint
projection by $\lambda$ is continuous. The requirement of covariance
convergence in item 2 does not rescue the failed centered-law claim.
In fact the scalar variance in (21.6) is unchanged by this deterministic
shift, so scalar covariance alone cannot detect the failure.
The equal-cap speed reformulation follows from $d_0=\delta/2$.
$\square$

**Theorem 21.4 (same issued record does not determine the actual outcome).**
If some $q_j>0$, no function of the retained issued record, even with
its deterministic schedule, known INITIAL and completed delimiter,
recovers the exact actual terminal lift throughout the exact-P
error domain. The obstruction also applies to the actual torus
outcome and primitive circle character. Nor do these record data
determine the actual conditional joint outcome law without a
specified joint error law.

Proof. Fix any realizable record and choose a real
$0<a\le q_j$ with $2a<2\pi$.
Take every P error zero and every Q error zero except $f_j=+a$
or $f_j=-a$, using constant speeds. These executions share the
entire issued record, all times, all heights, all source/permission
fields and every guard value that depends only on height.
Their terminal lift difference is $2ac_j$ and its primitive
projection is $2a$. Thus both the lifts and the primitive circle
characters differ. The source's unimodular phase torus then also
has distinct outcomes. A single record decoder returns the same
answer on both and cannot be exact. A randomized decoder has the
same output law on the two records and cannot almost surely equal
both different constants.

Concentrating the error law on one or the other profile gives
different conditional actual outcome laws on that same record;
mixing them gives still other laws. The fair-record law and nominal
joint law have not changed. Specifying three marginal phase laws
would in general also leave their cross dependence unspecified;
it is the common-record uniform vector coupling (20.4) that proves
the joint limit, not marginal convergence or a fitted tensor.
In particular no actual-error sensor, error independence or
error-dependent centering can be inferred from (21.1).
$\square$

## 22. A finite readable report with paid retained access

**Definition 22.1 (rational report subdomain and granted services).**
For this section restrict the known data
$Z,\kappa,l,u,k_0,\varepsilon^2$ to rationals satisfying the original
source/collar restrictions, and $b>0$ to a rational.
Every scheduled number, cap $p_i,q_i$, source certificate and tariff
used by the report has a finite rational/integer encoding.
The original table construction and fair-bit generation are still
QP's; they are not replaced by a new random source.
The preparation phases may remain arbitrary immutable real phases.
The report predicts all three *increments from that same $y_0$*.
An absolute numerical phase report additionally requires a supplied
rational vector $\widetilde y_0$ and certificate
$|\widetilde y_0-y_0|\le r_0$, with their calibration, input and
retention costs. Then the reported absolute center is
$\widetilde y_0+\bar Y-y_0$, with radius $r_0+\mathcal E$.
This is an optional known-INITIAL calibration subdomain, not a
current-state measurement or a way to acquire an unknown preparation.

There are granted rights to write and read this experiment's own
finite $R$ and the derived report, with its source identity and
reference alignment intact. A specified owned digital port exposes
these bytes and the completed delimiter, not the source state,
error profiles, unknown current clock, another experiment or a
pre-entry archive. Its semantics are exact finite byte delivery.
For explicit finite input/output lengths it supplies positive
throughputs $r_{\rm in},r_{\rm out}$ in bits per original time and
a finite port/setup latency $t_{\rm port}$. Access is nondisturbing
to the held source. These are additional permitted services, with
separate input/output tariffs when tariffs are counted.

The actuator accuracy in (18.2), exact holds and switch times must
themselves be granted guarantees on this same source and run.
If a separate precision-provision service is used, name its finite
provisioning time $t_{\rm acc}$, installation energy $E_{\rm acc}$,
and finite counts $U_{\rm acc},W_{\rm acc},I_{\rm acc},O_{\rm acc},
L_{\rm acc}$ for calculation, bit writes, input, output and peak
memory. Those counts include its calibration certificates and
precision installation. A requested $p_i,q_i$ without this stipulated
execution guarantee does not meet Definition 18.2. In particular a
finite precision *description* is not a physical accuracy service.

Use a bit model in which elementary operations, input scans,
temporary writes and output copies have charged counts.
A single elementary operation touches a bounded number of bits;
large-integer arithmetic is performed by finite bit operations.
All encoded inputs, bounds, rights and installed timing guarantees
must be present before use. Memory backing and readability persist
through the specified terminal use, including all its latency and
output. No indefinite retention or future grant is implicit.

**Theorem 22.2 (finite calculation and its report).**
Under Definition 22.1 and $P_\Sigma<g$, a finite computation from $R$
produces a rational piecewise-affine nominal path for
$(\bar K,\bar Y-y_0)$, with the original time breakpoints; the rational
certificate $P_\Sigma,\mathcal E$ of (19.2); and the exact rational
scalar endpoint interval (21.1) and radius $Q_\Sigma$ on exact P.
It also produces a certified rational bound for
$\mathcal E/\sqrt T$ and the original-schedule guard certificate.
The report is an approximation/certificate for the actual execution;
it does not select a point within its compatible-error set.

More explicitly, let $q\ge2$ bound the binary length of each rational
numerator/denominator and integer in the report input, including
source parameters, $m,N$, all caps and rational bounds for $C,L$,
and also the total length of its fixed metadata/certificate header.
An owned sequential report-input block stores this header and
the $J_i,\xi_i$, schedule and cap entries. It has $O((m+1)q)$
bits and is written with the issued tape; this copy is charged.
The full fair record and table remain in separate retained blocks.
The report need not rescan them or obtain random-access rights;
any additional scans, if performed, are included in §22.3's counts.
There is a source-independent constant $C_2$ for sufficient extra
quotas

$$
 U_{\rm rep}\le C_2(m+1)^4(q+1)^4,\qquad
 L_{\rm rep},O_{\rm rep}\le C_2(m+1)^2(q+1)^2.
\tag{22.1}
$$

The first is a bit-operation bound, the second bounds peak workspace
plus report bits and its complete output length. Input scans and
total temporary/output writes can each be bounded by
$C_2(U_{\rm rep}+L_{\rm rep}+(m+1)q)$ after enlarging $C_2$.
These are sufficient finite bounds, not optimal complexity claims.

Proof. The lattice heights are rational
$k_0+(J_i-j_0)h$. Formula (18.1) uses a fixed number of rational
operations at each such height. Its denominators are nonzero by
the strict source certificates. Rational upper bounds for $C,L$
can also be obtained by bounding the explicit rational coefficients
and their derivatives on $[l,u]$: the positive denominator
$H(k-a_\kappa)$ has a rational lower bound, and every polynomial
numerator is bounded by the sum of its coefficient magnitudes
times powers of $\max(1,|l|,|u|)$. Sum component bounds to bound
the Euclidean norm. This needs no exact norm or real-number oracle.

Compute the three-vector prefix sums
$\sum_{j\le i}z\xi_jc(k_{J_j})$ exactly as rational fractions.
Insert them at the Q endpoints, interpolate on Q, interpolate the
height on P, and insert the original constant holds. This gives
the entire nominal path as a finite list of rational knots and
affine formulas. Compute $P_i,Q_\Sigma$ by prefix sums, and compute
the sum needed for $\mathcal E$ as
$\sum_iP_i=\sum_{j=1}^m(m-j+1)p_j$.
This avoids repeatedly summing fractions with previously accumulated
denominators. The scalar interval is rational even
when the unpolled initial phase reference is not. To report a
normalized bound, find a positive rational $s$ with
$s^2\le T<4s^2$, by comparing rational powers of four with the
positive rational $T$, and return $\mathcal E/s$.
This is a certified upper bound for $\mathcal E/\sqrt T$.
If the finer requested additive precision is relevant, rational
bisection of a square-root enclosure is finite and its additional
requested bit width is included in $q$ and the counts.
Further guard tests use the rational endpoints and bounds in §23.
For a supplied finite rational continuation the same arithmetic
terminates, with its actual intermediate bit lengths and extra
quotas charged there. Bound (22.1) concerns the original lattice
schedule, whose field-evaluation inputs have length $O(q)$;
it is not a complexity bound for arbitrary future rational heights.

A field evaluation uses integers of length at most a constant
times $q$. Without reducing fractions, a prefix sum of at most
$m$ such terms has numerator and denominator length $O((m+1)q)$:
denominator lengths add under multiplication, and addition
increases the numerator length by at most the sum of operand
lengths plus a fixed carry allowance. The stored $O(m)$ prefixes
therefore have total length $O((m+1)^2(q+1))$.
Grade-school integer operations on length $s$ use $O((s+1)^2)$
bit operations. A linear number of rational field evaluations,
prefix operations, bounds and schedule operations is consequently
within the more generous first bound of (22.1); memory and output
fit its second bound. Computing a power-of-four enclosure needs
$O(q+1)$ comparisons and stored exponent bits.
Performing every scan and temporary write as counted bit actions
gives the stated input/write bound. Table generation, random
sampling, precision provisioning and source enclosures are
separate already charged services, not hidden in (22.1).

Finally the report's certificate is valid for *every* admissible
actual profile by Theorem 19.1. On exact P its scalar interval is
the exact compatibility interval by Theorem 21.1. Thus exact
rational arithmetic computes the promised predictor without
computing an exact real actual outcome. If the optional initial
enclosure is supplied, adding its rational center and applying the
triangle inequality gives the absolute radius $r_0+\mathcal E$;
its input, calculation and storage are included in the quotas.
$\square$

**Theorem 22.3 (same-run finite acquisition, output and retention charges).**
In addition to QP (70.4), choose finite quotas $U,W,I,O,L$ that bound
all actual service counts on this run: calculation, *total* bit
writes, input/read bits, output bits and peak retained/workspace
bits. They include QP's $U_*,L_*,F_*=m(B+1)$; (22.1);
all metadata, status/event and certificate copies; and Definition
22.1's precision-provision counts. The fair bits are sampled once
and retained. One may bound the base total writes and scans by a
fixed multiple of $U_*+L_*+F_*+$ the finite input length, using
the stated bit model; a peak-memory bound alone is not a
total-write bound.

Partition these counts into preparation counts and terminal-use
counts, retaining $L$ as a common peak bound. Let $n_{\rm load}$
bound every loaded timed piece, including $4m+2$ original pieces
and any additional service instruction loads charged by its
declared service. An adequate sufficient allocation is

$$
\begin{aligned}
 \iota\ &\ge t_0+t_{\rm acc}
  +\frac{U_{\rm pre}}{r_{\rm cpu}}
  +\frac{F_*}{r_{\rm bit}}
  +\frac{W_{\rm pre}}{r_{\rm write}}
  +\frac{I_{\rm pre}}{r_{\rm in}}
  +\frac{O_{\rm pre}}{r_{\rm out}}
  +\frac{n_{{\rm load},{\rm pre}}}{r_{\rm load}},\\
 r_*\ &\ge t_{\rm port}
  +\frac{U_{\rm use}}{r_{\rm cpu}}
  +\frac{W_{\rm use}}{r_{\rm write}}
  +\frac{I_{\rm use}}{r_{\rm in}}
  +\frac{O_{\rm use}}{r_{\rm out}}
  +\frac{n_{{\rm load},{\rm use}}}{r_{\rm load}} .
\end{aligned}
\tag{22.2}
$$

All transition-latency inequalities still hold. Preparation computes
and stores the report while the source is held; terminal use reads
and outputs it after the scheduled last cell. Serial service and
rational padding realize exactly the *already chosen* $\iota,r_*$
and intervening schedule. If these inequalities fail, this readable
use is not supplied by those holds.

For finite nonnegative input/output tariffs $e_{\rm in},e_{\rm out}$,
a sufficient total energy/accounting quota is

$$
\begin{split}
 E_{\rm all}={}&\mathsf E_{\rm upper}^{*}+E_0+E_{\rm acc}
 +e_{\rm cpu}U+e_{\rm bit}F_*+e_{\rm write}W
 +e_{\rm load}n_{\rm load}+e_{\rm in}I+e_{\rm out}O\\
 &+(p_0+p_{\rm mem}L)\tau ,
\end{split}
\tag{22.3}
$$

where $\mathsf E_{\rm upper}^{*}$ is the right side of (19.6).
Any other declared finite-service tariff is added with its actual
quota. These tariffs are stipulated accounting units.
No energy law of a physical implementation is inferred from them.

Proof. Perform source enclosures, table calculation, sampling, tape
and certificate writes, precision provisioning, report calculation
and loads serially within the first inequality. It overpays
parallelizable work and counts input scans rather than granting
unlimited random access. Read the stored report through its owned
port and produce the finite output within the second inequality.
Use the installed terminal delimiter and scheduled service events;
no read of an unknown current time or actual source coordinate is
needed. The exact held-state premise makes this whole use refer
to one unchanged actual terminal state. Earlier finishing is padded
within the respective original hold. All active dynamics are those
of Definition 18.2.

The retained tape, report and calibration/reference fields remain
available through the last consuming event and its output copies.
Their bit-time is at most $L\tau$; the maintenance charges also
include every installation and terminal unit. Summing operation
tariffs, this bit-time upper bound and the native bound (19.6)
gives (22.3). Loss, revocation, expired backing or an uninstalled
precision service violates a premise and cannot be repaired by the
report computation.

When Theorem 20.1 is also claimed along a sequence, (20.1) is
required for these *same* enlarged paid holds. In particular neither
(22.1) nor a requested precision implies enough throughput to make
the hold fraction vanish. They give a finite conditional readable
consumer at each stage; the additional original-time regime must
be met independently. $\square$

**Proposition 22.4 (one simultaneous symbolic paid-report regime).**
On the rational-source subdomain, use QP (70.7), including
$m_n=n^4$, $\iota_n=n$, $r_{*,n}=1$, and request
$p_{i,n}\le n^{-7}$, $q_{i,n}\le n^{-4}$.
Choose all reported bounds with $q_n=O(1+\log(n+1))$.
Assume the precision service actually guarantees Definition 18.2
at these caps, with all its operation/input/output/memory counts
at most $n^2$, $E_{{\rm acc},n}\le n^2$, $t_{{\rm acc},n}\le1$, and
$t_{{\rm port},n}\le1/2$.
Retain QP's source and latency premises, and grant every service
throughput in §22 at least
$C_3n^{20}(1+\log(n+1))^{16}$ for a sufficiently large fixed $C_3$.
There are finite quotas satisfying (22.2) for all sufficiently
large $n$, with all the original holds unchanged.
The complete joint regime (20.1), actual discrepancy limit and
finite readable terminal use then hold simultaneously.

Proof. The report-input block has $O(n^4(1+\log n))$ bits.
Equation (22.1) bounds report computation by
$O(n^{16}(1+\log n)^4)$ and peak/report-output bits by
$O(n^8(1+\log n)^2)$.
Total bit writes and scans fit the former bound.
QP (70.8)'s base counts and the precision-service counts are
smaller. A finite bit implementation needs at most a fixed
multiple of its operation count plus original piece count
for its additional instruction loads.
Divide these sufficient counts by the displayed throughputs
in (22.2). Preparation work takes $o(1)$ beyond its bounded
setup times and fits in $\iota_n=n$; terminal read/copy/output
work takes $o(1)$ beyond $t_{{\rm port},n}\le1/2$ and fits
in $r_{*,n}=1$. Retain all record/report bits through that use.
For bounded fixed tariffs (22.3) is, for example,
$O(n^{16}(1+\log n)^{16})$: native energy is $O(n^4)$
by (19.6), and bit-time is at most
$O(n^8(1+\log n)^2)O(n^2)$.
All these quotas are finite and may diverge.
QP (70.7) still gives (20.1), and Corollary 20.2 gives the
vanishing actual discrepancy. This proves compatibility of
the declared inequalities only. In particular the assumed
accuracy guarantee and growing throughputs are service
premises, not a construction or installation theorem for
an actuator. $\square$

## 23. Independent views, agreement and finite same-source continuation

**Definition 23.1 (four views and their different exposed data).**
For the one actual process of Definition 18.2 define the space view
at original time $t$ to be

$$
 \mathsf S_t=(K^*(t),[Y^*(t)])
       \in\mathcal J_\kappa\times(\mathbb R/2\pi\mathbb Z)^3 .
\tag{23.1}
$$

Its phase metric is the quotient of the original Euclidean metric;
a continuous lift along this process is fixed by INITIAL for the
error certificate. The space view is an actual source coordinate,
not a freely readable port. No physical spatial axes are assigned
to these coordinates.

The time view $\mathsf T_t=t$ is original elapsed duration from the
start of installation, independently of source displacement. At a
specified owned completed delimiter it is the sum of the installed
rational piece durations through that delimiter. The record port
has no query for an otherwise unknown current time.

For a prescribed future relative numerical command $\gamma$ with
duration $S$ and a particular covered future error realization,
write $a_\gamma^*(s)$ for its actual relative height path, starting
at zero. With $\mathcal J_\kappa=(j_-,j_+)$, the actual boundary/guard
view includes permission and the predicate

$$
 \mathsf B_t(\gamma,a_\gamma^*)=
 \left[
 \gamma\hbox{ is currently granted},\
 j_-<K^*(t)+\min_{s\le S}a_\gamma^*(s),\
 K^*(t)+\max_{s\le S}a_\gamma^*(s)<j_+
 \right].
\tag{23.2}
$$

An $I$-restricted task additionally uses the analogous inequalities
with $l,u$. This is N's actual whole-command domain, not merely
endpoint membership. With an uncertain actuator, guaranteed
lawfulness of an issued command means (23.2) for *every* allowed
future realization. No evaluation of a hidden future error or
source coordinate is thereby made available.

The retained-memory view $\mathsf M$ exposes only the owned finite
$R$, its report and its completed event fields, with the stated
read, backing and reference-retention rights. Error profiles and
actual phase lifts are absent. Its purpose is to issue a certified
approximation at a known delimiter and choose granted future
commands with a proved sufficient margin. It is not defined as
the inverse of any of the other three views.

**Theorem 23.2 (approximate recovery and route agreement at held cuts).**
Under §§18--22, at the terminal held cut the readable report gives
an exact elapsed duration from its completed delimiter, an actual
height interval $[\bar K-P_\Sigma,\bar K+P_\Sigma]$, and an actual
three-phase lift-increment ball of radius $\mathcal E$ centered at
$\bar Y-y_0$. Its space error in the product Euclidean/quotient
metric is at most $(P_\Sigma^2+\mathcal E^2)^{1/2}$.
This compares the actual state with the nominal state aligned to
INITIAL; without numerical INITIAL calibration, only the increment
ball is a numerical phase output.
The exact time is the recorded delimiter's time; the report does
not query the current time at an arbitrary later point in the hold.
On exact P the scalar report is the attained interval (21.1).
With the optional numerical INITIAL enclosure, replace the reported
phase radius by $r_0+\mathcal E$ and use its numerical center in
the product-space bound; (19.2)'s actual-versus-nominal radius stays
$\mathcal E$.

Computing the report by the chronological prefix sums, or composing
its rational nominal P/Q pieces and then taking the endpoint,
gives exactly the same nominal center, time and scalar interval.
For any two covered actual executions with that same record,
their corresponding lift/space discrepancies are at most twice
the stated radii. Thus the actual routes agree to these certified
errors; they are not asserted to have equal actual outcomes.
The continuation rule below supplies a sufficient recovered subset
of the actual guard, not its exact unknown boundary.

Proof. Time at a completed delimiter is its installed duration sum.
The height and phase claims are (19.2), and projection to the torus
cannot increase distance. P adds precisely its relative height
increment to the nominal state and leaves nominal phases fixed;
Q adds precisely $B_ic(k_{J_i})$ and leaves nominal height fixed.
Induction on the original chronological list therefore gives exactly
the prefix sums in Definition 18.1, including its zero-motion
holds. Projection by (21.3) gives the scalar nominal center.
The interval radius is the same sum of $q_i$ in either calculation.
A triangle inequality through this common nominal path proves
the two-actual-execution bounds. These facts use one record,
reference and INITIAL; they do not compare optima attained by
different sources. $\square$

**Theorem 23.3 (lawful finite continued use with the same actuator).**
Suppose the report is used during the original terminal hold and,
after that hold, a finite additional list of rational P pieces,
Q pieces and exact holds is granted on this same live source.
The list may be a finite computable function of the actually
read record/report; all its selector inputs and calculations
have the paid access and timing of §22. Each active piece has
a positive rational duration $d_j^f$, signed nominal displacement
$A_j^f$ for P or $B_j^f$ for Q, and error cap $p_j^f$ or $q_j^f$.
Its actual speed error is bounded by its cap divided by $d_j^f$,
with the same exact-field, exact-hold and exact-switch specification
as Definition 18.2. Error dependence on old and new retained
inputs may again be arbitrary.
When compatibility over an entire error box is asserted, the same
continuation grant and service premises must hold throughout that
record's original and future error box; a grant conditioned on a
hidden actual outcome cannot be treated as a common grant.

Continue the nominal source from its old nominal endpoint.
For any future time $s$, let $P^f(s)$ sum all future P caps whose
pieces have begun, including the full cap of a current P piece.
A sufficient finite robust guard is

$$
 l+P_\Sigma+P^f(s)<\bar K^f(s)
                 <u-P_\Sigma-P^f(s)
       \quad(0\le s\le S).
\tag{23.3}
$$

On each affine/constant piece the same inequalities can be checked
at its endpoints using the larger adjacent prefix cap, so this is
a finite rational sufficient certificate.
If it holds, every resulting actual concatenation is lawful in
$I$ and in the original native domain, and

$$
\begin{aligned}
 \sup_{s\le S}|K^f_*(s)-\bar K^f(s)|
    &\le P_\Sigma+\sum_{j\in P}p_j^f,\\
 \sup_{s\le S}|Y^f_*(s)-\bar Y^f(s)|
    &\le\mathcal E+
       L\sum_{j\in Q}|B_j^f|
          \left(P_\Sigma+\sum_{\substack{a\in P\\a<j}}p_a^f\right)
       +C\sum_{j\in Q}q_j^f .
\end{aligned}
\tag{23.4}
$$

Here $\bar Y^f$ includes the old nominal endpoint and $Y^f_*$ the
old actual endpoint; no initial error is discarded. If all original
and future P pieces are exact,
the accumulated scalar compatibility interval at any completed
future cut has nominal center
$\beta_R+\sum_{\text{completed }Q}B_j^f$ and exact radius
$Q_\Sigma+\sum_{\text{completed }Q}q_j^f$.

All future sampling, calculation, input/output, writes, loads,
precision provisioning, retention and latency require finite
additional quotas and scheduled holds. Their time is added to
$\tau$, and their native energy upper bound is

$$
 \sum_{j\in P}\frac{(|A_j^f|+p_j^f)^2}{\varepsilon^2d_j^f}
       +\sum_{j\in Q}\frac{(|B_j^f|+q_j^f)^2}{d_j^f}.
\tag{23.5}
$$

The service and bit-time tariffs are added as in (22.3) for the
extended retention interval. With no such continuation grant,
§22 asserts only finite terminal held-record use.

Proof. At the old terminal cut the actual height offset has
modulus at most $P_\Sigma$. Each future P piece increases its
bound by at most its cap; Q and holds do not change it.
This proves the first line of (23.4); applying the same partial
bound at every time proves lawfulness from (23.3).
On future Q piece $j$ height is fixed, and the old plus preceding
P offset has modulus at most the parenthesis in (23.4).
Subtracting the two phase increments as in (19.4) gives that
piece's contribution to the second line. Add the old phase
bound and sum all future Q pieces. Each true trajectory is the
original ODE solution for its own realized relative command.
N Theorem 9.2, or the exact additive-integral composition of
OriginalControlComposition, joins it to the actual earlier
history with both coordinates translated at the join.
Neither INITIAL nor the relative-control origin is reset.

For exact P, all completed Q displacement errors can again be
chosen independently throughout their allowed intervals.
Their Minkowski sum gives the asserted attained scalar interval.
A selector depending only on the shared readable record chooses
the same list for all errors in that record's fiber, so it
does not consume an unknown actual phase or height.
If (23.3) is not certified, the permitted report action can
return inconclusive and retain a hold; failure of this sufficient
test does not prove actual illegality.

Integrating the squared speed bound over each original future
duration proves (23.5). The same serial quotas as (22.2), now
including selection and new-input costs, suffice for finite
access and loads, provided their granted holds accommodate
them. Retaining the old record, added record, references and
report through their last use charges the full bit-time.
Thus mathematical composability is accompanied by the same
declared execution interface and finite paid use conditions.
There is no assertion of infinite continued precision, uniform
infinite-horizon storage, or a transport limit on a changed
future schedule without its own joint hypotheses. $\square$

**Proposition 23.4 (the remaining exact four-view obstructions).**
The approximate recovery above is not mutual exact recovery
of the independently defined four views.

If some $q_i>0$, memory, time and height-based guard data can
agree while actual space differs. If some P cap is positive,
the same record can also have different actual native guard
boundaries, whenever the distinguishing future P test is granted.
Even with zero errors, a terminal space/time/guard triple need
not determine the retained memory. Source displacement alone
does not determine elapsed time.

Proof. The first assertion is exactly the two actual executions
of Theorem 21.4. For the second, choose one P displacement error
$+a$ or $-a$, $a>0$ sufficiently small for Theorem 19.1, and all
others zero. The terminal heights are $\bar k+a,\bar k-a$.
Consider an exact future positive P displacement
$j_+-\bar k$, if granted. From the lower height its final
height is $j_+-a$ and every intermediate height stays in
$\mathcal J_\kappa$; from the upper height it reaches and
crosses $j_+$ and is not lawful. For the $I$-restricted boundary
use $u-\bar k$ instead. This tests actual extrema domains, not
an actual-boundary sensor. Granting only a smaller robust menu
can remove this particular test; it does not supply the missing
actual height.

For the memory assertion take $m\ge2$, exact execution, and a
height tape that stays at $j_0$ for two cells. Its dyadic stay
probability is positive, since its two off-diagonal probabilities
sum to less than one. The sign pairs $(+1,-1)$ and $(-1,+1)$
are both permitted and give exactly the same terminal phase,
height, duration and state-dependent native boundary, with
different retained records and different intermediate paths.
Finally any positive exact hold changes elapsed time with no
change of source position or its state-dependent native guard.
Thus no inverse of space alone supplies the clock.
These examples do not preclude the approximate certified
directions or the finite continued use just proved. $\square$

## 24. Finite-variation limits and exact supplier correspondence

**Theorem 24.1 (path information boundary with unrecorded execution error).**
At each finite stage satisfying Theorem 19.1's guard hypothesis,
every covered actual path is absolutely continuous and of finite
variation. For every measurable joint error law of Definition 18.2
on that domain, its actual full-path law is mutually
singular to both the continuous native Q law and the original
cemetery-inclusive killed reference on the same positive horizon.
Its relative entropy to that killed reference is $+\infty$.

Finite support, or a Shannon-entropy bound by the number of issued
fair bits, is not asserted for this enlarged actual error domain.
If error profiles are deterministic functions of the finite $R$
alone, finite support and the corresponding finite-record entropy
bound do hold. With unrecorded continuous error randomness they
can fail, even on exact P and within arbitrarily small positive
Q caps.

Proof. Theorem 19.3 gives finite variation, and integrating the
bounded active velocities on the finite schedule gives absolute
continuity. In particular the height has zero quadratic variation
along dyadic partitions. One direct proof is
$\sum(\Delta K)^2\le\max|\Delta K|\operatorname{TV}(K)$;
uniform continuity makes the maximum vanish.
Every actual history survives the horizon. The Borel event of
survival and zero terminal dyadic height quadratic variation
therefore has actual probability one.
Q has height quadratic variation $2\varepsilon^2\tau>0$.
The original reference has that same height quadratic variation
on its surviving paths, while its killed paths fail survival.
Both assign this event probability zero. This proves mutual
singularity, and failure of absolute continuity gives infinite
relative entropy. Weak convergence in (20.2) does not alter
this finite-stage separation.

A deterministic function of the $2^{m(B+1)}$ fair records has at
most that many values. Its discrete Shannon entropy is at
most $m(B+1)\log2$. But if $q_j>0$, choose a continuously
distributed $f_j$ in a nontrivial subinterval of $[-q_j,q_j]$
and constant speed $v_j=f_j/d_0$, all other errors zero.
Conditional on a fixed record, (21.3) makes the terminal scalar
increment an injective translate of $f_j$. The actual path law
is then nonatomic with infinitely many outcomes.
Those hidden error outcomes are not part of the retained tape;
a discrete entropy bound for the tape says nothing of this
actual path entropy. Disjoint full-measure carriers also do not
mean disjoint topological supports: finite-variation paths can
belong to diffusion support. $\square$

**Definition 24.2 (suppliers, hypothesis correspondence and scoped delta).**
The following correspondence fixes the ordinary-mathematics
provenance of §§18--24.

QP §§69--73 are used at the pinned source
[287302917d4083e0f5cf6157466b2b7fb93633e3](https://github.com/the-omega-institute/trureturing/blob/287302917d4083e0f5cf6157466b2b7fb93633e3/docs/develop/theory/FIB_NATIVE_LONG_TIME_PHASE_QUANTITATIVE_BOUNDS.md);
the full QP source has Git blob
$69f6690a573f95d9d7de6b9dc7d646a5bd2355d6$, identical to the
QP source at $7533e397dbc754bbfd4de3f9d33a434390a84413$.
QP Definition 69.1 supplies the signed coefficients, original
metric, fixed preparation/calibration and immutable INITIAL;
Assumption 69.2 supplies the conditional rights, fair bits and
finite services. Its *scalar exactness* is the single execution
premise replaced in Definition 18.2, while exact fields, holds
and timings remain premises. QP Definition 69.3 and Theorem 70.1
supply the issued lattice/table/tape, rational schedule and
nominal prefixes. QP Lemma 71.1, Proposition 71.2 and Theorem 72.1
supply the nominal uniform occupation, simultaneous limit and
endpoint covariance; their $h,e,\alpha,T,m2^{-B},\omega$ conditions
are exactly (20.1), not a sequential-limit substitute.
QP Corollary 72.2 supplies the selected analytic Q consumer only
under its original selection hypotheses. QP Proposition 73.1's
finite-support claim is restricted to deterministic finite-record
images in Theorem 24.1.

The underlying source suppliers at that same pinned repository
revision are G Definition 25.1, D Definitions 35.1, 37.1,
D Theorems 36.1, 39.1 and 50.1, and N Definition 9.1,
Theorem 9.2 and Proposition 10.2. Respectively these supply
the original signed probabilities/fields and killed reference;
the Q height/phase law; positive signed original tensor;
the primitive identity (21.3); and the actual partial
relative-command action, extrema guard, chronological joins
and original-time energy. The real lift is the winding cover of
these same actual phase periods. The added scalar errors never
change a field coefficient, source mean, sign convention or
absorbing face.

The existing formal-source pairs
[D5 OriginalControlComposition](../../../D5/S3/Quantum/Fibers/OriginalControlComposition.lean)
and its [owning Scribe](../../../Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.scribe.cs)
supply the original-control definition and exact translated
concatenation/additive weighted integrals.
Its private absolute-continuity helpers and concatenation
proof concern exact given controls; they supply no execution
accuracy, record acquisition or speed-error threshold.
[D5 QuantizedWordApproximation](../../../D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.lean)
and its [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.scribe.cs)
supply a different general result: total Lipschitz action maps,
a supplied global quantizer and finite-word geometric errors.
Its initialization $Q(x)$ and effective quantizer evaluation are
extra premises. They supply neither an acquired actual state
here nor the partial-command margins and scalar exact interval.
No global contraction of native Q is assumed in this appendix.
[D5 GuardedPhaseExecution](../../../D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.lean)
and its [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution.scribe.cs),
including its private path-splitting helpers, concern exact
discrete instruction epochs and one supplied observation field;
their guard is not a physical scalar-actuator tolerance.
[D5 NativeCommandLifetime](../../../D5/S3/Analytic/Probability/NativeCommandLifetime.lean)
and its [owning Scribe](../../../Blueprint/D5/S3/Analytic/Probability/NativeCommandLifetime.scribe.cs),
including its private chord, absolute-continuity and actual-lifetime
helpers, concern a different killed two-phase finite-sign model.
They do not supply the signed three-phase field (18.1), its scalar
execution-error interval, or the simultaneous consumer (20.1).

The present volume §§7--9 supplies paid simultaneous actual
samples, double-wall area/winding approximation and cumulative
future-loop error under its own source and sampling hypotheses.
Those are retained as existing results. The signed nonzero
single-wall source (18.1), owned *issued* record, absence of
actual error samples and full original-time long-time regime
here are different. The report in §22 uses rational source
data, not that double-wall unwrapping or quantum acquisition
port. [Paid point-observation tracking](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md)
§§50--54 likewise requires actual wrapped observations of an
unknown evolving source and its conditional bridge; no such
port is supplied by the issued record.

The atomic [boundary trichotomy volume](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md)
through ABT43 and [global-port orientation volume](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md)
have actual finite-tree read/update, source-binding, rights and
retention contracts. They are existing conditional acquisition
and continuation results for those sources. Their source
bindings and ports are not an actuator, source-state read or
accuracy guarantee for (18.1). Similarly the newly public
[quadratic-clock report-design §29](https://github.com/the-omega-institute/trureturing/blob/47057d2811fa29daa5468afe7ff20d86c6a5c5b7/docs/develop/theory/FIB_UNCALIBRATED_QUADRATIC_CLOCK_UNIFORM_REPORT_DESIGNS.md)
has common quadratic gain/offset, bounded report noise, and
an exact retained-index risk staircase. None of these is
the native speed-error box (18.2); its exact minimax theorem
is not used to supply (21.2) or a known current clock.
The public Circle ThreeRowParameters/ThreeRowScheduler/
ThreeRowSource expositions at
$b9295ac6746476e54f67337977be4af1b154f778$ concern complete
physical-label permutations at a half-modulus strip.
The identity-factory library note at that revision concerns
finite weighted Möbius identities and a signed Robin-kernel
boundary. Neither has the source, actuator, record or metric
hypotheses required here, and neither is used as a supplier.

Classical intermediate tools are the norm bound for an integral,
the triangle and Cauchy--Schwarz inequalities, and the two-point
absolute-loss lower bound. The pinned mathlib revision
$56a005855ea17e0b0958f73ec801ae140b0a1679$'s Bochner integral
source supplies integral addition and norm estimates; these
are not claimed as new results.
For the probability limit QP already applies Whitt,
*Proofs of the martingale FCLT*,
[arXiv:0712.1929v2](https://arxiv.org/abs/0712.1929v2),
Theorem 2.1(ii), with dimension three, vanishing bracket and
squared martingale jumps and predictable cross brackets
$2s\widehat M_\kappa$. That primary theorem concerns a local
martingale; arbitrary tape-dependent actual errors do not
satisfy its premise merely because the nominal signs are fair.
Theorem 20.1 instead transfers QP's established nominal result
by the proved strong discrepancy and explicit second-moment
estimate. QP's discrete Doob/taboo normalizations retain their
credited Chetrite--Touchette and Mazzolo source correspondence;
no new conditioned-process theorem is needed here.

Relative to precisely these repository suppliers, the additional
content is the signed native all-prefix error tube (19.2),
its same-run transport/covariance transfer, the attained
retained-record scalar ambiguity and necessary-and-sufficient
worst-case accumulated Q scale, and the finite rational
held-use/continuation composition with all its paid access
conditions. These are repository-derived conditional ordinary
proofs. This is a scoped comparison with the named source
contracts, not a claim of worldwide literature absence,
new Lean certification or a universal recovery theorem.

**Definition 24.3 (material limits of the conditional bridge).**
Exact source calibration, installed actuation accuracy and
timing, fair-bit service, owned record access, retention,
finite throughputs, rights and nondisturbance remain granted
premises. Neither the numerical accuracy requests nor their
symbolic feasible scales acquire any of them. Unknown
calibration, hold drift, timing errors, cross-field errors,
external-source tracking, arbitrary archived history and
unknown phase-reference acquisition are outside this
error domain. Without vanishing discrepancy, no centered
joint transport conclusion follows from nominal or marginal
data alone; Theorem 21.3 supplies an exact worst-case failure
within the declared domain.

The continued-use properties are only (23.3)--(23.5) with
the same stipulated actuator, current grants and retained
backing. They do not recover hidden exact outcomes, all
actual boundary decisions, unobserved time, or the old
record from space. The entropy-rate and shrinking-slab
selection gaps remain those of QP §§52--64; this appendix
does not turn finite-variation commands into finite-entropy
continuous Q histories. Physical spatial interpretation,
same-source nonlinear spatial realization, recursive/gluing
spectral stability, broader internal observers and the
universal generation/identification of these services by
alpha/beta relations retain their independent obligations.
The original fixed-model results and the four-expression
programme are not completed or narrowed by this conditional
execution-and-record bridge.

## 追加锚（本行以下为增补区）
