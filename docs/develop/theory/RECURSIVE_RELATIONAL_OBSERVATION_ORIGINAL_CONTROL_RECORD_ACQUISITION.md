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
