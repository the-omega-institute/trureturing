# Recursive relational observation: original-control event memory and coarse aliasing

> **Machine contract.** This is a `generic-v1` theory reference volume.
> Locators are determined from its own Markdown bytes. Once merged, its
> existing text is append-only: corrections and further results go after
> the terminal append anchor, with another terminal anchor retained.

## 1. Scope, consumer and mathematical provenance

This volume separates preservation of an actually acquired stopping event
from reconstruction of a terminal probability law. It gives a smooth
original-control source for a sharp finite-memory timestamp test, and an
opposite-orientation control pair for every finite fixed time partition.
The pair has exactly equal binned CP instruments but a fixed nonzero
exact-time separation. Both statements concern the canonical double-wall
stopped instrument already supplied by
[Instrument Boundaries](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md),
§5.2. They do not enlarge its ideal operation class.

The concrete consumers are retention of the actual joint archive in
[Quantum Carrier Minimum](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md),
§§1.3, 3.1 and 6, and the actual running image in
[Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md),
§34. The approximation consumer is the complete marked-law or quantum
output metric of
[Instrument Stability](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md),
§1. These consumers distinguish an old event from a newly drawn event
having the same marginal distribution.

These are ordinary mathematical proofs. This source carries no new
Lean/kernel verification, physical implementation or full-programme completion.
Lean declarations and Blueprint applications below are credited suppliers.

All repository suppliers are selected at the immutable revision
`5094da88f161741b61de3b6b16dbc3a115a83d63`. Mature finite-dimensional
quantum guessing, elementary CP postprocessing and the supplier's triangular
signed-loss construction are credited. The additional deductions are their
explicit applications to this source and these event/archive consumers.
No worldwide originality claim is made.

## 2. The original source and the exact recording interface

**Definition 2.1 (unchanged source and restricted examples).** For a valid
base $b=(X,Y,Z)$ put $r=1-Z$. The source of
`FiniteRectangleTransport` has

$$
\begin{aligned}
&0<Z<1,\quad 0<X,Y<r,\qquad
J(b)=(\max(0,X+Y-r),\min(X,Y)),\\
&p_b(k)=(r-X-Y+k,X-k,Z,Y-k,k),\qquad
d=(1,-1,0,-1,1),\\
&I_b(k)=\sum_{i\in\{0,1,3,4\}}p_b(k)_i^{-1},\qquad
w_b(k)_i=\frac{d_i}{p_b(k)_i I_b(k)}.
\end{aligned}
\tag{EM.1}
$$

Index $4$ denotes original mode $13$. An original control has finite
$T\geq0$, continuous real $k,\chi$ on $[0,T]$, strict $k(t)\in J(b)$,
finite variation of $\chi$, and either absolute continuity of both
coordinates or the supplied finite-piecewise-$C^1$ alternative with
continuous rates on the closed pieces. The latter also implies absolute
continuity by piecewise integration and telescoping. With a common
compatible initial real lift $\theta$, the actual transported lift is
$\theta_i+\int_0^t w_b(k(u))_i\chi'(u)\,du$; the state convention uses
its negative complex phase. A based phase loop retains every signed integer
$m$ in $\chi(T)-\chi(0)=2\pi m$.

The theorems here select the double wall

$$
b=(c,c,Z),\qquad 0<c<1/2,\qquad Z=1-2c,
\qquad p(k)=(k,c-k,Z,c-k,k),\quad 0<k<c.
\tag{EM.2}
$$

They select constant current phase, not a replacement for the original
all-sector class. The source, preparation, base, clock and calibrated
reference where supplied are common within each comparison. Unknown past
phase, winding and preparation parameters are never decoder inputs.

**Definition 2.2 (credited canonical complete instrument).** Fix
$k(0)=a\in(0,c)$. For one prescribed original control define

$$
\begin{aligned}
H_i(t)&=\int_0^t w_b(k(u))_i\chi'(u)\,du,\\
\lambda(t)&=\frac{(k'(t))_+}{k(t)}
             +\frac{(-k'(t))_+}{c-k(t)},\qquad
S(t)=\exp\left(-\int_0^t\lambda(u)\,du\right),\\
K_t&=\sqrt{S(t)}\operatorname{diag}_i
 \left(\sqrt{\frac{p_i(k(t))}{p_i(a)}}e^{-iH_i(t)}\right),\\
g_i(t)&=\lambda(t)-(\log p_i(k(t)))',\qquad
J_i(t)=\sqrt{g_i(t)}\,|f\rangle\langle i|K_t.
\end{aligned}
\tag{EM.3}
$$

Here $g_i\geq0$ almost everywhere and $f$ is the absorbing stopped
successor. The complete terminal output is either success, with
$K_T\rho K_T^\dagger$, or the exact first failure time $t$, original mode
$i$, and $f$, with CP density $J_i(t)\rho J_i(t)^\dagger$. Every Borel
time/mode event is retained. On a common joint reference $R$ write
$\rho_{ii}^R=\langle i|\rho_{LR}|i\rangle\geq0$.

The credited loss identity, for every common input with diagonal $p(a)$,
and its full-reference CP consequence are

$$
\begin{aligned}
F_i(t)&=p_i(a)-S(t)p_i(k(t)),\qquad f_i=F_i',\\
\mathcal I_i(E)(\rho_{LR})
 &=\frac{\int_E f_i(t)\,dt}{p_i(a)}
       |f\rangle\langle f|\otimes\rho_{ii}^R.
\end{aligned}
\tag{EM.4}
$$

The first line describes a whole law, not one emitted sample. For the
second line arbitrary common live inputs and normal trace-class references
are allowed. It follows directly by cancelling the phase of the single
nonzero jump column. Both identities are supplied by Instrument Boundaries
§§9–11 and are reused here.

Prescribed waveforms, calibrated Kraus operations, blank ancillas and exact
time/mode recording remain declared ideal services. No waveform sensor,
free environment port, whole-law oracle, repeated same-history copies,
tomography, reset, reversal or post-failure retry is supplied. A failed run
has its executed prefix and then $f$; its unperformed live tail is not an
executed history.

**Convention 2.3 (complete joint fields and lawful menu).** A complete
boundary retains the actual joint source/preparation/epoch identity,
archives, clock and alignment, calibration and reference, permissions,
controller and pending programme, every acquired event and every input
used for selection or update. These fields may be correlated; equality of
their separate marginals does not assert equality of that joint boundary.
On a live cut, the existing mathematical over-menu consists of permitted
prescribed original controls at the same base and matching height, with
relative real phase commands, either original regularity alternative and
any finite duration, including zero. Actual permission guards still apply.
An illegal request is unexecuted, with its declared visible rejection;
it is distinct from a performed failure. On failure, the exact old event
and $f$ remain, with only the supplied absorbing/stopped continuation.

`concatenate_original` gives the unchanged literal prefix and actual tail
$\chi(T+u)=\chi(T)+\chi_{\rm tail}(u)-\chi_{\rm tail}(0)$ at a matching
height, and adds the real increments and weighted integrals. This identity
does not reveal $\chi(T)$ to a controller. Feedback uses only actually
acquired records and the declared inputs. A different source-sensitive
programme archive or guard cannot be deleted to invoke an equality below.

**Definition 2.4 (two exact output distances).** On
$\Omega_T=\{\mathsf s\}\sqcup((0,T]\times\{0,1,2,3,4\})$ let
$d_{\rm mark}$ be total variation, in the probability convention, of the
complete source-family marked laws. For a common normalized live input
with any common reference define

$$
\begin{aligned}
D_\rho(\gamma,\widetilde\gamma)=\frac12\bigg(&
 \|\omega_{\gamma,\mathsf s}(\rho)
       -\omega_{\widetilde\gamma,\mathsf s}(\rho)\|_1\\
 &+\sum_i\int_0^T
 \|\omega_{\gamma,i}(t;\rho)
       -\omega_{\widetilde\gamma,i}(t;\rho)\|_1\,dt\bigg),\\
d_{\rm op}(\gamma,\widetilde\gamma)&=\sup_{R,\rho}D_\rho(\gamma,\widetilde\gamma).
\end{aligned}
\tag{EM.5}
$$

These are precisely the supplier's terminal-output metrics. Arbitrary
tests of this declared output are part of their mathematical definition;
no additional laboratory measurement permission is inferred. Exact time
is a measurable classical variable, not an uncountable Hilbert basis.
The actual-event recovery metric in §4 instead compares two coordinates
coupled to one and the same acquired input event.

## 3. A fixed smooth programme with a uniform acquired failure time

**Theorem 3.1 (explicit original-control event source).** Take

$$
c=2/5,\qquad Z=1/5,\qquad a=1/10,\qquad T=1,
\qquad k(t)=\frac{a}{1-t/2},\qquad \chi(t)=\chi(0).
\tag{EM.6}
$$

Use one fixed positive coherent preparation with diagonal $p(a)$ and a
compatible initial lift. This smooth control satisfies both original
regularity alternatives, all five probabilities are at least $1/10$,
$|k'|\leq1/5$, and phase variation is zero. Its canonical instrument has

$$
\begin{aligned}
S(t)&=1-t/2,\\
(F_0,F_1,F_2,F_3,F_4)(t)
 &=(0,ct/2,Zt/2,ct/2,0),\\
\Pr(\mathsf F)&=1/2,\qquad
\mathcal L(\tau\mid\mathsf F)=\operatorname{Unif}(0,1],\\
\Pr(i=1\mid\mathsf F)&=c,\quad
\Pr(i=2\mid\mathsf F)=Z,\quad
\Pr(i=3\mid\mathsf F)=c.
\end{aligned}
\tag{EM.7}
$$

Here $\mathsf F$ is the actual performed-failure event. Conditional on
$\mathsf F$, time and mode are independent. Modes $0,4$ never fail in
this example, and every failure has successor $f$.

**Proof.** Set $s=1-t/2$. Then $s\in[1/2,1]$,
$k'=a/(2s^2)>0$, $a\leq k\leq2a=1/5$ and
$\lambda=k'/k=1/(2s)$. Integrating the hazard gives $S=s$.
The probability band and derivative bound follow at once; the rational
formula extends smoothly across the closed interval, and the phase is
constant. In particular the actual transported phase increment is zero.
The original regularity and strict positivity conditions are verified
without replacing the source by its law coordinate.

Since $Sk=a$, (EM.4) gives zero loss in modes $0,4$. For mode $1$,

$$
F_1=(c-a)-S(c-k)=c(1-S)=ct/2.
$$

Mode $3$ has the same expression, and $F_2=Z(1-S)=Zt/2$.
Their sum is $t/2$, because $2c+Z=1$. Thus
$\Pr(\tau\in E,i\mid\mathsf F)=q_i|E|$ for Borel
$E\subseteq(0,1]$, where $(q_0,q_1,q_2,q_3,q_4)=(0,c,Z,c,0)$
and $|E|$ is Lebesgue measure. This proves uniformity and independence.

For completeness, its terminal success operator and failure CP densities
on arbitrary common inputs are

$$
\begin{aligned}
K_1&=\operatorname{diag}(1,1/\sqrt3,1/\sqrt2,1/\sqrt3,1),\\
\omega_i(t;\rho_{LR})
 &=r_i|f\rangle\langle f|\otimes\rho_{ii}^R,\qquad
(r_0,r_1,r_2,r_3,r_4)=(0,2/3,1/2,2/3,0).
\end{aligned}
\tag{EM.8}
$$

Integrating the last line and adding $K_1^\dagger K_1$ gives identity
mode by mode. Therefore the claimed event distribution is part of the
entire performed instrument, with its failure branches included, rather
than a law obtained by discarding failures. $\square$

The programme can be fully known to both encoder and decoder in the next
section. No unknown-programme identification is needed to obtain the
memory lower bound. The ideal recording service is still conditional;
(EM.6) is a mathematical source realization, not a physical clock or
detector construction.

## 4. Actual-event recovery through finite classical–quantum memory

**Definition 4.1 (all accessible assistance is in the retained memory).**
After the actual record in Theorem 3.1 is acquired, consider a coding
interval ending at the fixed terminal clock $1$. The joint information
accessible to the decoder factors through the finite algebra

$$
\mathcal B=\bigoplus_{\alpha=1}^n M_{d_\alpha},\qquad
n<\infty,\quad d_\alpha\geq1,\qquad
D=\sum_{\alpha=1}^n d_\alpha,\quad d=\max_\alpha d_\alpha.
\tag{EM.9}
$$

A state of $\mathcal B$ is a normalized block-diagonal density operator
on $\bigoplus_\alpha\mathbb C^{d_\alpha}$. $D$ is its total Hilbert
dimension, not its matrix-space dimension $\sum_\alpha d_\alpha^2$,
and not just the largest live block $d$.

The code may use the entire actually acquired time, mode and other
available joint inputs in preparing this state. Every source-dependent
register accessible across the interval is included jointly in (EM.9):
classical branches, mode records, clock latches, programme/controller and
archive states, ancillas, returned environments and timing ports. A
receiver's retained share of prior entanglement is also included if it
can assist decoding. It cannot be excused from this joint count because
its marginal was initially input-independent. An inaccessible reference
may remain, but cannot assist either channel. Fixed metadata and fresh
input-independent local randomness supply no missing event value.
Independent shared classical randomness is allowed by conditioning the
following proof on it and averaging. No outcome is removed by
postselection or by a state-dependent choice of decoder.

This is an explicit finite-memory factorization hypothesis. A decoder
reading an uncounted continuously running event-sensitive clock, old log,
programme pointer, external event copy or environment does not meet it.

**Definition 4.2 (same acquired event, not just a marginal).** For
$M\geq1$ partition $(0,1]$ into equal half-open bins
$I_x=((x-1)/M,x/M]$, $1\leq x\leq M$. Conditional on the actual
$\mathsf F$, let $X_M=x$ mean $\tau\in I_x$. Let a common decoder
of (EM.9) return $\widehat X_M$. Its event-preservation error is

$$
\Delta_M=\operatorname{TV}\bigl(
 \mathcal L(X_M,X_M\mid\mathsf F),
 \mathcal L(X_M,\widehat X_M\mid\mathsf F)\bigr).
\tag{EM.10}
$$

The first coordinate is the mathematical actual input label in both
couplings. It is not another copy or sensor supplied to the decoder.
The ideal second coordinate copies that same event. An abort or an output
outside the declared labels counts as incorrect. This metric is stronger
than matching the decoded marginal distribution.

**Theorem 4.3 (sharp bin-label capacity for this acquired event).** For
every $M\geq1$ and every code satisfying Definition 4.1,

$$
\begin{aligned}
\Pr(\widehat X_M=X_M\mid\mathsf F)&\leq\min(1,D/M),\\
\Delta_M&\geq\max(0,1-D/M).
\end{aligned}
\tag{EM.11}
$$

Both bounds are attained for the abstract task of retaining and decoding
the bin label alone, with already acquired exact input data and calibrated
encoding/decoding. Therefore conditional error at most $\delta<1$
requires $D\geq(1-\delta)M$. If $n\leq2^B$ and every block is at
most $d$ dimensional, a necessary condition is

$$
B+\log_2 d\ \geq\ \log_2 M+\log_2(1-\delta).
\tag{EM.12}
$$

This is a retained-information bound, not an acquisition, hardware, energy
or programme-description bound. Sharp attainment for this one label does
not assert simultaneous optimal retention of mode, controller and all
other archive fields at the same $D$.

For a concrete distinction, $M=1,D=1$ permits perfect bin-label retention.
It does not permit perfect retention of the actual mode in (EM.7): a
one-dimensional normalized memory state is constant, so any decoded mode
is independent of that input mode and has correct-guess probability at
most $\max(c,Z,c)=2/5$. Thus extending the sharp-attainment assertion
to the full event archive at the same dimension would be false already
in this displayed source.

**Proof.** By Theorem 3.1, $X_M$ is uniform on $M$ labels. Average the
encoded density operator over the actual conditional times, modes and any
other joint inputs given $X_M=x$ and $\mathsf F$; denote the resulting
normalized state by $\sigma_x$ on the $D$ dimensional embedding of
(EM.9). The common decoder induces a POVM $\{E_x\}$; additional abort
effects can be included or assigned to one label for an upper bound.
Because $0\leq\sigma_x\leq I$, positivity gives

$$
\Pr(\widehat X_M=X_M\mid\mathsf F)
 =\frac1M\sum_x\operatorname{tr}(E_x\sigma_x)
 \leq\frac1M\sum_x\operatorname{tr}E_x\leq\frac DM.
\tag{EM.13}
$$

Probability is also at most one. This is the mature finite-dimensional
quantum guessing inequality, here proved directly for arbitrary block
dimensions. In particular the set of possible code states need not be
finite: a continuum of exact density matrices still satisfies (EM.13).

Write $q(x,y)$ for the actual coupled output law. Its first marginal is
$1/M$, hence $q(x,x)\leq1/M$. The half-$L^1$ distance from the ideal
diagonal law equals

$$
\frac12\left(\sum_x(1/M-q(x,x))
                   +\sum_{x\ne y}q(x,y)\right)
 =1-\Pr(\widehat X_M=X_M\mid\mathsf F).
\tag{EM.14}
$$

Abort mass is included in the off-diagonal term. This proves the second
bound. For attainment, enumerate an orthonormal basis across the direct
summands and use $\min(D,M)$ basis states for that many distinct labels.
If $D<M$, send every remaining label to the first basis state; decoding
the selected basis labels gives exactly $D/M$ correct probability. If
$D\geq M$, use distinct basis states for all labels. This construction
lies in the block-diagonal algebra and needs no coherence between blocks.
It proves sharpness only for the stated abstract label task.
Finally $D\leq nd\leq2^Bd$ gives (EM.12). $\square$

Nayak, Theorem 2.4(2), gives the general most-probable-input mass bound for
an $m$-qubit encoding. Its uniform-input specialization is the inequality
used here. Neither that inequality nor its elementary proof is claimed as
new. The source contribution is that the uniform label is the bin of an
actual stopped event of the smooth original programme (EM.6), with its
complete law and absorbing branch verified.

**Corollary 4.4 (exact continuous timestamp joint-TV obstruction).** For
every fixed finite $D$ in Definition 4.1 and every common decoder returning
a real time $\widehat\tau$,

$$
\Pr(\widehat\tau=\tau\mid\mathsf F)=0,\qquad
\operatorname{TV}\bigl(
 \mathcal L(\tau,\tau\mid\mathsf F),
 \mathcal L(\tau,\widehat\tau\mid\mathsf F)\bigr)=1.
\tag{EM.15}
$$

If the actual success/failure flag is retained, the unconditional complete
joint archive error is at least
$\tfrac12\max(0,1-D/M)$ for $M$-bin event recovery, and at least
$1/2$ for exact continuous-time event recovery.

**Proof.** Bin any real decoded output using the same $M$ bins, assigning
outside values an extra incorrect symbol. Exact equality of times implies
equality of their bin labels. Thus its conditional probability is at most
$D/M$ for every positive integer $M$, and must be zero. The diagonal
$\{(t,t):t\in(0,1]\}$ is Borel. It has mass one under the ideal
coupling and zero under the decoded coupling, proving total variation
one. With the actual flag retained, the two flag blocks are disjoint;
their half-$L^1$ contributions are nonnegative, and the failure block has
weight $\Pr(\mathsf F)=1/2$. Projecting any larger archive onto these
coordinates cannot increase error, proving both unconditional bounds.
$\square$

This does not prohibit arbitrary observers or approximate timestamp
retention in a different metric. It rules out fixed finite all-accessible
memory for this exact same-event consumer. Merely encoding a real number
as a continuously varying finite-dimensional state does not recover that
number from one specimen. Conversely an actually retained exact event
archive lies outside (EM.9), and is not dismissed by the bound.

## 5. Opposite signed-loss controls for every fixed time partition

The triangular signed-loss construction in Instrument Stability §3.2 and
the Jordan range theorem in Instrument Boundaries §10 are suppliers.
Here the triangle is reflected, fitted to an arbitrary fixed finite
partition, and compared at the level of every time-binned CP operation.

**Definition 5.1 (the deliberately coarser recorder).** Fix any finite
strict partition

$$
\Pi:\quad 0=t_0<t_1<\cdots<t_N=1,\qquad N\geq1.
\tag{EM.16}
$$

Its recorder keeps terminal success with its quantum successor, or the
failure bin $j$, original mode $i$ and absorbing successor $f$. It omits
the subcell timestamp. This is a changed recording interface. All common
pre-existing reference fields are retained. An additional log identifying
which programme ran, or any separately supplied subcell clock or
source-sensitive meter, is not an input to the coarse-only comparison.
If such a field is actually retained, it must be included and the following
equality need not hold for that richer joint record.

**Theorem 5.2 (realized finite-bin CP aliases and exact separation).** Fix
arbitrary $0<c<1/2$, $Z=1-2c$, $a=c/2$, $T=1$, a common compatible
preparation and the partition (EM.16). Put $v=c/2$ and, in each cell
$[l,u]=[t_{j-1},t_j]$ with midpoint $m=(l+u)/2$, define

$$
\begin{aligned}
C(t)&=\begin{cases}v(t-l),&l\leq t\leq m,\\
                         v(u-t),&m\leq t\leq u,\end{cases}\\
S_*(t)&=1-t/2,\qquad
k_+(t)=a-\frac{C(t)}{2S_*(t)},\qquad
k_-(t)=a+\frac{C(t)}{2S_*(t)},\qquad
\chi_\pm(t)=\chi(0).
\end{aligned}
\tag{EM.17}
$$

These are original controls satisfying both regularity alternatives, with
actual canonical survival $S_*$ and actual signed-loss curves
$\ell_+=C$ and $\ell_-=-C$. They have the common bounds

$$
\begin{aligned}
&k_\pm(0)=k_\pm(1)=a,\quad
 c/4\leq k_\pm\leq3c/4,\quad S_*\geq1/2,\\
&\min_i p_i(k_\pm)\geq\min(c/4,Z)>0,\quad
 |k_\pm'|\leq3c/4,\quad \operatorname{TV}(\chi_\pm)=0,\\
&\operatorname{TV}(k_\pm)=\mathcal L_\pm\leq3c/4,\qquad
 \mathcal Q_\pm\leq9c^2/16.
\end{aligned}
\tag{EM.18}
$$

Here $\mathcal L=\int\sqrt{k'^2+\chi'^2}$ and
$\mathcal Q=\int(k'^2+\chi'^2)$ are the acquisition supplier's
coordinate costs. The two controls have equal pointwise absolute speeds
and equal actual variation, length and quadratic totals within the pair.
Their complete binned CP instruments are identical on every common live
input and arbitrary common reference. Nevertheless their exact-time
instruments satisfy

$$
D_\rho(\gamma_+,\gamma_-)
 =\frac12\sum_{i\in\{0,1,3,4\}}\operatorname{tr}\rho_{ii}^R,
\qquad d_{\rm op}=1/2,
\qquad d_{\rm mark}=c.
\tag{EM.19}
$$

For every common source-family input $D_\rho=c$ as well. No common bound
on the variation of the height derivative is assumed.

**Proof: original realization and margins.** The piecewise affine $C$
is continuous, vanishes at each partition endpoint and has $|C'|=v$
almost everywhere. Its accumulated variation is $V(t)=vt$. The Jordan
parts for $\ell_\pm=\pm C$ are

$$
P_\pm(t)=(vt\pm C(t))/2,\qquad
Q_\pm(t)=(vt\mp C(t))/2.
\tag{EM.20}
$$

They are nondecreasing with disjoint nonzero derivative supports, and
$P_\pm(1)=Q_\pm(1)=c/4<a=c-a=c/2$. The credited exact range theorem
therefore gives
$S=1-V/c=S_*$ and $k=(a-P_\pm)/S_*=k_\pm$.

These formulas also verify the original control directly. On a rising
triangle half $C'=v$ and on a falling half $C'=-v$; differentiating gives

$$
k_+'=-\frac{C'}{2S_*}-\frac{C}{4S_*^2}
 =\begin{cases}-(c-k_+)/(2S_*),&C'=v,\\
                         k_+/(2S_*),&C'=-v.
          \end{cases}
\tag{EM.21}
$$

Since $k_-=c-k_+$, its derivative is $-k_+'$. In either case the
actual hazard of both controls is $1/(2S_*)$; its integrated survival
is exactly $S_*$. Every piece is rational smooth with denominator at
least $1/2$ and derivative extending continuously to the closed half-cell.
The joined heights are continuous and hence finite-piecewise-$C^1$ and
absolutely continuous. The constant phases satisfy the same alternatives
and have zero transported increment.

For a cell of length $h\leq1$ its peak is $vh/2=ch/4\leq c/4$.
Thus $0\leq C/(2S_*)\leq c/4$, giving the height and probability
margins. The derivative expression bounds its modulus by
$c/2+c/4=3c/4$. Integrating this bound and its square proves (EM.18).
Reflection gives equal absolute height derivatives; since the phase rates
are zero, it gives equality of all the stated resource totals within the
pair. These are chosen-coordinate mathematical costs, not physical energy.

**Proof: equality of the entire binned operations.** Formula (EM.4)
and (EM.20) give the actual source-family CDFs

$$
F_0^\pm=F_4^\pm=P_\pm,\qquad
F_1^\pm=F_3^\pm=Q_\pm,\qquad F_2^\pm=Zt/2.
\tag{EM.22}
$$

At both endpoints of a cell $C=0$. For its length $h$, the increment
of every bottom CDF is $ch/4$, and the middle increment is $Zh/2$.
The initial bottom probabilities are all $a=c/2$. Therefore for every
original mode and every common joint input the binned failure map is
exactly

$$
\mathcal I_{j,i}^\pm(\rho_{LR})
   =\frac h2|f\rangle\langle f|\otimes\rho_{ii}^R.
\tag{EM.23}
$$

Terminal height is $a$, $S_*(1)=1/2$ and every $H_i(1)=0$, so both
success operators are $K_1=I_5/\sqrt2$. Thus their unnormalized success
maps, all bin/mode CP maps and the retained successors coincide, jointly
with arbitrary common references. This is more than equality of scalar
marginals. On the supplier's stopped extension both no-new-failure
operators are $(I_5/\sqrt2)\oplus1_f$ and all jumps annihilate $f$;
equality holds there too, including live–stopped coherences.
At every partition endpoint one also has $K_{t_j}=\sqrt{S_*(t_j)}I_5$.
No intermediate subcell read is being asserted equal.

**Proof: exact-time distance.** On each rising half-cell,
$(P_+',Q_+')=(v,0)$; on each falling half-cell it is $(0,v)$.
Reflection exchanges these two derivatives. After division by the
initial bottom probability $a=v$, the CP density coefficient of a given
bottom mode is $1$ or $0$, and the two programmes exchange them.
Middle coefficients are both $1/2$. Therefore the successful-output
difference and the middle-mode difference vanish, while for every bottom
mode at almost every time the difference of failure densities is

$$
\pm |f\rangle\langle f|\otimes\rho_{ii}^R.
\tag{EM.24}
$$

The reference block is positive. Its trace norm equals its trace, so
integrating over the full unit interval proves the $D_\rho$ formula
in (EM.19), for arbitrary references. Its supremum is $1/2$, attained
by a computational bottom-mode input; this supremum uses the declared
all-input operational metric. On any common original input the total
bottom probability is $2c$, giving $D_\rho=c$.

For marked laws define the Borel event

$$
E_+=\bigcup_{j=1}^N\left(
 ((t_{j-1},(t_{j-1}+t_j)/2)\times\{0,4\})
 \cup
 (((t_{j-1}+t_j)/2,t_j)\times\{1,3\})\right).
\tag{EM.25}
$$

Its probability under the plus programme is $c$, and under the minus
programme is zero. The opposite event exchanges these probabilities.
There are no endpoint atoms. Half the scalar $L^1$ density difference
is $c$, proving $d_{\rm mark}=c$ and completing the proof. $\square$

The source-family unmarked failure-time marginal is uniform, with total
mass $1/2$, in both programmes. The original-mode marginal is also the
same. Their differing subcell time–mode relation is essential. It cannot
be recovered from equality of those separate marginals.

**Corollary 5.3 (uniform reconstruction floors for the coarse-only task).**
Suppose a reconstruction procedure has access only to the binned
instrument of Definition 5.1 and common fields independent of the choice
of $\gamma_+$ or $\gamma_-$. It may even know the two candidate
constructions and their complete binned law. It is not given their actual
programme identity. Any common reconstructed exact-time marked law has
worst-case error at least $c/2$ on this pair. Any common reconstructed
complete quantum instrument has worst-case $d_{\rm op}$ error at least
$1/4$.

**Proof.** The input operations to the reconstruction procedure coincide
by (EM.23), with equal success and common references. Its output law or
operation is consequently one common object $Q$. Triangle inequality
bounds the exact distance between the two targets by the sum of their
distances from $Q$. Apply (EM.19) in the respective metrics. A common
randomized procedure has the same conclusion after its independent
randomness is averaged. $\square$

This is an unknown-programme reconstruction statement, not a failure of
the known-programme conditional law calculation in §6. A separately
retained programme archive can distinguish the candidates and invalidates
the coarse-only hypothesis. The equality does persist under common lawful
finite postprocessing or continuation of the retained coarse output,
provided every accessible controller, selector, archive and external input
is jointly matched. Failed branches remain absorbing. It supplies no
equivalence for a menu additionally reading the omitted old timestamp or
an intermediate live cut.

**Proposition 5.4 (refinement quantifiers and the missing regularity).**
For every fixed finite partition Theorem 5.2 has the same support, survival
and speed bounds and the same exact separations. If
$\|\Pi\|=\max_j(t_j-t_{j-1})$, then

$$
\|k_\pm-a\|_\infty\leq c\|\Pi\|/4.
\tag{EM.26}
$$

Nevertheless, as the number $N$ of cells tends to infinity, the variation
of either height derivative, understood with its one-sided piecewise
smooth representative, is at least $Nc/2$. Thus this family has no common
BV bound on the derivative, despite its common height-speed bound.

**Proof.** The peak estimate in the proof gives
$C\leq c\|\Pi\|/4$ and $2S_*\geq1$, proving (EM.26). At a
cell midpoint the change of $C'$ from $v$ to $-v$ gives a jump of
$k_+'$ of magnitude $v/S_*(m)\geq c/2$, by (EM.21).
Reflection gives the same magnitude for $k_-'$. Variation is at least
the sum of these $N$ midpoint jumps; this follows also by taking points
arbitrarily close on each side of every midpoint in the definition of
variation. The rational rates within the finitely many pieces have finite
variation individually, but these jump lower bounds are unbounded over
the family. $\square$

The quantifiers are $\forall\Pi\,\exists(\gamma_+,\gamma_-)$.
The pair changes with the chosen partition. No fixed pair is claimed to
agree for every arbitrarily refined partition, and no failure of
pointwise histogram convergence for a fixed integrable density is claimed.
The nonvanishing floors concern uniform reconstruction over this entire
bounded-speed class. A theorem using a common BV derivative bound,
derivative modulus or strong acquired loss-density approximation has an
additional hypothesis absent here. Such a hypothesis must itself be
justified on the actual source; naming it supplies neither samples nor a
certificate. Adaptive random quantizers and other observation metrics
require their own analysis.

## 6. Known-programme law resampling and actual-event preservation

**Proposition 6.1 (elementary mode-conditional law postprocessing).** Fix
one completely known prescribed canonical programme $\gamma$, with
the same $b,a,T$ and calibrated operations as in Definition 2.2. Put

$$
w_i(E)=\frac{F_i(E)}{p_i(a)},\qquad
W_i=w_i((0,T]),\qquad
\nu_i(E)=w_i(E)/W_i\quad(W_i>0),
\tag{EM.27}
$$

where $F_i(E)=\int_E f_i(t)\,dt$. Retain success unchanged and only
the failure mode on failed branches. If a separate exact sampler for
each actual programme-dependent $\nu_i$ is supplied, drawing and
attaching its new time reproduces the full terminal CP instrument,
also with every common initial reference. Modes with $W_i=0$ are
unused and require no division.

**Proof.** The mode-only failure operation on a common joint input is
$W_i|f\rangle\langle f|\otimes\rho_{ii}^R$. Its postprocessed
operation for a time event $E$ is

$$
\nu_i(E)W_i|f\rangle\langle f|\otimes\rho_{ii}^R
 =w_i(E)|f\rangle\langle f|\otimes\rho_{ii}^R,
\tag{EM.28}
$$

which is exactly (EM.4). Success is not modified. Multiplication and
countable additivity prove equality on every event and reference block.
This is ordinary classical Markov postprocessing of a CP-valued measure,
not a new sufficiency or acquisition theorem. $\square$

An exact programme-dependent sampler consumes the actual conditional
law, exact continuous randomness and calibrated output. A public finite
description that permits this sampling is an extra premise. Arbitrary
original real waveforms need not have finite effective descriptions.
The proposition does not infer an unknown programme from a single mode
outcome, acquire its densities or grant repeated same-history preparations.

For (EM.6), $\nu_i$ is uniform for each positive-mass mode. A fresh
uniform draw after retaining only that mode therefore reproduces the
correct terminal law. It is independent of the actual earlier uniform
time conditional on that mode, so equality of the two times has
probability zero. Its same-event joint-TV error is one conditional on
failure, although its time marginal is exactly correct. Corollary 4.4
extends this obstruction to every code through fixed finite accessible
memory, not just independent resampling.

Thus three different tasks have different inputs and conclusions:
unknown-programme inference from coarse outputs is limited by §5;
retention of the actual event is limited by §4 even for a known programme;
known-programme terminal law regeneration is the conditional elementary
postprocessing above. A regenerated time cannot restore its old relation
to a contemporaneous external log or retroactively implement a feedback
decision already made at that old event. Such a log or accessible controller
state belongs in the joint assistance count. No live original continuation
after failure is used in any of these statements.

## 7. Suppliers, mature overlap and verification boundary

The following repository links all select revision
`5094da88f161741b61de3b6b16dbc3a115a83d63`.

| Supplier | Exact contribution and boundary |
| --- | --- |
| [FiniteRectangleTransport Lean](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/D5/S3/Quantum/Fibers/FiniteRectangleTransport.lean), `ValidBase`, `probability`, `phaseWeight`, `weight_compatible`, `finite_rectangles_realize`; [owning Scribe](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/Blueprint/D5/S3/Quantum/Fibers/FiniteRectangleTransport.scribe.cs) | Positive five-mode source, signed transport, middle gauge, actual rectangles and ordinary all-signed-sector synthesis. The smooth and piecewise rational controls here satisfy that original law; no actuator or acquired waveform follows from it. |
| [OriginalControlComposition Lean](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/D5/S3/Quantum/Fibers/OriginalControlComposition.lean), `OriginalControl`, `FiniteC1Control`, `concatenate_original`; [owning Scribe](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/Blueprint/D5/S3/Quantum/Fibers/OriginalControlComposition.scribe.cs) | Both original regularity alternatives, arbitrary finite and zero durations, literal prefix and translated real-phase tail, matching heights and additive integrals. No inverse permission, reset or unknown past lift is granted. |
| [Instrument Boundaries](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_BOUNDARIES.md), §§5.2, 9–11, 14–15 | Entire canonical stopped instrument, loss balance and Jordan range, terminal classification, full-reference CP formula, matched joint finite continuation and stronger calibrated dense-cut law access. These are credited, not new targets; whole laws are not acquired outcomes. |
| [Instrument Stability](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md), §§1, 3.2, 5 | Exact output metrics, triangular signed-loss construction, bounded-speed forward discontinuity and sufficient strong derivative/loss-density data. The delta in §5 is reflection on every finite partition, full binned CP equality and exact separation/reconstruction floors. No existing bound is renamed. |
| [Quantum Carrier Minimum](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md), §§1.3, 3–6 | Exact $M_3$ live carrier plus absorbing sector preserves supplied correlated archives. Its separate unassisted live block minimum is three. Our total event-memory dimension $D=\sum d_\alpha$ is a different resource and task; the upper theorem's actual correlated assistance is not denied. |
| [Record Acquisition](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md), §§2–9, 11 | Finite-query obstructions, bounded-speed area approximation and conditional paid timing/calibration/arithmetic and signed-winding certificates. Those results are reused, not repeated as timestamp or full-loss-law acquisition. |
| [Transport-Memory Completion](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §§2.9–2.12, 2.18; [Process Geometry](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §34; [Atlas Stable Core](https://github.com/the-omega-institute/trureturing/blob/5094da88f161741b61de3b6b16dbc3a115a83d63/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md), §§1–3 | Actual common coherent source and port, aligned acquired readings, known nonzero gains and record overlap, joint source/epoch image, domains/routes, complete legal/failure responses and selector/update inputs. An archive marginal, abstract quotient or regenerated law supplies none of these missing maps. |

**Literature statement 7.1 (precise mature ingredients).**

| Primary source | Attested use and non-transfer |
| --- | --- |
| A. Nayak, [*Optimal lower bounds for quantum automata and random access codes*, quant-ph/9904093v3](https://arxiv.org/html/quant-ph/9904093v3), Theorem 2.4(2) | `literature-attested`: correct recovery from $m$ qubits is bounded by the probability mass of the $2^m$ most probable encoded inputs. The uniform dimension/alphabet bound in (EM.13) is mature. The direct proof here handles any direct-sum dimension $D$ without rounding it to a power of two. No bit-query random access menu, iid rate or source sensor is imported. |
| R. Koenig, R. Renner and C. Schaffner, [*The operational meaning of min- and max-entropy*, 0807.1338v2](https://arxiv.org/html/0807.1338v2), Theorem 1 and Eq. (18) | `literature-attested`: for a classical–quantum state, optimal POVM guessing probability is $2^{-H_{\min}(X\mid B)}$. This identifies the operational guessing resource; the proof here uses (EM.13), not an extra entropy, asymptotic or acquisition theorem. |

Both primary texts supply their stated theorem content. No premise here
is imported from inaccessible correction text for Kuramochi's erratum
DOI `10.1063/1.4961516`, or from the numerical-differentiation leads
DOIs `10.1090/S0025-5718-01-01307-2` and `10.5402/2011/164564`.
The elementary CP postprocessing in §6 stands on its displayed proof and
does not require a general minimal-POVM theorem or an unverified correction.

The source-specific constructions and applications in Theorems 3.1, 4.3
and 5.2, their exact event metrics and their consumer correspondence are
`repo-derived`. Guessing inequalities, Jordan decomposition, CP
postprocessing, total-variation duality and triangle inequality remain
mature mathematics. Bounded searches in the pinned original-control
volumes and relevant quantum/observer-memory declarations locate the
credited triangular construction and prior qualitative record limitations;
they do not establish an exhaustive literature search or worldwide novelty.

## 8. What the event relation changes, and what remains unresolved

An exact live carrier of dimension three does not discharge preservation
of the actual event archive. The smooth source in §3 makes one precise
part of that archive quantitatively unavoidable under the same-event
consumer: fixed finite accessible memory cannot recover its exact real
timestamp. Finite-bin label recovery has the sharp abstract bound (EM.11).
Retaining exact time as an ideal continuous archive, or increasing the
retained capacity with demanded bin resolution, are different declared
resource allocations. No finite capacity for the full archive follows
from an optimum for the specimen's live block.

The finite-partition pair changes a different proposed route. Replacing
the exact time/mode instrument by arbitrarily fine but finite binning
cannot, uniformly over the stated positive bounded-speed class, certify
its full marked-TV or quantum operational output. The lost relation is
the subcell ordering of time and mode, with actual legal controls and
absorbing successors realizing the difference. A common survival floor
and common speed alone do not repair it. Stronger acquired loss-density
information or additional justified regularity can address a different
class; the present family has no common BV derivative bound. A restricted
event/feedback menu or a programme-dependent reconstruction is an explicit
task change and must retain its own acquisition and resource premises.

The results establish neither a complete internal observer nor a no-go
theorem for all observers. They do not supply physical canonical
monitoring, same-source nondisturbing acquisition, calibrated common-port
readings, known nonzero record overlaps, unknown joint-overlap estimates,
phase-sensitive aligned reads, actual programme availability, lawful
selector/update closure on the whole joint running image, or an
unbounded-horizon certification. All such fields and errors must be
obtained and retained under the actual permission and failure contract.
One observed event remains one event, rather than a whole probability law.

The stationary native $\alpha/\beta$ late-target memory-rate/cofinality
task, the independent fixed-Hamiltonian five-mode quantum minimax task,
the C114 mixed-state source and twisted-ground lattice representation
remain different models. No source/action/observation/resource
correspondence to them is proved here. Full space/time/boundary/memory
mutual recovery and the continuing programme retain their original goals
and unresolved bridges.

## 追加锚（本行以下为增补区）
