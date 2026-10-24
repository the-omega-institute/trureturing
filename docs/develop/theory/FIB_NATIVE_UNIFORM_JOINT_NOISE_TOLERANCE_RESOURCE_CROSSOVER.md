# Uniform joint noise and tolerance native resource crossover

This volume fixes the native source and the original clock of the guarded
two-control model.  It isolates the parameter-uniform resource statement
which is not contained in the fixed-noise or zero-noise suppliers.

## 1. One persistent source and the stopped issuer class

**Definition 1.1 (the joint target).** Fix the native data of K, Definitions
2.1--2.2 and 11.1--11.4: $0<Z<1$, $r=1-Z$, $H=r/2$,
$0<l<k<u<H$, horizon $T>0$, arbitrary preparation phases, the negative
amplitude convention, both actual $2\pi$ periods, probabilities
$(k,H-k,Z,H-k,k)$, fields

$$
P=\partial_k,
\qquad
Q=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta,
$$

and the four unhalved original-clock costs.  On one probability space let
$W^1,W^2,C$ be independent covariance-$2$ Brownian motions.  For a real
parameter $\nu$ put

$$
K^\nu_t=\int_0^tW^1_s\,dW^2_s+\nu C_t,
\qquad
\tau=\inf\{t\geq0:k+W^1_t\notin(l,u)\},
\qquad S=\tau\wedge T.
$$

The stopped target is

$$
\bar q^\nu_t=
\left(k+W^1_{t\wedge S},
 [\alpha _0+W^2_{t\wedge S}/2],
 [\beta _0+c_0W^2_{t\wedge S}-K^\nu_{t\wedge S}/r]\right),
\qquad c_0=\tfrac12-k/r.
\tag{1.1}
$$

The same triple $(W^1,W^2,C)$ is used for every $\nu$; changing $\nu$ changes
only the target map.  The source is therefore one coupling, rather than a
family of independently resampled targets.  The parameter range below is
$|\nu|\leq\bar\nu$ for a fixed finite $\bar\nu$, and the drift is fixed at
$\lambda=0$.

**Definition 1.2 (ideal stopped-history finite numerical issuers).** The
issuer observes the usual augmentation of the stopped history
$(W^1,W^2,C,K^\nu)_{\cdot\wedge\tau}$, together with an optional seed
independent of the whole triple.  At each stopping-time issuance it chooses
one complete numerical pair of zero-start absolutely continuous profiles.
An interruption replaces only the unexecuted suffix; joins are continuous,
and the number of issuances through own death or $T$ is almost surely
finite.  The executed controls are denoted $(A,B)$ and retain

$$
J_t=\int_0^t A_s\,dB_s.
\tag{1.2}
$$

Every executed prefix, including an interrupted prefix and the continuation
after own death, obeys the whole-height guard
$k+A_t\in[l,u]\subset(0,H)$; after own death both controls are held.  The
native path is the affine periodic image of $(A,B,J)$ in (1.1), with the
original preparation phases and periods.  A rejected command, a Stop, a hold
and a command interruption change neither $J$ nor the source clock; a target exit
is not an own death.  Let $\zeta^{\rm N}$ and $S^{\rm N}$ be the actual
censored death record and cutoff, and let $V^a,V^b,L,E$ be respectively

$$
\int|\dot A|,\qquad \int|\dot B|,\qquad
\int\sqrt{\dot A^2+\dot B^2},\qquad
\int(\dot A^2+\dot B^2),
\tag{1.3}
$$

over the actually executed original-time prefixes.  For $\eta>0$ write
$\mathcal A(\eta,\nu)$ for this class with
$D_{\max}(\bar q^{\rm N},\bar q^\nu)\leq\eta$ almost surely, and set

$$
\mathsf C_x(\eta,\nu)=\inf_{\pi\in\mathcal A(\eta,\nu)}\mathbb E C_x(\pi),
\qquad (C_a,C_b,C_L,C_E)=(V^a,V^b,L,E),
\tag{1.4}
$$

with the convention $\inf\varnothing=+\infty$.  An infimum is not asserted
to be attained.  A simultaneous family means one choice
$\pi_{\eta,\nu}\in\mathcal A(\eta,\nu)$ for every
$0<\eta\leq\eta_0$ and $|\nu|\leq\bar\nu$ on the same source; the
additional allowed lifetime requirement is
$\zeta^{\rm N}_{\eta_n,\nu_n}\to\zeta$ for every deterministic sequence
$\eta_n\downarrow0$ (and, when stated, $\nu_n\to\nu_*$).  No exact
same-clock cemetery equality is included.

For the resource infima in (1.4), the admissible sub-class also requires
the permitted delayed-life bound

$$
0\leq S^{\rm N}-S\leq\eta .
\tag{1.5}
$$

This is a convergence allowance, not an exact-death requirement.  It makes
the lifetime quantifier part of the class at each tolerance and implies the
simultaneous-family convergence just stated.

At $\nu=0$, the coordinate $C$ remains visible in the supplied analytic
history, although it has coefficient zero in $K^0$ and is not needed by the
target.  Visibility is not a third actuator: the only native controls are
$P,Q$, and all $C$-dependent corrections below are made by loops in those
two controls.  An independent seed is randomization and supplies no source
increment.

## 2. The central-ledger connector

**Lemma 2.1 (uniform ledger service).** Put
$A^{\rm src}_t=\int_0^tW^1_s\,dW^2_s$ and, on a live prefix, write
$R_t=J_t-A^{\rm src}_t-\nu C_t$.  There are constants
$\Gamma\geq 1$ and $C_0<\infty$, depending only on the fixed native data,
$T$ and $\bar\nu$, with the following property.  Put
$\rho=\eta/\Gamma$ and assume $0<\rho\leq1$.  For every
$|\nu|\leq\bar\nu$ there is a finite numerical issuer in
$\mathcal A(\eta,\nu)$, with the target death delayed by at most
$\rho^2$, whose additional central-ledger service satisfies

$$
\begin{aligned}
\mathbb E V^a_{\rm led}+\mathbb E V^b_{\rm led}
  +\mathbb E L_{\rm led}
 &\leq C_0\left(1+\frac{\nu^2\mathbb ES}{\rho^2}\right),\\
\mathbb E E_{\rm led}
 &\leq C_0\left(\rho^{-2}+\nu^4\rho^{-4}\right).
\end{aligned}
\tag{2.1}
$$

The service is nonanticipating in the stopped history and uses no operation
outside $P,Q$.

*Proof.* First run the zero-central-noise mesh of K, §§26--30, with first
level thresholds $\rho$ and Lévy-area threshold $\rho^2$.  Its ordinary
connectors have total expected variation and length $O(\rho^{-1})$ and
energy $O(\rho^{-2})$, uniformly in $\nu$: the mesh and the connector
geometry use only $(W^1,W^2,\int W^1dW^2)$, and the stopped source clock is
unchanged.  They leave a chronological residual whose new martingale part
is $-\nu C$; the deterministic area residual is bounded by a fixed
multiple of $\rho^2$ on each cell.

For the new part use the hysteresis times of the continuous ledger
$X=\nu C$: set $\sigma_0=0$ and
$\sigma_{j+1}=\inf\{t\geq\sigma_j:|X_t-X_{\sigma_j}|=q\}$,
$q=\rho/8$.  The piecewise constant process which records the last value
$X_{\sigma_j}$ stays within $q$ of $X$.  Its increments are $\pm q$ and
the strong Markov property and the covariance-$2$ exit-time identity
$\mathbb E(\sigma_{j+1}-\sigma_j\mid\mathcal F_{\sigma_j})
=q^2/(2\nu^2)$ give, by summing complete intervals and charging the final
remainder positively,

$$
\mathbb E N_c\leq C\left(1+\frac{\nu^2\mathbb ES}{\rho^2}\right),
\tag{2.2}
$$

where $N_c$ counts the completed hysteresis intervals before $S$; for
$\nu=0$ it is zero.  Each recorded increment is realized by a finite concatenation of inward
rectangles.  Each rectangle has horizontal width $\rho/4$ and vertical
side chosen so that its chronological increment has magnitude at most
$\rho^2/64$; all rectangles have the same sign.  Thus a ledger increment
of size $q=\rho/8$ uses $M=O(\rho^{-1})$ rectangles, has total control
variation $O(1)$, and every prefix has second-control excursion at most
$\rho/4$.  At the next observed hysteresis time its preceding interval is
known, so a fraction of this finite concatenation is assigned to its
service.  The unfinished suffix is carried into the next first-level
cell and is replaced only at the first stopping time at which a first-level
threshold or the ledger threshold $q/4$ is met.  Its progress is monotone: a
rectangle is traversed once, even when the numerical profile is interrupted.
The resulting one-step service queue has service time $\theta\ell_j$ for
an interval of length $\ell_j$, with a fixed $0<\theta<1$; the unused
fraction is available for the ordinary area connector.  If $Q_j$ is the
unserved duration immediately before interval $j$, its workload satisfies

$$
Q_{j+1}\leq (Q_j+\theta\ell_j-\ell_{j+1})_+ .
\tag{2.3a}
$$

The $\ell_j$ are iid bounded-interval Brownian exit times after each
hysteresis hit, with finite first and second moments.  Hence
$\mathbb E(\theta\ell_j-\ell_{j+1})<0$ and the standard renewal
supermartingale argument gives a finite mean workload and a fixed expected
number of suffix replacements per completed rectangle.  The exponential
small-time estimate in K, (18.3), supplies the reciprocal moment used for
energy.  Thus the queue contributes only a fixed geometric factor to each
completed rectangle.
This is the stopping-time suffix mechanism of K, §36, with a causal
one-step delay and no future endpoint in an issued profile.

The preceding interval has the covariance-$2$ Brownian exit law at level
$q/|\nu|$.  Its inverse first moment is finite by the same exponential
small-time bound.  Assigning the known interval duration to the next
rectangle and charging a terminal truncated interval only to the base mesh
gives

$$
\mathbb E E_{\rm one\ loop}
 \leq C\frac{\nu^2+\rho}{\rho^2}.
\tag{2.3}
$$

The same estimate follows by Cauchy--Schwarz when the rectangle is
interleaved with the first-level cells.  In either description, every
issued profile is numerical at issuance and all replacements are stopping
times.  The rectangle's relative height and second control remain below
$\rho/4$; choosing $\Gamma$ larger than the fixed affine coefficients in
(1.1) keeps the complete native phase error below $\eta$.

The bounded area residual is absorbed by the base mesh.  During every
suffix, the complete residual obeys

$$
|R_t|\leq 2q+C\rho^2,
\tag{2.4}
$$

because the hysteresis ledger is within $q$, one delayed increment is at
most $q$, and one base cell contributes at most $C\rho^2$.  With
$q=\rho/8$ and $\rho=\eta/\Gamma$, (2.4), the first-level bounds and the
affine formulas in (1.1) give the claimed native tube.  Multiplying the
one-loop estimate by (2.2) gives

$$
\begin{aligned}
\mathbb E(V^a_{\rm led}+V^b_{\rm led}+L_{\rm led})
 &\leq C\left(1+\nu^2\rho^{-2}\right),\\
\mathbb E E_{\rm led}
 &\leq C\left(\rho^{-2}+\nu^4\rho^{-4}
                 +\nu^2\rho^{-3}+\nu^2\rho^{-2}\right).
\end{aligned}
$$

If $\nu^2\leq\rho$, the last two terms are $O(\rho^{-2})$; if
$\nu^2>\rho$, they are bounded by $O(\nu^4\rho^{-4})$.  This proves
(2.1).  The final inward connector at target death is the bounded terminal
connector of K, §37, and costs $O(\rho)$ variation and $O(1)$ energy on a
duration $\rho^2$.  It delays own death by at most $\rho^2$, preserves the
original clock and all four costs, and completes the proof. $\square$

The ledger argument is a sufficient construction, not a claim that a
particular threshold policy attains a sharp constant.  Its point is the
separation of the $\rho^{-1}$ area-cell charge from the
$\nu^2\rho^{-2}$ number of independent-central threshold crossings.

## 3. Uniform two-sided resource law

**Theorem 3.1 (uniform joint crossover).** There are positive constants
$c_a,c_b,c_L,c_E,C_a,C_b,C_L,C_E$ and $\eta_0>0$, depending only on the fixed native
data, $T$ and $\bar\nu$, such that for every
$0<\eta\leq\eta_0$ and $|\nu|\leq\bar\nu$,

$$
\begin{aligned}
c_a(\eta^{-1}+\nu^2\eta^{-2})
 &\leq \mathsf C_a(\eta,\nu)
 \leq C_a(\eta^{-1}+\nu^2\eta^{-2}),\\
c_b(\eta^{-1}+\nu^2\eta^{-2})
 &\leq \mathsf C_b(\eta,\nu)
 \leq C_b(\eta^{-1}+\nu^2\eta^{-2}),\\
c_L(\eta^{-1}+\nu^2\eta^{-2})
 &\leq \mathsf C_L(\eta,\nu)
 \leq C_L(\eta^{-1}+\nu^2\eta^{-2}),\\
c_E(\eta^{-2}+\nu^4\eta^{-4})
 &\leq \mathsf C_E(\eta,\nu)
 \leq C_E(\eta^{-2}+\nu^4\eta^{-4}).
\end{aligned}
\tag{3.1}
$$

The upper bounds are realized by one simultaneous family on the persistent
source.  Along every deterministic sequence
$\eta_n\downarrow0$, $\zeta^{\rm N}_{\eta_n,\nu_n}\to\zeta$ almost
surely for any bounded parameter sequence $\nu_n$ for which the delayed
terminal durations tend to zero.  The constants in (3.1) are independent
of $\eta$ and $\nu$ throughout the bounded interval.

*Proof.* Lemma 2.1 and K, Proposition 30.1, with $\rho=\eta/\Gamma$,
give the upper bounds. The target-first-exit law depends only on $W^1$;
the terminal connector therefore gives the same delayed death estimate as
K, Proposition 31.1, uniformly in $\nu$. The held paths converge on the
same source whenever $\eta_n\to0$, and the added terminal delay is
$O(\rho_n^2)$, so the stated lifetime convergence follows. This is a
same-clock observation statement; it does not identify the cemetery paths
uniformly at a fixed tolerance.

For the lower bounds, K, Theorem 13.2, applies on one target-only event
independent of the command family and of $\nu$, because its first-level
and chronological hypotheses are inherited from the native tube. Hence,
for every bounded sequence $(\eta_n,\nu_n)$ and every admissible family,

$$
\liminf_n\eta_n\mathbb EV^a_n\ge\mathbb ES,
\quad
\liminf_n\eta_n\mathbb EV^b_n\ge\mathbb ES/2,
\quad
\liminf_n\eta_n\mathbb EL_n\ge\sqrt5\,\mathbb ES/2,
\tag{3.2}
$$

and

$$
\liminf_n\eta_n^2\mathbb EE_n\ge5\pi^2\mathbb ES/24.
\tag{3.3}
$$

K, Theorem 33.2, specialized to $\lambda=0$, gives for every individual
policy

$$
F_{\eta,\nu}=[2\nu^2\mathbb ES-4r^2\eta^2]_+,
\tag{3.4}
$$

and

$$
\mathbb EV^a\ge\frac{F_{\eta,\nu}}{8r\eta^2},\qquad
\mathbb EV^b\ge\frac{F_{\eta,\nu}}{4r\eta^2},\qquad
\mathbb EL\ge\frac{\sqrt5F_{\eta,\nu}}{8r\eta^2},\qquad
\mathbb EE\ge\frac{5F_{\eta,\nu}^2}{64r^2\eta^4\mathbb ES}.
\tag{3.5}
$$

If $\nu_n^2\leq\eta_n$, the sum in each variation or length target is
at most twice its $\eta_n^{-1}$ term, and (3.2) supplies a fixed positive
fraction.  If $\nu_n^2>\eta_n$, then for all sufficiently large $n$,
(3.4) is at least $\nu_n^2\mathbb ES$, so (3.5) supplies a fixed
fraction of the $\nu_n^2\eta_n^{-2}$ term.  The same split, using (3.3)
in the first regime and the last inequality in (3.5) in the second,
supplies a fixed fraction of
$\eta_n^{-2}+\nu_n^4\eta_n^{-4}$ for energy.  This sequential lower
bound implies the pointwise infimum lower bound in (3.1): otherwise a
sequence of near-infimal policies, with costs within $1$ of the infimum,
would contradict the corresponding sequence estimate.  Exact minimizers
are neither needed nor asserted. $\square$

## 4. Degeneracy, sharpness and dimensions

**Corollary 4.1 (the two endpoint regimes).** At $\nu=0$, the central
ledger is identically zero and (3.1) reduces to

$$
\mathsf C_{a,b,L}(\eta,0)\asymp\eta^{-1},
\qquad
\mathsf C_E(\eta,0)\asymp\eta^{-2}.
$$

For every fixed $\nu\ne0$, the second terms dominate as $\eta\downarrow0$,
so

$$
\mathsf C_{a,b,L}(\eta,\nu)\asymp\nu^2\eta^{-2},
\qquad
\mathsf C_E(\eta,\nu)\asymp\nu^4\eta^{-4}.
$$

The crossover is genuine when $|\nu|\asymp\sqrt\eta$; neither endpoint
estimate can be relabelled as uniform in the pair $(\eta,\nu)$.

*Proof.* The first assertion is the inactive-ledger case of Lemma 2.1 and
the zero-noise lower part of Theorem 3.1. The second is (3.5) together
with the upper construction. At $|\nu|\asymp\sqrt\eta$ both summands in
each displayed target have the same order, so discarding either term
changes the joint asymptotic. $\square$

**Proposition 4.2 (state, covariance, controls and physical axes).** The
native state has three coordinates $(k,\alpha,\beta)$ and the primitive
control rank is two, generated by $P,Q$.  For $\nu\ne0$ the direct target
covariance rank is three, with local tensor

$$
2\left(P\otimes P+Q\otimes Q+\frac{\nu^2}{r^2}
\partial_\beta\otimes\partial_\beta\right)dt;
\tag{4.1}
$$

at $\nu=0$ its rank is two.  The state dimension, covariance rank, control
rank, homogeneous/spectral dimension and any number of physical spatial
axes are distinct quantities.

*Proof.* Differentiate (1.1):
$d\kappa=dW^1$, $d\widetilde\alpha=dW^2/2$ and
$d\widetilde\beta=(1/2-\kappa/r)dW^2-\nu\,dC/r$.  Independence gives
(4.1), while the command fields remain $P,Q$ for all $\nu$.  The rank
statements follow from the determinant of the three noise columns and do
not identify a stochastic covariance direction with a physical axis.
$\square$

## 5. Bounded occupation consumer and limits

**Theorem 5.1 (same-coupling bounded Green consumer).** Let
$F\in C(\overline I\times\mathbb T^2)$ be bounded and let
$B<\infty$.  Define the capped occupation

$$
\mathcal O_{T,B}(q)=\min\left\{B,\int_0^{T\wedge\zeta(q)}F(q_t)\,dt\right\}
\tag{5.1}
$$

for nonnegative $F$ (use positive and negative parts for signed $F$).
For any simultaneous family from Theorem 3.1 with
$\eta_n\to0$ and $\nu_n\to\nu_*$, and with the allowed delayed own-life
convergence, one has on the same source

$$
\mathbb E\,\mathcal O_{T,B}(\bar q^{\rm N}_{\eta_n,\nu_n})
\longrightarrow
\mathbb E\,\mathcal O_{T,B}(\bar q^{\nu_*} ).
\tag{5.2}
$$

In particular, taking $\nu_*=0$ is a same-coupling noise-removal consumer.
For the full killed Green occupation, first take this limit at fixed $T$ and
then $T\to\infty$; the target tail is controlled by the height exit and
the capped integrand, while no assertion is made for the uncapped singular
source-field occupation or for the paid-point contract.

*Proof.* The affine map (1.1) is uniformly continuous on stopped compact
paths.  If $\nu_n\to\nu_*$, then
$\sup_{t\leq T}|K^{\nu_n}_{t\wedge S}-K^{\nu_*}_{t\wedge S}|
\leq |\nu_n-\nu_*|\sup_{t\leq T}|C_{t\wedge S}|$, which tends to zero
almost surely.  The native tube and the delayed-life estimate therefore
give uniform convergence on the common live interval, and the usual
piecewise-linear time change gives $J_1$ convergence of the killed paths.
The bounded continuous capped functional (5.1) consequently converges
almost surely.  Dominated convergence proves (5.2).  This is exactly the
bounded occupation bridge of N, Theorem 6.2, with the present common
source; its Green tail estimate applies because the height process is the
same stopped Brownian coordinate for every $\nu$.  The bridge does not
remove the uniform-integrability obligation for an uncapped singular
field, and it does not turn the separately paid observation interface into
an ideal history. $\square$

## 6. Supplier correspondence and unresolved contracts

**Definition 6.1 (source correspondence).** The native source, guards,
periods, phases, chronology and costs are those of K, §§2, 11 and 20.
The zero-noise mesh, suffix execution, terminal connector and delayed
own-death estimate are reused from K, §§26--31.  The full killed Green law
and its bounded occupation bridge are N, §§1--6.  O, §§42--49 supplies a
different paid-point filtration and fixed-risk Read contract; it is not
used in Theorems 3.1 or 5.1.  V and G concern fixed-coefficient Green
stability and the two-control Green field, respectively, and do not alter
the operational class here.

The Brownian exit-time identity and stopped strong Markov property are the
standard covariance-$2$ Brownian facts used already in K, §§18 and 35.  The
truncated-variation result of Łochowski--Miłoś,
[arXiv:1109.0043v2, Theorem 1](https://arxiv.org/html/1109.0043v2),
supports the first-level lower supplier used by K, §12.  The scalar taut
string results of Lifshits--Setterqvist,
[arXiv:1405.1651v1](https://arxiv.org/html/1405.1651v1), and
Lifshits--Podchishchailov,
[arXiv:2411.04690v2](https://arxiv.org/html/2411.04690v2), support the
energy lower supplier used by K, §12.  None of these scalar statements
supplies a native control, a chronological integral, a guard, an original
clock, or a finite numerical issuer; those obligations are met here by the
two-control loop and suffix construction.

**Proposition 6.2 (separate boundaries).** The paid-point observation
contract, finite-risk Read laws and its acquisition costs remain separate
from the ideal stopped-history class.  Theorems 3.1 and 5.1 transfer only
bounded continuous or capped occupation observables.  An uncapped singular
source-field occupation requires a new uniform-integrability proof and is
not implied by the present tube or lifetime convergence.

*Proof.* These are exactly the scope boundaries in O, K, and N cited in
Definition 6.1.  The loop construction uses an ideal stopped history and
never assigns a paid Read, while the capped functional in (5.1) is bounded
for dominated convergence.  A singular unbounded field cannot be passed
through that argument without a uniform-integrability estimate. $\square$

## 追加锚（本行以下为增补区）
