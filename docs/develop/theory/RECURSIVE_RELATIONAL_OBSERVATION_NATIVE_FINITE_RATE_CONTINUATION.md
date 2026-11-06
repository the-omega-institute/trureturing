# Recursive Relational Observation: Native Finite-Rate Continuation

## 1. Original source and the history being compared

**Definition 1.1 (literal native source).** The source is exactly
[III145–148][III], with the literal matrices, ready and menus identified in
[XI1.1–1.4][XI]. In particular,

$$
\begin{gathered}
E=\{q\subseteq\{1,\ldots,9\}:q\text{ has no adjacent occupied sites}\},
\quad |E|=89,\quad e_{\rm r}=e_{\{3,7\}},\\
x=(\sqrt5-1)/2,\quad y=\sqrt x,\quad c=xy,\quad
\alpha=3\pi/5,\quad d=x-x^2,\quad A=4c^2=1-d^2,\\
Q_* =\begin{pmatrix}x&c\\c&x^2\end{pmatrix},\qquad
H_j=-\alpha(I+\mathcal P_j),\\
U_j(s)=e^{i\alpha s}[I+(e^{i\alpha s}-1)\mathcal P_j],
\quad 0\le s\le1,\qquad K_j=U_j(1).
\end{gathered}
\tag{1.1}
$$

Here $b_{-1}b_0=10$, $b_{10}b_{11}b_{12}=010$, and the original projection
is

$$
\mathcal P_j=n_{j-1}n_{j+1}
 +(1-n_{j-1})(1-n_{j+1})(Q_*)_{b_j}.
\tag{1.2}
$$

At an interior address its components are the original active pairs,
obtained by flipping $b_j$ with both neighbours zero, and blocked
singletons. On the latter the projection value is respectively $0$ or $1$
when one or both neighbours are occupied. The boundary projections are
$\mathcal P_0=n_1$, $\mathcal P_{10}=n_9$; their components are singletons.
The entire complex carrier, including the $26$-dimensional code and its
$63$-dimensional complement, is retained. In particular $K_j^{10}=I$ in
the original exact phase convention.

A prefix $a$ is a finite word in $\{0,\ldots,10\}$, and a post-read word
$f$ is a finite word in $\{0,\ldots,6\}$. Empty words are allowed.
$K_{aj}=K_jK_a$. The programme $\mathsf T(a)$ executes $a$ and the old
terminal. The programme $\mathsf R(a,f)$ executes $a$, reports and retains
$I=b_9(Q_-)$, preserves $Q_+=Q_-$, performs the original pure update,
executes the exogenous $f$, and calls the old terminal. The requested $f$
is independent of $I$. Each letter is one uninterrupted positive unit
pulse. No internal read, inverse control, fractional pulse, reset, fork or
new preparation is an operation of this menu.

Write $E_i=\{q:b_9(q)=i\}$ and let $M_i$ be its coordinate projection.
For a fixed prefix put

$$
\chi_a=K_ae_{\rm r},\qquad \tau_i(a)=\|M_i\chi_a\|^2.
\tag{1.3}
$$

The original process uses, on positive departure mass,

$$
J_s(q,r)=2\operatorname{Im}
  (\overline{\psi_s(q)}(H_j)_{qr}\psi_s(r)),\qquad
\sigma_s(q\mid r)=\frac{[J_s(q,r)]_+}{|\psi_s(r)|^2}.
\tag{1.4}
$$

Its initial vector and configuration are the same ready. Its node-safe,
nonexplosive law, square equivariance and at most two configuration jumps
per pulse are the supplied results III146.1 and III148.1. On a positive
original report branch the update is exactly
$M_i\chi_a/\sqrt{\tau_i(a)}$; a zero original branch has zero joint mass
and no conditional state. Denote this original law by $\mu^P$. The rate
cap introduced below does not redefine $\mu^P$.

**Definition 1.2 (common complete core histories).** Fix one actual
programme $P$, of $n$ calls. The common ambient history space retains the
entire $E$-valued càdlàg configuration path on $[0,n]$, all its exact jump
times, the literal calls and their times, the exact complex unit-vector
path in the phase convention of (1.1), and its projective path. At a read,
retain the ordered pre-read and post-read vector values, the literal
report, its retained copy, and the update position. The old terminal is
$W=(b_{-1},\ldots,b_8)(Q)$, with all $1024$ labels and, for $\mathsf R$,
all $2048$ formal $(I,W)$ pairs. Retain all original zero, failure,
refusal, stop, alarm and return coordinates; their ideal masses remain
those of the original contract. An original-node-occupied comparison
history is still an element of this ambient space.

One may take the finite-jump subspace of $D([0,n],E)$, with the ordered
read cut adjoined, together with the piecewise continuous vector
coordinates and the finite label factors. These are standard Borel
spaces. The paths with the stated native rules form measurable subsets.
For $n=0$ use the single ready configuration and the same ordered read
coordinates when present. Unused seeds, rejected proposal marks and
unexecuted counterfactual programmes are not retained source coordinates.
Throughout,

$$
\operatorname{TV}(\mu,\nu)=\sup_B|\mu(B)-\nu(B)|.
\tag{1.5}
$$

Each comparison concerns unconditional joint laws for the same executed
programme. It is not a claim about a joint coupling of all unexecuted
programmes, nor about equality of complete histories of different words.

**Assumption 1.3 (archive versions, when archives are included).** Fix
one specified family of normalized standard Borel causal archive kernels
$\kappa$ satisfying III145.2(3). Both laws consume this same family,
including its rules for emission times, counts and absence. The versions
are defined on every readable history reached by either law, not just
almost everywhere under the original law. Archive innovations are
independent of the configuration innovations. The kernels depend only on
already arrived requests and the actual readable past, do not query
hidden configuration or jump-time coordinates, and do not feed back into
configuration, vector or control. They preserve the original common-prefix
causality. Their sequential extension is a normalized history-to-archive
kernel. The complete core remains a projection of the extended history.
Without this assumption, statements below about TV concern the complete
core, and supply no comparison for arbitrary different archive rules.

## 2. Bounded node extension and exact read admission

**Definition 2.1 (separate capped comparison).** Fix a finite $L>0$ as a
comparison parameter, not as a new callable control. During a pulse, for
the current exact vector and the unique partner $q$ of an active-pair
configuration $r$, set

$$
\sigma_L(q\mid r)=
\begin{cases}
\min\{[J(q,r)]_+/|\psi(r)|^2,L\},&|\psi(r)|^2>0,\\
0,&|\psi(r)|^2=0.
\end{cases}
\tag{2.1}
$$

All other off-diagonal rates are zero, including singleton and cross-block
rates. The zero clause includes isolated nodes, persistently zero
coordinates, and entire zero-mass blocks even if the comparison has
positive configuration mass there. Gate seams preserve configuration;
there is no forced node evacuation or deterministic correction. Gate
exteriors have $H=0$. The vector follows the original exact pulses.

For a read use this process's own literal $I=b_9(Q_-)$, retain $Q$, and
apply exactly $M_I\chi_a/\sqrt{\tau_I(a)}$ if the denominator is nonzero.
No update is assigned to a positive-mass zero-projection report. The
notation $\mu_L^{\mathsf R(a,f)}$ is used only after its existence has
been established. The pre-read capped law and every capped $\mathsf T$
law are defined without this issue. No capped square equivariance is
assumed.

**Theorem 2.2 (native totality and cap-independent read domain).** Every
finite capped $\mathsf T(a)$ has a unique causal nonexplosive law. To
recognize exactly which original reads can be appended, write
$a=(j_1,\ldots,j_p)$ and
$v_k=K_{j_1\cdots j_{k-1}}e_{\rm r}$. Compute the original analytic
current $J_k(q,r;s)$ along $U_{j_k}(s)v_k$, $0\le s\le1$. Define

$$
\begin{aligned}
S_0&=\{\{3,7\}\},\\
S_k&=S_{k-1}\ \cup\
\{q:\exists r\in S_{k-1},\ \{q,r\}\text{ active for }j_k,
\ \exists s\in(0,1):J_k(q,r;s)>0\}.
\end{aligned}
\tag{2.2}
$$

For every finite $L>0$, $S_p$ is exactly the support of the capped
pre-read endpoint configuration distribution. Consequently, for every
finite original $f$, the unchanged capped $\mathsf R(a,f)$ law exists
uniquely if and only if

$$
\mathsf{Adm}(a):\quad
S_p\cap E_i\ne\varnothing\ \Longrightarrow\ \tau_i(a)>0
\qquad(i=0,1).
\tag{2.3}
$$

This condition is independent of the finite positive cap. It is a finite
exact recognition condition on the original prefix, not an added reader.

Proof. At every configuration there is at most one possible destination,
so (2.1) bounds total exit rate by $L$ everywhere. Independent rate-$L$
Poisson proposals and fresh uniform marks, accepting along the unique
edge with probability $\sigma_L/L$, construct the law. Proposals have no
atom at a deterministic seam or node; retaining configuration there
therefore agrees with the prescribed rule. Bounded measurable rates on
this finite carrier give uniqueness, and finitely many calls concatenate
causally. This construction explicitly supplies mathematical comparison
innovations; it infers neither original node safety nor physical noise
sources for the cap.

During a unit pulse, an entering support point survives to its end with
probability at least $e^{-L}>0$. No member of the entering support is
lost. If a directed current in (2.2) is positive at one interior point,
analyticity makes it positive on an open interval. On a smaller compact
subinterval the departure amplitude is nonzero and the clipped rate has
positive integral. There is positive probability to hold until that
interval, make exactly one partner jump there, and hold thereafter. Thus
its partner is in the endpoint support. Conversely any endpoint outside
the entrance support must have been reached from its partner. There is
no third point in its pulse component. A jump has positive probability
only if the corresponding current is positive on an interior interval;
isolated instants cannot carry jump mass. This proves (2.2), including
zero blocks, by induction. Positivity is unchanged by any finite positive
cap.

The literal report has positive capped mass precisely on the sectors
intersecting $S_p$. On each such report the original normalization exists
precisely when (2.3) holds. If it fails, a demanded update is undefined on
positive mass. If it holds, each occupied report has the specified pure
successor and the bounded construction continues on every finite $f$,
including configurations at individual zero coordinates of that
successor. No conditional state is needed on an unoccupied zero branch.
The specified update and pulse laws give uniqueness. ∎

**Theorem 2.3 (finite recognition and native nonempty domains).** The
criterion (2.3) can be decided by finitely many exact algebraic zero and
sign tests. Both $a=\epsilon$ and $a=(9)$ are admitted. The latter has
$\tau_1=x$, $\tau_0=x^2$, and permits every finite original $f$. More
generally $\tau_0\tau_1>0$ suffices without any uniform lower bound.
Every prefix omitting address $9$ is admitted, even when its record-one
projection is zero.

Proof. Prefix vectors have algebraic entries in the fixed number field
generated by $x,y,i,e^{i\alpha}$. On an active pair, the current divided
by $\alpha$ is a real algebraic linear combination of
$\sin(\alpha s)$ and $\cos(\alpha s)$. Setting
$z=\tan(\alpha s/2)$ turns its sign test into the sign of a quadratic
polynomial on $0<z<\tan(3\pi/10)$, an interval with algebraic endpoints.
Identically zero polynomials are included. The projection test is an
algebraic sum of squared moduli. Each call has at most $44$ pairs, hence
at most $88$ directed sign tests and an $89$-point support mask. This is
finite recognition, with no asserted bit-complexity bound.

The empty prefix has support only at ready. On the address-$9$ pair
$\{3,7\},\{3,7,9\}$, the original mass after one call is
$4c^2\sin^2(\alpha/2)=x$ on the latter point. Both record projections
are nonzero. Finally every other address preserves $b_9$ along each
configuration path and in the exact vector, including the diagonal
boundary address $10$. Such a prefix stays in record sector zero in
both laws. These examples verify (2.3). X13.2 additionally supplies
$M_0\chi_a\ne0$ for every original finite prefix, without a uniform
positive floor; the recognition theorem itself needs no such supplier. ∎

## 3. Actual zero-projection obstruction and its bounded-rate class

**Theorem 3.1 (ten original address-nine calls obstruct the unchanged
update).** For every finite $L>0$, the capped prefix $a=9^{10}$ has
strictly positive probability of literal report $1$, while
$M_1\chi_a=0$. Thus no complete capped $\mathsf R(9^{10},f)$ law with
the prescribed original update exists, for any original $f$, including
$\epsilon$ and $(1)$.

Proof. Put $q_0=\{3,7\}$ and $q_1=\{3,7,9\}$. These are the actual
address-$9$ active pair because $b_8=b_{10}=0$. Ten uninterrupted full
calls concatenate the same Hamiltonian on $[0,10]$. Their exact vector
satisfies

$$
p(t)=|\psi_t(q_1)|^2=A\sin^2(\alpha t/2),\qquad
K_9^{10}=I,\qquad \chi_a=e_{q_0},\qquad\tau_1(a)=0.
\tag{3.1}
$$

On $0<t<1$ the current points strictly from $q_0$ to $q_1$. Its capped
endpoint mass is

$$
u_L=1-\exp\left\{-\int_0^1
   \min\!\left(\frac{p'(t)}{1-p(t)},L\right)dt\right\}>0.
\tag{3.2}
$$

After reaching $q_1$ at time $1$, absence of proposals through time $10$
has probability $e^{-9L}$. Hence the pre-read law satisfies

$$
\Pr_L(I=1)\ge u_Le^{-9L}>0.
\tag{3.3}
$$

For $L\ge L_{\rm f}=A\alpha/(2d)$, the original rising rate is bounded
by $L_{\rm f}$, as computed in III186.2, and $u_L=p(1)=x$. The lower
bound is then $xe^{-9L}$. This event retains every node-occupied path;
no path was discarded or reclassified as failure. Its required successor
is $M_1e_{q_0}/\|M_1e_{q_0}\|=0/0$, which is undefined. Altering bounded
rate values at isolated nodes cannot remove a positive no-jump event.
An arbitrary successor, reset, forced jump or changed report would be a
different contract. ∎

**Theorem 3.2 (cap-independent separation for lawful bounded-rate
comparisons).** Fix $P=\mathsf R(9^{10},f)$. Let $\eta$ be any complete
law on the same history space that executes this programme, has the
exact original pre-read vector, uses the literal report, retains $Q$ at
the read and uses the unchanged original pure update. Suppose its
configuration is a causal pure-jump process on the entire $E$, with
predictable total exit intensity bounded by some finite $L$, and no
forced or deterministic configuration changes, killing or censored
paths. Its rates need not be clipped native rates, and it may have
additional passive archives. Then

$$
\operatorname{TV}(\eta,\mu^P)\ge A=4c^2.
\tag{3.4}
$$

Proof. Exact pre-read vector and a lawful original update require
$\eta(Q_{10}\in E_1)=0$. A bounded total jump intensity gives conditional
probability at least $e^{-L(10-t)}$ of no subsequent configuration jump
between any deterministic $t<10$ and $10$. This is the usual survival
bound obtained by integrating the bounded conditional hazard; it holds
also for history-dependent predictable intensities. With no other way
to change configuration,

$$
\eta(Q_{10}\in E_1)\ge
 e^{-L(10-t)}\eta(Q_t\in E_1).
\tag{3.5}
$$

Thus $\eta(Q_t\in E_1)=0$ for every such $t$. At the mathematical time
$t=\pi/\alpha=5/3$, the original programme has mass $A$ in $E_1$ by
(3.1) and original equivariance. The retained path event at this time
gives (3.4). It is a mathematical event, not an extra read operation.
Adjoining passive archives cannot remove a retained path event. ∎

**Definition 3.3 (scope of the obstruction).** Theorem 3.2 concerns
bounded-total-rate, exact-pre-read-vector, no-forced-change comparisons
with the unchanged report and update. It is not an obstruction to every
finite resource model. Unbounded integrated-risk mechanisms, perturbed
vector histories, additional deterministic configuration changes, or
changed updates are outside that class and require their own source and
interface correspondence. In particular the all-$\mathsf T$ comparison
below is consistent with (3.4): the capped prefix itself fails the lawful
read requirement, rather than being a lawful $\eta$ with small TV.

For the address-$9$ witness, $W(q_0)=W(q_1)$, since the old terminal
omits $b_9$. Thus $\mathsf T(9^{10})$ has identical exact vector history
and identical old terminal law in the two models, while (3.3) separates
its configuration endpoint and prevents the corresponding pure read
update. These are distinct observation fibres, as in III190–194.

## 4. Native excess-current bound and full-history composition

**Theorem 4.1 (uniform native pulse certificate).** Put

$$
\lambda=2\alpha c,\qquad
\vartheta_L=\frac{\lambda^2}{L^2+\lambda^2}.
\tag{4.1}
$$

For a mathematical input $v\in\mathbb C^E$, let $\psi_s=U_j(s)v$ and
use its unnormalized current in

$$
C_L(v,j)=\sum_{r\ne q}\int_0^1
 \bigl([J_s(q,r)]_+-L|\psi_s(r)|^2\bigr)_+\,ds.
\tag{4.2}
$$

Then for every original address, every input and every $L>0$,

$$
C_L(v,j)\le2\vartheta_L\|v\|^2,\qquad
C_L(zv,j)=|z|^2 C_L(v,j).
\tag{4.3}
$$

This includes $v=0$. No zero vector is normalized.

Proof. Consider one active block of constant mass $m$. Singletons
contribute zero. By the literal off-diagonal Hamiltonian modulus
$\alpha c$, on any current-direction interval the departing coordinate
mass $p$ decreases and its outward current satisfies

$$
v_p=-p'>0,\qquad v_p\le2\alpha c\sqrt{p(m-p)}
       =\lambda\sqrt{p(m-p)}.
\tag{4.4}
$$

If $v_p>Lp$ with $p>0$, squaring implies
$p<\vartheta_Lm$. At $p=0$ the current is zero, so the integrand has its
literal zero value. On a direction interval, monotonicity alone gives

$$
\begin{aligned}
\int(v_p-Lp)_+\,ds
&\le\int_{\{0<p<\vartheta_Lm\}}(-p')\,ds\\
&\le\vartheta_Lm.
\end{aligned}
\tag{4.5}
$$

The first set may be smaller; connectedness of the rate superlevel set
is unnecessary. By III146.4–146.5, each block coordinate has the form
$B+D\cos(\alpha s+\theta)$, and $\alpha<\pi$. There are at most two
current-direction intervals during one unit pulse. Apply (4.5) to their
respective donors, and sum over the disjoint blocks, whose masses total
at most $\|v\|^2$. A zero-mass block contributes zero throughout. This
proves the bound. Scaling the current and coordinate masses by $|z|^2$
proves homogeneity directly in (4.2). ∎

**Theorem 4.2 (all finite no-read words and exactly admitted reads).** For
$P=\mathsf T(a)$ put $n=|a|$. For
$P=\mathsf R(a,f)$ require $\mathsf{Adm}(a)$ and put $n=|a|+|f|$.
Then the original and capped laws exist on Definition 1.2 and satisfy

$$
\operatorname{TV}(\mu^P,\mu_L^P)
 \le\min\{1,\mathcal E_L(P)\}
 \le\min\{1,2n\vartheta_L\}
 \le\min\{1,8\alpha^2c^2n/L^2\}.
\tag{4.6}
$$

The explicit source-dependent certificate is as follows. With the $v_k$
of Theorem 2.2, write $f=(h_1,\ldots,h_m)$ and
$w_{i,\ell}=K_{h_1\cdots h_{\ell-1}}M_i\chi_a$. Then

$$
\begin{aligned}
\mathcal E_L(\mathsf T(a))
 &=\sum_{k=1}^{|a|}C_L(v_k,j_k),\\
\mathcal E_L(\mathsf R(a,f))
 &=\sum_{k=1}^{|a|}C_L(v_k,j_k)
   +\sum_{i=0}^1\sum_{\ell=1}^{|f|}C_L(w_{i,\ell},h_\ell).
\end{aligned}
\tag{4.7}
$$

Under Assumption 1.3 the same estimates hold on the full
archive-inclusive history space, and adjoining those archives preserves
the core-history TV exactly. For each finite $N$ the bound with $n$
replaced by $N$ is uniform over the stated programmes with $n\le N$.

Proof. Existence is Theorem 2.2 for the cap and III146–148 for the
original. The coupling used here is the standard common-minimum-rate
split, as in [Anderson, §3.1][Anderson], applied to the already existing
original process rather than to a fictitious uniformly bounded original
generator. Until the first discrepancy, a native jump is shared at
intensity $\min(\sigma,L)$ and occurs only in the original at residual
intensity $(\sigma-L)_+$. After the first residual jump, continue each
marginal by its proper conditional continuation law, with a permanent
flag recording that a discrepancy has occurred.

More explicitly, independently mark original jumps before separation:
a jump of intensity $\sigma>0$ is accepted for both paths with
probability $\min(1,L/\sigma)$; rejection changes only the original
configuration. The cap then uses its correct continuation. While the
histories agree, the cap's hazard for a change is the accepted intensity
$\min(\sigma,L)$; a rejection leaves its configuration unchanged and
switches to precisely the same bounded-rate continuation rule. Thus its
marginal is (2.1), including exact jump times. The original marginal is
unchanged. This is a coupling construction, not an original control or
an additional report. It is not the assertion that two different risks
can simply share one exponential threshold.

The original jump count is at most $2n$. The predictable marking and
counting-compensator identity therefore apply with finite expectation;
the identity is the standard one used in [Georgii–Tumulka, Lemma 5][GT].
One can first stop away from zero departure masses and at finitely many
jumps, and then remove the stopping by original node safety and
monotone convergence. If $D$ is the first separation time, this gives

$$
\begin{aligned}
\Pr(D\le n)
&\le\mathbb E_{\mu^P}\int_0^n
 \sum_{q\ne Q_t}(\sigma_t(q\mid Q_t)-L)_+\,dt.
\end{aligned}
\tag{4.8}
$$

Indeed the exact first-separation integral has the additional predictable
indicator of no prior discrepancy, which is bounded by one. The
expectation in (4.8) is in the original marginal. Singular point values
at nodes are not divided by; on the original law they are null
occupation events.

Before the read, original square equivariance changes each pulse term
in (4.8) into

$$
\int_0^1\sum_{r,q\ne r}
 p_s(r)(\sigma_s(q\mid r)-\sigma_{L,s}(q\mid r))\,ds
 =C_L(v_k,j_k).
\tag{4.9}
$$

Both sides use zero integrands on zero coordinates. No capped Born law
is used. At a matching read the configurations, and hence the literal
reports, agree. Their original nonzero projection updates and their
exact phases then agree. The read itself adds no discrepancy. Admission
is needed to ensure a proper cap continuation after an earlier
separation as well, not just on the matching event.

On each positive original report branch, the post-read configuration has
the squared distribution of the normalized original successor by
III148.1. Homogeneity gives

$$
\tau_i C_L(w_{i,\ell}/\sqrt{\tau_i},h_\ell)
 =C_L(w_{i,\ell},h_\ell).
\tag{4.10}
$$

A zero original branch contributes exactly zero on the right, without a
conditional state. Thus (4.8) is bounded by (4.7). The sum of original
branch weights is one, so (4.3) pays at most $2\vartheta_L$ for every
post-read call. These are the original unconditional reference weights;
they do not replace the cap's actual report probabilities, which can
differ. This proves $\mathcal E_L(P)\le2n\vartheta_L$ without any
inverse branch probability or common amplitude floor.

Before separation every configuration and exact jump time agrees. So do
the literal calls, vectors, projective vectors, reports, updates and
terminal coordinates. The coupling inequality gives the core-history
bound in (4.6). With Assumption 1.3, append the same specified normalized
archive kernel. TV contraction gives one inequality and retaining the
core projection gives the reverse, exactly the supplied argument
III187.4. This also covers archive emission times, counts and absence.
Finally $\vartheta_L\le4\alpha^2c^2/L^2$. ∎

**Theorem 4.3 (all original reads with only the future capped).** For
every original $\mathsf R(a,f)$, retain its exact original joint prefix,
actual read, pure update, already occurred archives and configuration.
From that actual cut continue $f$ with (2.1) and fresh independent
comparison innovations. Denote the resulting law by $\mu_{L,\mathrm{post}}^{a,f}$.
Then it exists for every prefix, without (2.3), and

$$
\operatorname{TV}(\mu^{\mathsf R(a,f)},
                  \mu_{L,\mathrm{post}}^{a,f})
 \le\min\left\{1,\sum_{i,\ell}C_L(w_{i,\ell},h_\ell)\right\}
 \le\min\{1,2|f|\vartheta_L\}.
\tag{4.11}
$$

The full retained past may be included in the joint history, and the
archive-inclusive version still requires Assumption 1.3 for future
archive extensions.

Proof. The common prefix/read is the original law, so every positive
report has a nonzero original projection. It does not inherit the
capped-prefix defect of Theorem 3.1. Start the preceding coupling at this
actual cut and charge only post-read calls. Integrate the reference
compensator over the entire original prefix law. On each original
report branch its unconditional cut configuration distribution is the
original square distribution. Equations (4.9)–(4.10) give (4.11).
Including the whole past in the coupled history costs nothing, since it
was sampled identically. This does not assert square initialization
conditional on each hidden past, or a uniform error bound for each such
conditional history. ∎

## 5. Repeated original words: accumulated history versus terminal error

**Theorem 5.1 (bounded-length order and the unbounded-length
obstruction).** Use the actual address-$1$ pair
$q_0=\{3,7\}$, $q_1=\{1,3,7\}$, and the original words
$\mathsf T(1^{10m})$, $m\ge1$. Put

$$
P_0=10/3,\qquad L_{\rm f}=A\alpha/(2d),\qquad
r_L=\frac{A\alpha^2}{L^2+\alpha^2},\qquad
F_L=r_L\exp\left[-\frac{2L}{\alpha}\arctan(\alpha/L)\right],
\quad L\ge L_{\rm f},
\tag{5.1}
$$

and $\rho_L=(1-A)F_L/A$. Then on the common complete core history,

$$
\operatorname{TV}(\mu^{\mathsf T(1^{10m})},
                  \mu_L^{\mathsf T(1^{10m})})
 \ge1-(1-F_L)^{3m}.
\tag{5.2}
$$

The two exact vector histories are identical throughout. At the old
terminal, however, their TV is only

$$
z_{3m}=F_L\frac{1-\rho_L^{3m}}{1-\rho_L}.
\tag{5.3}
$$

Consequently terminal TV stays $O(L^{-2})$ uniformly in $m$ for large
$L$, whereas complete-history TV tends to one as $m\to\infty$ for each
fixed finite $L\ge L_{\rm f}$. In fact the supremum over all finite
original $\mathsf T$ words is one for every finite $L>0$. If

$$
B_N(L)=\sup_{|a|\le N}
 \operatorname{TV}(\mu^{\mathsf T(a)},\mu_L^{\mathsf T(a)}),
\tag{5.4}
$$

then for $N\ge10$, $L\ge L_{\rm f}$,

$$
1-(1-F_L)^{3\lfloor N/10\rfloor}
 \le B_N(L)\le\min\{1,2N\vartheta_L\}.
\tag{5.5}
$$

For $N\ge10$, $L\ge\max\{L_{\rm f},\alpha\}$ these bounds have order
$\min\{1,N/L^2\}$ with constants depending only on the native source.

Proof. III183 and III186–187 supply the original periodic word and its
one-cycle capped residual $F_L$. Their fixed four-call computation is
used here, not asserted as a new result. A mathematical period has
length $P_0$, and $U_1(P_0)=I$ exactly. At every $kP_0$ the original
configuration is $q_0$ almost surely. There are $3m$ such periods in
$10m$ uninterrupted full calls.

Starting a capped period with mass $z$ at $q_1$, the rising part is
uncapped for $L\ge L_{\rm f}$. Its no-jump survival factor from $q_0$
is $1-A$, giving peak mass $A+(1-A)z$. The descending part has survival
factor $F_L/A$, the same scalar integral as III186–187. Its endpoint
mass is therefore

$$
z\longmapsto F_L+\rho_Lz.
\tag{5.6}
$$

This proves (5.3) starting from $z=0$. Here $0<\rho_L<1$, and the old
terminal distinguishes the two configurations through $b_1$, so this is
exactly their terminal TV. For large $L$, both $F_L$ and $\rho_L$ are
$O(L^{-2})$, proving the uniform terminal assertion.

Conditional on no earlier bad node endpoint, the capped configuration
at the next period entrance is $q_0$ and its exact vector is ready.
Causal fresh future innovations give probability $F_L$ of a bad endpoint
in that period. Thus the unconditional probability of at least one
$q_1$ endpoint among the $3m$ periods is $1-(1-F_L)^{3m}$. The original
law assigns this retained path event probability zero, giving (5.2).
This calculation conditions inside a proof of an event probability; it
does not condition away paths from either programme law. No reset was
inserted. Unit-call seams concatenate the same Hamiltonian, and the
noninteger $kP_0$ are only mathematical history coordinates, never new
stopping or read controls.

Choose $m=\lfloor N/10\rfloor$ for the lower bound in (5.5), and use
Theorem 4.2 for the upper bound. The supplied inequalities
$e^{-2}r_L\le F_L\le r_L$, together with
$1-e^{-z}\ge(1-e^{-1})\min\{1,z\}$ and
$\lfloor N/10\rfloor\ge N/20$, prove the stated two-parameter order.
In particular a fixed-word $O(L^{-2})$ statement cannot be promoted to
an all-length small-error bound. For $0<L<L_{\rm f}$, use the same
periodic law with ten-call blocks: its probability $z_L$ of a $q_1$
endpoint from $q_0$ is strictly positive by the first-pulse/no-further-
proposal argument of Theorem 3.1, also valid at address $1$. On
$\mathsf T(1^{10m})$ the event of at least one bad ten-call endpoint has
probability $1-(1-z_L)^m$ under the cap and zero under the original.
This proves the all-finite-$L$ supremum assertion. ∎

**Theorem 5.2 (the actual read residual in closed form).** For
$a=9^{10}$ and $L\ge L_{\rm f}$ the pre-read capped mass obstructing
the original read is exactly

$$
\Pr_L(I=1)=F_L(1+\rho_L+\rho_L^2)>0.
\tag{5.7}
$$

Proof. The address-$9$ active pair in Theorem 3.1 has the identical
literal $Q_*$ block and three mathematical periods in ten whole calls.
Apply (5.6) three times. This is a quantitative use of the supplied
single-cycle residual at a different original interface. It still
defines only the pre-read law when the original update is undefined. ∎

## 6. Rate, word length and continuation resources

**Theorem 6.1 (charged finite-length approximation).** For a suite of
programmes in Theorem 4.2 with at most $N\ge1$ calls and target
$0<\varepsilon<1$, the sufficient choice

$$
L\ge 2\alpha c\sqrt{2N/\varepsilon}
\tag{6.1}
$$

gives complete-history TV at most $\varepsilon$. The proposal count for
one $n$-call capped programme is Poisson with mean $nL$, and the number
of accepted configuration jumps is almost surely at most $2n$. For the
choice of equality in (6.1), the largest proposal mean in the suite is
$2\sqrt2\alpha c\,N^{3/2}/\sqrt\varepsilon$. For Theorem 4.3 the
corresponding proposal count and error budget involve only $|f|$; the
entire original prefix/read and all their acquisition costs are retained.

Proof. Substitute (6.1) in (4.6). Independent rate-$L$ proposals over
$n$ unit intervals have the stated Poisson sum. Accepted jumps follow
exactly the current directions, even when comparison node occupation
occurs. Each block has at most two direction intervals, and after a
jump in one direction no further jump is possible in that interval.
Thus there are at most two accepted jumps per pulse, as in the original
native direction argument. A zero coordinate or singleton adds none.
The post-read-only assertions use the same construction on its future
intervals. ∎

**Definition 6.2 (resource and realization boundary).** Poisson counts
have unbounded support. They are finite almost surely and have the
stated expectation; no tail has been deleted, no deterministic proposal
budget has been obtained, and no hard timeout is part of either law.
Exact real jump times, matrix entries, rate evaluation and acceptance
probabilities have not been assigned finite-bit computation costs.
Model pulse time is not a calibrated physical clock or energy cost.
Independent innovations, physical adoption of the native matrices and
current law, source acquisition, actual read/update realization,
archive reliability and storage retain their separate obligations.
The sufficient cap is a mathematical comparison resource relation.
It is not a physical implementation theorem or a lower bound for every
possible approximation mechanism. The programme of exact mutual
recoverability of spatial relations, continuation, boundary and memory
is not identified with any fixed finite-length approximation task.

## 7. Connection to the existing unconditional recovery consumer

**Definition 7.1 (fixed original posterior defect).** Use exactly
[XI43, XI47][XI] and [native mixing §6.2][Mix]. Fix one original prefix
$a$ and one fixed standard Borel already-occurred past function
$Y_{\rm cut}$ allowed there, before the future request arrives. Let
$\Lambda_h$ be the entire original unconditional law of
$(I,Y_{\rm cut},W)$ under $\mathsf R(a,h)$ and $\mathcal C_h$ its
supplied canonical block-mixture comparison. On a positive original
branch let $\nu_i$ be the past marginal, $\rho_{i,y}$ its cut
configuration posterior, $\pi_{i,s}$ its within-tail square law and
$\beta_{i,s}(y)$ its actual tail posterior. Set

$$
\bar\rho_{i,y}(q)=\beta_{i,s}(y)\pi_{i,s}(q)\quad(q\in E_s),\qquad
D_{\rm tot}=\sum_{i:\tau_i>0}\tau_i\int
 \operatorname{TV}(\rho_{i,y},\bar\rho_{i,y})\,d\nu_i(y).
\tag{7.1}
$$

Unoccupied tails and zero report branches contribute zero, without
normalized directions or conditional states. The original supplied
fixed identity word $g$ and $0<\delta<1$ have the minorization and
unconditional consumer

$$
D_{\rm tot}\le\delta^{-1}\operatorname{TV}(\Lambda_\epsilon,\Lambda_g),
\qquad
\operatorname{TV}(\Lambda_h,\mathcal C_h)\le D_{\rm tot}.
\tag{7.2}
$$

These are suppliers, not new claims about the capped source. If $Y$ was
specified only almost surely on the original prefix law, choose one
fixed measurable extension to the common ambient prefix space before
using it on capped prefixes. Use this same extraction map for every
future request. A hidden-past function permitted mathematically by XI43
does not thereby acquire a physical readout.

**Theorem 7.2 (finite-rate payment for the original consumer).** If
$\mathsf{Adm}(a)$, let $\Lambda_h^L$ denote the same extraction from
the capped complete law. Under the required archive versions whenever
$Y_{\rm cut}$ uses archives,

$$
\begin{aligned}
D_{\rm tot}
&\le\delta^{-1}\left[
 \operatorname{TV}(\Lambda_\epsilon^L,\Lambda_g^L)
 +2\vartheta_L(2|a|+|g|)\right],\\
\operatorname{TV}(\Lambda_h^L,\mathcal C_h)
&\le2\vartheta_L(|a|+|h|)+D_{\rm tot}.
\end{aligned}
\tag{7.3}
$$

For every original $a$, with no admission restriction, let
$\Lambda_{h,\mathrm{post}}^L$ instead be extracted from Theorem 4.3.
Then

$$
\begin{aligned}
D_{\rm tot}
&\le\delta^{-1}\left[
 \operatorname{TV}(\Lambda_\epsilon,\Lambda_{g,\mathrm{post}}^L)
 +2|g|\vartheta_L\right],\\
\operatorname{TV}(\Lambda_{g^r,\mathrm{post}}^L,\mathcal C_\epsilon)
&\le2r|g|\vartheta_L+(1-\delta)^rD_{\rm tot},
\qquad r\in\mathbb N.
\end{aligned}
\tag{7.4}
$$

The comparisons in (7.3)–(7.4) are on the indicated cut/terminal space,
not complete histories of two different requested words.

Proof. Measurable extraction contracts the full-history TV in Theorem
4.2. Apply the triangle inequality to $\Lambda_\epsilon,\Lambda_g$
through their capped versions and use (7.2). The two error payments are
$2|a|\vartheta_L$ and $2(|a|+|g|)\vartheta_L$. The second line of (7.3)
uses the same contraction for $h$ and the second inequality in (7.2).
Here $D_{\rm tot}$ remains the original posterior defect. Original and
capped past and record marginals need not coincide.

For the post-only construction the past and read joint law is exactly
original, and $\Lambda_{\epsilon,\mathrm{post}}^L=\Lambda_\epsilon$.
Theorem 4.3 and (7.2) give the first line of (7.4). For the second line,
use the supplied original minorization
$P_g^u(q,r)\ge\delta\pi_s^u(r)$ within each occupied tail. The standard
residual kernel in XI47.9–47.10 contracts a zero-total-mass discrepancy
within each tail by $1-\delta$. Because $K_g=I$ exactly, each repetition
has the same vector and original transition kernel, with independent
unused innovations. Iteration gives

$$
\operatorname{TV}(\Lambda_{g^r},\mathcal C_\epsilon)
 \le(1-\delta)^rD_{\rm tot}.
\tag{7.5}
$$

The canonical comparison at $g^r$ equals that at $\epsilon$ on this
cut/terminal space. Summation uses the original unconditional $\tau_i$
weights on the disjoint $I$ slices. Now apply (4.11) for the same word
$g^r$ and the triangle inequality. No original minorization or square
law is being asserted for the capped transition kernel. ∎

**Definition 7.3 (precise recovery use).** Every fixed measurable
recovery event or decoder on the common complete history space inherits
the probability error in (4.6), by pulling its events back to that
space. This controls an already specified lawful recovery relation; it
provides no hidden-history acquisition or estimator. Spatial adjacency
appears here as the native pair relation, temporal continuation as the
ordered pulses and jump path, the boundary as the literal projection
read, and memory as the retained path and permitted archives. The
admission criterion specifies exactly when this comparison still
supplies the original boundary-to-continuation update. Theorems 3.1–3.2
show why approximate endpoint agreement cannot supply that exact domain
condition.

For example, to pay at most $\xi>0$ for the added term in the first line
of (7.3), it suffices to take

$$
L\ge2\alpha c\sqrt{\frac{2(2|a|+|g|)}{\delta\xi}}.
\tag{7.6}
$$

The supplied $118$-digit word-length bound and the small $\delta$ remain
charged. Neither this inequality nor (7.4) reduces their acquisition or
realization cost. A uniform claim over all future word lengths, exact
reconstruction from approximate records, and unrestricted all-$\mathsf R$
finite-rate implementation are separate unsupplied conclusions. In the
class of Theorem 3.2 the last is obstructed, while Theorem 4.3 retains the
exact original acquisition/read rather than solving it with a cap.

## 8. Mathematical correspondence and attribution

**Definition 8.1 (source-specific increment and suppliers).** The
uniform native certificate (4.3), its unconditional finite-word
composition on the exactly recognized domain (2.3), and the actual
$9^{10}$ read obstruction with its bounded-rate separation are
`repo-derived` mathematical synthesis. The repeated-original-word use
of the existing residual makes the necessary length dependence explicit.
The consumer consequences instantiate existing recovery results. These
are ordinary prose proofs, not Lean-kernel-verified declarations; no
worldwide novelty assertion is made.

The underlying original process, node safety, square initialization,
current-direction geometry, reports and archives are [III145–148][III].
The single-cycle $r_L,F_L$, fixed four-call bounds and shared-archive TV
argument are [III183, III186–188][III]. They are used inside the native
proofs rather than supplied again as independent results. The different
configuration, projective-vector and exact-vector history fibres remain
[III190–194][III]. The coherent perturbation and positive guard in
[IV205–208][IV] concern a separately paid auxiliary reader; no such
instantaneous detector is supplied here. [X13.2–13.3][X] concern actual
endpoint projection support and zero-extension boundaries, not a capped
configuration law. [XI43–53][XI] and [native mixing][Mix] supply the
actual continuation/posterior consumer and its fixed $g,\delta$.

The common/minimum coupling and finite-stage comparison tools are
`literature-attested`. [V64, §§6.4–6.5][V64] already supplies generic
integrable supremum-rate path comparison; the singular native rates do
not give that uniform integrable supremum merely from finite state
space. The pulse certificate above instead controls the excess under
the original square-weighted law. The existing formal declarations
[measurable maximal coupling][Coupling] and
[measurable TV contraction][Contraction] concern normalized supplied
kernels and measurable maps; neither creates a successor for a positive
zero-projection report or supplies (4.3).

[Georgii–Tumulka, math/0312294v2, Assumption A, Proposition 1(a), Theorem 1
and Lemma 5][GT] supplies original finite-state existence, node handling,
equivariance and the expected counting-intensity identity. As in
III146, use $H_{\rm GT}=2H_j$ to match its $\hbar=2$ with the source's
$\hbar=1$. This does not establish capped equivariance.
[Dürr–Goldstein–Tumulka–Zanghì, quant-ph/0407116v1, §§2.7, 5.2][DGTZ]
supplies minimal-current rates and their standard-current meaning.
Capping changes that property. [Anderson, arXiv:1109.2890v2,
§3.1][Anderson] supplies the mature shared-minimum/residual coupling.
Its sensitivity estimates assume global Lipschitz and uniform parameter
rate bounds; those estimates are not transplanted across the native
singular nodes. Only the coupling construction is used, with the native
excess estimate and original finite-jump law supplying the required
integrability here.

[III]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_III.md
[IV]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md
[X]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_X.md
[XI]: AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XI.md
[Mix]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_FIBONACCI_MIXING_CERTIFICATES.md
[V64]: AURIC_APPROXIMATE_RELATIONS_RIGIDITY_SQUARE_CALIBRATION_AND_QUANTUM_READOUT_STABILITY_V64.md
[Coupling]: ../../../D5/S3/Estimation/DataProcessing/MeasurableMaximalCoupling.lean
[Contraction]: ../../../D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction.lean
[GT]: https://arxiv.org/html/math/0312294v2
[DGTZ]: https://arxiv.org/html/quant-ph/0407116v1
[Anderson]: https://arxiv.org/html/1109.2890v2

## 追加锚（本行以下为增补区）
