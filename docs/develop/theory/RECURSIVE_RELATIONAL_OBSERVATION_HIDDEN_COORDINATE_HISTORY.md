# Hidden-coordinate recovery from original-source records

This is a continuation of the original-source observation problem in
[Free diffusion quotient rigidity, §§7, 11–12, 18 and 24–28][F].
It concerns that source's actual hidden $z$-coordinate, not an additional
native control or a proposed physical dimension. There are two different
results. A causal stopped visible record has a Lebesgue-equivalent hidden
coordinate law away from contact. Separately, reflection of the entire
non-Friedrichs endpoint gives an exact sign-risk statement even when the
whole held output history is supplied. The proofs have different
information and time domains.

The arguments are ordinary mathematics relative to the named analytic
suppliers. They are `repo-derived` source-specific deductions, with no
claim of Lean verification or worldwide priority. This continuation has
only appendable numbered sections; subsequent additions belong after its
final append anchor.

[F]: FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md
[E]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md
[S]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md
[G]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md

## 1. One unchanged source and two observation records

**Definition 1.1 (full endpoint and actual initialization).** For every
original $a,\eta>0$ retain exactly [F, (7.1)–(7.2)]:

$$
\begin{gathered}
G=H^1\times\mathbb R,\quad e=(0,0,0,0),\\
(x,y,z,w)(x',y',z',w')
 =(x+x',y+y',z+z',w+w'+xy'),\\
d\mu=dx\,dy\,dz\,dw,\quad
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad
X_3=\partial_z,\quad L=-\sum_{j=1}^3X_j^2,\\
L\Gamma=\delta_e,\quad g_c=16\sqrt{a\eta},\quad
S_{\min}=(aL-\eta\partial_w^2-g_c\Gamma)
             |_{C_c^\infty(G\setminus\{e\};\mathbb C)}.
\end{gathered}
\tag{1.1}
$$

$\Gamma$ is the original positive degree-$-3$ unit-source Green
field. Use the entire maximal-domain coefficient maps of
[E, Theorem 112.2], its actual selector and its coefficient-positive
normalized zero state:

$$
\begin{gathered}
C(h)=c_h>0,\quad \|h\|_{L^2(\mu)}=1,\quad
\rho_*=A(h)/C(h),\quad
D(H)=\{u\in D(S_{\min}^*):A(u)=\rho_*C(u)\},\quad
Hu=S_{\min}^*u,\\
m=h^2\mu,\quad J_hv=hv,\quad
K=J_h^{-1}HJ_h,\quad T_t=e^{-tK},\\
\mathscr V=\mathscr V_0\dotplus\mathbb C1,\quad
\mathscr E(f,g)=\int_{G\setminus\{e\}}
 \left(a\sum_j\overline{X_jf}X_jg
       +\eta\overline{\partial_wf}\partial_wg\right)dm.
\end{gathered}
\tag{1.2}
$$

Here $\mathscr V_0$ and the full operator domain are exactly
[S, (115.14)–(115.17)]. The conservative continuous diffusion
$\mathbf Z_t=(x_t,y_t,z_t,w_t)$ has its legitimate law $\mathbb P_e$
started at $e$ at original time zero, as in [S, §§116–117]. In
particular $h$ is smooth and positive off $e$, $m(G)=1$ and
$m(\{e\})=0$. No value $h(e)$, stationary initialization, source
replacement or Friedrichs replacement for $H$ is used. The Friedrichs
operator $F$ below has only its already supplied source-killed and
spectral roles.

**Definition 1.2 (native preparation and held boundary).** Write $p$ for
the original native probability called $Z$ in [F], to distinguish it
from the process. For every $0<p<1$ put $r=1-p$, $H_{\rm n}=r/2$;
fix any $k_0\in(0,H_{\rm n})$, preparation phases $\alpha_0,\beta_0$
and all original fixed rotations $\delta_{ij}$. Set

$$
\begin{gathered}
c_0=\tfrac12-k_0/r,\quad
\mathcal S=\{-k_0<x<H_{\rm n}-k_0\},\\
\Psi(x,y,z,w)
 =\bigl(k_0+x,[\alpha_0+y/2],
                    [\beta_0+c_0y-w/r]\bigr).
\end{gathered}
\tag{1.3}
$$

The brackets mean reduction modulo $2\pi$. Identifying each real
ordered pair with a complex number, the ten signed doubled outputs
$\mathcal R(k,\alpha,\beta)$, in their original order, are

$$
\begin{aligned}
Y_{01}&=2\sqrt{k(H_{\rm n}-k)}e^{i(\delta_{01}+\alpha)},&
Y_{02}&=2\sqrt{pk}e^{i(\delta_{02}+\beta)},\\
Y_{03}&=2\sqrt{k(H_{\rm n}-k)}e^{i(\delta_{03}+\alpha)},&
Y_{1,13}&=2\sqrt{k(H_{\rm n}-k)}e^{i(\delta_{1,13}-\alpha)},\\
Y_{3,13}&=2\sqrt{k(H_{\rm n}-k)}e^{i(\delta_{3,13}-\alpha)}.
\end{aligned}
\tag{1.4}
$$

For any $I=[l,u]\Subset(0,H_{\rm n})$ with $l<k_0<u$ define

$$
\theta_I=\inf\{t:k_0+x_t\notin(l,u)\},\qquad
O_t^I=\mathcal R\Psi(\mathbf Z_{t\wedge\theta_I}).
\tag{1.5}
$$

At exit the formula uses its continuous extension to $I$ and then
holds. The source itself continues after $\theta_I$. This observation
restriction changes neither the native open slab nor any command guard.

**Definition 1.3 (causal and entire-history experiments).** Let
$v_t=(x_t,y_t,w_t)$ be the unwrapped visible projection. It is not the
four-state step approximation denoted $V$ in [F, §25]. Let $U$ be any
standard Borel random variable independent of the entire source path.
A visible stopping rule is an almost surely finite nonnegative Borel
nonanticipating rule $R=R(U,v)$: the decision through $t$ depends only on
$U$ and $v|_{[0,t]}$. Write

$$
\mathcal H_R=\overline{\sigma\bigl(U,R,
                   (v_{s\wedge R})_{s\ge0}\bigr)},\qquad
\mathcal A_I=\overline{\sigma\bigl(U,(O_s^I)_{s\ge0}\bigr)}.
\tag{1.6}
$$

Completion is under the actual joint law. Conditional distributions
are taken on the underlying standard Borel record and then completed;
all equalities of their versions are almost sure. Arbitrary independent
randomization can be included in $U$. Original elapsed time is available
in these timed records. The source remains autonomous. Passive sampling,
selection, retention and processing are permitted; source-correlated
advice, a hidden-coordinate port and source-changing interventions are
not included. The entire future held path in $\mathcal A_I$ is a stronger
comparison experiment, not a causal service offered to execution.

## 2. Positive recovery of visible paths, contacts and the source clock

**Proposition 2.1 (based path recovery and exact domain).** For every
preparation above, on the actual stopped path image the records

$$
(U,R,(O_{s\wedge R}^I)_{s\ge0})
\quad\hbox{and}\quad
(U,R,(v_{s\wedge R})_{s\ge0})
\tag{2.1}
$$

have causal Borel inverse maps whenever $R\le\theta_I$. In particular
the corresponding stopping rules and completed stopped sigma-fields
agree on this domain. At a finite exit the inverse includes its endpoint.
For unrestricted observation time, $O^I$ recovers precisely the stopped
visible path $v_{\cdot\wedge\theta_I}$ by this construction.

Proof. Recover the height by $k=|Y_{02}|^2/(4p)$. Both relevant
amplitudes in (1.4) are positive on all of $I$, including $l,u$. The
based circle paths

$$
\xi_1=e^{-i(\delta_{01}+\alpha_0)}
             \frac{Y_{01}}{2\sqrt{k(H_{\rm n}-k)}},\qquad
\xi_2=e^{-i(\delta_{02}+\beta_0)}
             \frac{Y_{02}}{2\sqrt{pk}}
\tag{2.2}
$$

equal $e^{iy/2}$ and $e^{i(c_0y-w/r)}$, respectively. Let $a,b$ be
their unique continuous real argument lifts with $a(0)=b(0)=0$.
The actual source coordinates furnish these lifts, so uniqueness gives

$$
x=k-k_0,\qquad y=2a,\qquad w=r(2c_0a-b).
\tag{2.3}
$$

Restricting a based path to an earlier prefix restricts its unique lift;
thus the inverse is causal and commutes with stopping. It is Borel:
on each compact time interval, sufficiently close based circle paths
have their pointwise ratio in one fixed arc about one; the continuous
principal argument of that ratio is exactly the difference of their
lifts. This proves continuity in the compact-open topology locally at
each based path. Countably many compact intervals give Borel
measurability. Conversely (1.3)–(1.4) calculate all ten outputs from
the same visible path. Substitution in both orders gives identity on
the actual image, proving route agreement. This is the application of
the original formulas and standard covering-path lifting, not a new
general lifting theorem. A current wrapped output alone, an unknown
initial lift or a finite sample list does not satisfy this argument.
After holding, it gives no continuation of the source visible path.
$\square$

**Proposition 2.2 (contact and normalized clock suppliers).** On one
probability-one event under $\mathbb P_e$,

$$
v_t=0\ \Longleftrightarrow\ \mathbf Z_t=e
       \quad\hbox{for every }t\ge0.
\tag{2.4}
$$

For the held observation, $O_t^I=\mathcal R\Psi(e)$ holds exactly at
source contacts with $t<\theta_I$. The exact output history also
recovers the Revuz-$\delta_e$-normalized source clock
$\mathsf L_{\cdot\wedge\theta_I}$ of [F, §18], with its original
normalization. These assertions remain valid at the stopping times of
Definition 1.3 on their stated domains.

Proof. [F, Theorem 11.2] supplies one all-time exceptional-set avoidance
event. Its false preparation fiber includes the entire punctured line
$\{(0,0,z,0):z\ne0\}$. This proves (2.4), including all random times
on that event. The same theorem proves the held-output contact identity;
the exit height is $l$ or $u$, hence cannot be a preparation contact.

For precision, let $C_\epsilon^I(t)$ count only completed gaps $(g,d)$
away from the preparation output with $0\le g<d<\theta_I$,
$d\le t$ and $d-g>\epsilon$. Neither an open gap nor an exit-cut
gap is completed. With the actual killed operator $F$, put

$$
\nu(B)=\langle h,E_F(B)h\rangle_{L^2(\mu)},\qquad
\kappa(\epsilon)=\int_{(0,\infty)}s e^{-\epsilon s}\nu(ds).
\tag{2.5}
$$

[F, Theorem 18.2] gives, simultaneously for every finite $T$,

$$
\sup_{t\le T}\left|
 C_\epsilon^I(t)/\kappa(\epsilon)-\mathsf L_{t\wedge\theta_I}
\right|\longrightarrow0\quad\hbox{almost surely}.
\tag{2.6}
$$

The counts through $t$ use only that exact observed prefix. Thus
restriction at $R\le\theta_I$ recovers the stopped clock too. Its
known spectral denominator, original elapsed units and complete-gap
requirement are essential premises. This reuses the existing normalized
clock theorem; it neither installs an exact recorder nor derives that
clock from the finite approximations of [F, §§24–28]. Adding this
already measurable clock to (2.1) does not enlarge its sigma-field.
$\square$

**Proposition 2.3 (native action correspondence retained).** For every
original finite-variation relative command $\gamma=(a_c,b_c)$ with
terminal data $A_c=a_c(T)$, $B_c=b_c(T)$ and
$J_c=\int_0^T a_c\,db_c$, right multiplication by
$(A_c,B_c,0,J_c)$ gives

$$
(x,y,w)\longmapsto(x+A_c,y+B_c,w+J_c+xB_c).
\tag{2.7}
$$

Its image under $\Psi$ is exactly

$$
(k,\alpha,\beta)\longmapsto
 \bigl(k+A_c,[\alpha+B_c/2],
  [\beta+(1/2-k/r)B_c-J_c/r]\bigr).
\tag{2.8}
$$

The complete legal domain is
$k+\min a_c>0$, $k+\max a_c<H_{\rm n}$, with the original
pulled-back domain under concatenation. All ten readouts are (1.4).

Proof. This is [F, Proposition 7.2]: substitute the actual group product
in (1.3), and do so at every prefix. Composing two products gives the
original cross term $A_cB_c'$, so composition and all inverse routes in
Proposition 2.1 agree wherever the full guard holds. The coordinate $z$
is unchanged by this deterministic command. This statement does not
assert that native commands are installed interventions on the
autonomous diffusion, or that its generator descends through $\Psi$.
$\square$

## 3. C: conditional hidden laws at causal noncontact times

**Theorem 3.1 (contact classification and the exact recovery optimum).**
For every source, preparation, independent seed and visible stopping
rule of §1, let
$\pi_R=\mathbb P_e(z_R\in\cdot\mid\mathcal H_R)$. Then

$$
\begin{cases}
\pi_R=\delta_0,&v_R=0,\\
\pi_R\sim\operatorname{Leb}_{\mathbb R},&v_R\ne0.
\end{cases}
\tag{3.1}
$$

Equivalence is on the whole real line, not just non-atomicity on a
smaller support. Consequently every real $\mathcal H_R$-measurable
estimate $\widehat z$ satisfies the exact identity

$$
\mathbb P_e(\widehat z=z_R)
 =\mathbb P_e(v_R=0,\ \widehat z=0)
 \le\mathbb P_e(v_R=0).
\tag{3.2}
$$

The maximum is attained by $\widehat z=0$. Exact full current-state
recovery from this record is possible almost surely if and only if
$R$ is a source contact almost surely. At every deterministic $t>0$
every such real estimator has exact success probability zero. On
$R\le\theta_I$ these conclusions apply equally to the exact native
prefix (2.1), including its recovered stopped source clock.

Proof. The contact part follows from (2.4), with $z_0=0$ also covering
$R=0$. For the other part we localize only a final observed noncontact
interval; no change of measure across the singular source is needed.

On $G\setminus\{e\}$, the local generator of the actual process is

$$
\begin{aligned}
\mathcal D_h&=\mathcal D_0+b,\\
\mathcal D_0&=a(X_1^2+X_2^2+X_3^2)+\eta\partial_w^2,\\
b&=2a\sum_{j=1}^3(X_j\log h)X_j
             +2\eta(\partial_w\log h)\partial_w.
\end{aligned}
\tag{3.3}
$$

This follows by expanding $-h^{-1}H(hf)$ on punctured compact tests
and using $Hh=0$ there; the local full-form generator agrees with it.
Its noise frame is globally Lipschitz and nonsingular since $a,\eta>0$.
A reference process for $\mathcal D_0$ has independent standard
Brownian motions $B^1,\ldots,B^4$ and equations

$$
\begin{aligned}
dx&=\sqrt{2a}\,dB^1,&dy&=\sqrt{2a}\,dB^2,\\
dz&=\sqrt{2a}\,dB^3,&dw&=x\sqrt{2a}\,dB^2+\sqrt{2\eta}\,dB^4.
\end{aligned}
\tag{3.4}
$$

There is no omitted Itô correction: $X_2x=0$. In particular the
future visible triple does not use the fresh $B^3$.

Fix a rational $s>0$, an integer $T>s$, and a bounded rational open
box $D\subset\mathbb R^3$ whose closure avoids zero. Define the
observed event

$$
E_{s,T,D}=\{s<R\le T,\ v_{[s,R]}\subset D\}.
\tag{3.5}
$$

It belongs to $\mathcal H_R$. For each positive integer $M$ restrict
further to
$E_M=E_{s,T,D}\cap\{\sup_{s\le t\le R}|z_t|<M\}$.
The latter event need not be observed. On a compact neighborhood of
$\overline D\times[-M,M]$, the original drift is smooth and its
Brownian-frame coefficients

$$
\vartheta=\bigl(\sqrt{2a}X_1\log h,
 \sqrt{2a}X_2\log h,\sqrt{2a}X_3\log h,
 \sqrt{2\eta}\partial_w\log h\bigr)
\tag{3.6}
$$

are bounded. The neighborhood avoids $e$ for every hidden coordinate
because $0\notin\overline D$. Choose a smooth compact cutoff equal
to one there and multiply $\vartheta$ by it, extending by zero.
The resulting drift perturbation of (3.4) is smooth with compact
support. Both this cutoff process and (3.4) are nonexplosive, with
globally Lipschitz noise and drift. On $[s,T]$ their path laws are
equivalent: the Girsanov density is

$$
\exp\left(\int_s^T\vartheta^{(M)}\!\cdot dB
                   -\tfrac12\int_s^T|\vartheta^{(M)}|^2dt\right)>0.
\tag{3.7}
$$

Boundedness gives the martingale condition on this finite horizon.
This is also the finite-path theorem of Elworthy–Le Jan–Li cited in
§8. It is applied to the cutoff processes on all of $\mathbb R^4$,
not to the original singular process globally.

To retain the actual past, give both reference and cutoff continuations
the same joint distribution of $U$ and the entire actual source past
through $s$, and start at its actual endpoint. Their fresh Brownian
increments are independent of this past. Equivalence remains true
after integrating these conditional continuation laws. Off $e$,
local smooth martingale-problem uniqueness identifies the actual
continuation and the cutoff continuation up to exit from
$D\times(-M,M)$. On $E_M$ that exit is strictly later than $R$.
Nonanticipation makes $R$ and its stopped record determined before
the exit. Thus the original and the single free-reference law have
equivalent stopped-path restrictions on $E_M$. This statement concerns
only information through $R$; no assertion about their continuations
after the exit is used. Events outside $R\le T$ can be given a
cemetery stopped-record value in this comparison.

Every continuous hidden path on $[s,R]$ is bounded, so
$E_{s,T,D}=\bigcup_M E_M$ under either law. The same free reference
is used for every $M$; only its equivalent cutoff comparison varies.
Hence the two stopped-path laws restricted to $E_{s,T,D}$ are
equivalent. Indeed an event has zero mass on the union exactly when
it has zero mass on each $E_M$. Pushforward gives equivalence of the
joint laws of the stopped visible record and $z_R$ on this observed
event.

Under the free reference, conditional on the full past through $s$,
$U$ and the stopped visible record, the time $R>s$ is fixed and the
fresh $B^3$ is independent. Therefore the endpoint law is

$$
N\bigl(z_s,\,2a(R-s)\bigr).
\tag{3.8}
$$

It has a strictly positive density on all $\mathbb R$. Disintegrating
away the extra true past gives a mixture of such densities, still
equivalent to Lebesgue measure, for almost every observed record in
$E_{s,T,D}$.

Here is the conditional-measure step explicitly. If the reference
joint law is $\lambda(dq)\,k(q,dz)$ and an equivalent joint law has
positive finite density $L(q,z)$, its conditional law is

$$
\frac{L(q,z)\,k(q,dz)}{\int L(q,u)k(q,du)}.
\tag{3.9}
$$

The denominator is finite and positive for almost every record.
Thus conditional equivalence is preserved. This is conditional Bayes
disintegration; it does not say the original posterior is Gaussian.
Applying it on the observed event (3.5) gives the second part of
(3.1) there.

On every path with $v_R\ne0$, continuity supplies some final interval
$[s,R]$ and such a box $D$; $R>0$ because $v_0=0$. Rational $s$,
rational boxes and integer $T$ give a countable cover of that event.
The conditional equivalence therefore holds on the whole noncontact
branch, without an uncountable exceptional-set argument.

An atomless conditional law assigns zero mass to the singleton
$\{\widehat z(q)\}$, also when the singleton depends measurably on
the record. Equivalently its graph is null for record law times
Lebesgue measure. Conditioning on the two branches proves (3.2).
The visible endpoint is in the record; on contact the full endpoint
is $e$, and off contact its remaining coordinate cannot be recovered.
This proves the full-state criterion. Finally [S, Theorem 117.2]
gives $\mathbb P_e(\mathbf Z_t\in dp)=g_t(p)m(dp)$ for each $t>0$;
since $m(\{e\})=0$, the contact probability at that fixed time is
zero. Proposition 2.1 and (2.6) give the native-prefix assertions.
$\square$

**Corollary 3.2 (estimator quantifier at contact).** Success equals the
contact probability for an estimator that returns zero on the contact
branch. It need not do so for every estimator. For example $R=0$ is a
lawful rule with contact probability one; the constant estimate one
has success zero, while the constant estimate zero has success one.

Proof. Apply (3.2) and the actual initialization. This also includes
the degenerate base time without extending the positive-time
zero-success assertion to time zero. $\square$

## 4. C: actual projected timed-service records

**Definition 4.1 (one coupled service and its projection).** Fix
$\epsilon,\delta>0$ and the actual recursion of [F, Theorem 24.3],
coupled to this very $\mathbf Z$. Its successive arrivals are
$(R_i,C_i,P_i)$, with types $\mathrm E,\mathrm C,\mathrm D$.
In source mode begun at $c$, let

$$
g_c(t)=\sup\{s\in[c,t]:v_s=0\},\qquad
D_\epsilon(c)=\inf\{t\ge c:t-g_c(t)\ge\epsilon\}.
\tag{4.1}
$$

By (2.4) this is exactly the original age-$\epsilon$ entrance
announcement, and $P_i=\mathbf Z_{R_i}$. After an entrance or survived
release, the next event is first source contact within $\delta$
(type $\mathrm C$) or survival to $\delta$ (type $\mathrm D$).
A contact restarts source mode; it does not kill the full source.
The actual Borel laws and reached-state versions remain [F,
(24.1)–(24.5)], calibrated to its $F,h,q,P^0,\nu,\kappa$.

Let $\mathcal J_i$ be the completed sigma-field generated by $U$,
all preceding and current types and timestamps, the corresponding
projected states $(x,y,w)(P_j)$, and the request/nonarrival record
through $R_i$. It omits every hidden $z$ payload. Request modes are
those of this same recursion, not a new policy depending on an
unrevealed state. The full service record of [F, Assumption 25.1]
is a different record: at arrival it explicitly discloses all four
actual coordinates.

**Theorem 4.2 (projected releases do not disclose noncontact hidden
states).** For every release index $i$, $R_i$ is a finite Borel
visible stopping rule and $\mathcal J_i\subseteq\mathcal H_{R_i}$.
On each positive-probability branch $C_i=\mathrm E$ or
$C_i=\mathrm D$, the conditional law of $z_{R_i}$ given
$\mathcal J_i$ is equivalent to Lebesgue measure. Every
$\mathcal J_i$-measurable real estimate has exact success zero
on those branches. On $C_i=\mathrm C$ the complete state is $e$.
For an interpretation entirely in native boundary history retain
$R_i\le\theta_I$; no post-exit native inverse is asserted.

Proof. The contact set in (4.1) is a Borel closed-set functional of
the visible path. The age entrance is a nonanticipating Borel rule:
the event that it occurs strictly before $t$ is tested by rational
times $q<t$ having no zero on $[q-\epsilon,q]$, as in the original
proof of [F, Theorem 24.3]. The original excursion law assigns no
mass to lifetime $\epsilon$; thus an age-$\epsilon$ arrival is
inside a noncontact excursion almost surely. Recursively the next
contact or elapsed-$\delta$ decision has the same stopping and
measurability properties. The original recurrence and reached-state
versions give finite waits; their countable intersection gives
finiteness at each index. Ties at the killed lifetime $\delta$ have
zero probability, with the original contact-first convention retained.

This proves that the times, types, request starts, nonarrival intervals
and projected states through $R_i$ are functions of the stopped
visible path. Therefore $\mathcal J_i\subseteq\mathcal H_{R_i}$.
An $\mathrm E$ event has positive excursion age, a $\mathrm D$
event survives without contact, and a $\mathrm C$ event is exactly
contact. Apply Theorem 3.1 at $R_i$. The event
$\{C_i\in\{\mathrm E,\mathrm D\}\}$ is $\mathcal J_i$-measurable
and is noncontact. Conditioning down mixes the Lebesgue-equivalent
conditional laws on that branch. A mixture remains equivalent: it
annihilates every Lebesgue-null set, and its density is positive for
Lebesgue-almost every real value by Fubini. This also proves a zero
probability of hitting any measurable estimator graph. On the contact
branch (2.4) gives $e$. Proposition 2.1 gives the native-history
interpretation before or at its observation exit. $\square$

The full service can disclose $z_{R_i}$ exactly because it supplies
additional information by premise. Theorem 4.2 neither disputes its
joint coupling nor constructs it from the projected record. Independent
resampling from a posterior would be a new random value, not recovery
of this same actual endpoint.

## 5. D: reflection of the entire endpoint and source-start path law

**Theorem 5.1 (full-domain hidden-coordinate reflection).** Put
$\mathfrak r(x,y,z,w)=(x,y,-z,w)$ and $\mathcal Pf=f\circ\mathfrak r$.
For every original $a,\eta>0$, $\Gamma\circ\mathfrak r=\Gamma$,
$h\circ\mathfrak r=h$, and

$$
\begin{gathered}
A(\mathcal Pu)=A(u),\quad C(\mathcal Pu)=C(u)
                       \quad(u\in D(S_{\min}^*)),\\
\mathcal P D(H)=D(H),\quad H\mathcal P=\mathcal PH,\quad
\mathcal P\mathscr V=\mathscr V,\quad
\mathscr E(\mathcal Pf,\mathcal Pg)=\mathscr E(f,g),\\
\operatorname{tr}(\mathcal Pf)=\operatorname{tr}(f)
                       \quad(f\in\mathscr V),\quad
T_t\mathcal P=\mathcal PT_t.
\end{gathered}
\tag{5.1}
$$

The full continuous-path law under the actual $\mathbb P_e$ is
invariant under pointwise $\mathfrak r$. The observation exit and
the entire held path $O^I$ are unchanged pathwise by reflection.

Proof. The symmetry-through-full-form method is already used for
planar rotations in [S, the proof of Theorem 120.2]. Here the
specific hidden reflection additionally requires its actual maximal
coefficients and is consumed into the path-law and risk conclusions.
The independent $z$ heat factor in [G, Proposition 85.4,
(85.12)] is $(4\pi t)^{-1/2}e^{-z^2/(4t)}$. Its central inverse
transform and the unit-source heat integral are therefore $z$-even.
This proves parity of the actual $\Gamma$ where that representation
applies; its smoothness off $e$ extends the identity to all of
$G\setminus\{e\}$. No finite value at $e$ is required. The map
$\mathcal P$ is unitary for raw Haar measure, preserves the punctured
core, commutes with $X_1,X_2,\partial_w$ and reverses $X_3$.
It consequently commutes with $S_{\min}$ and its adjoint on their
whole respective domains. This checks the potential as well as the
principal part.

The source coefficients require a further check. In the exact original
chart [E, (109.1)–(109.3)] put
$\kappa_0=\sqrt{\eta/a}$, $s=w-xy/2$, $t=s/\kappa_0$ and
$\xi=(x,y,z)$. Reflection preserves $s$ and
$R=|(\xi,t)|$; on $S^3$ it is an orthogonal reflection of the
$z$ component. It fixes the positive angular profile

$$
e_0=\frac{\Phi|_{S^3}}{\|\Phi|_{S^3}\|_2},\qquad
\Phi(\xi,t)=\frac{2}{\pi|\xi|}
                         \arctan\frac{|\xi|}{|t|},
\tag{5.2}
$$

with the supplied continuous values. Pullback also preserves the
weighted cylinder remainder space in the full expansion [E, (112.2)]

$$
H_u(\tau,\omega)=(A(u)+\tau C(u))e_0(\omega)+Z_u(\tau,\omega),
\qquad e^{\tau/8}Z_u\in H^1.
\tag{5.3}
$$

Uniqueness of those coefficients gives their two identities in (5.1)
for every complex maximal-domain vector, not just for zero states.
The reflected coefficient-one maximal zero vector is again the
coefficient-one vector of [E, Theorem 110.2]; its uniqueness gives
$h\circ\mathfrak r=h$. The selector $A=\rho_*C$ is therefore
preserved in its entire domain, with precisely the same $\rho_*$.
The Friedrichs completion, when used as a supplier, is preserved by
the same punctured-core unitary; it has not replaced this selector.

Now $m$ is invariant under reflection. The punctured weighted form
norm, its closure $\mathscr V_0$ and the constant in
$\mathscr V_0\dotplus\mathbb C1$ are preserved. Formula (1.2)
gives energy invariance and thus semigroup commutation. The source
trace is the constant coefficient in that direct sum; it is invariant
too. On the operator domain this agrees with the supplied identity
$\operatorname{tr}(f)=C(hf)/C(h)$. Thus the trace statement includes
the singular source component, rather than only off-source tests.

To pass to the actual source-start law, use [S, Theorem 117.2]: for
each $t>0$ and bounded Borel $f$,
$\mathbb E_e f(\mathbf Z_t)=\operatorname{tr}(T_t[f])$.
Trace invariance and semigroup commutation prove invariance of this
marginal. For several positive ordered times, the Markov product is
a nested expression of $T_t$ and multiplication by the test functions.
Pullback by $\mathfrak r$ commutes with the former and transports the
latter to the reflected test. The initial marginal at the earliest
positive time is absolutely continuous with respect to $m$ by the
same theorem; subsequent marginals also are. Hence the $L^2(m)$
commutation identities determine these actual expectations without
transition-version ambiguity on $m$-null sets. Taking the source
trace at the first step proves reflection invariance of every
finite-dimensional law, including time zero because $\mathfrak r e=e$.
Rational-time cylinders generate the Borel sigma-field of continuous
paths, giving full path-law invariance. This uses the legitimate
source start, not an invariant-law surrogate.

Finally (1.3)–(1.5) ignore $z$, including the height exit, so the
observed path and its holding time agree pointwise on a reflected
pair of source paths. $\square$

## 6. D: entire-history sign risk and quantitative coordinate error

**Theorem 6.1 (deterministic and random time domains).** Under all
parameters of §1, for every fixed original time $t>0$,

$$
\mathbb P_e(z_t=0)=0,\qquad
\mathbb P_e(z_t>0\mid\mathcal A_I)
 =\mathbb P_e(z_t<0\mid\mathcal A_I)=\tfrac12.
\tag{6.1}
$$

Every $\mathcal A_I$-measurable binary decision for the sign has
error exactly $1/2$, also conditional on any positive-probability
event of $\mathcal A_I$. For every real $\mathcal A_I$-measurable
estimate $\widehat z$, every $d>0$ and every
$B\in\mathcal A_I$,

$$
\mathbb P_e\bigl(B,\ |\widehat z-z_t|\ge d,\ |z_t|\ge d\bigr)
 \ \ge\ \tfrac12\mathbb P_e\bigl(B,\ |z_t|\ge d\bigr).
\tag{6.2}
$$

For $B$ the whole space, its right-hand side is strictly positive
for every $d>0$. In particular exact full source-state recovery at
that fixed time is impossible from this record.

For every finite nonnegative $\mathcal A_I$-measurable random time
$S$, which need not be a stopping time, the exact assertion is

$$
\mathbb P_e(z_S>0\mid\mathcal A_I)
 =\mathbb P_e(z_S<0\mid\mathcal A_I)
 =\tfrac12\mathbb P_e(z_S\ne0\mid\mathcal A_I).
\tag{6.3}
$$

The analogue of (6.2) holds with $t$ replaced by $S$, without a
claim that its right-hand side is positive. At a genuine observed
source contact before $\theta_I$, $z_S=0$ on that contact event.
At $S=0$ it is zero identically. The deterministic-time target $z_t$
in (6.1)–(6.2) belongs to the unheld original source, also when
$t>\theta_I$; it is not silently replaced by $z_{t\wedge\theta_I}$.

Proof. On canonical path space reflect the source path and leave $U$
fixed. Independence of $U$ and Theorem 5.1 make this a
measure-preserving involution. Its observed whole history is fixed,
so each bounded $\mathcal A_I$-measurable test is invariant, up to
the usual null modification. Reflection interchanges $z_t>0$ with
$z_t<0$; their integrals against every such test agree. The
deterministic-time law $g_tm$ of [S, Theorem 117.2] gives zero mass
to the raw-Haar-null hyperplane $z=0$, since $m=h^2\mu$.
The two conditional probabilities therefore sum to one and are
each $1/2$. A decision partitions the record into its positive
and negative choices; integrating (6.1) on that partition proves
the exact error, including after conditioning on any observed event.
This includes any randomized causal observer dominated by the record.

For (6.2), fix a reflected pair with $|z_t|\ge d$. Its two target
values are $z_t$ and $-z_t$, separated by at least $2d$, while $B$
and the estimate agree on the pair. The estimate cannot have
distance strictly less than $d$ from both targets. Consequently

$$
\mathbf1_{\{|\widehat z-z_t|\ge d\}}
 +\mathbf1_{\{|\widehat z+z_t|\ge d\}}\ge1
                   \quad\hbox{on }\{|z_t|\ge d\}.
\tag{6.4}
$$

Multiply by the invariant indicator of $B\cap\{|z_t|\ge d\}$
and integrate. The two integrals on the left are equal by reflection,
which proves (6.2), including the equality boundary $|z_t|=d$.
Strict positivity for the whole space follows because $g_t>0$
$m$-almost everywhere, $h>0$ off $e$, and the set $|z|\ge d$
has positive Haar measure. No moment or uniform density bound is
needed.

If $S$ is $\mathcal A_I$-measurable, it is invariant under the
same involution. Evaluating the continuous path at $S$ is measurable;
reflection therefore interchanges the positive and negative events
at $S$ as well. Their sum is now the event $z_S\ne0$, giving
(6.3); the same pair argument gives the stated error inequality.
The all-time identity (2.4) and [F, Theorem 12.2] identify genuine
observed contacts with $e$. There is no deterministic-time density
argument at a random contact. $\square$

Theorem 3.1 does not prove (6.1): a Lebesgue-equivalent conditional
density can favor one sign. Conversely (6.3) permits symmetric atoms
and does not prove (3.1). Their distinct causal-prefix and
entire-held-history records, contact branches and proofs are essential.
Neither statement alone addresses a fixed time-homogeneous Markov
recovery link or its full-source continuation tests.

## 7. Retained use, independent meanings and same-run resources

**Proposition 7.1 (projected delivery and the existing native consumer).**
Under [F, Assumptions 25.1 and 26.1], retain the same arrival times,
types and source samples of §4, and deliver only $(x,y,w)$ at
$\mathrm E/\mathrm D$ arrivals; a $\mathrm C$ arrival denotes the
known point $e$. The existing consumer of [F, Definition 26.2]
uses this projection without changing its numerical native commands,
own exit or ten outputs. It retains the original conclusions and
domains of [F, Theorems 26.3 and 27.1]. This is reuse of that
consumer, not a new source sampler or an acquisition theorem.

Proof. Each cell prescription uses the two most recent released
$(x,y,w)$ triples, known at its grid start, clips its own next
height segment and applies the original six-leg connector. Its
subdivision, chronological integral, guards and readout formulas
contain no $z$. Induction over cells thus gives literally identical
issued instructions, and hence the same actual endpoint and all
outputs on each run. It uses no reset of the accumulated real
integral at a source contact. In particular, at a completed held cut
the realized finite command and its current native coordinates are
available for legal native continuation; any further command must
obey the same full prefix guard and concatenation refusal rule of
Proposition 2.3. This is callable mathematical native use under the
actuation premise, not an authentic hardware grant created by a
decoder. The existing common-source limit, for each deterministic
design sequence $\epsilon_n,\delta_n,\rho_n\downarrow0$,
$N_n\to\infty$, is unchanged:

$$
\|\mathcal O_n-O^I\|_{[0,T]}\to0,\qquad
\widehat S_n\to T\wedge\theta_I
                         \quad\hbox{almost surely}.
\tag{7.1}
$$

The target exit and target modulus remain proof quantities, not
execution inputs. $\square$

**Definition 7.2 (meaning and recovery table).** All rows below refer
to one jointly realized path and, when used, its coupled service and
actual native consumer. A record is retained only if the stated
experiment grants or acquires it.

| Expression | Independently specified meaning | Recovery established here or reused |
| --- | --- | --- |
| Space | The actual point $\mathbf Z_t\in G$; separately, its native height and two phases where $\Psi$ is defined | Projection gives the native point; (1.4) and its two nonzero pairs give the inverse between that native point and its current boundary outputs. The full point has the hidden-law obstructions of §§3–6. |
| Time | Original elapsed time, actual source contacts and their completed-gap chronology | The exact history gives the stopped normalized source clock by (2.5)–(2.6). A clock value alone has no state inverse supplied here. |
| Boundary | The ordered ten native coherence outputs, together with their height observation exit | Its based continuous prefix gives the stopped visible triple by (2.2)–(2.3). Its entire held history has the separate sign-risk theorem. |
| Memory | A chosen observer's acquired and retained prefix, timestamps, request status and computed controller state | Projected releases are retained in $\mathcal J_i$ and suffice for the existing consumer. They do not disclose actual noncontact $z$. The full continuous history is only an upper-information comparison experiment. |

The path inverses in §2 commute with restriction and stopping and agree
with direct projection. Proposition 2.3 checks the actual native
deterministic action square, including domains and complete readouts.
For the autonomous source, future prediction at a visible stopping
time remains possible as posterior averaging: for bounded Borel $f$
and $s\ge0$,

$$
\mathbb E_e\bigl[f(\mathbf Z_{R+s})\mid\mathcal H_R\bigr]
 =\int T_sf(v_R,z)\,\pi_R(dz).
\tag{7.2}
$$

The notation on the right restores the coordinate order $(x,y,z,w)$.
This is the original strong Markov property followed by conditional
expectation, with legitimate versions on reached states. It does not
make $v$ a Markov state, supply an effective finite filter, or assert
controlled-diffusion equivalence. Waiting for a later contact recovers
the then-current $e$; it does not recover an earlier noncontact value.

**Definition 7.3 (one-run resource vector and acquisition boundary).**
The continuous records granted in Theorems 3.1 and 6.1 contain exact
real information and unrestricted monitoring/retention. No finite
sample, finite-bit, finite-bandwidth or finite-storage implementation
of them is asserted. Their strength makes the obstructions apply to
every passive actual record measurable in them; it is not a resource
saving credited to a receiver.

For an actual finite service/consumer run on $[0,T]$, keep its own
$\epsilon,\delta,N,\rho$ and its actual polygon variations
$V_A,V_B,V_W$, with $K_I=\max(|l-k_0|,|u-k_0|)$. The reused bounds
on this same run are

$$
\begin{aligned}
N_{\rm arr}&\le2\lfloor T/\epsilon\rfloor+\lfloor T/\delta\rfloor,\\
N_{\rm init}&\le N_{\rm arr}+1,\\
N_{\rm legs}&\le
6\left(N+\frac{V_A+V_B}{\rho}
          +\frac{V_W+K_IV_B}{\rho^2}\right)+1.
\end{aligned}
\tag{7.3}
$$

These are event and leg counts from [F, (24.6), (26.5)]. Type
$\mathrm C$ packets denote a known source, while each
$\mathrm E/\mathrm D$ packet has three exact-real projected state
fields instead of four, as well as its type and original timestamp.
For realized arrival counts $n_{ED}$ and $n_C$, the literal full
service of [F, Assumption 25.1] delivers $4(n_{ED}+n_C)$ state
coordinate fields. This projected format delivers $3n_{ED}$ such
fields, omitting $n_{ED}+4n_C$. If contact packets instead keep their
four known zero coordinates, deleting only the hidden coordinate
from $\mathrm E/\mathrm D$ packets omits exactly $n_{ED}$ fields.
Types, timestamps and framing are counted separately in either format. It changes no event
time, monitoring interval, native leg or own exit. The law provider
can still require hidden state internally; deletion of delivered
fields does not remove its source calibration or memory.

The simultaneous resource vector includes the original source and
preparation, fixed rotations and constants, calibrated
$F,h,q,P^0,\nu,\kappa$ service, exact original clock, nonarrival
monitoring and notification, selection and request work, actual
arrived state fields/types/timestamps, retained and callable records,
all comparisons, clipping, ceiling and connector calculations,
actuation durations and operands, requests and complete returns,
framing and acknowledgement traffic, and all retained copies and
workspace. Exported or duplicated records and computed predictions
pay their own arithmetic, precision, storage and output costs.
Independent randomization has its own source and retention cost;
independence gives no access to a hidden source seed. No physical
tariff or measured bit count is supplied for these exact-real
contracts. Finite per-run counts do not give a uniform lifetime
memory, precision, speed, energy or computation bound.

The projected values are measured service disclosures under its
availability premise; lifted paths, posterior laws, connector targets
and regenerated outputs are computed mathematical objects. Theorems
3.1 and 6.1 do not acquire an ideal path. Proposition 7.1 does not
acquire the service from bare native operations. If only the existing
native-output approximation is required, its consumer already avoids
$z$ and reuse suffices. If the task is instead sign recovery at a
specified $t>0$, an explicitly installed port disclosing the actual
bit $\mathbf1_{\{z_t>0\}}$ supplies it. Both bit values occur, so
two distinct messages are necessary for deterministic exact success
in that added-port task; sensor installation, same-source coupling,
time selection, reference and traffic remain separately charged.
This is neither a full-state repair nor a physical minimum theorem.

## 8. Source correspondence, reuse and surviving mathematical duties

**Definition 8.1 (precise suppliers and scope).** The source-specific
new deductions are the localized stopping classification and its
projected-service consequence in §§3–4, and the full-endpoint
reflection and whole-history risk in §§5–6. Section 2 is a credited
application of existing native/contact/clock formulas and classical
path lifting; §7 reuses the existing consumer and its same-run bounds.

| Supplier | Exact use and boundary |
| --- | --- |
| [G, Proposition 85.4, (85.12)–(85.13)] | The actual unit Green field has its independent even $z$ heat factor. No replacement Green potential is inserted. |
| [E, Definitions 109.1/110.1, Theorems 109.2/110.2/112.2] | The original source chart, unique coefficient-one zero vector and full complex maximal expansion. These supply the domain check in Theorem 5.1. |
| [S, Theorems 115.2–115.3, 116.3–116.4 and 117.2] | Positive $h$, whole transformed form, trace, conservative legitimate source start and strictly positive deterministic-time density. |
| [F, Proposition 7.2, Theorems 11.2/12.2/18.2/24.3/25.2/26.3/27.1] | Original partial actions/readouts, all-time false-fiber avoidance, contact/reset, exact stopped clock and the already positive causal-service/consumer coupling. Assumptions 25.1 and 26.1 remain additions. |
| Elworthy–Le Jan–Li, *The Geometry of Filtering*, [arXiv:0810.2253v1](https://arxiv.org/pdf/0810.2253v1), Lemma 5.1.1 and Theorem 9.1.3, pp.84–85 and 133–135 | `literature-attested`: conditional Bayes and finite-path Girsanov equivalence for the conservative smooth cutoff/reference processes. No global change of measure through the original singular source is invoked. |
| Hatcher, *Algebraic Topology*, [§1.3, Proposition 1.30 and its path-lifting consequence](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf) | `literature-attested`: covering-path lifting with a fixed initial lift. The application is (2.2)–(2.3), with Borel dependence proved there. |
| Pinned mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, [Topology/Homotopy/Lifting.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Homotopy/Lifting.lean), `IsCoveringMap.exists_path_lifts`, `liftPath_lifts`, `liftPath_zero`, `eq_liftPath_iff`, `liftPath_trans` | Existing covering/lifting vocabulary; source reading is not a new compilation of this continuous-time source theorem. |
| D5 `InvariantOriginRecoveryObstruction.no_absolute_origin_reconstruction`, with its owning Scribe | Existing invariant-readout obstruction. It does not by itself establish the actual endpoint path-law symmetry or a statistical risk value. |
| D5 `ZeroBayesResidualCriterion.statistical_residual_eq_zero_iff_mutually_singular`, with its owning Scribe | Existing common-mass statistical criterion. The actual conditional sign probabilities here are proved from the source law. |
| D5 `StochasticDescentEquivalence.stochastic_descent_equivalence`, `CompactSignatureRealization.finite_compatibility_global_realization` and their owning Scribes | Discrete PMF descent and compact signature realization retain their own domains; neither supplies acquisition or the singular continuous-time stopping proof. |

**Proposition 8.2 (adjacent public additions have different targets).**
The exact source and observation hypotheses of §§1–6 are compatible
with the following existing additions; none asserts the conclusion
of Theorem 3.1 or Theorem 6.1 in their place.

Proof. [Selection calculus, §27](AURIC_FIB_ATOM_SELECTION_CALCULUS.md)
starts from an explicitly encoded finite Boolean relation network,
its declared variable universe and a specified uniform complete law.
Its exact counting/conditional-generation application, contingent on
its pinned external counting supplier, obtains rational conditional
probabilities of those finite completions. The input is not a
visible record of an unknown actual diffusion coordinate. In
particular obtaining a conditional law there does not identify an
already realized hidden sample here.

[Hierarchical phases and predictive spectra, §14](AURIC_FIB_OBSERVATION_HIERARCHICAL_PHASES_AND_PREDICTIVE_SPECTRA.md)
uses its original-vertex Boolean encoding and deterministic auxiliary
gates to count and decode cardinality-constrained independent sets.
Its parameter-preserving complete-assignment correspondence is a
different finite source and task, not a readout or intervention on
$G$.

[S, §120] supplies a positive constrained quadratic direction for
the ordered passive-pair functional
$Q(u,w)=\int g_tuT_\Delta w\,dm$. [S, Theorem 121.2] uses it
and compact attainment to choose an optimum with no simultaneous
$1/3$ emission overlap. It is an existence theorem for that
nonstationary pair-law optimization, not deterministic attainment,
hidden-coordinate filtering or an entire-history sign decoder.
Its actual $g_t,T_t,h$ are precisely the inherited suppliers here.

[Self-calibrating relation mathematics IV, Theorem 15.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md)
proves two constant and distinct first responses for exactly four
complete worlds with its original-root $L_7$ failure premise.
Its gain polynomials, sampled clocks and trace histories are not the
autonomous diffusion or the sigma-fields (1.6).
The native formal-prefix suppliers also retain their exact carrier.
D5 `NativeFunctionalEffectivePrefix.effective_prefix` and its owning
Scribe prove termination of `prefixProgram` and equality with the
inclusive cutoff of the existing canonical native leaf-limit solution,
for arbitrary optional joint equations, parameters and reconstruction
expressions. The proof uses finite pattern states, monotone leaves,
pigeonhole stabilization and cutoff compatibility. Its bound is
$P(d)^{m+1}$ passes with $P(0)=1$ and $P(d+1)=2+P(d)^2$;
actual expression evaluation and parameter expansion still cost work.
`NativeSymbolicFiniteForcing.symbolic_finite_forcing` supplies finite
original-coordinate forcing in every joint solution, while
`NativeCompletionPrefixLifting.cutoff_embed` identifies the original
finite-tree cutoff. Their native trees, substitutions and query tables
supply neither a diffusion sample nor an exact continuous recorder,
posterior law or source-start reflection. No prefix result is used as
an acquisition certificate here.

D5 `FinitePrefixLocalConstancy.finite_prefix_locally_constant_off_boundary`
and its owning Scribe give a common neighborhood for a finite symbolic
prefix avoiding its boundary union. This finite topological stability
does not supply a continuous exact observation or its hidden posterior.

The owning Scribe of D5 `Quantum.Matrix.SchurMinimum` also states
the exact linear hidden-variable elimination formula and exhibits a
positive quadratic energy whose projected gradient trajectory differs
from the Schur-gradient trajectory. That finite deterministic block
system has arbitrary full initial data and its own Euclidean clock.
It supports keeping minimization and dynamical closure distinct; it
supplies neither the singular source law nor either posterior here.

The exact adjacent coherent reference is
[Coherent reconstruction, §36, Proposition 36.2](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md):
the physical five-level polar support, incompatible complete native
readout and read-created zero-mode mass. It is not a root-resolved
layer/quotient-count theorem and is not a premise of §§3–6.
These distinctions follow from their stated carriers, inputs and
conclusions, rather than a source-search non-hit. $\square$

**Definition 8.3 (remaining original-goal duties).** No result here
provides mutual inverses among all four independently meaningful
expressions on a complete internal-observer process. The exact
native legal-source/evolution/representation/readout correspondence,
native acquisition of the calibrated timed service or any
$z$-sensitive port, a faithful controlled-diffusion intervention
interface, effective finite-bit/noisy acquisition and uniform
accuracy/resource rates remain separate obligations. Reflection
alone does not decide recovery of $|z|$ or a maximal observable
quotient; the causal density result does not assert a smoothing
density after all future observations. No universal alpha/beta
sufficiency or minimality, common physical apparatus, physical
spatial dimension or full why-three conclusion follows.

The exact fixed-$G_{gc}$, original-$Q$, parked-consumer and
unchanged-initialization problems keep their original scopes.
Native legal growth/Tick completion and finite-phase-cover fixed
Markov recovery are separate tasks, not consequences supplied by
this hidden-coordinate continuation. The reserved serial-clock
repair, digital dense/lattice acquisition, native multiplication
calibration and fixed-DU selective-read outcomes are not suppliers
used here. Public native U1–U5 and NCR/PVC/PR57/Atlas results retain
their actual acquisition, law, authority, memory and continuation
domains; their resource optima are not combined with this diffusion
model. An ownership/fiber-factorization framework is reuse, not a
standalone new theorem. The exact positive conditional service and
consumer remain valid alongside these obstructions. Source readiness
is an ordinary mathematical claim subject to independent review and
repository admission; it is not new kernel verification or completion
of the sustained four-expression objective.

## 追加锚（本行以下为增补区）
