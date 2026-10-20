# Recursive relational observation: affine calibration fibers

An unbounded affine source distinguishes uncertainty about a normal direction
from uncertainty about its offset. For the native destructive instrument of
[Process Geometry, Definition 44.15][PG], a single static calibration message
that leaves two nonparallel normals possible gives infinite uniform
initial-state recovery risk. If the message fixes the normal up to sign,
the offset diameter and the original reachable normal gain give an exact
joint noise-and-calibration risk. The lower bounds concern complete records
of two actual runs, including every later permitted adaptive observation.

These are ordinary mathematical results. The affine inverse, native gain
table and bounded-error continuation invariant have their existing PG and
[Boundary Geometry][BG] ownership. The addition is their calibration-fiber
classification, with actual witnesses even for nonclosed offset sets.
Exact real replies and set-theoretic estimators remain distinct from finite
stored data and effective calibration acquisition. No Lean-kernel or
physical realization claim is made.

## 1. One source, one message and the original instrument

**Definition 1.1 (common instrument and actual initialization).** Let
$E=\operatorname{Im}\mathbb H$ have its fixed oriented orthonormal basis
$e_1,e_2,e_3$, and give $W=E\oplus\mathbb H$ its Euclidean norm. A hidden
calibration is a pair $(n,\lambda)$ with $|n|=1$ and $\lambda\in\mathbb R$.
Its actual initial source is the entire set

$$
\mathcal D_{n,\lambda}
 =\{(a_0,b_0):a_0\in E,\ \langle b_0,n\rangle=\lambda\}.
\tag{ACF.1}
$$

The visible $a_0$ is independent and arbitrary; the hidden affine
hyperplane has no amplitude bound. Initialization supplies one actual
$x_0\in\mathcal D_{n,\lambda}$, one overwritten current $W$ register,
the same axes and unit anchor $d=e_4$, and the exact destructive updates

$$
A_c(a,b)=(c\times a,bc),\qquad
A_d(a,b)=(\operatorname{Im}b,-a).
\tag{ACF.2}
$$

Fix either the original AB menu $c\in\{e_1,e_2\}$ or the original ABC menu
$c\in\{e_1,e_2,-e_3\}$, together with $A_d$. The known tree calibration
values and their actuator transfer are the supplied PG 44.15 ones.
No continuous choice of $c$, mixed control, copy, reset, second initial
specimen or new observation port is added. The affine equation constrains
only $x_0$; updates act on all of $W$.

A Read does not change the register and returns the complete real vector

$$
y=P_Ez+e,\qquad e\in E,\quad \|e\|\le\delta,\quad \delta>0,
\tag{ACF.3}
$$

where $z$ is this run's current state. Errors can be jointly adversarial,
correlated and history dependent. There is no independent-sampling or
precision-refinement hypothesis. Exact actuation and the error promise
are separate supplied resources.

**Definition 1.2 (static-message fiber).** Fix one finite message $k$ and
a nonempty set

$$
\mathcal C\subseteq\{(n,\lambda):|n|=1,\ \lambda\in\mathbb R\}
\tag{ACF.4}
$$

of calibrations compatible with that message. Replace PG's exact public
$(n,\lambda)$ by $k$. Every other observable initialization field,
installed controller configuration and reference is common throughout
$\mathcal C$. There is no further calibration access, calibration-bearing
identity, timing field or source-dependent initial advice. The actual
calibration is fixed on the same run as $x_0$ and all subsequent actions.

The mathematical specification fixes $\mathcal C$; it need not provide
an enumeration, membership algorithm or finite descriptions of its real
parameters. A fiber of a finite message can itself be infinite. The
abstract estimator class below allows arbitrary mathematical functions
for this one common specification. Thus the positive theorem is an
abstract risk theorem, not a claim that the literal message $k$ effectively
supplies its real coefficients.

**Definition 1.3 (complete-record risk and budget).** Fix
$N\in\mathbb N_0$. A controller is deterministic, has the common
initialization of Definition 1.2, chooses its next Read, menu update or
Stop from its finite observed prefix, and uses at most $N$ updates on
each legal run. As in PG 44.17, complete records may be finite or
naturally indexed countable records, each with a definite $W$-valued
initial-state estimate; there is no event after a countable prefix and
no extra limit Read. Every legal complete record must have an estimate.

A complete record retains all permitted replies, their Read positions,
ordered action and constant identities, stopping decisions and output;
any deterministic local fields formed from these are included as well.
Private true states and error vectors are not new observations. Let
$M_\pi(n,\lambda,x,e)$ be that record and set

$$
\begin{aligned}
E_\pi(\mathcal C,N,\delta)
 &=\sup_{(n,\lambda)\in\mathcal C}
   \sup_{x\in\mathcal D_{n,\lambda}}
   \sup_{e\text{ satisfying }(\mathrm{ACF}.3)}
   \|\widehat x_\pi(M_\pi(n,\lambda,x,e))-x\|,\\
\mathcal R_N(\mathcal C,\delta)
 &=\inf_\pi E_\pi(\mathcal C,N,\delta).
\end{aligned}
\tag{ACF.5}
$$

All suprema refer to actual initializations and actual error traces of
this same instrument. The estimate may be any point of $W$, as in PG;
it need not belong to the union of the possible source hyperplanes.
Randomized, average-risk and bounded-amplitude tasks are different tasks.

## 2. Reachable charts and complete-record coupling

**Convention 2.1 (the reused native gain).** A first-anchor prefix has
$j\le N-1$ internal updates $c_1,\ldots,c_j$, with chronological product
$p=c_1\cdots c_j$; the empty product is $1$. Write $\mathcal P_N$ for
the set of these reachable products, and $\mathcal P_0=\varnothing$.
Each product lies in $Q_8=\{\pm1,\pm e_1,\pm e_2,\pm e_3\}$.
For a unit $n$ write

$$
np=\alpha_p+\beta_p,\quad
\alpha_p\in\mathbb R,\quad\beta_p\in E,\quad
h_p=|\alpha_p|,\qquad
 g_N(n)=\max_{p\in\mathcal P_N}h_p,
\tag{ACF.6}
$$

with maximum zero for the empty set. The product does not encode all
visible-prefix dynamics; the actual ordered internal word is retained.
For $n=r+v_1e_1+v_2e_2+v_3e_3$ and
$G=\max(|r|,|v_1|,|v_2|,|v_3|)$, PG 44.16 gives

$$
\begin{array}{c|c|c|c|c}
 &g_0&g_1&g_2&g_N\ (N\ge3)\\\hline
\mathrm{AB}&0&|r|&\max(|r|,|v_1|,|v_2|)&G\\
\mathrm{ABC}&0&|r|&G&G.
\end{array}
\tag{ACF.7}
$$

Right multiplication by $p$ preserves the quaternion inner product.
Thus, for $b_0p=s+w$, the source equation is exactly

$$
\alpha_p s+\langle\beta_p,w\rangle=\lambda.
\tag{ACF.8}
$$

When $\alpha_p\ne0$, its inverse is
$b_0=((\lambda-\langle\beta_p,w\rangle)/\alpha_p+w)p^{-1}$.
This is PG (PG.4420), already supplied by BG 41.2. The inverse
multiplication is decoder arithmetic, not an inverse source action.

**Lemma 2.2 (two slots after the first anchor).** Suppose two actual
runs follow the same internal prefix, with half-differences in their
visible initial values of norm at most $\delta$. Suppose their hidden
values at the first anchor have imaginary half-difference of norm at
most $\delta$. From that anchor onward, if they follow the same actions,
each of the two current component half-differences has norm at most
$\delta$. At every Read their true visible values therefore have
distance at most $2\delta$. Reporting their midpoint is a legal reply
in both runs. Before the anchor the same conclusion holds for every
Read, independently of the hidden half-difference.

Proof. Before the anchor, every visible update is $a\mapsto c\times a$,
whose norm is at most one; every hidden update is right multiplication
by a unit. If the last pre-anchor visible values are $a_j^\pm$ and the
hidden values have imaginary parts $w^\pm$, the anchor produces
$(w^\pm,-a_j^\pm)$. Its two component half-differences have the asserted
bounds. Subsequently an internal action contracts the visible component
and is an isometry on the hidden one. An anchor takes the imaginary
part of the hidden component and negates the visible component; it
also preserves both bounds. Induction proves the invariant. At a Read,
the two errors needed for the midpoint report are opposite visible
half-differences, so each satisfies (ACF.3). This is the PG 44.17
continuation invariant, with its hypotheses made explicit. It requires
neither a third actual source nor independent errors. $\square$

**Lemma 2.3 (common zero prefix and blind branches).** Fix any controller
of Definition 1.3. Feed it zero replies before its first anchor. This
pre-anchor record is lawful: take $a_0=0$ on any one of the allowed
hyperplanes and use zero Read errors. It fixes one ordered internal
prefix and, if an anchor occurs, its product $p\in\mathcal P_N$.
If no anchor occurs, the controller has infinite risk. If an anchor
occurs and $\operatorname{Re}(np)=0$ for even one
$(n,\lambda)\in\mathcal C$, it also has infinite risk. Both assertions
hold using exact replies.

Proof. With no anchor, the entire observed record on $a_0=0$ is
independent of $b_0$ on one unbounded affine hyperplane. Two such hidden
points can have arbitrarily large separation while keeping the complete
record and estimate equal. This also covers a countable record with
no anchor; the controller must assign it a definite estimate.

In the second case write $np=\beta$ with $|\beta|=1$, choose
$w=\lambda\beta$ and define

$$
b_t=(t+w)p^{-1},\qquad t\in\mathbb R.
\tag{ACF.9}
$$

Equation (ACF.8) shows that all $(0,b_t)$ are legal actual initial
states for this same calibration. Their pre-anchor zero records agree;
the anchor sends all of them to $(w,0)$. Every later actual state,
exact reply, action and output then agrees by causality. The initial
separation is $|t-t'|$, so the worst-case error is infinite. The same
argument gives infinite risk whenever every reachable gain is zero.
$\square$

## 3. The sharp calibration-fiber classification

**Theorem 3.1 (two nonparallel normals give infinite risk).** If
$\mathcal C$ contains $(n_1,\lambda_1)$ and $(n_2,\lambda_2)$ with
$n_2\notin\{n_1,-n_1\}$, then every controller of Definition 1.3 has
infinite risk. The conclusion already holds on the subfamily of exact
Read replies; it therefore holds for every $\delta>0$ and every
original update budget $N$.

Proof. Fix a controller and apply Lemma 2.3 to its common zero prefix.
The no-anchor and zero-gain cases have already been proved. Otherwise
both $\alpha_i=\operatorname{Re}(n_i p)$ are nonzero. Write

$$
n_i p=\alpha_i+\beta_i,\qquad
\tau_i=\lambda_i/\alpha_i,\qquad
\gamma_i=\beta_i/\alpha_i.
\tag{ACF.10}
$$

If $\gamma_1=\gamma_2$, then
$n_1p=(\alpha_1/\alpha_2)n_2p$, so the two unit normals differ only by
sign. Thus $\gamma_1-\gamma_2\ne0$. For any $w\in E$, take the two
actual initial states

$$
x_i(w)=(0,b_i(w)),\qquad
b_i(w)=(\tau_i-\langle\gamma_i,w\rangle+w)p^{-1}.
\tag{ACF.11}
$$

Each belongs to its original complete hyperplane by (ACF.8). All
pre-anchor replies are zero, so the controller really selects the same
prefix used to define them. The first anchor sends both states to
$(w,0)$. From that event onward the two actual runs have identical
current states. Give them their exact Read replies. Causality yields
the same complete record, including all later actions and stopping,
and the same estimate, even for a countable continuation.

Their initial distance is

$$
\|x_1(w)-x_2(w)\|
 =|\tau_1-\tau_2-\langle\gamma_1-\gamma_2,w\rangle|.
\tag{ACF.12}
$$

Taking $w=t(\gamma_1-\gamma_2)$ makes this unbounded. For each fixed
$t$ these are two legal actual runs, and a common estimate has error
at least half their initial distance on one of them. Hence this one
controller has infinite uniform risk. The argument applies to every
controller without changing any menu, initialization or source cap.
$\square$

**Definition 3.2 (one unoriented normal and its offsets).** In the
remaining case choose one unit representative $n_\circ$ such that every
normal in $\mathcal C$ is $\sigma n_\circ$, $\sigma\in\{1,-1\}$.
For each $(n,\lambda)$ put $\mu=\sigma\lambda$ and define

$$
 I=\{\sigma\lambda:(\sigma n_\circ,\lambda)\in\mathcal C\},\qquad
 \Delta=\sup_{\mu,\nu\in I}|\mu-\nu|\in[0,+\infty].
\tag{ACF.13}
$$

Then the source union is precisely
$\{(a,b):a\in E,\ \langle b,n_\circ\rangle\in I\}$; opposite
calibration labels describing the same plane do not change the source.
The set $I$ is only required to be nonempty. It need not be closed,
convex or discrete. If $\Delta<\infty$, put

$$
 \ell=\inf I,\qquad u=\sup I,\qquad
 m=(u+\ell)/2,\qquad d=(u-\ell)/2=\Delta/2.
\tag{ACF.14}
$$

These are finite real constants, with $|\mu-m|\le d$ for all $\mu\in I$.
There is no assertion that $m,\ell$ or $u$ is an allowed actual offset.
Changing representative to $-n_\circ$ changes $I,m$ to $-I,-m$ and
leaves $\Delta$ and the gains unchanged.

**Theorem 3.3 (exact common-normal noise-and-offset curve).** Under
Definition 3.2 write $g=g_N(n_\circ)$. If $\Delta=+\infty$ or $g=0$,
every controller of Definition 1.3 has infinite risk, already for
exact replies. Otherwise

$$
\boxed{
\mathcal R_N(\mathcal C,\delta)
 =\left[2\delta^2+
   \left(\frac{\delta\sqrt{1-g^2}+\Delta/2}{g}\right)^2
   \right]^{1/2}.}
\tag{ACF.15}
$$

An abstract two-Read estimator attains this minimax value using a
reachable maximal-gain prefix. Its update and Read counts are the
original ones. Attainment here refers to the infimum over estimators;
the worst source/error supremum need not be attained.

Proof. First dispose of the infinite cases. If $g=0$, Lemma 2.3
applies to every controller. For $\Delta=+\infty$, use its common zero
prefix; a missing anchor or zero gain again gives infinite risk.
Otherwise write $n_\circ p=\alpha+\beta$, $\alpha\ne0$. For any two
actual offsets $\mu,\nu\in I$, the actual states

$$
 (0,(\mu/\alpha)p^{-1}),\qquad
 (0,(\nu/\alpha)p^{-1})
\tag{ACF.16}
$$

have exact zero replies throughout the pre-anchor branch and both
become the zero current state at that anchor. Their complete exact
records remain equal, and their initial distance is
$|\mu-\nu|/|\alpha|$. Such distances are unbounded. No infinitely
large or limiting actual offset is used.

Now let $\Delta<\infty$ and $g>0$. For the upper bound choose an
actual ordered prefix with product $p$ attaining $h=|\alpha|=g$, where
$n_\circ p=\alpha+\beta$. Take one Read before any update, execute
that prefix and the anchor, and take one Read immediately afterward.
For the actual source's oriented offset $\mu\in I$, their replies are

$$
 y_0=a_0+e_0,\qquad y_1=w+e_1,\qquad
 w=\operatorname{Im}(b_0p),\quad \|e_i\|\le\delta.
\tag{ACF.17}
$$

Retain these two replies and the actual action/Stop identities. Use the
existing affine inverse with the interval-center offset:

$$
 \widehat a=y_0,\qquad
 \widehat b=
 \left(\frac{m-\langle\beta,y_1\rangle}{\alpha}+y_1\right)p^{-1}.
\tag{ACF.18}
$$

The actual initial hidden scalar is
$s=(\mu-\langle\beta,w\rangle)/\alpha$. Orthogonality of real and
imaginary quaternion components gives the exact error identity

$$
 \|\widehat x-x_0\|^2
 =\|e_0\|^2+\|e_1\|^2+
   \frac{(m-\mu-\langle\beta,e_1\rangle)^2}{\alpha^2}.
\tag{ACF.19}
$$

Consequently the error squared is at most
$2\delta^2+(d+\delta\|\beta\|)^2/h^2$. Since
$\|\beta\|=\sqrt{1-h^2}$, this is the square of (ACF.15).
The construction uses one original source, $j+1\le N$ updates and two
Reads. It never re-prepares an initial state. The estimate is allowed
to lie on the center plane even when $m\notin I$.

For the matching lower bound fix an arbitrary controller. Use the
common zero pre-anchor branch of Lemma 2.3. Its blind cases give
infinite risk, so suppose its product $p$ has
$n_\circ p=\alpha+\beta$ with $h=|\alpha|>0$; then $h\le g$.
Choose any actual pair $\mu_+,\mu_-\in I$ with $\mu_+\ge\mu_-$,
allowing equality. Put $q=(\mu_+-\mu_-)/2$. Choose unit vectors
$v,z\in E$, with $z=\beta/\|\beta\|$ when $\beta\ne0$ and arbitrary
unit $z$ when $\beta=0$. Define

$$
\begin{aligned}
 a_0^+&=\delta v,& a_0^-&=-\delta v,\\
 w^+&=-\delta z,&w^-&=\delta z,\\
 s^\pm&=\frac{\mu_\pm-\langle\beta,w^\pm\rangle}{\alpha},&
 b_0^\pm&=(s^\pm+w^\pm)p^{-1},\qquad
 x^\pm=(a_0^\pm,b_0^\pm).
\end{aligned}
\tag{ACF.20}
$$

Both $x^+$ and $x^-$ belong to actual source hyperplanes represented
in $\mathcal C$, not to hypothetical endpoint planes. Before the
anchor their visible midpoint is zero and each visible value has norm
at most $\delta$. Report zero at every such Read, using the negative
of its actual visible value as the error. These legal replies force
the controller to execute exactly the prefix used in (ACF.20).

At the anchor the visible values are $w^\pm$, and the hidden values
are the negatives of the pre-anchor visible values. The two current
states have midpoint zero and component half-differences of norm at
most $\delta$. Lemma 2.2 now preserves these bounds under every later
common action. All updates are linear, so their current midpoint
remains zero. At every later Read report zero, again by errors that
are the negative actual visible values and have norm at most $\delta$.
Thus these two fixed actual sources produce the same complete zero
reply record, with the same actual choices, counts, Stop and estimate.
Induction on finite prefixes proves this for the whole naturally
indexed countable record as well.

Only the two endpoints are actual sources in this argument. Their
algebraic midpoint has oriented offset $(\mu_++\mu_-)/2$, which may
be outside $I$; it is used only to compute a linear midpoint after
an update. Neither legality of a third source nor a controller run
from that third source is assumed.

Their initial half-distance is exactly

$$
 \frac{\|x^+-x^-\|}{2}
 =\left[2\delta^2+
   \left(\frac{q+\delta\|\beta\|}{h}\right)^2\right]^{1/2}.
\tag{ACF.21}
$$

Indeed the visible half-difference has norm $\delta$, the hidden
imaginary half-difference is $-\delta z$, and its real half-difference
is $(q+\delta\|\beta\|)/\alpha$. Orthogonality and $|p|=1$ give the
identity. A common estimate has error at least this half-distance on
one of the two actual runs.

Taking the supremum over pairs in $I$ replaces $q$ by $\Delta/2$ in
this continuous expression. For completeness, boundedness of $I$
gives $\Delta=u-\ell$: the upper bound is immediate, while for every
$\varepsilon>0$ one can choose actual $\mu_+>u-\varepsilon$ and
$\mu_-<\ell+\varepsilon$. If $u>\ell$, choose sufficiently small
$\varepsilon$ so that they are ordered. If $u=\ell$, $I$ is a
singleton and the equal-offset pair already suffices. There is no
assumption of diameter attainment or of a limiting legal source.

Finally, for $d\ge0$ the function

$$
 F_d(h)=\left[2\delta^2+
       \left(\delta\sqrt{h^{-2}-1}+d/h\right)^2\right]^{1/2},
       \qquad 0<h\le1,
\tag{ACF.22}
$$

is decreasing: both nonnegative summands inside the inner parentheses
are decreasing, and the first is strictly decreasing because
$\delta>0$. Hence $F_d(h)\ge F_d(g)$. Every controller has risk at
least (ACF.15), matching (ACF.18). $\square$

**Corollary 3.4 (exact finite-cap condition).** In the finite case of
Theorem 3.3, a prescribed real error cap $B\ge0$ is attainable by an
abstract controller if and only if

$$
 B\ge\sqrt2\,\delta,\qquad
 \frac{\Delta}{2}
 \le g\sqrt{B^2-2\delta^2}-\delta\sqrt{1-g^2}.
\tag{ACF.23}
$$

In particular, the original exactly calibrated cap
$R=\delta\sqrt{1+g^{-2}}$ can be retained if and only if $\Delta=0$.
Any positive offset diameter strictly increases the minimax risk.

Proof. Theorem 3.3 gives attainability exactly when $F_{\Delta/2}(g)\le B$.
Squaring requires $B^2\ge2\delta^2$; taking the remaining nonnegative
square root and rearranging gives (ACF.23). The stated $R$ makes its
right-hand side zero. Conversely $\Delta=0$ reduces (ACF.15) to $R$.
For positive $\Delta$ the inner nonnegative term in (ACF.15) strictly
increases, including when $g=1$. $\square$

**Example 3.5 (open offsets and the unchanged menu threshold).** Let
$n_\circ=1$, $I=(0,L)$ with $L>0$, and $N\ge1$. Both original menus
have $g=1$, so the exact value is
$\sqrt{2\delta^2+L^2/4}$. The center $L/2$ is usable in (ACF.18),
while neither offset endpoint is an actual source. The lower bound is
the supremum of (ACF.21) for actual interior offset pairs. Even
$I=\{0,L\}$ gives the same value although its center is not in $I$.

For $n_\circ=e_3$, AB with $N=2$ has $g=0$, even if $I$ is a
singleton. AB needs its original three-update chart; ABC can use its
original two-update chart. Offset advice does not create a missing
native control axis or authorize BG 41's continuous controls.

## 4. What the static message does and does not acquire

The classification isolates a calibration resource on the original
unbounded source. A fiber with any two nonparallel normals fails even
with exact replies, regardless of how close those normals are. This
is not a fixed-coefficient error estimate: Theorem 3.1 excludes every
causal controller on that whole fiber, with actual merged successors.
Once the unoriented normal is fixed, the finite offset diameter can
be tolerated at exactly (ACF.15). Further Reads cannot improve that
curve under the joint error contract.

Theorem 3.3's positive estimator is a common set-theoretic rule for the
fiber, using $n_\circ$, the center $m$, a maximal-gain native prefix
and six real reply coordinates. Finiteness of $k$ alone supplies no
algorithm for any of those real constants. In particular knowing that
$I$ is nonempty and bounded does not provide effective access to its
infimum and supremum. A description of a bounded set and a certified
finite representation of its center are different inputs.

The lower bounds apply to finite-description observers whenever their
only calibration information is such a static fiber. The positive
bound does not install a finite-description observer on arbitrary
unrepresented original calibrations. It requires the abstract constants
just named and the original real-valued Read/retention contract. There
is no theorem here about digitizing a noisy real reply, attaining the
curve with finite terminal values, productive rounding at grid walls,
or the arithmetic error of approximating those coefficients. Each of
those changes requires its own representation and total-error contract.

On the upper-bound run, acquisition really consists of the initial
Read, the chosen ordered internal prefix, one anchor and its Read.
If the prefix has length $j$, the simultaneous source-operation
counts are exactly two Reads and $j+1\le N$ updates. All six acquired
real coordinates, the message, chart/reference data, installed decoder,
actual action identities and Stop metadata must be available to the
retained decoder. They are not a finite bit count. Literal histories,
if required by the calling interface, retain their full separate costs;
computing $p$ does not replace their identities or order. Choosing an
AB or ABC calibration tree, preparing the actual affine source,
maintaining its arbitrary amplitude, transferring controls and supplying
truthful sensor errors are the independent PG resources. No cost-optimal
claim is made about those coordinates.

For a bit implementation, code/configuration acquisition, coefficient
representation and evaluation, reply production and complete framing,
local scratch, output precision, stored widths and all later accesses
must be paid on the same run. A finite program is not a bound on its
changing memory or the source amplitudes. This volume supplies an exact
static-advice obstruction and abstract error budget, without supplying
those independent finite implementation bridges.

## 5. Independent views and the recovery directions actually supported

**Definition 5.1 (four readings of this process).** Space exposes the
actual initial affine point $x_0$ and its evolving current $W$ state;
the affine constraint and Euclidean distances have their own geometric
meaning. Event time exposes the ordered Read/update/Stop occurrences
and their identities on that same source. It is an event order, not
an additional available clock or a record of analog error values.
Boundary data expose the actual Read vectors attached to the specified
cuts of that event sequence. Memory exposes what the observer has
actually acquired and retained: the message and available calibration
representation, numerical replies, action/Stop fields and estimate.
A mathematical past, an unavailable real constant or a discarded reply
is not automatically retained memory. None of the views is defined
as an unrestricted encoding of the entire history.

**Proposition 5.2 (report/estimate routes at the acquired cut).** For a
chosen nonzero-gain chart $p$ and center $m$, the map (ACF.18) is an
affine bijection from the numerical pair $(y_0,y_1)\in E\times E$
onto $\mathcal D_{n_\circ,m}$. Its numerical inverse is

$$
 y_0=\widehat a,\qquad y_1=\operatorname{Im}(\widehat b p).
\tag{ACF.24}
$$

Thus the acquired numerical boundary pair, with that chart fixed,
and the retained estimate determine each other exactly. On every
actual upper-bound run the latter approximates the original $x_0$
within (ACF.15). This is approximate source recovery, not equality of
source and record fibers.

Proof. Multiplying (ACF.18) by $p$ gives imaginary part $y_1$ and
real part $(m-\langle\beta,y_1\rangle)/\alpha$, which satisfies
(ACF.8) with offset $m$. Conversely any point on that plane has this
unique scalar part once its imaginary part is given. This is the
supplied affine inverse with the declared center. Theorem 3.3 gives
the error on the actual source regardless of whether its offset is
$m$. These numerical identities return only the two report vectors.
Any requested chronology, frame fields, calibration label or error
information still needs its own determination from supplied or retained
data; it is not an extra output of (ACF.24). $\square$

**Proposition 5.3 (same-action dynamics and retained numerical use).**
Let $T_v$ be the composition of the original updates in a finite
chronological word $v$. For any actual source $x_0$ and any retained
estimate with $\|\widehat x-x_0\|\le B$, one has

$$
 \|T_v\widehat x-T_vx_0\|\le B,\qquad
 \|P_ET_v\widehat x-P_ET_vx_0\|\le B.
\tag{ACF.25}
$$

These inequalities hold simultaneously for every such word. Sequential
numerical evaluation and evaluation of the composed map agree. In
particular they apply to the same actual selected actions in the
acquisition prefix and any lawful continuation within the original
total budget $N$. They require no extra source Read, reset or copy.

Proof. For unit native $c$,

$$
 \|A_c(a,b)\|^2
 =\|c\times a\|^2+|bc|^2\le\|a\|^2+|b|^2,
 \qquad
 \|A_d(a,b)\|^2=|\operatorname{Im}b|^2+\|a\|^2
 \le\|b\|^2+\|a\|^2.
\tag{ACF.26}
$$

All maps are linear, so their compositions are nonexpansive and
composition acts equally on a difference. Projection also has norm
at most one, proving (ACF.25). Associativity of composition gives
$T_{uv}=T_vT_u$ for chronological concatenation, proving route
agreement. Apply the pointwise inequalities to the word actually
chosen by the observer. The result is the existing nonexpansive
transport principle on this instrument, not a new controller
simulation theorem. $\square$

To use (ACF.25), the numerical decoder must retain and be able to
access its estimate and the relevant action identities under its
supplied arithmetic contract. An abstract real register does not
establish finite callable storage. The bounds predict the true Read
values; an actual noisy reply can differ from the prediction by up
to $B+\delta$. A policy driven by predictions need not choose the
same actions as a policy driven by actual replies. Numerical evaluation
of a word beyond the remaining budget grants no physical action.

The missing inverse directions have concrete witnesses. If $I$
contains two distinct offsets and a nonzero chart is available,
(ACF.16) gives different initial points with identical exact complete
records and the same zero current state after their first anchor.
Thus neither that boundary record nor the current state recovers the
initial offset. Even when $I$ is a singleton, (ACF.20) with equal
offsets gives different actual initial points and identical full noisy
records for $\delta>0$. Their approximate estimates therefore cannot
be treated as exact source identifiers. Conversely, a fixed two-Read
acquisition event word carries no numerical source data: varying
$a_0$ with exact replies changes its numerical boundary while leaving
that event word unchanged. The selected pair of numerical replies
also omits chronology: inserting a redundant exact initial Read gives
the same selected pair on the same source but a different full event
sequence. Any obligatory full record is retained separately.

On the restricted noiseless, singleton-offset contract with an
available nonzero chart, exact initial recovery is precisely the
already supplied PG 44.16 inverse. The positive-noise or uncertain-offset
model here does not imply four-way exact recovery, chronology
authentication or restoration of an erased source.

## 6. Suppliers, mathematical delta and retained boundaries

The source-specific additions are Theorems 3.1 and 3.3 and the cap
condition of Corollary 3.4. They are `repo-derived` ordinary
mathematical synthesis. Nonparallel normalized chart slopes give the
unbounded actual merger. In the parallel case the offset separation
and Read errors occupy one and the same actual pair, and Lemma 2.2
keeps that pair indistinguishable through the full causal record.
Optimizing the original reachable gain yields the matching curve.
No optimization of unrelated marginal error models is used.

| Supplier | Exact use and interface boundary |
| --- | --- |
| [PG 44.15–44.18 and §44.9][PG] | Entire unbounded $\mathcal D_{n,\lambda}$, independent $a_0$, one overwritten register, fixed AB/ABC axes, exact transfer, native gain table, affine inverse, original error/cap quantifiers and the two-slot invariant. Replacing exact public calibration by one static fiber is the explicit change here. |
| [BG 37–42, especially 41.1–41.4][BG] | Quaternion source geometry, the affine chart and complete-record bounded-error method. Its continuous internal controls are not added to PG's native menu. BG 54's two-radius source $\mathcal D_2$, with radii $7,25$ and a cone constraint, is a different domain; its finite envelope is not an affine amplitude bound. |
| [Finite Affine Calibration Advice, §§1–4, 21–23][FA] | Finite calibration data, exact finite arithmetic, actual acquisition and complete parsing are different obligations. Its source is the initialized no11 Step/Extent producer, observing $b+q\alpha^d$, not this $W$ register. Its positive acquisition and restored parser do not install a PG calibration or Read port. |
| [Fixed Offset Precision Payload, §§2, 10–11][FO] and [Capped Precision Permanent Blindness, §§2–7][CP] | Full finite replies, payload order, paid centered-service installation and actual persistent collisions retain their own initialized source and floor backend. Neither theorem licenses replacing PG's abstract real replies by those services. |
| [Parameterized Cross-product Recovery, §§20, 73–79, 87–88][PCR] and [Autonomous Predictive Memory, §§1, 8][APM] | Closed finite data, historical precision names, coefficients, evidence and changing interpreter memory have explicit different contracts. Their three tree-vector Reads and future-response task do not provide this affine calibration fiber or two-Read implementation. |

The formal declarations and their owning Scribes keep their original
telescopes. `SelfCalibratingFibers.full_fiber_and_signed_capacity` in
[D5/S3/ConceptDynamics/Experiment/SelfCalibratingFibers.lean][SCF]
concerns strictly positive rank-one $2\times2$ sources, two shear
readouts and a selected third read. Its open-interval injectivity
criterion does not instantiate the present quaternion instrument.
`FiniteWordFiberDiameter.finite_word_fiber_prediction_diameter` in
[D5/S3/Observer/MetricGeometry/FiniteWordFiberDiameter.lean][FWD]
requires a global output-diameter bound and discounted future metric.
The present unbounded initial-state risk has neither hypothesis.
`QuantizedWordApproximation.quantized_word_approximation` in
[D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.lean][QWA]
assumes a supplied covering quantizer; it does not acquire one for
this unbounded source. `UniqueInterfaceKernelCriterion`'s factorization
criterion is the abstract exact-fiber principle, without an instrument
or error radius. `AffineCodebookMemory` studies a driven finite
codebook, and `RationalResponseRefinement.post_word_run` parses its
specified ternary arithmetic response. Their same-path Blueprint
Scribes state those hypotheses. None is being re-presented as a new
inverse or finite calibration algorithm here.

The later source results in *LAB Arithmetic Growth* (local addressed
growth and arithmetic records), *Adaptive Selected Retrieval* §11
(weighted whole-coordinate acquisition), *Autonomous Stopped
Environment Memory* §13 (stopped quantum/classical history queries),
*Exact Original Point Unlocking* §8 (initialized Step/Extent origin
fibers) and *Native Mixed Screen Completion* §§19–22 (fixed Boolean
control graphs and their Native lifting) retain their respective
sources, observations and prices. They provide no identification of
those instruments with the PG source and menu. The calibration
classification does not settle or reclassify any of their original
controller or acquisition problems.

| Primary or upstream source | Literature-attested scope |
| --- | --- |
| S. Foucart and C. Liao, *Optimal Recovery from Inaccurate Data in Hilbert Spaces*, [arXiv:2111.02601v1](https://arxiv.org/pdf/2111.02601v1), §1.1 and Lemma 11 | Worst-case consistent sets and the symmetric-pair lower-bound method are established optimal-recovery tools. That fixed linear-information model does not supply the native destructive prefix, two-slot continuation or actual calibration-dependent merger used here. |
| A. Pauly, *On the topological aspects of the theory of represented spaces*, [arXiv:1204.3763v3](https://arxiv.org/pdf/1204.3763v3), §3 and Proposition 3 | A realizer acts on supplied names; computability of evaluation and composition presupposes the relevant representations and access. This does not turn a finite message into arbitrary exact real constants, supply finite complete replies or install calibration acquisition. |
| Pinned mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, [Mathlib/Analysis/Quaternion.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Quaternion.lean) | Quaternion norm multiplicativity, Euclidean tuple isometry and inner-product conventions are reused algebra. They supply no actual source, permitted action, retained representation or sensor contract. |

These correspondences credit the reused methods; they make no global
priority or exhaustive-literature claim. The substantive gain over a
generic quotient, replay or finite-arithmetic wrapper is the exact
calibration resource forced by actual PG complete-record fibers.
NCR/PVC/PR57 and the structural/callable atlases retain their own
installed clocks, acquired syntax, tapes, references, permissions and
continued-use interfaces. None of those supplies calibration advice
or an extra action here by a change of terminology.

**Open problem 6.1 (the finite implementation bridge).** For PG's
original arbitrary exact public real calibration and abstract noisy
Read traces, a finite-description implementation still needs actual
coefficient acquisition, finite reply representation, paid arithmetic
error and output precision contracts compatible with its declared cap.
The static-message theorem identifies which calibration uncertainty
already prevents that cap, or even any finite uniform cap, on the
unbounded domain. It does not construct the missing finite port,
effective center/gain selection or finite retained callable observer.
Changing the initialization, reply relation, source domain or allowed
error cap is a separate model, not a proof of the original obligation.

The fixed-$G_{\rm gc}$, original-$Q$, parked-consumer and unchanged
initialization obligations retain their exact earlier scopes.
Independent four-view mutual recovery, physical source/reference and
actuation realization, and universal minimal relation generators remain
outside the proved directions. The calibration fiber classification
is one bounded contribution to that sustained objective.

[PG]: RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[BG]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md
[FA]: RECURSIVE_RELATIONAL_OBSERVATION_FINITE_AFFINE_CALIBRATION_ADVICE.md
[FO]: RECURSIVE_RELATIONAL_OBSERVATION_FIXED_OFFSET_PRECISION_PAYLOAD.md
[CP]: RECURSIVE_RELATIONAL_OBSERVATION_CAPPED_PRECISION_PERMANENT_BLINDNESS.md
[PCR]: RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md
[APM]: RECURSIVE_RELATIONAL_OBSERVATION_AUTONOMOUS_PREDICTIVE_MEMORY.md
[SCF]: ../../../D5/S3/ConceptDynamics/Experiment/SelfCalibratingFibers.lean
[FWD]: ../../../D5/S3/Observer/MetricGeometry/FiniteWordFiberDiameter.lean
[QWA]: ../../../D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.lean

## 追加锚（本行以下为增补区）
