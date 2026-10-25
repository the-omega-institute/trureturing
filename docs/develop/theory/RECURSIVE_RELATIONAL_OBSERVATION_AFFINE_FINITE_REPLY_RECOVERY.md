# Recursive relational observation: affine finite reply recovery

The source is the unbounded external affine instrument of [Process Geometry,
Definition 44.15 and Theorems 44.16–44.17][PG]. The target remains its original
initial state. A single current register is overwritten by the original native
updates; there is no reset, copy or second initial-state experiment. The
finite-value obstruction below retains the original real-reply interface.
The floor and rational total-error interfaces are expressly different
interfaces on that same source. Their calibration and implementation
hypotheses are stated separately.

The source-specific additions are the saturation condition for an original
optimal estimate with a finite closed value, and the sharp full-record risk
of a fixed coordinate floor encoder. The affine inverse, native gain table,
quaternion identities and general symmetric-pair lower-bound method are
credited suppliers. Effective arithmetic and continued use enter only as
consumers of these results.

## 1. Original affine source and the declared task

**Definition 1.1 (one actual affine instrument).** Let
$E=\operatorname{Im}\mathbb H$ with its ordered orthonormal basis
$e_1,e_2,e_3$, and let $W=E\oplus\mathbb H$ have its Euclidean sum norm.
Fix a unit quaternion $n=r+v$, a real $\lambda$, a real $\delta>0$, an
integer $N\ge0$, and either the AB or ABC menu. The initial source is

$$
\mathcal D_{n,\lambda}
 =\{(a_0,b_0):a_0\in E,\ b_0\in\mathbb H,
                  \ \langle b_0,n\rangle=\lambda\}.
\tag{AFR.1}
$$

The two initial coordinates are independent subject only to this equation.
In particular neither coordinate has an amplitude bound. The current state
$z=(a,b)$ occupies one $W$ register. Its exact destructive updates are

$$
A_c(a,b)=(c\times a,bc),\qquad
A_d(a,b)=(\operatorname{Im}b,-a).
\tag{AFR.2}
$$

Here $d$ is the separately supplied unit anchor. AB supplies the two native
unit axes $c=e_1,e_2$; ABC also supplies $c=-e_3$. These are actual calibrated
controls and an actual transfer interface, not arbitrary continuous controls
obtained by linear span. Negative versions of these axes can also be
included without changing the arguments. The initial affine equation is
not a constraint on later current states.

Read does not update the register. In the original interface it returns
$P_Ez+e$, where $\|e\|\le\delta$. Errors are jointly adversarial, may be
correlated, and may depend on history. Calibration, anchor, source
preparation, read binding and exact actuation are supplied. Initialization
of the observer is independent of the unknown $x_0=(a_0,b_0)$.

A deterministic causal controller selects each next Read, update or Stop
from the public calibration and its finite acquired record. There are at
most $N$ updates. As in PG44.17, a complete legal record may be finite or
indexed by the natural numbers; it has a specified $W$-valued estimate.
There is no event after an entire countable prefix and no extra limit Read.
For a controller $\pi$, its risk is

$$
E_\pi=\sup_{x_0\in\mathcal D_{n,\lambda}}
       \sup_{\text{legal complete errors}}
       \|\widehat x_\pi-x_0\|.
\tag{AFR.3}
$$

Every actual request, reply, action identity, order and stopping field
permitted by the interface belongs to the record. Framing is a fixed
function of the reported values and public/request fields. It provides no
additional source, timing, private-work or private-state channel.

**Definition 1.2 (native charts and supplied gain).** For $N\ge1$, let
$\mathcal P_N$ be the set of quaternion products
$p=c_1\cdots c_j$ of at most $N-1$ native internal updates, including the
empty product. For $N=0$ put $\mathcal P_0=\varnothing$. Every such product
belongs to

$$
Q_8=\{\pm1,\pm e_1,\pm e_2,\pm e_3\}.
$$

For $p\in\mathcal P_N$, write

$$
np=\alpha_p+\beta_p,\quad \alpha_p\in\mathbb R,\quad\beta_p\in E,
\qquad h_p=|\alpha_p|,\qquad
 g=\max_{p\in\mathcal P_N}h_p,
\tag{AFR.4}
$$

where the maximum of the empty set is zero. The exact gain table, reused
from PG44.16, is

$$
\begin{array}{c|cccc}
 &N=0&N=1&N=2&N\ge3\\\hline
\mathrm{AB}&0&|r|&\max(|r|,|v_1|,|v_2|)&\max(|r|,|v_1|,|v_2|,|v_3|)\\
\mathrm{ABC}&0&|r|&\max(|r|,|v_1|,|v_2|,|v_3|)&\max(|r|,|v_1|,|v_2|,|v_3|).
\end{array}
\tag{AFR.5}
$$

When $g>0$ set

$$
R=\delta\sqrt{1+g^{-2}}.
\tag{AFR.6}
$$

PG44.17 proves that $R$ is the original all-controller minimax risk;
when $g=0$ that risk is infinite. These are source- and menu-specific
statements, with no bounded-amplitude or statistical-noise substitution.

For a nonzero-gain chart, the existing two-read decoder is

$$
D_p(Y_0,Y_1)=\left(Y_0,
 \left(\frac{\lambda-\langle\beta_p,Y_1\rangle}{\alpha_p}
            +Y_1\right)p^{-1}\right).
\tag{AFR.7}
$$

It is applied after an initial Read, the internal prefix realizing $p$,
one anchor, and one Read of that anchored state. If the true numerical
values at these cuts are $a_0,w$, then
$w=\operatorname{Im}(b_0p)$ and $D_p(a_0,w)=x_0$. Right multiplication
by $p^{-1}$ is decoder arithmetic, not an inverse source action.
The associated tangent lift is

$$
L_pz=z-\frac{\langle\beta_p,z\rangle}{\alpha_p}\in\mathbb H,
\qquad
\|L_pz\|^2=\|z\|^2+
             \left(\frac{\langle\beta_p,z\rangle}{\alpha_p}\right)^2,
\qquad \|L_p\|=h_p^{-1}.
\tag{AFR.8}
$$

The scalar term is real and $z$ is imaginary. The lift has zero inner
product with $np$, so $(L_pz)p^{-1}$ is tangent to the original affine
plane. Equations (AFR.7)–(AFR.8) reuse Boundary41.2 and PG44.16–44.17;
they are not new inverse theorems.

## 2. Exact-cap saturation and finite closed values

**Definition 2.1 (closed finite value).** Fix a finite alphabet $\Sigma$
and a map $\mathrm{Dec}:\Sigma^*\to W$, fixed independently of the
unknown source. It may depend on the fixed calibration and may even be
noncomputable. A closed finite-value estimate is
$\widehat x=\mathrm{Dec}(s)$ for one completed finite word $s$.
The word contains every source-dependent parameter determining that value.
There is no retained analog reply, source-linked handle, later source
access, infinite name or implicit source-dependent decoder parameter.
The word length need not have a uniform bound.

**Theorem 2.2 (original exact-cap nonattainment).** Suppose $g>0$ and
retain the original real replies of Definition 1.1. Every deterministic
controller with closed finite-value estimates has

$$
E_\pi>R,
\tag{AFR.9}
$$

possibly $E_\pi=+\infty$. More precisely, fix any noiseless complete
branch on any $x_*\in\mathcal D_{n,\lambda}$. If its first anchor has
chart gain $h>0$, and its output is $y$, then

$$
E_\pi^2\ \ge\ \delta^2(1+h^{-2})+\|y-x_*\|^2.
\tag{AFR.10}
$$

A branch with no anchor or zero first-anchor gain already forces infinite
risk. Consequently an original controller of risk at most $R$ would
have gain $g$ and output exactly $x_*$ on every noiseless branch.

Proof. Use the actual tangent pair in PG44.17, keeping its center $x_*$.
Before the first anchor, the visible trajectory depends only on $a_*$,
so the noiseless record determines the actual internal prefix $p$ without
knowing the hidden coordinate. In a blind branch, an unbounded hidden
line has identical reads before the anchor and identical current states
after it, if an anchor occurs. This proves the infinite-risk assertion.

In the other case, choose a unit $u\in E$ and a unit $v\in E$ parallel
to $\beta_p$; if $\beta_p=0$, any unit $v$ will do. Put

$$
\xi=\bigl(\delta u,\ \delta(L_pv)p^{-1}\bigr),\qquad
 x_\pm=x_*\pm\xi.
\tag{AFR.11}
$$

Both endpoints are actual allowed initial states and
$\|\xi\|^2=\delta^2(1+h^{-2})$. At every pre-anchor Read their visible
half-difference has norm at most $\delta$. Immediately after the anchor,
the two current components have half-differences of norms at most
$\delta$: these are $\delta v$ and minus the current visible
half-difference. Internal native updates contract the visible component
and preserve the hidden norm; an anchor interchanges the components and
projects the old hidden one. Thus the same two-component bound persists
through every later actual action.

At each Read, give both endpoints the true read of the midpoint run.
The required errors are opposite half-differences, hence legal. Equal
complete prefixes force the same choices, action identities, stopping
and output. Linearity makes the midpoint run exactly the specified
noiseless branch on $x_*$. Induction proves equality at each finite
prefix and therefore throughout any allowed countable record. The
parallelogram identity gives

$$
\max\{\|y-x_+\|^2,\|y-x_-\|^2\}
 \ge\frac{\|y-x_+\|^2+\|y-x_-\|^2}{2}
 =\|y-x_*\|^2+\|\xi\|^2.
$$

This proves (AFR.10). Since $h\le g$, a risk at most $R$ forces
$h=g$ and $y=x_*$. The range of $\mathrm{Dec}$ is countable, whereas
$\mathcal D_{n,\lambda}$ is uncountable. It cannot contain every such
$x_*$. This contradiction proves (AFR.9). $\square$

**Corollary 2.3 (infimum and fixed-length distinction).** In the abstract
original-controller class, restricting terminal values to finite words
does not raise the infimum $R$ when $g>0$, although it prevents its
attainment. No controller-independent positive excess over $R$ follows
from Theorem 2.2. By contrast, imposing a fixed maximum terminal word
length makes the risk infinite, for every finite claimed error cap.

Proof. Apply the existing maximal-gain decoder to the original real
replies and round its seven output coordinates to a sufficiently fine
fixed dyadic lattice. For every $\eta>0$ a lattice mesh can be chosen
so that this last displacement is at most $\eta$, uniformly over all
amplitudes. The output has a finite signed-integer word on each run and
risk at most $R+\eta$. This construction is an abstract real-input
controller, not a finite acquisition implementation of that interface.
The original lower bound gives the infimum. With a fixed word-length
cap the decoder has only finitely many output values. Their visible
coordinates are bounded, while $a_0$ is arbitrary, giving infinite risk.
$\square$

## 3. A fixed complete floor port

**Definition 3.1 (changed finite-reply contract).** Fix $m\ge0$ before
the run, and put $q=2^{-m}$ and $c=q/2$. Replace each real Read reply
by the completed signed integer triple

$$
K=\left\lfloor\frac{P_Ez+e}{q}\right\rfloor\in\mathbb Z^3,
\qquad\|e\|\le\delta,
\tag{AFR.12}
$$

coordinate by coordinate. Its whole integer parts and signs are sent in
a canonical finite self-delimiting format. Length fields, identifiers,
delimiters and completion are fixed functions of $K$ and common fields
only. The controller receives no error literal, clipped/modular value,
precision-request argument, private sensor state or timing channel.
Every reached invocation productively delivers this whole frame. The
errors may still be arbitrarily correlated and history dependent.
Only the reply contract changes; (AFR.1), (AFR.2), initialization, the
single register and the $N$-update cap remain exactly as before.

The cell-center numerical interpretation is

$$
Y=q\bigl(K+(1/2,1/2,1/2)\bigr).
\tag{AFR.13}
$$

This is a finite rational triple, but its integer width has no uniform
bound over the unbounded source. Define the compact symmetric body

$$
U_c=\delta B_2^3+c[-1,1]^3,\qquad
 A_c=\delta+\sqrt3c,\qquad
 H_p(c)=\max_{z\in U_c}\|L_pz\|\quad(h_p>0).
\tag{AFR.14}
$$

Here $B_2^3$ is the closed Euclidean unit ball. The use of the closed
cube is for suprema: a floor cell itself has a half-open endpoint.
Let $\mathcal R^{\rm floor}_N(\delta,q)$ be the infimum of (AFR.3)
over the full deterministic causal controller class with (AFR.12),
including every permitted repeated Read and complete countable record.
For this definition the terminal estimate can initially be any $W$ value.
Finite implementation of particular estimators is addressed in Section 5.

**Lemma 3.2 (native coordinate ancestry).** A native update on seven
real coordinates is a signed partial coordinate permutation: each row
and each column has at most one nonzero entry, equal to $1$ or $-1$.
Products have the same property. Before a first anchor, every visible
triple is a signed coordinate restriction of the initial visible triple.
After a first anchor with visible value $w$ and previous visible value
$a_j$, every later visible triple is a signed coordinate restriction
of either $w$ or $a_j$, never a mixture of coordinates from both.
The same assertion holds for perturbations.

Proof. The map $a\mapsto c\times a$ for a signed coordinate axis
annihilates one coordinate and interchanges the other two with signs.
The map $b\mapsto bc$ is a signed permutation of four coordinates.
The anchor sends the three imaginary hidden coordinates to the visible
block, sends minus the visible block to the hidden imaginary coordinates,
and sets the hidden real coordinate to zero. These explicit formulas
prove the row and column assertions. They also show that neither an
internal update nor an anchor mixes the two blocks. Immediately after
the first anchor the two blocks have the stated distinct ancestors.
Induction preserves their ancestry, although an anchor can exchange it
and subsequent projections can erase coordinates. $\square$

**Theorem 3.3 (sharp risk of the actual fixed floor encoder).** For the
entire unbounded domain (AFR.1) and the whole controller class above,

$$
\mathcal R^{\rm floor}_N(\delta,q)=
\begin{cases}
+\infty,&g=0,\\[2mm]
\displaystyle\min_{p\in\mathcal P_N,\ h_p>0}
             \sqrt{A_c^2+H_p(c)^2},&g>0.
\end{cases}
\tag{AFR.15}
$$

Every reachable chart of maximal native gain $h_p=g$ minimizes the
expression. Its two actual reads, interpreted by (AFR.13) and decoded
by (AFR.7), attain this abstract minimax value. In particular,

$$
\sqrt{A_c^2+\frac{(\delta+c)^2}{g^2}}
\ \le\ \mathcal R^{\rm floor}_N(\delta,q)
\ \le\ A_c\sqrt{1+g^{-2}},
\qquad
\mathcal R^{\rm floor}_N(\delta,q)>R.
\tag{AFR.16}
$$

For $n=1$ and $N\ge1$ its value is exactly
$\sqrt2(\delta+\sqrt3q/2)$. Whenever $g\ge1/2$, its upper excess over
$R$ is at most $\sqrt{15}q/2$.

Proof of the upper bound. For a real read value $t$ and its reported
cell center $Y$, write $Y-t=e+\rho$ with
$\|e\|\le\delta$ and $\rho\in c[-1,1]^3$. Thus $Y-t\in U_c$.
The maximum norm on $U_c$ is $A_c$: the triangle inequality gives the
upper bound, and a cube corner together with a ball vector pointing
along that corner gives equality. The two-read decoder therefore has
visible error at most $A_c$ and hidden error at most $H_p(c)$ on the
same run. The sum norm proves the upper half of (AFR.15).

Proof of the full-record lower bound. Fix any controller. Give its
initial visible source the value $a_*=(c,c,c)$. Until a first anchor,
follow the actual zero-sensor-error floor replies of this visible
trajectory. This determines the complete pre-anchor branch without any
hidden input. If no anchor occurs, an arbitrary unbounded hidden plane
remains invisible. If a first anchor has $\alpha_p=0$, the blind line
$b+t p^{-1}$ lies in the original plane and merges exactly at that
anchor. In each case complete equal records give infinite risk, even
with every later legal continuation. This proves the $g=0$ case as well.

Otherwise this finite prefix selects $p$ with $h_p>0$. Choose the
actual hidden midpoint source by

$$
w_*=(c,c,c),\qquad
 s_*=(\lambda-\langle\beta_p,w_*\rangle)/\alpha_p,
 \qquad b_*=(s_*+w_*)p^{-1}.
\tag{AFR.17}
$$

The source $(a_*,b_*)$ is allowed. It realizes exactly the already chosen
pre-anchor branch, and its first-anchor visible value is $w_*$. Continue
this nominal run with zero sensor errors. From the first anchor onward,
each readable coordinate is a center $c$ or $-c$, or an inserted zero,
by Lemma 3.2. Before that anchor the same is true of the visible block.
The possibly noncentral hidden scalar before the anchor is never read
and is erased at the anchor.

Fix $0<c'<c$. Write
$U_{c'}=\delta B_2^3+c'[-1,1]^3$. Choose $u,v\in U_{c'}$ satisfying

$$
\|u\|=\delta+\sqrt3c',\qquad
\|L_pv\|=H_p(c').
$$

Compactness gives both choices. Take decompositions
$u=u_B+u_C$, $v=v_B+v_C$, with
$\|u_B\|,\|v_B\|\le\delta$ and
$\|u_C\|_\infty,\|v_C\|_\infty\le c'$. The two actual endpoints are

$$
x_\pm=(a_*,b_*)\ \pm\bigl(u,(L_pv)p^{-1}\bigr).
\tag{AFR.18}
$$

The tangent equation in (AFR.8) puts both endpoints in the same original
affine plane. At the first anchor their visible perturbations are
$\pm v$ and their hidden perturbations are minus the pre-anchor
visible perturbations. All later readable triples have the following
more precise form: their nominal values are signed restrictions of
$(c,c,c)$, and their perturbations are the *same restrictions* of either
$\pm u$ or $\pm v$. An inserted zero has exactly zero perturbation.
This follows from the block-ancestry proof, not just from a bound on the
seven-dimensional norm.

At any such Read, cancel the restricted ball part by the sensor error.
A signed coordinate restriction cannot increase its Euclidean norm,
so this error has norm at most $\delta$. The remaining perturbation
is a restricted cube vector whose coordinates have magnitude at most
$c'<c$. Every nonzero nominal coordinate stays strictly inside its
original cell, whose center is $c$ or $-c$. An inserted zero remains
exactly zero, with floor integer zero. Thus the actual floor integers
of both endpoints are exactly the nominal integers at every Read.

Equal integers give identical whole frames. Causality then gives the
same requests, action identities, local decisions, stopping and output.
Induction on finite event prefixes proves the coupling; every coordinate
of an allowed countable record lies in one of these prefixes. The
argument uses no future source read, second source, independent error
sample, or observation after a countable prefix.

The endpoint half-distance is

$$
\sqrt{(\delta+\sqrt3c')^2+H_p(c')^2}.
$$

A common estimate has at least this error at one endpoint. As $c'$
increases to $c$, $H_p(c')$ tends to $H_p(c)$: the Hausdorff distance
between the bodies is at most $\sqrt3(c-c')$, and $L_p$ has norm $1/h_p$.
The supremum lower bound is therefore
$\sqrt{A_c^2+H_p(c)^2}$ for this controller's selected chart, hence at
least the minimum in (AFR.15). This also explains why no endpoint
attainment inside a half-open floor cell is being assumed.

Proof of gain ordering and the displayed consequences. Put
$t_p=(|\beta_{p,1}/\alpha_p|,|\beta_{p,2}/\alpha_p|,
|\beta_{p,3}/\alpha_p|)$. The body $U_c$ is invariant under signs and
coordinate permutations. Taking absolute coordinate values shows that

$$
H_p(c)^2=\max_{z\in U_c,\ z_i\ge0}
                   \bigl(\|z\|^2+(t_p\cdot z)^2\bigr).
\tag{AFR.19}
$$

It depends only on the sorted entries of $t_p$ and is nondecreasing in
each of them. Native right multiplication permutes, with signs, the
four normal coordinates. Consider two possible scalar magnitudes
$a\ge b>0$, with remaining magnitudes $t_1,t_2$. Selecting $a$ leaves
ratios $(b/a,t_1/a,t_2/a)$; selecting $b$ leaves
$(a/b,t_1/b,t_2/b)$. The former entries are no larger under this matching.
Sorting preserves the componentwise comparison. Therefore any largest
accessible scalar magnitude minimizes $H_p(c)$ among all accessible
charts, including ties.

The body $U_c$ contains $(\delta+c)B_2^3$ and is contained in $A_cB_2^3$.
Equation (AFR.8) gives
$(\delta+c)/h_p\le H_p(c)\le A_c/h_p$. This proves (AFR.16), including
its strict comparison with $R$ for every fixed $q>0$. If $n=1$, the
identity chart has $h_p=1$, $\beta_p=0$ and $H_p(c)=A_c$; it is optimal.
Finally
$(A_c-\delta)\sqrt{1+g^{-2}}\le\sqrt{15}c$ when $g\ge1/2$.
This proves the last assertion. $\square$

The comparison $g\ge1/2$ is available at the full native gain budgets
$N\ge3$ for AB and $N\ge2$ for ABC. It does not replace the gain of a
smaller declared budget. The theorem optimizes this fixed port under
adversarial sensor errors; changing precision during the run, changing
framing, or selecting a different encoder defines another problem.

## 4. Finite calibration and two distinct error contracts

**Definition 4.1 (installed rational-projective calibration).** A finite
calibration packet contains $\mathbf h\in\mathbb Z^4\setminus\{0\}$ and
$\ell\in\mathbb Z$, representing the plane

$$
\langle b,\mathbf h\rangle=\ell,
\qquad n=\mathbf h/\|\mathbf h\|,\quad
\lambda=\ell/\|\mathbf h\|.
\tag{AFR.20}
$$

The packet, its finite code and correct association with this instrument
are actually acquired and installed independently of $x_0$. Their cost
is charged. This is a restriction on the original calibration class,
not an approximation to an unspecified original plane. Normalized
coordinates can be irrational; their ratios have the finite exact
projective description. For a native chart put

$$
\mathbf h p=A_p+B_p,\qquad A_p\in\mathbb Z,\quad B_p\in\mathbb Z^3.
$$

For the finite implementations in this section $\delta>0$ is rational
and is included in the actual public packet. The original arbitrary
source amplitudes and source points remain allowed.

**Corollary 4.2 (finite implementation attaining the floor-port value).**
Under Definition 4.1, the installed floor port of Definition 3.1, and
$g>0$, one fixed finite algorithm acquires a rational initial-state
estimate on every legal run, in two completed Reads and at most $N$
updates, with risk exactly (AFR.15). It retains a finite rational squared
error certificate, for example

$$
C_{\rm floor}=(\delta+2c)^2
          \left(1+\frac{\|\mathbf h\|^2}{A_p^2}\right),
\qquad \|\widehat x-x_0\|^2\le C_{\rm floor}.
\tag{AFR.21}
$$

This certificate need not be the sharp minimax number itself.

Proof. The finite native gain table lists the accessible unsigned scalar
coordinates of $\mathbf h$. Integer square comparisons select a largest
nonzero $|A_p|$ without deciding equality of arbitrary reals. A fixed
representative uses at most two internal updates for AB or one for ABC,
subject to the smaller original budget in (AFR.5). Acquire $K_0$, perform
that prefix and the anchor, and acquire $K_1$, on this same register.
Form the two rational centers and compute

$$
\widehat x=\left(Y_0,
 \left(\frac{\ell-B_p\cdot Y_1}{A_p}+Y_1\right)p^{-1}\right).
\tag{AFR.22}
$$

Only finite integer/rational operations occur. Each port invocation is
productive by hypothesis and all finite received integers have finite
width. Nonzero integer $A_p$ makes division total. Theorem 3.3 gives the
sharp upper risk, and its lower bound applies to this algorithm as a
member of the same full controller class, hence gives equality. Since
$\delta+\sqrt3c\le\delta+2c$ and
$h_p^{-2}=\|\mathbf h\|^2/A_p^2$, (AFR.16) gives (AFR.21).
The two reports, chart, calibration, certificate and actual identities
can all be retained. No coefficient is stored as an exact unnamed real.
$\square$

**Definition 4.3 (alternative rational total-error port).** In place of
both the original real port and the floor port, an expressly installed
Read can deliver complete rational fields $(Y,d)$ with

$$
Y\in\mathbb Q^3,\quad d\in\mathbb Q,\quad
0\le d\le\delta,\qquad \|Y-P_Ez\|\le d.
\tag{AFR.23}
$$

Every reached call finishes, and all reply sequences satisfying (AFR.23)
are allowed, including arbitrary correlations and dependence on history.
The reported $d$ certifies the *total* discrepancy, including any finite
representation error. There is no preceding $\delta$-noisy real reply
that the observer is then entitled to round without further allowance.
Frames depend only on these reported fields and public/request data.
The calibration is Definition 4.1 and the physical source/menu/update
contract remains Definition 1.1. This defines a relation of possible
finite replies, not one particular deterministic quantizer.

**Corollary 4.4 (relation-wide exact risk with total-error replies).**
For Definition 4.3 and $g>0$, the finite rational estimator (AFR.22),
using a maximal-gain chart and its same two Reads, has certificate

$$
C=d_0^2+\frac{\|\mathbf h\|^2}{A_p^2}d_1^2\le R^2.
\tag{AFR.24}
$$

The minimax risk over this entire reply relation is $R$. For $g=0$ it
is infinite. Equality is asserted for this relation of replies, not for
every deterministic finite backend satisfying its numerical inequality.

Proof. The discrepancy vectors of the two actually returned rational
triples have norms at most their respective $d_j$. Equation (AFR.8)
proves (AFR.24); it is a finite rational squared certificate. This gives
the upper bound for every allowed correlated trace.

For the converse, fix any competing controller and any rational
$0<t<\delta$. The rational plane (AFR.20) has a rational point: choose
one nonzero coordinate of $\mathbf h$ and solve that coordinate for
$\ell$, setting the other three to zero. Choose a rational visible
coordinate as well. Follow this rational nominal initial source, at
every Read reporting its exact rational visible value and the rational
certificate $d=t$. Native matrices have integer entries, so every
nominal read remains rational. This is an allowed complete branch.

A branch with no anchor or zero gain has the original unbounded blind
pair. Otherwise apply (AFR.11) about this nominal source with $t$ in
place of $\delta$, and with the actual first-anchor gain $h$. At every
Read both endpoints can report the nominal rational visible value with
the same field $d=t$: the two-component invariant gives discrepancy at
most $t$. The entire rational frames and all later choices agree.
The endpoint half-distance is $t\sqrt{1+h^{-2}}\ge
 t\sqrt{1+g^{-2}}$. Thus every competitor has at least this risk for
every rational $t<\delta$. Taking the supremum as $t$ tends to
$\delta$ proves the lower bound $R$. No rationality of the endpoint
source or of a norm-maximizing tangent direction is required; the source
domain still contains every real point of the plane. $\square$

This equality does not contradict Theorem 2.2. The original interface
admits every exact noiseless real report at every real source. The
rational total-error interface instead supplies only finite rational
reports, with the representation already included in the certified
radius. In particular it removes those noiseless real traces that drove
the saturation condition. It is a changed sensor contract, not a new
finite implementation of all original traces.

**Proposition 4.5 (why post-rounding does not preserve the old cap).**
Let a deterministic digitizer send a completed old real reply $r\in E$
to $Q(r)\ne r$. Then on the original source there is a legal true
visible value and a legal error of norm $\delta$ for which the digitized
value has error $\delta+\|Q(r)-r\|$.

Proof. Set $v=Q(r)-r$ and choose the actual initial visible coordinate
$a=r-\delta v/\|v\|$. This is allowed independently of any hidden point
of the affine plane. The real reply $r$ has error
$r-a=\delta v/\|v\|$, whereas
$Q(r)-a=(1+\delta/\|v\|)v$. Taking its norm gives the assertion.
$\square$

The proposition explains why (AFR.23) needs an installed total-error
supplier and why the fixed floor port pays a separate cell uncertainty.
It is not a lower bound on every possible alternative readout apparatus.

## 5. Effective calibration, positive slack and productive finite replies

**Assumption 5.1 (finite local calibration programs).** For this section,
replace the projective packet by actual finite programs for $n$ and
$\lambda$. On every input $r\in\mathbb N$, they halt with rational
approximations, each coordinate having absolute error at most $2^{-r}$.
Their finite code, input convention, validity guarantee, installation and
instrument association are supplied and paid. The programs use only
finite local computation and their finite installed data; they have no
real oracle, unknown seed, further source endpoint, or source-dependent
advice. Correctness and totality are hypotheses about the supplied
programs, not properties inferred by a universal program verifier.

The fixed $n$ is unit, $\lambda$ is arbitrary, and $g>0$ is promised for
the original menu and budget. Positive rational $\delta,\epsilon$ are
supplied. A productive floor port as in Definition 3.1 can be configured
with one $m\ge0$ chosen from these source-independent calibration data
before any source Read or update. The same configured $m$ is used at
both Reads. The source does not evolve during local computation; its
only changes are the declared updates.

**Theorem 5.2 (finite same-source acquisition with effective slack).**
Under Assumption 5.1 there is a single finite algorithm, uniform in the
supplied finite data, that terminates on every legal run and returns a
rational $\widehat x$ and a rational $B$ such that

$$
\|\widehat x-x_0\|\le B<R+\epsilon
\tag{AFR.25}
$$

for every $x_0\in\mathcal D_{n,\lambda}$ and every allowed complete
sensor-error choice. It uses exactly two source Reads and a native
prefix followed by one anchor, with at most $N$ updates. All other
refinement is local; there is no reset, copy, extra read, clock or exact
real equality test. The fixed positive $\epsilon$ is part of this
changed approximate contract. The theorem does not assert attainment
of the original cap $R$.

Proof. There are at most four accessible unsigned normal coordinates,
listed in (AFR.5). Certified coordinate approximations give rational
intervals $[l_i,u_i]$ for their absolute values, with widths tending to
zero. Set $l=\max_i l_i$ and $u=\max_i u_i$. These satisfy
$l\le g\le u$ and $u-l\to0$. Once $l>0$, choose a chart $p$ whose
lower endpoint is $l$. Its true gain $h_p$ is at least $l$. Such a
stage is reached by the promise $g>0$; no choice between exact ties is
needed.

Write $F(t)=\delta\sqrt{1+t^{-2}}$ for $t>0$. At successive stages
with $l>0$, finite rational square-root bisection supplies $U,L$ with

$$
U\ge F(l),\qquad L\le F(u),\qquad U-L<\epsilon/3.
\tag{AFR.26}
$$

A stage satisfying the last test exists. Indeed, take square-root
enclosures whose own errors tend to zero along the calibration stages;
then both bounds converge to $F(g)=R$. Bisection brackets positive
rational square roots by integer comparisons, so all tests are finite.
Monotonicity of $F$ gives

$$
F(h_p)\le U<R+\epsilon/3.
\tag{AFR.27}
$$

Now set $S=U/\delta$ and choose a dyadic $q=2^{-m}$, $m\ge0$, so that
$qS<\epsilon/3$. Configure that floor port before the two actual Reads.
Read $K_0$, perform the selected internal prefix and anchor, and Read
$K_1$. Convert to the finite rational centers $Y_0,Y_1$.
Each center has total discrepancy at most
$\delta+\sqrt3q/2<\delta+q$. If the chart coefficients were exact,
(AFR.7) would therefore have error at most

$$
(\delta+q)\sqrt{1+h_p^{-2}}\le U+qS.
\tag{AFR.28}
$$

No operation so far has changed the allowed source amplitudes or used
an unreported source value.

The four coefficients needed in the scalar part of the decoder are

$$
\tau=\lambda/\alpha_p,\qquad
\gamma_i=\beta_{p,i}/\alpha_p\quad(1\le i\le3).
$$

The nonzero lower gain $l$ permits certified interval division. Refining
the supplied programs eventually gives rational approximations to all
four coefficients with any prescribed positive error. In detail,
intervals for $\alpha_p$ eventually avoid zero and have width tending
to zero; intervals for the numerators converge to finite real values.
The images of these rectangles under division then have widths tending
to zero. Rational endpoint operations certify that fact at each stage.

After $Y_1$ has actually arrived, choose $k$ so that

$$
2^{-k}(1+\|Y_1\|_1)\le\epsilon/3,
\tag{AFR.29}
$$

and refine until all four coefficient errors are at most $2^{-k}$.
Use the resulting rational $\widehat\tau,\widehat\gamma$ to output

$$
\widehat x=\left(Y_0,
  (\widehat\tau-\widehat\gamma\cdot Y_1+Y_1)p^{-1}\right).
\tag{AFR.30}
$$

Relative to the exact-coefficient decoder the only error is a real
scalar of magnitude at most the left side of (AFR.29), followed by
orthogonal right multiplication. Thus (AFR.28) and the triangle
inequality give the rational certificate

$$
B=U+qS+\epsilon/3<R+\epsilon.
\tag{AFR.31}
$$

All searches terminate by the stated positive-gain and total-program
hypotheses. Every finite actual reply has finite magnitude, so (AFR.29)
requires finite precision even though it is not uniformly bounded over
sources. The source is not queried during this refinement. The chosen
chart has a representative within the original budget, exactly as in
the gain table. This proves every assertion. $\square$

The bound is uniform in source amplitude and sensor errors; the amount
of work and coefficient precision is per actual run. With an unbounded
$Y_1$, a fixed coefficient error cannot be converted to a uniform small
output error. For instance a nonzero slope discrepancy $\Delta\gamma$
produces the scalar discrepancy
$\Delta\tau-\Delta\gamma\cdot Y_1$, unbounded over $Y_1$ in its
nonzero slope direction. In a nonzero-gain chart every $w\in E$ is an
allowed true first-anchor value by (AFR.17) with $w$ in place of $w_*$.
The sensor can have zero error, so the corresponding floor centers also
range unboundedly in every coordinate direction. The magnitude-sensitive
refinement in (AFR.29) closes this particular arithmetic gap without
an amplitude restriction. This observation is a statement about this
coefficient-based decoder, not a general lower bound on all algorithms.

**Proposition 5.3 (the productive floor hypothesis is additional).**
Bare Cauchy-name access to the actual visible coordinate does not
uniformly implement the exact productive port (AFR.12), even with
$e=0$, on all the original source. This remains true with the fixed
public calibration and any fixed $q>0$.

Proof. Suppose a finite algorithm, given arbitrary rational
approximations with error at most $2^{-r}$ on request $r$, always
finishes with the exact first floor integer. Run it on the zero
coordinate with replies zero. It halts after finitely many requests;
let $r_*$ be their maximum, or zero if there are none. Choose
$0<\eta<\min(q,2^{-r_*})$. The same finite zero replies are valid
approximations to the actual coordinate $-\eta$, and extend to a full
valid Cauchy name for that coordinate. The same finite computation
must then output the same integer. But the floors of $0/q$ and
$-\eta/q$ are respectively $0$ and $-1$. Both visible coordinates
occur in (AFR.1) with any common allowed hidden point. This is a
contradiction. $\square$

The proposition concerns that specified approximation-access
representation. It does not rule out a separately supplied productive
sensor, a representation with a justified grid-wall decision, or a
weaker approximate finite port. Neither Theorem 3.3 nor Theorem 5.2
constructs such a sensor from exact real mathematical parameters.

## 6. Retained use of the acquired finite estimate

**Corollary 6.1 (same-run native response use and simultaneous digital
resources).** Retain an estimate acquired by Corollary 4.2, Corollary 4.4
or Theorem 5.2, together with its finite certificate, calibration,
configuration and acquisition identities. Write its certified bound as
$\|\widehat x-x_0\|\le B$, allowing $B=\sqrt C$ to be represented by a
rational squared certificate. For every subsequent actually selected
native action sequence, retain the accumulated map $T$ from the initial
state. A seven-row code with 28 bits suffices for this map. It can be
updated and used to compute the rational prediction $T\widehat x$ with

$$
\|T\widehat x-Tx_0\|\le B.
\tag{AFR.32}
$$

Sequential prediction and prediction by the composed word agree
exactly. No coordinate's rational numerator or denominator grows in
width merely because the action sequence grows longer. Visible true
responses satisfy the same bound after applying $P_E$.

For the projective floor implementation, take a fixed sequential binary
integer representation, schoolbook arithmetic, and a fixed number of
rational fields. Let $L$ bound the total bit width of the installed
integer calibration and rational error-bound fields; let $m$ be the
*numerical* exponent in $q=2^{-m}$, not its encoded input length. Let
$K$ be the maximum bit length, including sign, of the six received floor
integers. Let $P$ count the actually installed finite program bits, and
$J$ count all genuinely retained framing, identity, binding, rights,
mandatory-history and control bits on this run. The two-read numerical
decoder, squared certificate and retained state admit simultaneous
bounds

$$
\text{peak digital storage}=O(P+J+L+m+K),\qquad
\text{numerical bit work}=O((L+m+K)^2).
\tag{AFR.33}
$$

Actual input acquisition, parsing, copies, output and protocol work are
charged in addition. Once this estimate is acquired, a supplied stream
of $s$ native action tokens can be interpreted with numerical work
$O((s+1)(L+m+K))$, plus its actual token, output and history traffic.
For the rational total-error version, replace the numerical-width
quantity by the total bit width of its actual rational calibration,
reply and certificate fields. For Theorem 5.2, program evaluations,
coefficient refinements, their output widths and scratch are additional
actual resources; no bound for them is asserted by (AFR.33).

Proof. Lemma 3.2 gives at most one signed coordinate in each row and
column of every native update. The product of two such matrices again
has at most one signed coordinate in each row and column: an output
row either vanishes or selects one row of the right factor with a sign,
and distinct surviving rows select distinct columns. Thus products
remain signed partial coordinate permutations and have Euclidean
operator norm at most one.

Index the initial real coordinates by $1,\ldots,7$. For each output row
store one of $0,+1,-1,\ldots,+7,-7$, meaning zero or the signed selected
initial coordinate. Fifteen symbols fit in four bits, hence seven rows
fit in 28 bits. The actual action token composes this code on the left
with its prescribed native matrix. Evaluating the code only selects,
negates or zeroes coordinates of the retained rational estimate.
Therefore (AFR.32) follows by nonexpansion, and widths stay bounded by
those of the retained estimate. Associativity of matrix multiplication
gives agreement between sequential evaluation and word composition,
including the actual acquisition prefix. The map is not a separately
acquired source specimen; it is a finite record of the declared actions.

For (AFR.33), each dyadic center is $(2K_i+1)/2^{m+1}$. Its explicit
integer numerator and denominator have $O(K+m+1)$ bits in total.
The integer quaternion product $\mathbf h p$ only permutes and negates
four calibration coordinates. The fixed-dimensional formula (AFR.22)
uses a fixed number of additions, multiplications and divisions by the
nonzero integer $A_p$. Unreduced rational pairs suffice: multiplying
a fixed number of denominators and numerators increases their lengths
by at most a constant factor. The squared certificate (AFR.21) has the
same property. Schoolbook integer operations of this width use linear
scratch and at most quadratic bit work, giving (AFR.33). The constant
number of retained reports and output coordinates adds only another
constant factor. Selecting among the at most four native gain
coordinates also satisfies this bound. Each later code update is
constant work on fixed-size labels, and producing its seven rational
coordinates uses at most a fixed number of scans of width
$O(L+m+K)$. This proves the stated stream bound. $\square$

The actual source updates during this use must still respect the
original *total* cap $N$, including acquisition. If a separate continuing
update budget is installed, its extra actions and cost are separately
charged. Formula (AFR.32) can also evaluate a numerical counterfactual
word, but that arithmetic grants no physical source action or initial
state restoration. The result compares the same already selected
word on the estimate and the source. It does not show that a policy fed
predictions would choose the actions selected from actual noisy replies.
To predict a later noisy reply rather than the true visible value,
its additional sensor and cell errors must be added under that reply's
own contract.

The 28-bit map does not replace the six acquisition fields, any output
coordinates, or a required authenticated chronology. Its fixed size
does not bound $J$. On the original unbounded domain the whole signed
floor payload and the output's integer parts can be arbitrarily long.
Even zero sensor error and an arbitrarily large initial visible
coordinate force unbounded $K$. Accordingly these are finite-per-run
storage bounds for a uniform finite program, not bounded-memory or
whole-system constant-storage claims. The source, sensor, exact
actuator, reference, source provisioning, installation and any physical
cost of their production remain additional coordinates of the resource
vector. None of the numerical bounds is a cost-optimality assertion.

## 7. Independent views and the recovery directions actually supported

**Definition 7.1 (four readings of the same process).** Space exposes
the actual initial affine point $x_0$ and the current point $T_tx_0$ in
$W$. The source equation is a geometrical constraint on $b_0$, not a
record of observations. Time exposes the actual ordered Read, internal
update, anchor and Stop events and their identities. It has no external
clock and by itself contains no numerical reply values. Boundary
exposes the finite port frames at their bound read cuts: their whole
signed values, configuration, required tags and completions. Memory
exposes what the observer has actually acquired and retained: the
calibration/configuration, two replies and their cut identities, finite
estimate and certificate, accumulated native-map code, and any mandatory
history and installed continuing rights. A view has no unrestricted
copy of the entire history by definition.

A complete world specifies one initial point, one installed interface,
one actual source/right binding, and the complete admissible error
choices on its actual event history. The same world generates all four
readings. Rights to call or update are supplied installation conditions;
they cannot be reconstructed merely by decoding a number or printing a
record. The approximate continuation task here is to return estimates
of the initial point and of its true native responses with the declared
Euclidean error bound. It is not exact identification of every real
source, authenticated past, or future noisy report.

**Proposition 7.2 (numerical recovery, transport and information limits).**
For the two-read acquisitions above, the following directions hold.
Acquired boundary fields and retained calibration determine the stated
finite estimate and certificate; those retained data support the native
response task by Corollary 6.1. In the exact-coefficient projective
versions, the estimate and chart recover the numerical pair of reported
values exactly:

$$
Y_0=\widehat a,\qquad Y_1=\operatorname{Im}(\widehat b p).
\tag{AFR.34}
$$

For the floor version $q$ further recovers the six numerical integers
by $K_i=Y_i/q-1/2$ coordinatewise. In Theorem 5.2, (AFR.34) also holds
for its approximate-coefficient output (AFR.30), but that output alone
need not recover the coefficient approximations or its certificate.
For the total-error version the fields $d_j$ also require their own
retention. None of these numerical inverses recovers unretained frames,
chronology, errors or rights.

Every initial source in a common acquired-record fiber lies within the
proved bound of its common decoded estimate. Any common native word
has the same error guarantee by (AFR.32), and therefore two such sources
have response distance at most twice that bound. Record equality does
not imply exact equality of their initial states or their native
response functions. There is no four-way exact equivalence of the
independent readings.

Proof. The forward computation is (AFR.22) or (AFR.30), with the actual
certificate construction in the appropriate theorem. In either formula
$\widehat b p$ has imaginary part exactly $Y_1$ because its remaining
part is a real scalar; this proves (AFR.34). The floor center relation
then gives its integers. Real scalar addition carries no information
about framing or a separately reported radius. The route from reports
to estimate to the recovered numerical reports agrees exactly on the
actual report domain. The route from a retained estimate through
successive native actions agrees with the composed-word route by the
code proof in Corollary 6.1. These establish the stated route agreement
and dynamics compatibility, without inverting a destructive update.

The error theorem holds for every complete world in a record fiber,
so applying it to each source in that fiber proves the common-center
and twice-radius claims. Distinct allowed worlds can nevertheless have
identical entire records. The actual tangent pair (AFR.11) supplies
such worlds for real or rational-total-error reports; (AFR.18) supplies
them for the actual fixed floor port, with distinct initial sources.
Thus the task's exact equality kernel cannot be inferred from the
approximate error guarantee.

The fixed two-read acquisition word can be used for arbitrarily many
initial visible coordinates, producing different numerical reports;
its event word alone cannot recover those numbers. Conversely an
extra repeated Read can be inserted at the same cut with the same
reported value, yielding the same two retained numerical values with
a different event history; the estimate and chart do not determine
that history. The current register cannot recover all erased initial
data: for example one internal $A_{e_1}$ annihilates an arbitrary
initial visible component along $e_1$, with the hidden coordinate
held fixed. The resulting current states are identical for distinct
initial states in (AFR.1). Those observations establish the asserted
failures in the full declared source/menu domain. $\square$

In the original noiseless real interface, the existing inverse recovers
$x_0$ exactly from $(a_0,w)$ in a nonzero-gain chart. That is the
Boundary41/PG result. Positive adversarial noise or a fixed positive
cell width instead supports the approximate tasks proved here. Retaining
an estimate neither recreates an erased physical point nor authenticates
unretained past events. Native response prediction remains operational
arithmetic on the acquired memory, with the actual actions and rights
subject to their original limits.

## 8. Sources, mathematical delta and remaining domains

**Attribution 8.1 (reused suppliers and new synthesis).** The original
source, native gain table, affine decoder, operator norm and actual
midpoint two-component invariant are [PG44.15–44.17][PG] and
[Boundary41.1–41.4][BOUNDARY]. They are used at their original unbounded
initial-state quantifiers. Boundary54 instead uses the two hidden
radii $7,25$, a cap condition and a continuous internal-control menu;
it does not supply the present domain or native floor theorem.

The representation distinctions in [Finite Affine Calibration Advice,
Sections 2–3, 18 and 21–23][FACA], [Fixed Offset Precision Payload,
Sections 7–11][FOP] and [Capped Precision Permanent Blindness,
Sections 2–5][CPB] are reused: full integer parts and complete frames,
productive installed backends, and equality of complete actual
continuations matter separately from a real error inequality. Their
source is the initialized no11 Step/Extent producer and their calibrated
quantity is $b+q\alpha^d$. Its finite quadratic floor evaluation is
not an implementation of an arbitrary real visible coordinate in $W$.
Their exact arithmetic is a supplier example, not a sensor port here.

[Parameterized Cross Product Recovery, Sections 58, 73–76, 79 and
87–88][PCR] and [Autonomous Predictive Memory][APM] already distinguish
finite closed rational data, retained names, finite-per-instance memory,
certified numerical computation and actual acquisition/use. Their
prepared-tree, cross-product and future-response contracts do not
supply this instrument. The native structural and callable storage
atlases similarly require their own source acquisitions, tapes and
installed rights. No source map or actuation bridge from those
interfaces to (AFR.1) is assumed.

At the formal source level,
[`QuantizedWordApproximation.quantized_word_approximation`](../../../D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.lean)
and its [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.scribe.cs)
assume a supplied finite-center quantizer; they do not construct one
on this unbounded source or implement its port.
[`FiniteWordFiberDiameter.finite_word_fiber_prediction_diameter`](../../../D5/S3/Observer/MetricGeometry/FiniteWordFiberDiameter.lean)
and its [Scribe](../../../Blueprint/D5/S3/Observer/MetricGeometry/FiniteWordFiberDiameter.scribe.cs)
require a global output diameter and discount, absent here.
[`UniqueInterfaceKernelCriterion.unique_interface_factorization_iff_reverse_kernel`](../../../D5/S3/ConceptDynamics/Factor/UniqueInterfaceKernelCriterion.lean)
is an exact abstract factorization criterion, not the acquired
approximate guarantee (AFR.32).
The finite-carrier premise in
[`DefectGraphMinimumColoring`](../../../D5/S3/ConceptDynamics/Coding/DefectGraphMinimumColoring.lean),
including its private existence helper, does not apply to this affine
source. The actual hypotheses of
[`SelfCalibratingFibers`](../../../D5/S3/ConceptDynamics/Experiment/SelfCalibratingFibers.lean)
are positive rank-one two-by-two shear experiments; those of
[`AffineCodebookMemory`](../../../D5/S3/Observer/LinearMemory/AffineCodebookMemory.lean)
include a driven finite codebook and its stated linear dynamics.
Neither installs the calibration of (AFR.1).
[`RationalResponseRefinement.post_word_run`](../../../D5/S0/Computability/RationalResponseRefinement.lean)
and its [Scribe](../../../Blueprint/D5/S0/Computability/RationalResponseRefinement.scribe.cs)
consume a particular arithmetic word grammar; generic finite
rational operations are not claimed as new mathematics here.

The new repo-derived synthesis is Theorem 2.2's retained displacement
term and finite-value saturation consequence, and Theorem 3.3's actual
floor-cell coupling and maximal-native-gain ordering. Its two originating
vectors remain separate under the *actual* native actions, which is
why one legal sensor ball suffices at every later Read. A marginal
optimization over two unrelated noisy observations would not prove its
full-controller lower bound. Corollaries 4.2–4.4 and 6.1 consume these
results; their ordinary inverse/arithmetic/contraction ingredients are
credited. The source-specific effective completion in Theorem 5.2
selects a nearly optimal chart without an equality oracle and refines
its coefficients against the magnitude of the actually acquired reply.
It retains the changed finite-port and positive-slack hypotheses.

**Attribution 8.2 (literature and scope).** Symmetric indistinguishable
pairs are an established optimal-recovery method; see S. Foucart and
C. Liao, [arXiv:2111.02601v1, Lemma 11](https://arxiv.org/abs/2111.02601v1).
That lemma supplies the general worst-case same-data lower-bound
principle, not the destructive native-action or actual floor-frame
coupling above. A. Pauly,
[arXiv:1204.3763v3, Sections 3–4 and Proposition 3](https://arxiv.org/abs/1204.3763v3),
defines representations and realizers and supplies computable evaluation
on represented spaces. Infinite names and their evaluation are not
finite installed packets; no finite acquisition theorem is inferred
from that proposition. Quaternion norm multiplication and Euclidean
coordinates are standard; the pinned mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`,
[`Mathlib/Analysis/Quaternion.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Quaternion.lean),
contains its normed-division-ring instance and tuple linear isometry.
These are algebra suppliers, not acquisition or physical evidence.

The later weighted-history query, autonomous STOP-history, original-point
prediction-window, LAB arithmetic-growth and mixed-screen results have
their own initialized sources and tasks. In particular an acquired
no11 prefix/window, a paid LAB growth service, or a native mixed-screen
latch has no supplied map into this external $W$ sensor. Their same-source
and retained-use distinctions are respected; they do not turn the
finite-port hypotheses here into conclusions. The results here are
ordinary mathematical deductions at these declared scopes, not a claim
of exhaustive literature coverage, worldwide priority or a new general
optimal-recovery principle.

**Boundary 8.3 (unclosed original obligations).** The original cap $R$
remains the exact all-real-reply minimax value. Theorem 2.2 excludes its
attainment by each closed finite-value output but leaves its infimum
unchanged. The positive fixed-floor excess concerns one explicitly
specified encoder with additional representation uncertainty. Rational
total-error attainment concerns a different relation of reply traces.
Effective-slack acquisition concerns finite local calibration programs,
an installed productive floor port and a declared $\epsilon>0$.
None of these statements silently converts one interface into another.

For arbitrary original calibration without a finite effective
representation, the required finite observer has not been supplied.
For arbitrary original real replies, no finite acquisition procedure
preserving all original traces and attaining $R$ is asserted. Productive
finite readouts of arbitrary actual amplitudes, exact actuation,
source/reference/anchor preparation, instrument binding, continuing
rights and physical implementation are independent supplier obligations.
The finite calibration programs in Assumption 5.1 are promised correct
and total; their acquisition and certification are not free. Uniform
running-time, uniform memory, all-resource optimality, arbitrary
adaptive precision, probabilistic improvement and actuation-error
robustness are outside the proved contracts.

The four independent views have the partial recovery and transport
arrows of Proposition 7.2, not equal exact task kernels. A universal
internal source reduction, arbitrary-cut view equivalence, the original
fixed-$G_{\rm gc}$ and original-$Q$ tasks, parked-consumer and unchanged-
initialization obligations retain their original open scopes. This
external affine model does not resolve them. The mathematical proofs
here neither supply new Lean certification nor establish a physical
ontology or the full mutual-recovery programme.

[PG]: RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[BOUNDARY]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md
[FACA]: RECURSIVE_RELATIONAL_OBSERVATION_FINITE_AFFINE_CALIBRATION_ADVICE.md
[FOP]: RECURSIVE_RELATIONAL_OBSERVATION_FIXED_OFFSET_PRECISION_PAYLOAD.md
[CPB]: RECURSIVE_RELATIONAL_OBSERVATION_CAPPED_PRECISION_PERMANENT_BLINDNESS.md
[PCR]: RECURSIVE_RELATIONAL_OBSERVATION_PARAMETERIZED_CROSS_PRODUCT_RECOVERY.md
[APM]: RECURSIVE_RELATIONAL_OBSERVATION_AUTONOMOUS_PREDICTIVE_MEMORY.md

## 追加锚（本行以下为增补区）

## 9. Distinct bounded quadratic-clock model: finite and countable exact-cap answers

**Definition 9.1 (bounded calibrated quadratic clock).** Fix an integer
$h\ge1$, real $0<\varepsilon\le h^2/2$ and finite $B>r$, where

$$
r=\varepsilon/h,\qquad m=-h/2,\qquad K=[m-B,m+B].
\tag{QC.1}
$$

The unknown origin is $\tau\in K$. The calibrated passive clock is
$H(t)=t^2$, with known unit gain and zero offset. Its two actually acquired
reports, indexed by $0,h$, are

$$
S_h(t)=\bigl(t^2,(t+h)^2\bigr),\qquad
 y=S_h(\tau)+\eta,\qquad \eta\in[-\varepsilon,\varepsilon]^2.
\tag{QC.2}
$$

For every origin, every vector in this full closed square is allowed,
including its boundary. There is no probability law or additional joint
error constraint. Write $Y=S_h(K)+[-\varepsilon,\varepsilon]^2$ for the
reachable reports. A decision is any deterministic map
$\delta:\mathbb R^2\to\mathbb R$, with risk

$$
\mathcal R(\delta)=
 \sup_{\tau\in K}\ \sup_{\eta\in[-\varepsilon,\varepsilon]^2}
 |\delta(S_h(\tau)+\eta)-\tau|.
\tag{QC.3}
$$

No measurability, computability or membership of the answer in the
compatible-origin set is required. This is the two-report source of
[Clock, Definitions 77.1 and 79.1 and Proposition 79.5](https://github.com/the-omega-institute/trureturing/blob/6b48dd4bf915980ce45d7998d0347d031e63a1bc/docs/develop/theory/FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md).
It is distinct from the affine source of Definition 1.1 and from Clock
§§80–81's three-report clock with unknown gain and offset. The prior $K$
is fixed once $h$ is chosen; changing $h$ in (QC.1) changes that prior.

**Definition 9.2 (completed answer representations).** The completed
answer range of $\delta$ is $A_\delta=\delta(Y)$. A finite-range decision
has finite $A_\delta$. A closed word-valued decision factors as
$\delta=\mathrm{Dec}\circ E$ on $Y$, where $\Sigma$ is a fixed finite
symbol alphabet, $E:Y\to\Sigma^*$ and
$\mathrm{Dec}:\Sigma^*\to\mathbb R$ are deterministic maps, and the decoder
is fixed independently of the unknown origin and errors. Public fixed
calibration may parameterize both maps. All source- or report-dependent
operands determining the answer are in the completed word: no analog
reply, implicit decoder parameter, callable backing, infinite name or
later source access is additionally available to that decoding.
Here “closed” concerns this operand boundary, not topological closedness
of $A_\delta$. A uniform word-length bound means one finite $L$ with
$|E(y)|\le L$ for every $y\in Y$; per-instance finiteness means only
$E(y)\in\Sigma^*$ for each $y$.

This uses Definition 2.1's representation distinction with a scalar
codomain. The finite-codebook viewpoint is also used by Zhu and Lafferty,
[*Quantized Minimax Estimation over Sobolev Ellipsoids*, §2](https://arxiv.org/html/1503.07368v3):
a fixed bit budget bounds the number of decoded estimates. Their risk
is expected squared error under statistical laws, and their principal
model is Gaussian white noise over Sobolev ellipsoids; their asymptotic
bounds are not bounds for (QC.3).

**Theorem 9.3 (finite nonattainment and countable dyadic attainment).**
Under Definition 9.1, the unrestricted real-answer minimax risk is the
existing value $r$. Every decision with finite completed answer range
satisfies $\mathcal R(\delta)>r$. Nevertheless there is a decision with
values in the fixed dyadic set

$$
\mathbb D=\{j2^{-n}:j\in\mathbb Z,\ n\in\mathbb N\}
\tag{QC.4}
$$

whose risk is exactly $r$. Consequently the least cardinality of a
completed answer range attaining this risk is $\aleph_0$. A fixed binary
symbol alphabet suffices for completed finite words attaining $r$ as
arbitrary maps; no uniform length bound can suffice.

Proof. Reuse Clock Theorems 79.2–79.3 and Proposition 79.5. Their secant
identity and balanced-prior radius are

$$
\|S_h(t)-S_h(s)\|_\infty
 =|t-s|\bigl(h+|s+t+h|\bigr),\qquad
 \inf_\delta\mathcal R(\delta)=\min(B,\varepsilon/h)=r.
\tag{QC.5}
$$

For the finite-range obstruction, fix any finite proposed range $A$.
For $0<x<B-r$, put

$$
\begin{aligned}
d_x&=\frac{2rh}{h+2x},&
s_x&=m+x-d_x/2,& t_x&=m+x+d_x/2,\\
y_x&=\frac{S_h(s_x)+S_h(t_x)}2,&
w_x&=r-d_x/2=\frac{2rx}{h+2x}.
\end{aligned}
\tag{QC.6}
$$

Since $0<d_x/2<r$ and $x+r<B$, both $s_x,t_x$ lie in $K$.
Their sum is $2m+2x=-h+2x$, so (QC.5) gives

$$
\|S_h(t_x)-S_h(s_x)\|_\infty
 =d_x(h+2x)=2\varepsilon.
\tag{QC.7}
$$

Thus the same report $y_x$ is legal at both origins, with opposite
errors $[S_h(t_x)-S_h(s_x)]/2$ and its negative. Their maximum norms
are exactly $\varepsilon$; the closed-square boundary is used.
A common answer accurate to $r$ at both origins must belong to

$$
\begin{aligned}
J_x&=[s_x-r,s_x+r]\cap[t_x-r,t_x+r]\\
   &=[m+x-w_x,m+x+w_x].
\end{aligned}
\tag{QC.8}
$$

The assumption $2r\le h$ gives $0<w_x<x$ for every $x>0$, including
$2r=h$. Hence $J_x\subset(m,m+2x)$, and these intervals approach $m$
while excluding it. If $A$ has no element above $m$, every $J_x$ misses
$A$. Otherwise let $a=\min\{v-m:v\in A,\ v>m\}>0$ and choose
$0<x<\min(B-r,a/2)$. Again $A\cap J_x=\varnothing$. Any answer in $A$
at this one report therefore has error strictly greater than $r$ at
one of its two legal origins. The witness pair may depend on $A$.
This proves strict nonattainment for every finite range, without a
range-independent positive excess.

For countable attainment, retain the actual compatibility set

$$
C(y)=\{t\in K:\|S_h(t)-y\|_\infty\le\varepsilon\},\qquad y\in Y.
\tag{QC.9}
$$

It is nonempty compact and need not be an interval. Write
$p_y=\min C(y)$ and $q_y=\max C(y)$. Equation (QC.5) and the common-report
triangle inequality give $q_y-p_y\le2r$. Exactly the answers accurate
to $r$ at every origin compatible with $y$ form the nonempty interval

$$
J(y)=\bigcap_{t\in C(y)}[t-r,t+r]
     =[q_y-r,p_y+r].
\tag{QC.10}
$$

If it has positive length, dyadic density gives $J(y)\cap\mathbb D\ne
\varnothing$. If it is a singleton, then $q_y-p_y=2r>0$ and

$$
2r\bigl(h+|p_y+q_y+h|\bigr)
 =\|S_h(q_y)-S_h(p_y)\|_\infty
 \le2\varepsilon=2rh.
\tag{QC.11}
$$

Therefore $p_y+q_y=-h$ and $J(y)=\{m\}$. Since $h$ is integral, $m$ is
dyadic. Thus every $J(y)$ meets the same countable set $\mathbb D$.
Fix an enumeration $(a_n)_{n\in\mathbb N}$ of $\mathbb D$ and define

$$
\delta_{\mathbb D}(y)=a_{\min\{n:a_n\in J(y)\}},\quad y\in Y;
\qquad \delta_{\mathbb D}(y)=m,\quad y\notin Y.
\tag{QC.12}
$$

The minimum exists and the selected value has error at most $r$ on
every allowed source/error pair. The existing lower bound in (QC.5)
makes its risk exactly $r$. In particular the common report
$y_0=(h^2/4+r^2,h^2/4+r^2)$ of $m-r,m+r$ forces the unique cap-$r$
answer $m$. This also realizes the singleton case rather than merely
allowing it abstractly.

Encode the finite index in (QC.12) by a fixed binary word and decode it
by the fixed enumeration. This gives a closed word-valued decision.
Its attained range is infinite by the finite-range obstruction and is
countable by construction. Words of uniformly bounded length over a
finite symbol alphabet have only finitely many possibilities, so the
lengths cannot have a uniform bound. $\square$

The same-data two-object lower-bound method in this proof is
literature-attested: Foucart and Liao,
[*Optimal Recovery from Inaccurate Data in Hilbert Spaces: Regularize,
but what of the Parameter?*, Lemma 11 and §4.1](https://arxiv.org/abs/2111.02601v1),
use linear Hilbert-space observations, a subspace-approximability model
and a norm-ball uncertainty set. Their whole regularization theorem is
not instantiated by the nonlinear signature (QC.2). Compatible-target
midpoints also occur in Foucart,
[*Learning the Maximum of a Hölder Function from Inexact Data*, Theorem 1](https://arxiv.org/html/2509.25209v1),
for a Hölder model and a monotone Banach-lattice-valued target; this
clock source is not that model. These general methods, dyadic density,
and (QC.5) remain suppliers. The repo-derived mathematical addition is
the shrinking family (QC.6)–(QC.8) together with the singleton-center
classification (QC.11), yielding this source's finite/countable
separation. No worldwide priority claim is attached to that distinction.

The index selection (QC.12) is a definition of an arbitrary map using
exact real predicates, including non-strict compatibility and singleton
membership. Its existence supplies no terminating encoder on real-input
names, acquisition procedure, work bound or memory bound. Pauly,
[*On the topological aspects of the theory of represented spaces*,
§§3–4 and Proposition 3](https://arxiv.org/abs/1204.3763v3), defines
representations and realizers and proves computable evaluation for
supplied function and argument names. That result does not supply a
realizer for (QC.12). Proposition 5.3's distinction between real-name
access and a productive discrete port remains applicable. No
computability or noncomputability theorem for this selector is asserted.

**Assumption 9.4 (original complete adaptive main history).** Fix
nonnegative integers $k,d$. A main world is $W=(R,G,D,\tau)$, where $R$ is a real $2$ by
$2$ matrix with strictly positive entries, rank one and trace one,
$G$ is a nonzero real polynomial of degree at most $k$, and $D$ is a
real polynomial of degree at most $d$. The main actions are the original

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\tag{QC.13}
$$

There is one trajectory with $A_0=I$ and $A_{i+1}=U_iA_i$ after the
chosen action $U_i\in\{M,J\}$. Each action advances the index once and
immediately produces an exact main report, which is retained:

$$
z_i(W)=G(i+\tau)\operatorname{tr}(A_iR)+D(i+\tau),\qquad
q(W)=\bigl(R,G(\mathord\cdot+\tau),D(\mathord\cdot+\tau)\bigr).
\tag{QC.14}
$$

The ambient class $\varnothing\ne\mathscr W$ is closed under every
$T_v(R,G,D,\tau)=(R,G(\mathord\cdot+v),D(\mathord\cdot+v),\tau-v)$.
The restricted source class is exactly
$\mathscr W_K=\{W\in\mathscr W:\tau\in K\}$. There is no additional
origin/main-parameter coupling or absolute anchor. For each such world,
every error pair of (QC.2) is legal independently of its main parameters.
Side reports are passive at the actual indices $0,h$ and do not advance
the trajectory. Every policy actually acquires these two reports and
no other side information; all intermediate main reports are included.

The observer's initialization and public advice are fixed independently
of the unknown world and errors. A deterministic causal policy may use
the entire acquired main/side record to choose the next action, legal
extension, stopping and real answer. Request identities, indices,
framing and stopping fields expose only those reports and the policy's
choices, with no additional source channel. Every legal complete run
has a specified answer depending only on its acquired history. If an
infinite complete history is admitted, it supplies no extra limit read.
This is Clock §§77 and 79.8–79.9's full-history contract, with the source
and original action matrices also given in
[Self-Calibrating Relation Mathematics, Definitions 2.1 and 3.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md).
The restricted class itself is not assumed translation closed.
For an allowed policy $\Pi$, write $H_\Pi(W,\eta)$ for its complete
acquired history and $\widehat\tau_\Pi(H)$ for its specified answer. Its
full-history origin risk is

$$
\mathcal R_{\mathscr W}(\Pi)=
 \sup_{W\in\mathscr W_K}\ \sup_{\eta\in[-\varepsilon,\varepsilon]^2}
 |\widehat\tau_\Pi(H_\Pi(W,\eta))-\tau(W)|.
\tag{QC.14a}
$$

**Theorem 9.5 (translation-orbit application with full histories).**
Under Assumption 9.4 and (QC.1), every such policy whose completed real
answer range over all legal complete runs is finite has worst origin
error strictly greater than $r$. The least completed answer-range
cardinality attaining $r$ is still $\aleph_0$. When $k\ge1$ and the
source is restricted to the explicit orbit (QC.18) within the full
degree class, the same finite/countable statement holds for the
original coordinate $G(0)$.

Proof. By ambient nonemptiness and translation closure choose
$W_0=(R_0,G_0,D_0,0)\in\mathscr W$. Then for every $t\in K$ the actual
world

$$
W_t=\bigl(R_0,G_0(\mathord\cdot-t),D_0(\mathord\cdot-t),t\bigr)
     =T_{-t}W_0
\tag{QC.15}
$$

belongs to $\mathscr W_K$, has the same effective target $q(W_t)$, and
on every common action prefix has the main reading

$$
z_i(W_t)=G_0(i)\operatorname{tr}(A_iR_0)+D_0(i),
\tag{QC.16}
$$

independent of $t$. For the policy's finite answer range $A$, use the
specific $s_x,t_x,y_x$ chosen in Theorem 9.3. Give the worlds $W_{s_x}$
and $W_{t_x}$ their two opposite legal error vectors from (QC.7), so
both actually acquire the same two indexed side reports $y_x$.

Initialization and initial main readings agree, as does the side report
at index zero. If the complete acquired prefixes agree, deterministic
causality gives the same next action or simultaneous stopping. The
resulting cumulative matrices agree, (QC.16) gives the same next exact
main reading, and the side readings agree whenever index $h$ is reached.
Thus induction includes every actual intermediate output, side-dependent
control choice, extension and stopping field. All finite prefixes
coincide; any admitted infinite histories coincide as well. The common
answer is therefore in $A$ and outside $J_x$, so one legal full world
has error strictly greater than $r$. This is the original Clock 79.9
orbit induction applied to the new shrinking pairs, not a comparison
of unrelated marginal experiments.

For the upper bound, follow $M$ until index $h$, retaining each main
read and actually taking both side reports, and apply (QC.12) while
ignoring the main values for this answer. It has countable range and
risk $r$. The lower-bound pair $m-r,m+r$ can likewise be placed in the
same orbit, so the unrestricted full-history optimum remains $r$.

In the full degree class, an explicit legal zero-origin representative
for every $k,d\ge0$ is

$$
R_0=\tfrac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
G_0=1,\qquad D_0=0.
\tag{QC.17}
$$

It has positive entries, rank one, trace one and a nonzero allowed gain.
For the gain-coordinate application when $k\ge1$, instead take
$G_0(u)=u$, with the same $R_0,D_0$. Its orbit has

$$
G_t(u)=u-t,\qquad q(W_t)=(R_0,u,0),\qquad
z_i(W_t)=i\operatorname{tr}(A_iR_0),\qquad G_t(0)=-t.
\tag{QC.18}
$$

Negating an answer preserves absolute error and finite or countable
range, so Theorem 9.3 and the full-history argument apply to this
original gain coordinate on this orbit. The polynomial $u-t$ is
nonzero even if an individual read vanishes. The orbit is a member of
the full class, not necessarily of every chosen ambient subclass.
This coordinate conclusion is not recovery of the whole $G$, $D$ or
an independently meaningful spatial view. $\square$

If a separately supplied main policy recovers an effective initial-world
target $F=\bar F\circ q$ with $1\le n_\pi(W)\le N$ main reads, Clock
Proposition 79.8 supplies a same-run composition preserving its answer
and obtaining the two side reports. Its exact acquisition counts remain

$$
\bigl(\text{main actions},\text{main reads},\text{side reads}\bigr)
 =\bigl(\max(n_\pi(W)-1,h),\max(n_\pi(W),h+1),2\bigr).
\tag{QC.19}
$$

This uses the supplied legal single-action padding, with each padding
read retained. Substituting (QC.12) as the abstract origin answer changes
none of these acquisition counts, but supplies no bound on the work or
storage of that selection. There is no reset, copied specimen, erased
mandatory history or new main-policy recovery bound in this application.

**Definition 9.6 (complete finite usable boundary for this answer).**
At a fixed later use of the origin-estimation task, fix the genuinely
source-independent public operands $p$, including the declared
calibration and query. A complete finite usable boundary means a finite
set $C_p$, a retained-state map $c$ from the legal complete acquisitions
to $C_p$, and a fixed decoder $f_p:C_p\to\mathbb R$ such that the
actual later answer is $f_p(c(H))$ for every legal history $H$.
All retained or later-usable source- or report-dependent operands are
included in $c(H)$: numerical payload and retained main/side outputs,
program or advice choice, control and program counter, phase,
lengths, cut and ordinal, informative timing or schedule fields,
addresses and identities, selectors and decoder parameters, references
with every accessible source-linked backing, all source-dependent
current rights, callable services, and later inputs or source accesses
used to determine the answer. Every such later operand is inside the
claimed finite boundary; there is no additional distinguishing operand
outside this factorization. Fixed public
parameters do not vary along the adversarial source family.

This is the closed-boundary premise of Definition 2.1 for this named
scalar task. The distinction between mathematical extraction and
callable retained possession is also explicit in
[Structural Storage Atlas §§7 and 9](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md)
and [Paid View Conversion, Assumption 1.2](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md).
The latter assumes authentic acquired finite-word inputs and its own
fixed-height installation and rights; arbitrary real reports (QC.2)
do not supply those premises.

**Corollary 9.7 (conditional finite usable-state consequence).**
Under Assumption 9.4 and (QC.1), a later origin answer satisfying
Definition 9.6 cannot have worst error at most $r$.

Proof. At the fixed public operands $p$, its completed answer range
is contained in the finite set $f_p(C_p)$. Theorem 9.5 applies to the
resulting full-history decision and gives a legal source/error pair
with error strictly greater than $r$. A short pointer into an unbounded
source-linked archive does not establish the premise: its accessible
backing remains an operand in Definition 9.6. A finite program with
unbounded variable data likewise does not establish finite $C_p$.
The generally real-valued retained main history in Assumption 9.4 has
not been shown to satisfy this finite-boundary premise. $\square$

**Proposition 9.8 (end regimes, slack and the affine comparison).**
For the same balanced prior and calibrated two-report source, allow
arbitrary finite $B\ge0$ and $\varepsilon\ge0$ while keeping integer
$h\ge1$. The unrestricted risk is $\min(B,\varepsilon/h)$. If
$B=0$, one value recovers the origin exactly. If $\varepsilon\ge hB$,
including equality, one value attains the saturated optimum $B$.
If $\varepsilon=0$ and $B>0$, attaining the optimum zero requires an
uncountable completed answer range. Under (QC.1), for every
$\zeta>0$ a finite-range decision has risk at most $r+\zeta$; hence

$$
\inf_{\delta:\,|A_\delta|<\infty}\mathcal R(\delta)=r,
\quad\text{with no finite-range minimizer.}
\tag{QC.20}
$$

Thus Theorem 9.3's countable positive-noise attainment differs from
Theorem 2.2's affine obstruction even for countably many closed values.

Proof. The risk formula is Clock Proposition 79.5. For a singleton
prior the answer is its known point $m$. In the saturated case the
same constant has worst error $B$ and meets that formula; this includes
$B=\varepsilon/h$, outside the strict $B>r$ premise of Theorem 9.3.
In the noiseless case (QC.5) implies injectivity of $S_h$, since $h>0$.
Zero error therefore forces $\delta(S_h(t))=t$ for every $t\in K$;
this interval is uncountable when $B>0$. The inverse on $S_h(K)$ attains
zero with that uncountable range.

Under (QC.1), the existing midpoint rule
$\delta_*(y)=(p_y+q_y)/2$ lies in compact $K$ and has error at most $r$.
Choose a finite $\zeta$-net of $K$ and round each midpoint to a net
point at distance at most $\zeta$. The triangle inequality gives risk
at most $r+\zeta$, and the existing lower bound gives (QC.20).
This is an arbitrary-map approximation, with no effective-input claim.
The finite-center propagation result
[`QuantizedWordApproximation.quantized_word_approximation`](../../../D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.lean)
and its [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.scribe.cs)
assume a supplied quantizer and Lipschitz dynamics/readout. They do not
supply an exact-cap quantizer or a real-input encoder for this clock.

For the affine source, Theorem 2.2 forces the answer on each noiseless
branch to equal its uncountably varying center; it therefore excludes
countable closed-value ranges. Here (QC.11) forces only the single
center $m$, while every other acceptable interval has positive length.
The two sources and their source-specific conclusions remain distinct.
Neither boundedness nor positive optimal risk alone entails countable
attainment. For example, in the different scalar identity-observation
model $y=t+\eta$, $t\in[m-B,m+B]$, $|\eta|\le r<B$, each interior report
$y\in(m-B+r,m+B-r)$ has compatible endpoints $y-r,y+r$. A cap-$r$
answer must equal $y$, requiring uncountably many answers. Its
unrestricted risk is $r$ by the estimator $y$ and that same endpoint
pair. This comparison isolates the quadratic calculation rather than
a general cardinality principle. $\square$

Theorem 9.3 includes $\varepsilon=h^2/2$, since $w_x<x$ remains strict
there. It makes no unsaturated finite/countable classification for
$\varepsilon>h^2/2$, no $h=0$ claim, and no limit-uniform assertion as
$\varepsilon\downarrow0$. Changing the prior, the full closed error
relation, the side indices, initialization or available anchors requires
a new argument. Positive slack changes the target cap and is distinct
from exact attainment; no fixed-cardinality excess curve or uniform
positive finite-range penalty follows from (QC.20).

Theorems 9.3 and 9.5 constrain completed answers, while Corollary 9.7
requires its full usable-boundary premise. Productive real-report
acquisition and finite encoding, authentic callable retention with
lawful continuation, and a native alpha/beta realization are not
consequences of these statements. No independently meaningful four-view
inverse system, route agreement or dynamics compatibility is constructed.
The original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer,
unchanged-initialization and main-policy matching-bound obligations
retain their original scopes. These ordinary mathematical deductions
do not supply new Lean certification or complete the mutual-recovery
programme.

## 追加锚（本行以下为增补区）

## 10. First-report retention boundary for an uncalibrated quadratic clock

The preceding calibrated-clock section changes the clock itself. This section
keeps the uncalibrated three-index source and changes only what remains usable
after its first observed report. The nuisance gain and offset below are the
clock parameters $A,B$; they are independent of the $R,G,D$ parameters of the
main source.

**Definition 10.1 (three-index source and first-retention contract).** Fix
integers $1\le u<v$, a real $m>0$, and a nonempty compact interval
$K=[a,b]$. Put

$$
h=-\frac{u+v}{2},\qquad L=b-a,
$$

$$
\ell_-=(\min\{b,h\}-a)_+,
\qquad
\ell_+=(b-\max\{a,h\})_+,
\tag{FR.1}
$$

where $x_+=\max\{x,0\}$. For an origin $t\in K$, gain $A\ge m$, and
offset $B\in\mathbb R$, let

$$
P_t(A,B)=\bigl(A(i+t)^2+B\bigr)_{i\in\{0,u,v\}}.
\tag{FR.2}
$$

An allowed run observes

$$
y_i=A(i+t)^2+B+\eta_i,
\qquad \eta=(\eta_0,\eta_u,\eta_v)\in[-\varepsilon,\varepsilon]^3,
\tag{FR.3}
$$

with the whole closed cube allowed independently for each legal world. A
first-report map is a fixed source-independent map $e:\mathbb R\to M$. At
index $0$ it is applied to the actual observed value $y_0$; the later
consumer receives the exact real values $y_u,y_v$ as reported, including
their errors. The raw $y_0$ is not reread, archived for the consumer, or
recoverable through an unlisted backing channel. For a finite $M$, define

$$
\mathcal R_\varepsilon(e,D)=
\sup_{\substack{t\in K,\ A\ge m,\ B\in\mathbb R\\
                  \eta\in[-\varepsilon,\varepsilon]^3}}
\left|D\bigl(e(y_0),y_u,y_v\bigr)-t\right|,
\tag{FR.4}
$$

for $D:M\times\mathbb R^2\to\mathbb R$. The finite alphabet concerns only
the retained first message. The later exact real operands are not being
replaced by finite bits, and no total observer-memory bound is part of this
definition.

**Theorem 10.2 (signed finite-fiber noiseless risk, endpoint and
nonattainment cases).** In the noiseless case $\varepsilon=0$, for every
finite $M$ and every $e:\mathbb R\to M$,

$$
\inf_D\mathcal R_0(e,D)
 =\frac12\max\{\ell_-,\ell_+\}.
\tag{FR.5}
$$

If $h\notin K$ and $L>0$, the larger stratum is all of $K$ and the lower
bound is witnessed by a pair of finite legal worlds at the two endpoints
$a,b$. If $h\in K$ and $L>0$, the value in (FR.5) is a supremum of finite
collision witnesses: for every nonempty strict stratum and every
$d$ below its length there is a finite legal collision with origin distance
$d$, but no distinct collision can use the endpoint $h$ of that stratum.

Proof. First note the signed difference identity

$$
P_t(A,B)_v-P_t(A,B)_u
 =A(v-u)(u+v+2t)=2A(v-u)(t-h).
\tag{FR.6}
$$

It identifies the sign stratum from the two later reports. In the noiseless
case, output the midpoint of $K\cap(-\infty,h)$ when the difference in
(FR.6) is negative, the midpoint of $K\cap(h,\infty)$ when it is positive,
and $h$ when it is zero. Empty strata may be assigned arbitrary values.
This decoder ignores $e(y_0)$ and has error at most the right side of
(FR.5), proving the upper bound.

For the lower bound, use the following finite-fiber fact explicitly. Since
$M$ is finite and the fibers of $e$ cover $\mathbb R$, at least one fiber is
unbounded above and at least one (possibly different) fiber is unbounded
below. Thus, for either sign $\sigma\in\{-1,+1\}$ and every prescribed
finite magnitude, one can choose two finite numbers $x_s,x_t$ in one fiber
with $\sigma(x_s-x_t)>0$ and with $|x_s-x_t|$ larger than that magnitude.
This is the oriented-difference step: if every fiber were bounded above (or
below), their finite union would be bounded above (or below), contrary to
$\mathbb R$.

Choose $s<t$ in one strict stratum, set $d=t-s$, and write
$H_x=u+v+2x$. Let $\sigma=\operatorname{sgn}(H_s)=\operatorname{sgn}(H_t)$.
Choose the same-fiber values so that

$$
\Delta=x_s-x_t,\qquad
\operatorname{sgn}(\Delta)=\sigma,\qquad
\frac{|\Delta|\min\{|H_s|,|H_t|\}}{2uvd}\ge m.
\tag{FR.7}
$$

Put

$$
r=\frac{\Delta}{2uvd},\qquad
A_s=rH_t,\qquad A_t=rH_s,
\tag{FR.8}
$$

$$
B_s=x_s-A_ss^2,\qquad B_t=x_t-A_tt^2.
\tag{FR.9}
$$

The signs in (FR.7) make both gains positive, and the last inequality makes
them at least $m$; all parameters are finite. A direct expansion gives, for
$i\in\{0,u,v\}$,

$$
\begin{aligned}
&\bigl(A_s(i+s)^2+B_s\bigr)-\bigl(A_t(i+t)^2+B_t\bigr)\\
&\qquad=\Delta+r\{H_t(i^2+2is)-H_s(i^2+2it)\}
 =2rd(i-u)(i-v).
\end{aligned}
\tag{FR.10}
$$

Consequently the two later reports are exactly equal, while the first
reports are $x_s,x_t$ and therefore have the same retained message. Giving
both worlds zero sensor error is legal, so every decoder receives one common
input on two separate legal runs. Its common answer has error at least
$d/2$ for one of the origins. Letting $d$ increase to the length of either
strict stratum proves the lower bound in (FR.5).

If $h\notin K$, choose $s=a,t=b$ in (FR.7); this is a finite endpoint
witness. If $h\in K$, the preceding construction uses only $s,t$ on one
side of $h$, so it reaches but does not use $h$. Conversely, equality of the
two later noiseless reports for distinct origins implies
$A_sH_s=A_tH_t$. Positivity of the gains forces the same strict sign; if
one factor is zero, both are zero and the origins are both $h$. Thus a
distinct legal collision cannot have distance equal to a stratum length whose
endpoint is $h$. This proves the endpoint and nonattainment statements. ∎

**Theorem 10.3 (one-sided full-noise-cube plateau with finite endpoint
witnesses).** Assume $L>0$ and either $a>h$ or $b<h$. For every finite $M$ and
every $e:\mathbb R\to M$,

$$
\inf_D\mathcal R_\varepsilon(e,D)=\frac L2.
\tag{FR.11}
$$

The lower bound is witnessed by finite legal nuisance parameters at the two
prior endpoints and by zero errors, hence it is a witness inside every full
closed noise cube.

Proof. The constant midpoint $(a+b)/2$ gives the upper bound $L/2$. In the
strictly positive stratum $a>h$, use $s=a,t=b$ and choose a fiber unbounded
above, so that $\Delta>0$ in (FR.7). In the strictly negative stratum
$b<h$, use a fiber unbounded below and choose $\Delta<0$. Equations
(FR.8)--(FR.10) then give finite $A_s,A_t\ge m$ and finite $B_s,B_t$ with
identical later reports and identical first messages. Set
$\eta_s=\eta_t=0$. The two endpoint worlds are separate legal runs, and
the common decoder input forces error at least $L/2$ in one of them. This
proves (FR.11) for every $\varepsilon$, including zero. ∎

**Theorem 10.4 (arbitrary-message exactness is exactly injectivity).** Let
$K$ be nondegenerate ($a<b$), let $M$ be any set, and let
$e:\mathbb R\to M$. There is a decoder $D:M\times\mathbb R^2\to\mathbb R$
with exact noiseless recovery for every $t\in K$, $A\ge m$, and $B\in\mathbb R$
if and only if $e$ is injective.

Proof. If $e$ is not injective, choose $x\ne x'$ with $e(x)=e(x')$. A
nondegenerate $K$ contains two distinct origins $s<t$ in one strict sign
stratum. Take them close enough that the last inequality in (FR.7) holds
with $|\Delta|=|x-x'|$, and assign $x_s,x_t$ to $x,x'$ in the orientation
required by the common sign. Equations (FR.8)--(FR.10) give two distinct
origins with the same complete consumer input, contradicting exactness.

If $e$ is injective, its inverse on $e(\mathbb R)$ is a set-theoretic map.
For a noiseless input $(y_0,y_u,y_v)$, set

$$
d_u=\frac{y_u-y_0}{u},\qquad
d_v=\frac{y_v-y_0}{v},\qquad
A=\frac{d_v-d_u}{v-u},
\tag{FR.12}
$$

and return

$$
t=\frac{d_u/A-u}{2}.
\tag{FR.13}
$$

On legal noiseless data $A\ge m>0$, so the denominator is nonzero. This
gives exact recovery after replacing $y_0$ by the inverse of $e(y_0)$.
The inverse need not be computable or installed. Since no injection exists
from $\mathbb R$ into a countable set, no countable-valued first message can
give uniform exact noiseless recovery. This statement is separate from the
finite-alphabet noisy plateau in Theorem 10.3 and makes no countable plateau
claim. ∎

**Definition 10.5 (usable continuation and actual-source semantics).** A
continuation may use the declared tuple

$$
\bigl(e(y_0),y_u,y_v,\mathsf{MainArchive}\bigr),
\tag{FR.14}
$$

where the main archive contains every mandatory exact main report, its
actual action and index identities, and the legal extension and stopping
fields. The original main acquisition is side-blind: its actions are chosen
from its main history and fixed public calibration, and every reached main
report is retained and charged. Any later action, control, timing, selector,
address, decoder parameter, or source-linked reference must be a fixed
function of (FR.14) and public operands. In particular, there is no hidden
raw-$y_0$ reread, timing or schedule signal, extra side report, or callable
backing that still distinguishes the discarded first report. The $e$ in
(FR.14) acts on the actual observed $y_0$ in (FR.3), while $y_u,y_v$ remain
the exact noisy values actually reported; they are not silently replaced by
their noiseless values.

The contract constrains the operands actually accessible to the continuation;
it does not assert physical erasure. A raw $y_0$ may remain in storage that is
inaccessible to this consumer, and that existence neither enters (FR.14) nor
distinguishes two permitted inputs. If a consumer-accessible archive or
backing retains $y_0$, any source-dependent function of it, or a pointer whose
backing can be followed, that data is an operand and must be included in
(FR.14); omitting it violates the contract. A short pointer is finite only if
its accessible backing is also inside the declared boundary. It also
distinguishes a mathematical inverse from an installed recovery procedure,
exact real operands from a finite bit budget, and the source acquisition bill
from the full computation, encoding, decoding and storage cost.

**Theorem 10.6 (transport to the nonconstant linear consumer).** Fix
$C\ne0$, $B_0\in\mathbb R$, and

$$
R_0=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix},
\qquad
G_t(x)=C(x-t)+B_0,
\qquad D_t(x)=0.
\tag{FR.15}
$$

Use the same main world and original matrices as the source's Sections 7--8,
with $\tau=t$. Then every member has the same effective main target
$q=(R_0,x\mapsto Cx+B_0,0)$, because

$$
G_t(i+t)=Ci+B_0,
\qquad
z_i=(Ci+B_0)\operatorname{tr}(A_iR_0).
\tag{FR.16}
$$

For every nonempty compact set $J\subset\mathbb R$, define

$$
\mathcal B(J)=\left\{f:J\to\mathbb R:
\|f\|_{\infty,J}:=\sup_{x\in J}|f(x)|<\infty\right\}.
\tag{FR.17a}
$$

The target $G_t|_J$ belongs to $\mathcal B(J)$ by compactness. Fix the
public operands in Definition 10.5, let $\iota(t,A,B,\eta)$ be the actual
available tuple (FR.14) in the resulting legal run, and let $\mathcal I$ be
the range of these tuples. Define the corresponding origin and function
risks by

$$
\begin{aligned}
\rho^{\rm org}_\varepsilon
  &=\inf_{d:\mathcal I\to\mathbb R}
    \sup_{\substack{t\in K,\ A\ge m,\ B\in\mathbb R\\
                    \eta\in[-\varepsilon,\varepsilon]^3}}
    |d(\iota(t,A,B,\eta))-t|,\\
\rho^{\rm fun}_{\varepsilon,J}
  &=\inf_{\Gamma:\mathcal I\to\mathcal B(J)}
    \sup_{\substack{t\in K,\ A\ge m,\ B\in\mathbb R\\
                    \eta\in[-\varepsilon,\varepsilon]^3}}
    \|\Gamma(\iota(t,A,B,\eta))-G_t|_J\|_{\infty,J}.
\end{aligned}
\tag{FR.17b}
$$

When $\iota$ is restricted to $(e(y_0),y_u,y_v)$, $\rho^{\rm org}_\varepsilon$
is the infimum in (FR.4). Under Definition 10.5 and the first-report
contract, for every such $J$,

$$
\rho^{\rm fun}_{\varepsilon,J}=|C|\,\rho^{\rm org}_\varepsilon.
\tag{FR.17c}
$$

In particular, in the strictly one-sided case of Theorem 10.3, the same
endpoint collision has identical permitted tuples even when MainArchive is
included, so

$$
\rho^{\rm fun}_{\varepsilon,J}=|C|\frac{b-a}{2}.
\tag{FR.17}
$$

If the raw first report is retained instead, the supplier result in
[FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN, Section 8.2](FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN.md)
gives the original full-report guarantee $|C|R^*_{u,v}$ under its original
contract; the finite-message obstruction is therefore a change of retention
interface, not a refutation of that result.

Proof. The identity (FR.16) shows that two worlds used in
(FR.7)--(FR.10), with their separately chosen clock parameters and errors,
produce identical main histories whenever the same main actions are taken.
The original main acquisition is side-blind, so its initial actions depend
only on the common main history and public calibration. Starting from the
common initialization, induction on main-action prefixes gives the same
actions, reports and mandatory archive because (FR.16) makes every next main
report equal. The collision equations make the three side inputs equal as
well. Thus the complete tuple $\iota$ is equal when it becomes available;
Definition 10.5 then makes every later action, control field, timing field,
selector, reference and output equal. If a continuation is infinite, the
same finite-prefix induction gives the same complete history. The comparison
is between two separate legal runs; no run contains two worlds. Thus the
collision argument applies to the full actual tuple $\iota$, not only to its
three displayed side coordinates.

For the upper bound, take any origin decoder $d$ and define

$$
\Gamma_d(\iota)(x)=C\bigl(x-d(\iota)\bigr)+B_0,
\qquad x\in J.
$$

This is in $\mathcal B(J)$, and its uniform error is exactly
$|C|\,|d(\iota)-t|$. Hence
$\rho^{\rm fun}_{\varepsilon,J}\le|C|\rho^{\rm org}_\varepsilon$.
Conversely, fix any $x_0\in J$. For a function decoder $\Gamma$ define

$$
d_\Gamma(\iota)=x_0-
\frac{\Gamma(\iota)(x_0)-B_0}{C}.
$$

For every legal run,

$$
|d_\Gamma(\iota)-t|
 =\frac{|\Gamma(\iota)(x_0)-G_t(x_0)|}{|C|}
 \le\frac{\|\Gamma(\iota)-G_t|_J\|_{\infty,J}}{|C|}.
$$

Taking the supremum and then the infimum over $\Gamma$ gives the reverse
inequality and proves (FR.17c). In the one-sided case, the finite endpoint
worlds in Theorem 10.3 have zero errors and identical $\iota$, so the same
pair forces $\rho^{\rm org}_\varepsilon\ge L/2$; the constant midpoint gives
the reverse inequality. Substitution into (FR.17c) yields (FR.17).
The full-report comparison is exactly the source-specific Section 8.2
consumer, with no change to its raw-report assumptions. ∎

For a side-blind main policy using $n_\pi$ main reports, acquisition of the
three passive side reports at indices $0,u,v$ on the same trajectory has the
actual counts

$$
\bigl(\text{main actions},\text{mandatory main reports},\text{side reports}\bigr)
 =\bigl(\max(n_\pi-1,v),\max(n_\pi,v+1),3\bigr).
\tag{FR.18}
$$

For the Section 8.2 instance with $n_\pi=1$, these are $v$, $v+1$, and $3$.
This is one composed legal run: the passive side acquisition and the original
main policy share that trajectory; the two-world comparison above uses two
separate runs only to prove the lower bound.
The associated source bill is, for nonnegative unit costs,
$c_A\max(n_\pi-1,v)+c_M\max(n_\pi,v+1)+3c_S$.
Encoding, retention, decoding, output and any archive access add their own
costs; (FR.18) does not call those operations free, and a finite program does
not imply bounded total memory.

The exact source correspondence is as follows. The nuisance model (FR.2)--
(FR.3) is the three-index source at published commit
`23de8df989f92c6374b6979fe782d9ec8f27345c` in
[FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN, Sections 1--3](FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN.md), whose
full-report risk $R^*_{u,v}$ and finite-gain constructions are suppliers.
The actual main orbit, side-blind continuation and mandatory archive use
[FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II, Sections 77, 79 and 81](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md).
The source-specific delta here is the post-observation factor $e(y_0)$ and
the signed finite-fiber collision (FR.7)--(FR.10), including its exact
one-sided full-noise endpoint consequence. The elementary interpolation and
midpoint arguments are also stated in those supplier sections. The supplier
volume credits Casini--Garulli--Vicino, [*A linear programming approach to
online set membership parameter estimation for linear regression models*,
§4, equations (7)--(10)](https://control.dii.unisi.it/~casini/pdf/IJACSP_2017a.pdf),
for its strip-intersection method; that theorem is not being imported as a
proof of (FR.5) or (FR.11).
The external literature credits and model limitations recorded by the
supplier volume therefore remain in force, and no worldwide novelty claim is
made.

This appendix does not install an encoder or an effective inverse, does not
turn the uncalibrated clock parameters into the main $\alpha/\beta$ sources,
and does not provide spatial, boundary or four-view mutual recovery. The
original raw-report, fixed-$G_{\rm gc}$, original-$Q$, parked-consumer and
unchanged-initialization obligations retain their original scopes. The
full programme remains open.



## 追加锚（本行以下为增补区）

## 11. Finite-word causal acquisition on the complete uncalibrated clock

**Definition 11.1 (raw source and productive delivery contract).** In this
section CLOCK denotes
[FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN](FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN.md).
Its Definition 23.1 supplies the complete raw worlds

$$
\tau\in[-4,1],\qquad A\ge1,\qquad B\in\mathbb R,\qquad
\eta\in[-1,1]^4,\qquad y_i=A(i+\tau)^2+B+\eta_i\quad(0\le i\le3).
\tag{FW.1}
$$

The entire world, including all four errors, is fixed before execution.
There is no bound on $A$ or $B$, no rationality assumption on any parameter,
and no independence or distribution assumption. The side menu is the
original strictly increasing controlled-index menu: read at $0$, then a
chosen $u\in\{1,2\}$, then a chosen $v\in\{u+1,\ldots,3\}$, without
reset, duplication or an additional side read.

The following is an added delivery interface, not an assertion that the
original apparatus already implements a finite sensor. Fix

$$
h=2^{-8},\qquad
\mathcal P_h(x)=\{k\in\mathbb Z:|hk-x|\le h\}.
\tag{FW.2}
$$

A side request at $i$ returns one $k_i\in\mathcal P_h(y_i)$. Its complete
frame consists of a side tag, the requested index, the fixed precision tag
$8$, a canonical signed binary integer, a delimiter and completion. Zero
has one spelling; nonzero magnitudes have no leading zeroes. Framing has
no other variable field. Thus the integer part is supplied in full, with
arbitrary finite length. All legal choices in (FW.2) are admitted. An
augmented world fixes the four choices before execution, including unread ones;
none of the proofs chooses a new raw error after observing a prefix.

The interface is source independent: (FW.2) and the framing rule are the
same for every real input and every source. The observer receives no exact
real operand, extra calibration, unknown seed, source-dependent reference,
price, delay measurement or private-work output. A productive port is
assumed to finish each reached read in finite time. Installation, lawful
read binding and service are supplied resources with costs; their existence
is not derived from the existence of a real number. For example, a port
that productively supplies a rational approximation within $h/4$ can round
that rational to a nearest $h$-grid point and satisfy (FW.2), with error at
most $3h/4$. This sufficient implementation does not decide whether an
unknown real lies exactly on a rounding wall.

Local calculation and port delivery do not advance the native index or
change (FW.1). Only an issued native advance does so. No physical elapsed
time is read, and completion and scheduling carry no additional numerical
channel. These are controlled-timing assumptions of the added model.
They give no uniform bound on service latency or computation time. In
particular they are not a pause or a control right borrowed from a passive
diffusion source.

**Definition 11.2 (finite causal program).** Read at $0$ and $1$ and put
$r=hk_0$, $s=hk_1$. The actual third side index is

$$
v=\begin{cases}3,&k_1-k_0\le0,\\2,&k_1-k_0>0.\end{cases}
\qquad z=hk_v,\qquad E=1+h.
\tag{FW.3}
$$

No report at the skipped side index is requested. Choose the rational prior

$$
J_-=[-4,1/2+h]\quad(v=3),\qquad
J_+=[-3/2-h,1]\quad(v=2).
\tag{FW.4}
$$

In variables $(\lambda,t,\omega)$ form the rational polyhedron

$$
\begin{aligned}
P=\{(\lambda,t,\omega):\;&0\le\lambda\le1,\quad t\in J_\pm,\\
&|\lambda q_i-i^2-2ti-\omega|\le E\lambda
       \quad(i=0,1,v)\},\qquad(q_0,q_1,q_v)=(r,s,z).
\end{aligned}
\tag{FW.5}
$$

There are ten scalar non-strict inequalities. Enumerate the at most
$\binom{10}{3}=120$ triples of boundary hyperplanes. For each triple with
nonzero determinant solve its three equations by rational arithmetic,
and keep the solution if it satisfies all ten inequalities. Take the
smallest and largest $t$ among the retained solutions and their midpoint
$m$. If no solution is retained use $m=0$. This specifies a terminating
rational program even on unattainable integer inputs.

Round $m$ to a nearest member of

$$
\mathcal T=\{-4+j/64: j=0,\ldots,320\},
\tag{FW.6}
$$

choosing the smaller index at a tie. Output the index $j$ and discard the
side acquisition operands when they are no longer needed. The retained
origin answer is $\widehat\tau=-4+j/64$. The program has a fixed finite
instruction description; its integer and rational operands have variable
length.

**Lemma 11.3 (robust prefix and shared-error diameter).** On every lawful
run of Definition 11.2 the actual $\tau$ belongs to the $t$-projection of
$P$. This projection has diameter at most $5E/3$. The conclusion holds for
every common acquired prefix, including prefixes whose raw difference
$y_1-y_0$ has the opposite sign from $k_1-k_0$.

**Proof.** Write $e_i=hk_i-y_i$ and $\xi_i=\eta_i+e_i$. Then
$|e_i|\le h$, $|\xi_i|\le E$, and each acquired rational report is
$A(i+\tau)^2+B+\xi_i$. This enlarged cube is only a proof relaxation of
the specified finite delivery of the original cube; it is not a replacement
of (FW.1). In particular

$$
s-r=A(1+2\tau)+\xi_1-\xi_0.
\tag{FW.7}
$$

For every candidate origin and gain giving the same rational prefix with
errors in $[-E,E]$, $s-r\le0$ implies
$1+2t\le2E/A\le2E$, hence $t\le1/2+h$. If $s-r>0$, then
$1+2t>-2E/A\ge-2E$, hence $t>-3/2-h$. Thus all such candidates, not just
the actual one, lie in the selected closed prior (FW.4). The program's
integer sign test is precisely this rational prefix test.

For these rational reports the positive-denominator correspondence in
CLOCK Theorem 3.1 is

$$
\lambda=1/A,\qquad t=\tau,\qquad\omega=t^2+B/A;
\qquad A=1/\lambda,\quad B=(\omega-t^2)/\lambda.
\tag{FW.8}
$$

It identifies (FW.5) with the enlarged-noise compatible fiber on the
selected prior. Its constraints still share a single $\omega$ and hence a
single zero-index residual. Equivalently, for any fixed candidate $t,A$,
the two difference residuals and $0$ have range at most $2E$; they are not
independent errors in $[-2E,2E]$.

Apply the per-fiber diameter bound of CLOCK Theorem 3.1 with
$(m,\varepsilon,c)=(1,E,2E)$. Its five rational candidates, before taking
the maximum and the prior-width truncation, are as follows.

| Selected prior and design | $d_0$ | $d_R$ | $e_R$ | $d_L$ | $e_L$ |
| --- | --- | --- | --- | --- | --- |
| $J_-,(1,3)$ | $2E/3$ | $2E(5+2h)/(7+4h)$ | $2E(4+2h)/(6+4h)$ | $14E/(10+4h)$ | $10E/(6+4h)$ |
| $J_+,(1,2)$ | $E$ | $10E/(6+4h)$ | $8E/(5+4h)$ | $2E(2+2h)/(6+4h)$ | $2E(1+2h)/(5+4h)$ |

For $0\le h\le1/4$, divide by $E$ and bound numerators upwards and
positive denominators downwards. The first row is bounded coordinatewise
by $(2/3,11/7,3/2,7/5,5/3)$ and the second by
$(1,5/3,8/5,5/6,3/5)$. Each coordinate is at most $5/3$.
The prior-width truncation cannot increase this bound. This use of the
supplier is on an explicitly enlarged compatible set with a verified
parameter correspondence. The actual world belongs to that set by
(FW.7)--(FW.8), proving both assertions. ∎

**Theorem 11.4 (finite acquisition and bounded retained origin).** Over
all complete worlds (FW.1) and all deliveries (FW.2), Definition 11.2 uses
exactly three actual side reads and terminates after finite computation.
The retained origin field takes values in a 321-symbol alphabet, can occupy nine bits,
and satisfies the uniform bound

$$
|\widehat\tau-\tau|\le e_0:=\frac{1297}{1536}<\frac67,
\qquad \frac67-e_0=\frac{137}{10752}.
\tag{FW.9}
$$

No uniform bound on the acquisition word lengths is part of this claim.

**Proof.** The side sequence is $(0,1,3)$ or $(0,1,2)$, chosen from the
actual two-word prefix. Each reached reply is finite by the port
assumption. It remains to justify that the rational program computes the
required midpoint rather than calling an exact-real optimization oracle.

The polyhedron (FW.5) is nonempty on a lawful run by Lemma 11.3. It contains
no point with $\lambda=0$: otherwise the monic polynomial
$i^2+2ti+\omega$ vanishes at the three distinct indices $0,1,v$, which is
impossible. It is bounded, since $\lambda\in[0,1]$, $t\in J_\pm$ and the
zero-index constraint gives $|\omega|\le |r|+E$. It is closed, hence
compact. In particular its positive $\lambda$ has a positive minimum, so
the inverse in (FW.8) gives finite legal enlarged-model parameters at
every point. Its $t$-projection is a nonempty compact interval.

Both coordinate extrema occur at points with three linearly independent
active constraint normals. Here is also a justification when the
polyhedron has dimension less than three. At a $t$-maximizer, suppose the
active normals have rank less than three. Choose a nonzero vector
orthogonal to them. Small moves in both directions remain feasible,
because all other inequalities are strict. Its $t$ component must be zero,
since otherwise one direction increases $t$. Move in this direction to an
endpoint of the feasible segment, which exists by boundedness. At least
one new active normal is independent of the previous ones: it has a
nonzero inner product with the motion vector. The new point still
maximizes $t$. Repeat until the rank is three. The same argument applies
to a minimum. Consequently each extremum is among the enumerated
nonsingular three-plane intersections. Exact determinant tests,
substitution and rational comparisons decide the entire list in finite
time; a fixed lexicographic enumeration resolves irrelevant ties.

Thus on a lawful run $m$ is the true midpoint of this outer interval,
not the default. Lemma 11.3 gives $|m-\tau|\le5E/6$ and $m\in[-4,1]$.
The grid (FW.6) includes both endpoints and has spacing $1/64$, so its
rounding error is at most $1/128$. Therefore

$$
|\widehat\tau-\tau|
 \le\frac{5(257/256)}6+\frac1{128}
 =\frac{1297}{1536}.
$$

Multiplying by the positive common denominator $10752$ gives the strict
gap in (FW.9). The 321 grid indices have distinct nine-bit encodings.
This is a bound on the final origin field, not on the operands used to
obtain it. ∎

**Proposition 11.5 (transport of the fixed-triple obstruction).** Let a
fixed-triple competitor choose $(u,v)$ before observing any source data
and use only its three side frames at $0,u,v$, with delivery (FW.2). Even
an unrestricted deterministic decoder of those frames has worst-case
origin error at least $6/5$ for $(1,2)$ and at least $6/7$ for $(1,3)$ or
$(2,3)$. Hence the finite program in Theorem 11.4 strictly beats every
fixed triple under the declared finite-report relation.

**Proof.** Use the complete original-world pairs displayed in CLOCK
Theorem 23.2. Their selected raw reports are respectively identical
triples $(0,-9,-12)$, $(0,1,13)$ and $(0,-12,-13)$, and their origin
separations are respectively $12/5$, $12/7$ and $12/7$. These are finite
gain and offset worlds in the full original cube, not pairs of freely
chosen difference errors. For each common raw coordinate choose the same
integer in its nonempty set (FW.2) in both worlds; choose all unread
coordinates legally before execution as well. Equal integers give equal
complete frames, including lengths, index and completion. The deterministic
decoder therefore gives a common answer. The triangle inequality forces
at least half the origin separation as error in one of the two worlds.
This proves a lower bound for the worst case over the finite relation.
If the port instead uses a particular deterministic source-independent
encoding satisfying (FW.2), equal raw inputs still have equal encodings,
so this lower-bound argument remains valid. It does not assert that
finite-report and raw-report fixed-triple risks are equal. ∎

## 12. A same-run original-coordinate consumer with native continuation

**Definition 12.1 (main source and actual acquisition schedule).** Couple
(FW.1) to the nonconstant main family of CLOCK Proposition 8.2 with known
slope $C=1$. Independently choose $b_0\in\mathbb R$ and set

$$
R_0=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
G(x)=x-\tau+b_0,\qquad D=0.
\tag{FW.10}
$$

The shared $\tau$ is the actual original-coordinate origin. The side
gain $A$, side offset $B$ and main intercept $b_0$ have no hidden coupling.
Every clock world (FW.1) and every $b_0$ are admitted. The initial
matrix $R_0$ has strictly positive entries, rank one and trace one, and
$G$ is a nonzero degree-one polynomial. Allowing $\tau\in\mathbb R$
before imposing its prior gives the translation-closed underlying main
class required by CLOCK Section 7. The main native
atoms and raw read rule are the original ones from
[FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II, Section 77](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md):

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U_0=I,\quad U_{n+1}=E_nU_n,
\quad z_n=(n+b_0)\operatorname{tr}(U_nR_0).
\tag{FW.11}
$$

The program uses $E_n=J$ throughout; it does not replace the native menu
by a continuously chosen control. Since $JR_0=R_0$, its actual main
reports are $z_n=n+b_0$. Every native atom advances the index by one and
requires an immediate main read, with the initial main read at index zero.

Main delivery is expressly also finite: at every mandatory main read
acquire $\ell_n\in\mathcal P_h(z_n)$ in a frame with a main tag, the
requested index in binary, precision tag $8$, canonical integer, delimiter
and completion. The raw rule (FW.11) is unchanged; an exact-real main
archive is not supplied. All legal finite delivery choices are permitted,
with the same productivity, timing and no-extra-channel conditions as in
Definition 11.1. They can be fixed before the run. For a policy using other
native words, the same relation applies at each actual main read; possible
reply assignments on the native action tree specify a world of the port,
not a table accessible to the observer.

Initially take the mandatory main read and the side read at zero. Store a
separate consumer copy of $\ell_0$ and put $\widehat b=h\ell_0$, so
$|\widehat b-b_0|\le h$. Issue $J$, take the mandatory main read and side
read at one, and perform the branch test (FW.3). Issue $J$ until index
$v$ is reached, taking and retaining every intervening mandatory main
frame; take the third side read only at $v$. Now compute and retain $j$
by Definition 11.2. The main and side sources, all controls and all these
readings belong to this one actual run. Selection uses only the acquired
side words; no main report, unread side coordinate or future action is
used in that test.

The source handle and continuation rights are fixed nonnumerical binding
resources, supplied independently of the unknown parameters. Lawful $J$
advances and their mandatory main reads remain available for every finite
requested continuation. Their installation, storage and invocation are
charged; a reference is not an additional origin sensor.

**Definition 12.2 (retained service).** At readiness the origin payload is
$j$ alone. Keep its nine-bit field separate from the consumer datum
$\ell_0$, the complete main-frame/action archive, the finite controller,
the live binary native counter $n=v$, source binding and rights, and
scratch space. The acquired side words are dispensable after producing
$j$; keeping copies instead incurs separate storage.

A call supplies one of the following finite requests. Rational arguments
are given as signed integer numerators and positive integer denominators.

* `Origin` returns $\widehat\tau=-4+j/64$.
* `Value(x)` returns the rational $\widehat G(x)=x-\widehat\tau+\widehat b$
  in the original coordinate $x$.
* `Chart(t)` returns $\widehat H_n(t)=t+n+\widehat b$ in the current
  local coordinate $t$.
* `Advance` issues one actual $J$, takes and appends its mandatory main
  frame and action identity, increments $n$, and returns readiness at the
  new index. It requests no side report.

The first three calls perform finite rational arithmetic on retained
fields and their argument, without source reads, archive reads, replay or
native updates. Copies, output words and query scratch space are not part
of the nine-bit payload. Calls are serialized. No source moves during
local work; each `Advance` performs exactly its specified native move.

**Theorem 12.3 (continued use and commuting coordinates).** Under
Definitions 11.1 and 12.1 every finite sequence of the calls in Definition
12.2 terminates lawfully on the same source. On every reached index $n$
and every rational argument, its original-coordinate consumer satisfies

$$
|\widehat G(x)-G(x)|\le e_0+h=\frac{1303}{1536}<\frac67,
\qquad \frac67-\frac{1303}{1536}=\frac{95}{10752}.
\tag{FW.12}
$$

The same uniform inequality holds for the affine extensions to all real
$x$; the program itself accepts finite rational arguments. Both $G$ and
$\widehat G$ have slope one and are nonconstant.

Let the true and estimated current origins be
$\theta_n=n+\tau$ and $\widehat\theta_n=n+\widehat\tau$, and let
$H_n(t)=G(t+\theta_n)$. Then the following agreements are exact:

$$
\begin{aligned}
\theta_{n+1}&=\theta_n+1,&
\widehat\theta_{n+1}&=\widehat\theta_n+1,\\
H_n(t)&=t+n+b_0,&\widehat H_n(t)&=t+n+\widehat b,\\
H_{n+1}(t)&=H_n(t+1),&
\widehat H_{n+1}(t)&=\widehat H_n(t+1),\\
G(x)&=H_n(x-\theta_n),&
\widehat G(x)&=\widehat H_n(x-\widehat\theta_n),\\
G(t+\theta_n)&=H_n(t),&
\widehat G(t+\widehat\theta_n)&=\widehat H_n(t).
\end{aligned}
\tag{FW.13}
$$

Also $|\widehat\theta_n-\theta_n|\le e_0$ and
$|\widehat H_n(t)-H_n(t)|\le h$, uniformly over all reached $n$.

**Proof.** At readiness all stored numeric fields are finite words by
Theorem 11.4 and productivity of the finitely many main reads. Each
record-only request requires finitely many rational operations. At an
`Advance`, lawful continuing rights provide $J$ and its mandatory read;
productivity finishes that read, and incrementing a finite integer and
appending a finite frame terminate. Induction on any finite call sequence
gives the termination and same-source assertions. For an infinite stream
this means every finite prefix finishes, not that an infinite stream has
a final completion event.

The value error is
$|\tau-\widehat\tau+\widehat b-b_0|\le e_0+h$, proving (FW.12).
Formula (FW.11) and $JR_0=R_0$ hold on the actual continued path.
Substituting (FW.10) into $G(t+n+\tau)$ gives $H_n(t)=t+n+b_0$.
The other equations in (FW.13) follow by substitution, with identical
unit translations in both routes. The two remaining bounds follow from
(FW.9) and $|\widehat b-b_0|\le h$. Thus translation of the retained
origin, evaluation in the original coordinate, and the current chart
agree under actual native updates, without re-estimating or accumulating
rounding error. This does not identify future main delivery errors: the
prediction $n+\widehat b$ is within $h$ of raw $z_n$, and within $2h$ of
the delivered number $h\ell_n$. ∎

**Proposition 12.4 (fixed triples cannot obtain the consumer advantage
from main continuation).** In the common source of Definition 12.1 a
deterministic competitor with one preselected side triple, no other side
read and no extra numerical channel still has the origin lower bounds of
Proposition 11.5 even if it uses every mandatory main frame, chooses
native actions causally, makes finitely many continuing calls and stops
causally. Requests are public, with the same request stream in the paired
runs, or are chosen deterministically from the acquired history; an
external source-dependent requester is an extra channel. For an
original-coordinate value at any specified rational $x$,
or a function answer in uniform norm on any nonempty compact original
coordinate domain, its worst-case error has the same lower bound.

**Proof.** Pair each of the two clock worlds used in Proposition 11.5
with the same $b_0$ and $R_0$. For any common native word $U_n$, not only
for repetitions of $J$, the raw main value is
$(n+b_0)\operatorname{tr}(U_nR_0)$ in both worlds by (FW.11).
Choose equal legal main frames at every common action prefix, and equal
side frames at the three selected indices as in Proposition 11.5.
These choices can be fixed throughout the action tree before execution;
there is no need to resample an error after a decision. They use the full
original clock domain and the declared product with the main family.
Induction from the initial read now gives the same complete acquired
history, actions, frame lengths, counters, requests, replies and stopping
decisions in the two worlds. Backing and continuation rights are the same;
physical delay observations are excluded by the contract. Hence all
answers are equal. The origins have the supplier's separation, and the
two original functions $x-\tau+b_0$ differ everywhere by that same constant
separation. The scalar triangle inequality, or its uniform-norm version,
therefore gives half the separation in one world. This lower bound uses
no assertion that the main finite archive is exact. ∎

## 13. Independent meanings, retained sufficiency and actual resource bounds

**Definition 13.1 (four views of this common process).** The spatial
object is the original affine coordinate line with its order and distance,
the actual event positions $n+\tau$, and the nonconstant scalar field
$G$ in (FW.10). In particular the distance between positions $m+\tau$
and $n+\tau$ is $|m-n|$; the absolute origin is not silently included in
the temporal record. This is one-dimensional original-coordinate
geometry, not a claim about ambient physical space. The temporal view is the order of native actions,
read completions and calls, together with the count of native unit
advances from the initial index zero. It exposes neither $\tau$ nor the
numerical side values and is not a measurement of physical elapsed time.
The boundary view is the typed finite main and side frames at their
actual read cuts, with index identities. This boundary is an observation
interface, not an absorbing or reflecting spatial wall. The memory view
consists of the records actually retained by Definition 12.2, including
its distinct numeric fields, archive and bindings; it is not an unrestricted
copy of an unobserved history. These meanings are specified by the source,
event order and interfaces before choosing a decoding map.

**Proposition 13.2 (the recovery directions established here).** The
three actual side boundary frames acquire a finite origin payload giving
the task error (FW.9). Together with the initial main datum it supplies
the original spatial field consumer (FW.12), and together with the native
counter it supplies the current chart and position estimates (FW.13).
All routes through these retained fields commute with actual native
advances. No omitted side frame or retrospective choice of a world is
required. These are approximate task-sufficiency claims, not exact
mutual recovery of the four views.

**Proof.** Acquisition is Definition 11.2 and Theorem 11.4. Subsequent
origin calls access only $j$, and value calls access only $(j,\ell_0)$
and their argument. Current charts additionally access $n$; the main
archive supplies no hidden operand to these calls. The estimates and
agreements are those proved in Theorem 12.3 on the same continued run.
As a quantitative statement of retained equivalence, two admitted runs
with the same $j$ have a common origin answer within $e_0$ of each
origin, so their origins differ by at most $2e_0$. With the same
$(j,\ell_0)$ they have the same $\widehat G$ and their original fields
differ by at most $2(e_0+h)$ uniformly. With the same $n$ they also have
the same estimated current chart. These statements do not infer equality
of the worlds or recover their gain, offset, errors or full histories. ∎

**Proposition 13.3 (source and finite-word accounting).** Suppose
acquisition ends at $v\in\{2,3\}$, followed by $N$ `Advance` calls and
$Q$ record-only calls. The actual source counts are

$$
\begin{aligned}
\text{native main atoms}&=v+N,\\
\text{mandatory main reads}&=v+N+1,\\
\text{side reads}&=3,\\
\text{source reads for the }Q\text{ record-only calls}&=0.
\end{aligned}
\tag{FW.14}
$$

For nonnegative unit source costs the source bill is
$c_A(v+N)+c_M(v+N+1)+3c_S$. It is only the source component of the bill.
The numeric origin field has nine bits. Acquisition words, the main
consumer datum, archive, source handle and continuing rights, controller,
live counter, incoming query, rational scratch, output, port installation,
framing and service must be accounted separately.

For a bit-cost bound excluding physical port service, let $L$ be the
complete acquisition-frame length, including all three side integers and
all main frames through $v$. One may implement the numerical acquisition
with $O(L+1)$-bit operands and numerical scratch, and $O((L+1)^2)$ bit
work using elementary integer arithmetic. These are per-run bounds with
absolute constants for this fixed program. For a record-only call whose
rational argument has length $B_x$, numerical workspace beyond the
already stored archive, controller and counter is at most

$$
O(B_x+|\ell_0|+\log(n+2)+1),
\tag{FW.15}
$$

and the square of that quantity suffices for numerical bit work. Here
$|\ell_0|$ denotes its binary word length. An `Advance` additionally pays
for its new main frame, archive append, binding invocation and service.

**Proof.** Acquisition issues $v$ actual atoms and reads at every index
$0,\ldots,v$, with side reads only at $0,1,v$. Each `Advance` adds one
atom and one mandatory main read. None of the other calls touches the
source. This proves (FW.14), including the branch with an unobserved side
index but an observed mandatory main index.

All coefficients in (FW.5) are rational functions of fixed small
integers and the three acquired integers. Each has bit length $O(L+1)$.
There are at most 120 systems of dimension three. Determinant expressions
have a fixed number of products and sums, so their numerators and
denominators have $O(L+1)$ bits. Feasibility, running extrema and comparison
against the 321 grid points require only a fixed number of such
operations. Rational pairs need not be reduced: positivity of denominators
and cross multiplication suffice for comparisons. Elementary multiplication
and division on these operands give the stated quadratic work bound;
streaming the candidate list with running extrema gives the scratch bound.
The finite input words and retained archive themselves have their own
$L$-bit storage bill. The call formulas use a fixed number of rational
operations on their argument, fixed-grid $\widehat\tau$, $h\ell_0$ and,
for `Chart`, $n$. Their operand lengths give (FW.15). Writing outputs and
reading input frames are included in the respective per-run word costs.

After continuation to index $n$, let $T_n$ be the sum of all retained
main-frame, action-identity and archive-framing lengths. Ready internal
storage is this $T_n$, the nine-bit origin field, the separate
$|\ell_0|$-bit consumer copy, the $O(\log(n+2))$-bit counter and the
fixed finite controller and binding fields. During a call, its input,
scratch and output are additional storage. Any implementation backing
the supplied port or continuation rights has separate storage and service
cost; neither its size nor latency is bounded by these internal numerical
bounds. None of these charges is assigned to the origin field. Unbounded $B$ makes the raw initial side
value $A\tau^2+B+\eta_0$ unbounded, so the full integer frames in (FW.2)
have no uniform length bound; sequentially reading them likewise has no
uniform time bound. Unbounded $b_0$ makes the separate main datum
unbounded. More generally a wholly finite-state retained service with no
backing or source access could not approximate
$G(0)=b_0-\tau$ with any fixed finite uniform error over all $b_0$:
finitely many states give finitely many answers at zero, whose bounded
union of fixed-radius intervals cannot cover the real line. Thus the
nine-bit claim cannot be promoted to a bound on all callable storage.
All actual finite prefixes still have finite frames, archive, counter
and workspace by productivity and finite arithmetic. ∎

**Definition 13.4 (parsimony relative to the stated task).** The source
uses the original native menu and a single actual initialization. The
program's action alphabet is the singleton $\{J\}$ within that menu;
one finite sign test selects between the legal third side positions.
Some nonfixed selection is indispensable to strict improvement over all
fixed triples under this contract, by Proposition 11.5. Three reports,
the particular grid, nine origin bits and the vertex enumeration are not
claimed minimal. The retained origin payload replaces the large side
acquisition words for subsequent origin use; the separate unbounded main
datum is needed for the unbounded-intercept consumer, and the archive and
counter remain actual resources. This is a task-relative compression and
acquisition result, not a physical optimum or a universal generator theorem.

## 14. Source correspondence, uncovered join and remaining scope

**Definition 14.1 (supplier correspondence and mathematical delta).**
CLOCK Definition 23.1 and Theorem 23.2 supply (FW.1), the published ideal
causal advantage $5/6<6/7$ and the fixed-triple world pairs. CLOCK Theorem
3.1 supplies the five-formula diameter law and positive-denominator fiber
geometry; its Proposition 8.2 and Section 7 supply the nonconstant main
family and the same-orbit lower-bound method. The identification is
$\alpha=A$, $\beta=B$, $m=1$, original $\varepsilon=1$, prior $[-4,1]$
and original horizon $3$. Only the outer proof calculation uses
$\varepsilon=E$; the observed world still has error cube $[-1,1]^4$.
The main family's intercept is $b_0$, not the clock offset $B$.

Sections 5--8 of this volume supply productive rational-reply,
quantization and retained-use distinctions. Section 9 treats a different
calibrated bounded clock and arbitrary-map exact-cap answers; Section 10
compresses a first real report before later exact-real operands and proves
its sharp retention boundary. Neither is an implementation of (FW.3):
here the first finite word can have arbitrary length, remains available
through acquisition, and is compressed into a bounded field only after
all three finite reports. No Section 10 saturation statement is changed.

The new source-specific join is the robust same-prefix enlargement
(FW.4)--(FW.7), its finite rational endpoint computation, the nine-bit
retention bound strictly below $6/7$, the explicit finite-report transport
of the original fixed-triple obstruction, and the actual common-run
consumer and continuation (FW.10)--(FW.15). The exact-report causal
advantage, generic interpolation, scalar midpoint rule, linear programming,
rational arithmetic and finite-grid quantization are suppliers, not new
results claimed here. In particular an infimum/supremum definition alone
would not supply this program or its finite operands.

The relevant later published supplements have different conclusions.
[FIB_UNCALIBRATED_QUADRATIC_CLOCK_UNIFORM_REPORT_DESIGNS, Sections 24--25](FIB_UNCALIBRATED_QUADRATIC_CLOCK_UNIFORM_REPORT_DESIGNS.md)
classifies report sets fixed before values, including the six-position
menu $\{0,1,2,8,9,10\}$ and minimal subsets for uniform target widths;
it does not provide this three-read finite causal acquisition/retention
join. The distinct stochastic source in
[FIB_NATIVE_UNIFORM_JOINT_NOISE_TOLERANCE_RESOURCE_CROSSOVER, Sections 1, 5--8](FIB_NATIVE_UNIFORM_JOINT_NOISE_TOLERANCE_RESOURCE_CROSSOVER.md)
uses native paths, noise tubes and a stopped-history resource comparison.
Its domain, stopping and continuation are not (FW.1) or (FW.11).
[FINITE_START_PREDICTIVE_MEMORY, Sections 13--18](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_START_PREDICTIVE_MEMORY.md)
uses a killed three-axis diffusion, for which observation time continues
to consume lifetime. No control, pause, productive port or cost exponent
is transported from either source to this construction.

The fixed-source acquisition and installation distinctions of
[NATIVE_PAID_VIEW_CONVERSION](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md),
the acquired backing and continuing-call distinctions of
[NATIVE_CALLABLE_STORAGE_ATLAS](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md),
and the acquired tapes of
[NATIVE_CLOCKED_RECOVERY_AND_ORDER](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md)
remain suppliers for how to state the missing operational obligations.
They do not install the port (FW.2) on this clock. The actual-complex
channel bound in
[AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY, Section 18](AURIC_OMEGA_PHASE_GAIN_AND_QUTRIT_RECOVERY.md)
is not identified with this polynomial main/clock product.

**Definition 14.2 (literature and formal-library boundaries).** The
bounded-error strip-intersection framework is literature-attested in
M. Casini, A. Garulli and A. Vicino,
[*A linear programming approach to online set membership parameter
estimation for linear regression models*, Sections 2--5, especially
Section 4, equations (7)--(10)](https://control.dii.unisi.it/~casini/pdf/IJACSP_2017a.pdf),
DOI [10.1002/acs.2701](https://doi.org/10.1002/acs.2701).
The regression vector here is $(i^2,i,1)$ and its unknown coefficient
vector is $(A,2A\tau,A\tau^2+B)$. The desired origin is a ratio, not a
coordinate of that vector. The positive-denominator conversion (FW.8)
is the supplier's exact joint construction. No coordinate outer box or
recursive outer approximation from the paper is substituted for it.

D. Krieg, E. Novak and M. Ullrich,
[*On the power of adaption and randomization*, Sections 1--2 and 4](https://doi.org/10.1017/fms.2025.10101),
provides context for adaptive information, not the constant in (FW.9).
As CLOCK Section 23 explains, including the fixed four noise coordinates
makes each raw report linear in the enlarged coefficient/noise input,
but the target remains the nonlinear ratio $q_1/(2q_2)$ on a nonsymmetric
input class. The strictly increasing index menu also is not an arbitrary
linear information class. No general no-adaptation theorem is being
violated or applied without its hypotheses.

The repository's
[D5 QuantizedWordApproximation](../../../D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.lean)
and its
[owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.scribe.cs)
supply finite quantized words and error propagation on their stated
systems, not acquisition of this sensor. The retained clock origin here
is not repeatedly quantized under an update: the counter supplies an
exact integer translation. The different productive grammar of
[RationalResponseRefinement](../../../D5/S0/Computability/RationalResponseRefinement.lean)
and its
[owning Scribe](../../../Blueprint/D5/S0/Computability/RationalResponseRefinement.scribe.cs)
is likewise not an installed clock port. The pinned mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`,
[Mathlib/Analysis/Convex/Extreme.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Convex/Extreme.lean),
contains general extreme-point infrastructure. The elementary finite
rank argument in Theorem 11.4 supplies the specific degeneracy-safe
algorithm here. These comparisons and ordinary proofs assert neither a
new compiled Lean theorem nor global mathematical originality.

**Definition 14.3 (remaining model and programme obligations).** The
productive finite port, controlled timing, source binding and continuing
rights are explicit supplied premises. This mathematics does not construct
an original-apparatus sensor, calibrate unknown gain or offset exactly,
provide a uniform acquisition bit/time bound, or prove physical optimality.
It gives approximate recovery and genuine subsequent original-coordinate
use in the named common source. It does not identify that source with the
original affine instrument of Section 1, with an alpha/beta-generated
universal apparatus, with fixed-$G_{\rm gc}$ or original-$Q$ tasks, or
with parked-consumer and unchanged-initialization models elsewhere.
All such original-model settlements retain their original statements.
The independently meaningful views of Definition 13.1 have only the
proved directions of Proposition 13.2; temporal order alone does not
supply the numerical boundary words, and memory does not recover a whole
spatial world or exact raw noise. Exact four-view mutual recovery and the
full parsimonious relational-process objective remain unresolved.

## 追加锚（本行以下为增补区）

## 15. Finite complete states at every acquisition handoff

**Definition 15.1 (cuts, public operands and complete usable state).**
Keep the entire source (FW.1), the finite delivery relation (FW.2),
$h=2^{-8}$, and the three-read menu $0,u,v$ of Definition 11.1.
A side-frame handoff is the cut after the complete frame has been
processed and before the next source request. A deterministic
frame-synchronous receiver has one fixed finite nonempty carrier $Q$
for its complete usable state at each such cut. The stage, current
index, selected next index and finite controller may be included in
$Q$; adjoining these finite fields does not change the condition.
Between cuts a whole finite word may be processed with arbitrary
terminating local work. This is a cut condition, not a bound on all
intermediate parser configurations or on incoming frame lengths.

Fix the public operands and receiver before choosing a world.
Public query arguments, calibration, code and advice are the same in
compared runs and supply no unknown source parameter. Completeness
means that everything from the processed prefix which can influence a
later permitted request or answer factors through the cut state and
these fixed operands. It includes accessible records, controller and
program position, saved lengths and counters, address values and
accessible backing, pending commands, informative timing or schedules,
and source writes usable as memory. An emitted word that a later
consumer can consult is an accessible record. A fixed handle binds the
actual source and its rights; it is not permission to inspect the
source's hidden parameters or to reread a discarded report. Immutable
hidden source parameters are not receiver registers: their subsequent
influence is only through the declared source interface. A short
reference to unbounded accessible backing does not satisfy the finite
condition. Discarded bytes may physically exist, but cannot remain an
operand outside $Q$. The final origin answer is a function of the last
cut state and fixed public operands.

The next side index is chosen lawfully and may depend on the current
state. There is no restriction to a preselected triple. All four errors
and all delivery choices are fixed before the run; the worst case ranges
over this full relation. The receiver must finish on every lawful run.
For a receiver $\mathcal R$ write

$$
\operatorname{err}(\mathcal R)
 =\sup_{\substack{\tau\in[-4,1],\ A\ge1,\ B\in\mathbb R\\
                   \eta\in[-1,1]^4,\ \text{legal deliveries}}}
       |\widehat\tau_{\mathcal R}-\tau|.
\tag{AC.1}
$$

The finite carrier is fixed over this supremum; its size is otherwise
arbitrary. These conditions exclude using the source, a requester,
physical frame delay or an external archive as uncounted memory.
They do not remove a channel from a receiver that actually has it:
that receiver must count it and may fail the finite-carrier premise.

**Theorem 15.2 (exact all-handoff origin minimax).** In Definition 15.1,

$$
\inf_{\substack{\mathcal R\text{ deterministic, lawful}\\
                \text{one fixed finite complete carrier}}}
       \operatorname{err}(\mathcal R)=\frac52.
\tag{AC.2}
$$

Every receiver in this class has worst-case error at least $5/2$
already with $\eta=0$, integer $A\ge1$ and integer $B$, and exact
integer-valued raw reports delivered by $k_i=256y_i$. The infimum is
attained by a constant-answer receiver. The statement does not say that
every receiver attains the infimum.

**Proof.** Use the following classical consequence of Hales--Jewett:
for a finite coloring $C:\mathbb Z\to F$ and a nonempty finite
$S\subset\mathbb Z$, there are integers $a>0$, $b$ such that
$C(b+as)$ is constant on $S$. To obtain this consequence, use $S$ as
the finite word alphabet and color a word by the color of the sum of
its letters. A monochromatic combinatorial line has a nonempty set of
variable positions. If their number is $a$ and the sum of its fixed
letters is $b$, its sums are exactly $b+aS$. The supplier and its
precise library statement are given in Definition 18.1. There is no
regularity condition on the coloring.

For an integer $x$, let $\Phi_i(x)$ be the complete canonical side
frame at index $i$ with integer payload $256x$. It is a lawful delivery
of the raw value $x$. With public operands fixed, processing this frame
from a state $q$ at a stage $j$ induces a macro transition
$T_{j,i}(q,x)$ to the next cut state. Include all stage/index/control
fields in that state. On off-path combinations on which no such
transition finishes, use one extra symbol $\bot$. There are finitely
many $q,j,i$, and each outcome is in the finite set $Q\cup\{\bot\}$.
Consequently

$$
C(x)=\bigl(T_{j,i}(q,x)\bigr)_{q,j,i}
\tag{AC.3}
$$

is a finite coloring of $\mathbb Z$. It is a coloring by transition
outcomes, not by raw frames: different integers can have different
frame bytes, lengths and local processing while inducing the same
complete usable outcomes.

Apply the supplier to $S=\{0,1,4,9,16\}$. Obtain integer $a\ge1$
and $b$ for which all $b+as$ have the same color. Consider the two
complete worlds

$$
(\tau_-,A_-,B_-,\eta_-)=(-4,a,b,0),\qquad
(\tau_+,A_+,B_+,\eta_+)=(1,a,b,0).
\tag{AC.4}
$$

Their four raw vectors are respectively

$$
b+a(16,9,4,1),\qquad b+a(1,4,9,16).
\tag{AC.5}
$$

Every coordinate therefore has the common color. Deliver every
coordinate exactly as $256$ times its raw integer, including the unread
coordinates. The initial states agree. Equal colors give equal states
after the first frame, hence the same chosen $u$. They then give equal
states after the second frame, hence the same chosen $v$, and equal
states after the third frame. All these transitions terminate because
the worlds and deliveries are lawful. The final answers are equal,
although the discarded raw histories need not be equal. Since
$|\tau_+-\tau_-|=5$, the scalar triangle inequality forces error at
least $5/2$ in one world. No range argument about an unbounded offset
or about answer word lengths has been used.

For the reverse inequality choose the legal indices $0,1,2$, ignore
the numeric data and always answer $-3/2$. Its error on $[-4,1]$ is
at most $5/2$. A finite controller can pass over each productive frame
until its delimiter and completion, retaining only its stage, so this
is a receiver of the declared kind. It proves attainment. $\square$

The lower bound also allows a terminal scalar answer to be written
while processing the last frame, without retaining that answer in $Q$.
Adjoin to (AC.3), for every possible pre-final state and index, the
one-bit class specifying whether this terminal answer is less than
$-3/2$. Use a default class off path. The coloring is still finite,
and the same construction gives equal answer classes in the endpoint
worlds. In the class below $-3/2$ the $\tau=1$ world has error greater
than $5/2$; in the other class the $\tau=-4$ world has error at least
$5/2$. This variant prevents a final streaming-output convention from
supplying an exception. A word saved for subsequent use is still memory
under Definition 15.1.

## 16. Compressing only the first handoff

**Definition 16.1 (first-state risk with unrestricted later records).**
For the noiseless experiment set $\eta=0$ in (FW.1). At the first
handoff retain only $q=e(y_0)$, where $e:\mathbb R\to Q$ is any
fixed map into a finite nonempty carrier. All the completeness and
public-operand conditions of Definition 15.1 apply at this first cut.
Thereafter allow exact real reports and unrestricted retention and
local computation. A continuation chooses

$$
u=f(q)\in\{1,2\},\qquad
v=g(q,u,y_u)\in\{u+1,\ldots,3\},\qquad
\widehat\tau=D(q,u,v,y_u,y_v).
\tag{AC.6}
$$

The functions are deterministic and total on legal inputs. Define

$$
R_0(e)=\inf_{f,g,D}
 \sup_{\tau\in[-4,1],\ A\ge1,\ B\in\mathbb R}
       |D(e(y_0),u,v,y_u,y_v)-\tau|.
\tag{AC.7}
$$

Thus the continuation is optimized for the supplied map $e$; this is
not a statement that every fixed continuation has optimal risk. A
controller's first-report-dependent choice of next index is itself
usable first-state information and must be included when describing
its actual map. A contract that independently forces a particular
second index is an additional restriction on (AC.7).

**Theorem 16.2 (sharp noiseless first-cut risk, including adaptive
indices).** For every map $e$ of Definition 16.1,

$$
R_0(e)=\frac54.
\tag{AC.8}
$$

The lower bound permits both later indices to be chosen as in (AC.6).
It holds without a measurability, effectiveness or geometry assumption
on the finite fibers of $e$.

**Proof.** The upper bound ignores $q$ and takes $u=1$, $v=2$.
The noiseless difference is

$$
y_2-y_1=A(3+2\tau).
\tag{AC.9}
$$

If this difference is negative, answer $-11/4$; if positive, answer
$-1/4$; if zero, answer $-3/2$. Positive $A$ makes these the midpoints
of the respective prior strata $[-4,-3/2)$ and $(-3/2,1]$, with exact
recovery at the separating point. The error is at most $5/4$.

For the lower bound fix a rational $s$ with $-3/2<s<1$, and put $t=1$.
Let $\mathcal P=\{(1,2),(1,3),(2,3)\}$. For every $(u,v)\in\mathcal P$
put

$$
\begin{aligned}
H_s^{uv}&=u+v+2s>0,& H_t^{uv}&=u+v+2t>0,\\
a_{uv}&=-H_t^{uv}u(u+2s),&
b_{uv}&=-H_s^{uv}u(u+2t).
\end{aligned}
\tag{AC.10}
$$

All these numbers are rational. Choose a positive integer $L$ which
clears their denominators and those of
$H_t^{uv}s^2,H_s^{uv}t^2,H_t^{uv},H_s^{uv},2sH_t^{uv},2tH_s^{uv}$,
and is large enough that $LH_s^{uv},LH_t^{uv}\ge1$ for every pair.
This is possible because there are only three pairs and all six
$H$'s are positive. In particular

$$
S=\{La_{uv},Lb_{uv}:(u,v)\in\mathcal P\}\subset\mathbb Z
\tag{AC.11}
$$

is finite and nonempty. Color an integer $x$ by $e(x)$. The classical
supplier used in Theorem 15.2 gives integers $d>0,c$ such that all
$c+dS$ have one color $q_*$. Put $r=Ld$. For each pair construct two
candidate worlds with first reports

$$
x_s^{uv}=c+ra_{uv},\qquad x_t^{uv}=c+rb_{uv},
\tag{AC.12}
$$

and parameters

$$
\begin{aligned}
A_s^{uv}&=rH_t^{uv},&
B_s^{uv}&=x_s^{uv}-A_s^{uv}s^2,\\
A_t^{uv}&=rH_s^{uv},&
B_t^{uv}&=x_t^{uv}-A_t^{uv}t^2.
\end{aligned}
\tag{AC.13}
$$

These are finite legal parameters, with gains at least one. Both gains
and offsets are integers by the choice of $L$. Write
$p_s^{uv}(i)=A_s^{uv}(i+s)^2+B_s^{uv}$ and similarly for $t$.
Direct expansion gives

$$
\begin{aligned}
p_s^{uv}(u)&=p_t^{uv}(u)=c,\\
p_s^{uv}(i)-p_t^{uv}(i)&=2r(t-s)(i-u)(i-v).
\end{aligned}
\tag{AC.14}
$$

Indeed the quadratic coefficient of the difference is
$r(H_t^{uv}-H_s^{uv})=2r(t-s)$, its linear coefficient is
$2r(H_t^{uv}s-H_s^{uv}t)=-2r(u+v)(t-s)$, and its constant
coefficient is $r(a_{uv}-b_{uv})=2ruv(t-s)$. Substitution at $u$
using $a_{uv},b_{uv}$ gives the first line; the second gives equality
at $v$. All four reports in both worlds are integers: their polynomial
coefficients are respectively $x_s^{uv},A_s^{uv},2sA_s^{uv}$ and
$x_t^{uv},A_t^{uv},2tA_t^{uv}$, all integers by the choice of $L$.
This last fact is not needed for the exact-real argument, but makes
the finite-delivery embedding exact.

The same $q_*$ is obtained from every first report in (AC.12), for
all three pairs simultaneously. The actual continuation therefore
chooses $u_*=f(q_*)$. In each candidate with this second index the
second report is the same number $c$. It consequently chooses
$v_*=g(q_*,u_*,c)$. Select the pair $(u_*,v_*)$ from the constructed
collection. Its two worlds have the same available first state, the
same second exact report, the same final exact report, and the same
selected indices. Their answers coincide and one has error at least
$(t-s)/2$. This selection is a choice of two complete worlds before
running the receiver, not a change of a world after a decision. Every
candidate had all four reports fixed.

Let rational $s$ decrease to $-3/2$. The separations $t-s$ tend to
$5/2$, so the supremum error of any continuation is at least $5/4$.
No collision at $s=-3/2$ is asserted: the positive gains are finite at
every chosen $s$, with no uniform upper bound. Taking the infimum over
continuations and combining with (AC.9) proves (AC.8). $\square$

**Corollary 16.3 (first-cut lower bound in the original noisy finite
contract).** Keep the full four-error cube and finite port of Definition
11.1. Suppose only the first side-frame handoff has a fixed finite
complete usable carrier; later acquired frames, records and computation
are unrestricted, and both later indices may be adaptive. Every such
deterministic receiver has worst-case origin error at least $5/4$.
This is a lower bound for that original contract, not a claimed exact
noisy risk or a noisy upper bound.

**Proof.** Fix the receiver and color an integer $x$ by its complete
first cut state on the exact frame $\Phi_0(x)$ with payload $256x$.
Use (AC.10)--(AC.14) with this finite coloring. The first states again
have one common value $q_*$ across all three candidate pairs. All
candidate raw reports are integers, so fix the four deliveries in each
world as $k_i=256p(i)$ and all four errors as zero. They are members of
the original relation, whose worst case also admits nonzero errors
and nonexact deliveries. The second frame has the same index $u$ and
payload $256c$ in every candidate with that second index. Thus the
actual $u$ and $v$ select one constructed pair as in Theorem 16.2.
Its two final frames coincide as well. Their complete usable inputs
from the first cut onward agree, and their origin separation is $t-s$.
The limiting half-separation bound is $5/4$. All unread errors and
deliveries have been fixed in these worlds before execution. Allowing
later exact real values in addition could not distinguish these paired
later reports either. $\square$

In particular (AC.9) supplies no noisy upper bound: in the noisy
experiment its right side has the additional term $\eta_2-\eta_1$,
and finite delivery introduces another difference error. The sign
partition for the upper bound was a noiseless argument.

## 17. The actual original-coordinate consumer after a memory cut

**Definition 17.1 (same-source composition and accessible channels).**
Use the product source, native atoms, immediate main reads and finite
main port of Definition 12.1, with the same shared $\tau$, independent
side $A,B$, and independent main intercept $b_0$. Acquisition takes
place on the one actual native trajectory through the three side
indices $0,u,v$. It has at most three native advances, with every
mandatory intervening main read included. Side-frame cuts are the
frame-synchronous cuts of Definition 15.1; there is no extra side read
or reset. Native action choices may depend causally on the permitted
acquired information. After readiness allow any permitted finite
continuation by native atoms and their mandatory main reads, as well
as local calls and causal stopping. The service in Definition 12.2
uses $J$; allowing the whole native menu $\{M,J\}$ strengthens the
negative conclusion below. Requests have a common fixed public stream,
or are chosen deterministically from accessible data. A requester
whose private knowledge distinguishes the worlds supplies an extra
operand.

For an all-handoff finite receiver, its alleged finite carrier must
include the whole receiver/consumer state usable across each cut,
including any accessible main archive and source writes. For a
first-cut finite receiver this requirement applies at the first cut;
all later main and side records may be retained without a finite
bound. The source handle, rights and main initialization are the same
in the compared runs. A handle cannot inspect the side parameters or
call back a discarded side value. Informative physical timing,
source-dependent advice, copies, backing and mutable external records
are channels under Definition 15.1. No resource is made free by calling
only the origin register finite.

**Theorem 17.2 (transport through lawful main continuation).** For the
actual original-coordinate target $G_\tau(x)=x-\tau+b_0$ in (FW.10),
the following lower bounds hold in Definition 17.1, even on the
subfamily $b_0=0$:

* Complete finite states at every side-frame cut force worst-case
  error at least $5/2$ for an original-coordinate value at any fixed
  rational $x$.
* A finite complete first cut, with arbitrary later storage, forces
  worst-case error at least $5/4$ for that value. This holds for
  noiseless exact reports as well as as a lower bound in the full noisy
  finite-delivery contract.

Both bounds also hold for a function answer in uniform norm on any
nonempty compact original-coordinate set. They survive all the stated
later main continuations and causal stopping. They are not lower
bounds for the origin-independent local chart $H_n(t)=t+n+b_0$.

**Proof.** Restrict the independently available main parameter to
$b_0=0$. For every native word $U_n$, (FW.11) gives

$$
z_n=n\operatorname{tr}(U_nR_0),
\tag{AC.15}
$$

which is independent of $\tau,A,B,\eta$. All entries of $U_n$ are
integers. Since $R_0$ has entries $1/2$, $z_n$ is a half-integer and
$256z_n$ is an integer. Fix, on the entire native action tree, the
exact legal main delivery $\ell_n=256z_n$. This defines replies before
any receiver decisions and gives a common main backend for the paired
runs. In particular the initial main frame is the common zero frame.
No exact-real main archive has been added to the finite contract.

For the all-handoff case, the native action word during acquisition
has length at most three. There are only finitely many such words,
and each determines all its indices, exact main frames and archive.
Adjoin this actual finite word to the receiver's alleged finite state
when forming (AC.3). This is a finite augmentation, not omission of
the live main source state. It includes any choice of $M$ rather than
$J$ used as a source write. Processing a side frame and consequent
lawful acquisition moves has a well-defined macro outcome in this
augmented finite carrier: main replies along those moves are fixed
by (AC.15). Equal colors give equal augmented handoffs, including the
actual native prefix, regardless of whether local processing used the
side bytes to select that prefix. Applying (AC.4)--(AC.5) yields the
endpoint origins and the same complete usable readiness state with
the same actual main prefix. Discarded side frames can differ; this
argument does not assert equality of those erased histories.

For the first-cut case, the initial main state and frame are fixed.
Absorb their processing and all first-report-dependent finite control
in the finite first-state map. After that cut, along each hypothetical
second report $c$, the deterministic main actions and main replies
before the final side read are determined by this state and the fixed
backend (AC.15). Thus the effective second-index and final-index
choices are functions $f(q)$ and $g(q,u,c)$ as in (AC.6), even if the
implementation intersperses main actions and saves their entire
archive. Apply (AC.10)--(AC.14), or the finite-word version in
Corollary 16.3. Choosing the actual pair leaves identical accessible
data and the same actual native prefix at readiness in the two worlds,
with origin separation $t-s$.

In either case start a later continuation from the paired readiness
states. Identical accessible data and public requests give the same
next local output, native action or stopping decision. A common native
action gives the same updated $U_n$ and index; (AC.15) supplies the
same mandatory main frame. Local arithmetic changes no source.
Induction gives identical subsequent accessible records, requests,
outputs and stopping decisions at every finite continuation prefix.
It covers arbitrary finite lengths and, prefixwise, an infinite
continuation; an answer promised after finite work must occur at a
finite prefix. No answer after an infinite execution is presumed.
The underlying clock worlds remain different but no fourth side read,
parameter inspection or raw-first-report callback is available.

For any fixed $x$, their original values obey

$$
|G_s(x)-G_t(x)|=|t-s|.
\tag{AC.16}
$$

A common scalar answer has error at least half this separation in one
world. The endpoint construction gives $5/2$; letting $s$ decrease to
$-3/2$ in the first-cut construction gives $5/4$. For function answers
on a nonempty compact set, the two true functions have uniform
distance $|t-s|$. The same triangle inequality gives the identical
lower bounds; bounded-error candidate functions suffice, and an
unbounded error already satisfies the conclusion. This argument uses
a fixed bounded subfamily of target values at each $x$, since $b_0=0$
and $\tau\in[-4,1]$. It uses no unbounded-intercept obstruction.

If the all-handoff receiver writes its terminal scalar answer while
processing the last side frame, the final one-bit coloring variant of
Theorem 15.2 applies, using the threshold $x+3/2$ for $G_\tau(x)$
and the endpoint values $x+4$ and $x-1$. Later main computations with
the fixed backend can be included in that terminal-answer function.
For a function output use its value at one fixed point of the nonempty
domain. If an output is saved for a later consumer, it is an accessible
record subject to the cut condition. Finally the actual local chart
is $t+n+b_0$ by (FW.13); it loses the origin even before compression,
so (AC.16) pertains specifically to the original-coordinate task.
$\square$

**Corollary 17.3 (bounded final field and necessary earlier capacity).**
The finite origin payload of Theorem 11.4 and service of Theorem 12.3
coexist with Theorems 15.2 and 17.2. Under the unchanged complete-state
and no-extra-channel conditions, any uniformly correct origin scheme
of error strictly less than $5/4$ must have infinitely many possible
complete usable states at its first side handoff. In particular the
bound $e_0=1297/1536$ cannot be acquired with a fixed finite complete
first state, even if every later acquisition operand has unrestricted
memory. It also cannot be acquired with fixed finite complete states
at all handoffs. A finite alphabet only for the final origin field
imposes neither restriction.

**Proof.** A finite complete first state would satisfy Corollary 16.3,
contradicting the strict bound below $5/4$. The all-handoff assertion
also follows from Theorem 15.2. In the positive construction the first
acquired integer and later rational operands remain usable during
acquisition. Only after three reports and the rational endpoint
calculation are they replaced, for the origin service, by one of 321
values. Its archive, consumer datum, controller, counter, binding,
query and scratch remain distinct charged resources as in Definitions
12.1--12.2 and Proposition 13.3. Its first complete state is not
alleged to lie in a fixed finite carrier; the bounded final field is
consistent with both lower bounds. $\square$

## 18. Mathematical correspondence and resource boundaries for the cuts

**Definition 18.1 (classical supplier and source-specific delta).** The
finite homothetic-copy result used inside the proofs is a classical
consequence of Hales--Jewett. William Gasarch,
[*A Color Focusing Proof of the Hales-Jewett Theorem*, Sections 0.3--0.4,
Theorem 0.4.1, and Section 0.8](https://www.cs.umd.edu/~gasarch/TOPICS/vdw/hj.pdf),
states the finite-alphabet combinatorial-line theorem and its
arithmetic application. The direct sum-of-letters deduction in the
proof of Theorem 15.2 specifies the signed-integer version required.
At mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`,
[Combinatorics.exists_mono_homothetic_copy in
Mathlib/Combinatorics/HalesJewett.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Combinatorics/HalesJewett.lean)
states this supplier for any finitely colored additive commutative
monoid and finite subset: its positive natural dilation, monoid
translation and common color specialize to $a,b,C$ above with the
monoid $\mathbb Z$. Neither that classical theorem nor its library
proof is claimed as new content here.

The source correspondence is exactly (FW.1)--(FW.2), including the
full error cube, positive unbounded gain, arbitrary offset, actual
finite frames and adaptive increasing menu; the witnesses are legal
subfamilies of that domain. The transition-table coloring and
source-specific square pattern (AC.5) give the complete finite-cut
obstruction for a bounded origin target. The simultaneous three-pair
pattern (AC.10)--(AC.14) supplies the adaptive first-cut lower bound.
Theorem 10.2 already gives fixed-pair noiseless finite-first-state
risks, and its pair $(1,2)$ supplies the $5/4$ upper bound used in
(AC.9). It does not choose both indices adaptively or provide the
common-state, common-second-report construction across all three
pairs. Theorem 10.3's one-sided noisy plateau has different prior
conditions. Propositions 11.5 and 12.4 treat preselected triples with
uncompressed side acquisition; the cut restrictions and constants here
are different. The main transport uses the original $M,J,R_0$ and
read rule of (FW.10)--(FW.11), with the explicit $b_0=0$ subfamily
and finite-prefix augmentation. It grants no source-blind restriction
on otherwise lawful causal main action choices.

The fixed-before-values report-support quantifiers in
[FIB_UNCALIBRATED_QUADRATIC_CLOCK_UNIFORM_REPORT_DESIGNS, Sections 24--26](FIB_UNCALIBRATED_QUADRATIC_CLOCK_UNIFORM_REPORT_DESIGNS.md)
concern which indices are retained across prior widths; Section 26's
unbounded grid-size requirement is not a bound on a receiver's
acquisition cut state at this four-position source. The native
Brownian paid-point model in
[FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING, Sections 50 and 54](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md)
uses wrapped points, a seed-generated conditional history, native
control costs and a chance-class target. Its continuous internal
records and randomization are not finite complete carriers in this
deterministic polynomial experiment. The finite quantizer and
productive rational-word suppliers and their owning Scribes compared
in Definition 14.2 retain their stated scopes. They neither acquire
this clock nor assert these cut obstructions. These are source-specific
ordinary deductions, without a claim of global originality or new
Lean certification.

**Definition 18.2 (same-run accounting and remaining conclusions).**
Acquisition still has exactly three side reads, $v$ native atoms and
$v+1$ mandatory main reads. A continuation of $N$ atoms adds $N$ main
reads and no side reads. All actual main frames, their action/index
identities, controller, source binding, rights, accessible backing,
query, outputs and local work are resources of that same run. The
finite condition bounds distinguishable usable states at the named
cuts; it gives no acquisition word-length bound, uniform running time,
bound on within-frame scratch, or optimal bit-growth rate as gain or
offset increases. The homothetic-copy supplier selects finite witness
parameters without an optimized scale estimate.

The unchanged meanings in Definition 13.1 remain independent: temporal
order and a native count do not expose an absolute spatial origin;
actual boundary words may acquire it; memory must retain enough of
those words until later reports arrive; and a retained approximate
origin can then support the original-coordinate consumer. These
statements add necessary acquisition conditions to the proved positive
recovery directions in Proposition 13.2. They give no noisy $5/4$
upper bound for a finite first cut, arbitrary-randomness lower bound,
universal equivalence of four views, physical memory impossibility,
or alpha/beta reduction of this supplied main/clock product. A finite
program with variable records is outside the fixed finite carrier
condition. Original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer,
unchanged-initialization and full relational-process objectives retain
their stated open obligations.

## 追加锚（本行以下为增补区）

## 19. Fresh private randomness at every finite complete handoff

**Definition 19.1 (randomized complete-state origin experiment).** Keep
Definition 11.1's entire raw source, delivery relation and canonical
framing. A complete lawful world is

$$
\begin{aligned}
W&=(\tau,A,B,\eta,k_0,k_1,k_2,k_3),\\
\tau&\in[-4,1],\quad A\ge1,\quad A,B\in\mathbb R,\quad
\eta\in[-1,1]^4,\\
y_i&=A(i+\tau)^2+B+\eta_i,\qquad
k_i\in\mathbb Z,\qquad |k_i/256-y_i|\le1/256
\quad(0\le i\le3).
\end{aligned}
\tag{RC.1}
$$

All parameters are finite reals where applicable. The entire $W$,
including errors and deliveries at unread indices, is fixed before
all receiver randomness. The source supplies the fixed report for a
requested index; it cannot change $W$ in response to coins or requests.
Each acquired frame contains exactly the side tag, requested index,
precision tag $8$, canonical signed binary integer $k_i$, delimiter
and completion specified in Definition 11.1. Frame length is not
bounded. There is no further variable field or informative delivery
schedule.

Fix a receiver $\mathcal R$ and its public operands independently of
$W$. It reads exactly three side frames at strictly increasing indices
$0,u,v$, where $u\in\{1,2\}$ and $v\in\{u+1,\ldots,3\}$. The
indices may be chosen adaptively. At every handoff after a frame has
been processed and before another report is requested, the receiver
has one fixed finite nonempty complete usable carrier $Q$. Its initial
state has a fixed distribution $\lambda$ on $Q$, independent of $W$.
The stage, legal next index, controller and all other persistent
quantities usable by future requests or answers factor through $Q$
and the fixed public operands. Finite controller bookkeeping is
charged to this carrier. In particular a randomized next-index choice
is included in the retained state, so equal complete states at the
same stage prescribe the same actual next index.

At a frame the receiver uses a stochastic kernel from its current
state, stage/index and that actual complete frame to a probability
distribution on $Q$. The kernel may depend arbitrarily on the discrete
frame. Fresh private randomness is independent of $W$ and of previous
randomness conditional on the retained state and actual acquired
input. No future influence of past randomness is available except
through the new state. Every future-usable record, archive, backing
store, length, address, informative timing or schedule, source write,
persistent seed and retained random history is counted in $Q$, with
the completeness meaning of Definition 15.1. There is no extra report,
reset, copy, rereading of erased data, uncounted reusable random tape,
source-dependent advice or physical timing channel. Neither an exact
real input port nor an additional source service is supplied. Each
reached frame is processed by arbitrary terminating local work, with
variable transient scratch permitted. This bounds handoff states,
not every intermediate configuration, frame length or total runtime.

The final answer $T\in[-4,1]$ has any probability kernel $H(q,\cdot)$
on the Borel subsets of $[-4,1]$, depending only on the final state
$q\in Q$ and fixed public operands. Its randomization is included in
the expectation below; the last input frame or erased transcript is
not an additional final operand. Define

$$
\operatorname{Risk}(\mathcal R)
   =\sup_{W\text{ satisfying }\mathrm{(RC.1)}}
       \mathbb E_{\mathcal R,W}|T-\tau|.
\tag{RC.2}
$$

Each receiver has its own fixed $Q$ throughout this supremum. There
is no common bound on $|Q|$ across receivers. The expectation is over
that receiver's initial distribution, frame randomization and final
kernel for a fixed complete world, not over a world selected after
seeing the coins.

**Theorem 19.2 (randomized all-handoff origin minimax).** For the
experiment of Definition 19.1,

$$
\inf_{\mathcal R}\operatorname{Risk}(\mathcal R)=\frac52.
\tag{RC.3}
$$

More precisely, for every such $\mathcal R$ and every $\varepsilon>0$
there are two complete worlds $W_-,W_+$, fixed before its coins, with
$\tau_-=-4$, $\tau_+=1$, zero raw errors, a common integer gain
$A\ge1$, a common integer offset $B$ and exact canonical integer
reports, for which

$$
\max\left\{
 \mathbb E_{\mathcal R,W_-}|T+4|,
 \mathbb E_{\mathcal R,W_+}|T-1|
\right\}\ge\frac52-\varepsilon.
\tag{RC.4}
$$

The value in (RC.3) is attained by the constant-answer receiver of
Theorem 15.2. The endpoint worlds in (RC.4) may depend on the receiver
and $\varepsilon$; no endpoint pair is asserted to work for all
receivers or all precisions.

**Proof.** Fix $\mathcal R$, its public operands and $\varepsilon>0$.
Enumerate its complete states as $Q=\{q_1,\ldots,q_m\}$, including
all the charged control fields. For an integer $x$, write $\Phi_i(x)$
for the complete canonical frame at index $i$ with payload $256x$.
It is exactly a lawful delivery of the raw value $x$. For
$j\in\{1,2,3\}$ and $i\in\{0,1,2,3\}$, let

$$
K_{j,i}(q,x)\in\Delta(Q)
\tag{RC.5}
$$

be the distribution of the next complete cut state when frame
$\Phi_i(x)$ is processed from state $q$ at read number $j$.
These are the actual stochastic rows, including randomized control
updates. There are only $12m$ row positions $(j,i,q)$, although each
row can depend arbitrarily on $x$.

A row belonging to an inconsistent or unreachable state/stage/input
combination may lack an operational meaning. At any such combination
where there is no specified normalized terminating row, assign the
fixed distribution concentrated at $q_1$. This is only a totalization
for the coloring, not a new source behavior. On every combination
reached with positive probability in a lawful run use the receiver's
actual normalized row, as required by Definition 19.1. Thus all rows
in (RC.5), including defaults, are probability distributions. A
possibly nonterminating off-path computation is not turned into a
subprobability row. No default replaces a row on a lawful run or
changes its next-index legality.

Choose an integer $N\ge1$ such that

$$
\frac{15(m-1)}{2N}\le\varepsilon,
\qquad \delta=\frac{m-1}{N}.
\tag{RC.6}
$$

For a probability vector $p=(p_1,\ldots,p_m)$ define its finite
simplex code by

$$
\begin{aligned}
a_r(p)&=\lfloor Np_r\rfloor\quad(1\le r<m),\\
a_m(p)&=N-\sum_{r<m}a_r(p),\qquad
\widehat p_r=a_r(p)/N.
\end{aligned}
\tag{RC.7}
$$

The integers $a_r$ are nonnegative and sum to $N$, so $\widehat p$
is a probability vector in a finite simplex grid. Moreover
$d_{\rm TV}(p,\widehat p)\le(m-1)/N$: the first $m-1$
coordinates are rounded down by less than $1/N$, and their total
rounding deficit is exactly the last coordinate's excess. If $p,p'$
have the same code, each of their first $m-1$ coordinate differences
has absolute value at most $1/N$, and

$$
\begin{aligned}
|p_m-p'_m|&\le\sum_{r<m}|p_r-p'_r|,\\
d_{\rm TV}(p,p')
 &=\frac12\sum_{r=1}^m|p_r-p'_r|
 \le\sum_{r<m}|p_r-p'_r|\le\delta.
\end{aligned}
\tag{RC.8}
$$

When $m=1$ the code is $(N)$, every row is the same point mass and
$\delta=0$. Thus (RC.8) also covers this case. In particular the
same-cell bound is obtained directly, without adding two errors
from comparison with a grid representative.

Color each integer by all its row codes at once:

$$
C_N(x)=\bigl(a(K_{j,i}(q,x))\bigr)_{j,i,q}.
\tag{RC.9}
$$

There are finitely many colors: each code has $m$ integer coordinates
between $0$ and $N$, and there are $12m$ row positions. Equal colors
therefore give the uniform estimate

$$
C_N(x)=C_N(x')\quad\Longrightarrow\quad
 d_{\rm TV}\bigl(K_{j,i}(q,x),K_{j,i}(q,x')\bigr)\le\delta
 \quad\text{for every }j,i,q.
\tag{RC.10}
$$

This finite coloring concerns complete-frame transition laws, not
frame bytes, lengths, parsing paths or individual coin realizations.
It requires no regularity of the kernels as functions of the integer
input.

Use the classical homothetic-copy supplier already attributed in
Definition 18.1 to this coloring of $\mathbb Z$ and
$S=\{0,1,4,9,16\}$. Its parameters are the coloring $C_N$, the
additive monoid $\mathbb Z$ and this five-element $S$. The positive
natural dilation and integer translation supplied by
`Combinatorics.exists_mono_homothetic_copy` at the mathlib revision
specified there are denoted $a\ge1$ and $b\in\mathbb Z$. Thus
$C_N$ is constant on $b+aS$. Equivalently, Gasarch's
[Theorem 0.4.1 and Section 0.8](https://www.cs.umd.edu/~gasarch/TOPICS/vdw/hj.pdf)
supply the finite-alphabet combinatorial line, with the
sum-of-letters specialization in the proof of Theorem 15.2 giving
this signed-integer copy. This is a reuse of that classical supplier
inside the clock argument.

Set, simultaneously for all four indices,

$$
\begin{aligned}
W_-&=(-4,a,b,0,k^-_0,k^-_1,k^-_2,k^-_3),&
k^-_i&=256\bigl(b+a(i-4)^2\bigr),\\
W_+&=(1,a,b,0,k^+_0,k^+_1,k^+_2,k^+_3),&
k^+_i&=256\bigl(b+a(i+1)^2\bigr).
\end{aligned}
\tag{RC.11}
$$

Here $0$ denotes the four-coordinate zero error vector. The raw
report vectors $x^-=(y^-_i)_{i=0}^3$ and $x^+=(y^+_i)_{i=0}^3$ are

$$
x^-=b+a(16,9,4,1),\qquad
x^+=b+a(1,4,9,16).
\tag{RC.12}
$$

Every coordinate is an integer of the common color. Both worlds
satisfy (RC.1) with delivery error exactly zero. All four canonical
report words, including unread ones, are now fixed. They depend on
$\mathcal R$ and $N$, but on no sampled initial state, private seed,
coin sequence, requested triple or realized execution history.

We next compare the actual three adaptive reads. For finite
probability vectors the half-sum formula for total variation and a
coupling with disagreement probability exactly that distance are the
classical facts in Levin--Peres,
[*Markov Chains and Mixing Times*, second edition, Propositions 4.2
and 4.7](https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf).
Apply these facts to the two rows in (RC.10). Such a coupling has
agreement probability at least $1-\delta$. It can be selected for
each pair of states and inputs needed below, since at each stage the
state pairs and legal indices form finite sets. The coupling is an
analysis of the two laws; it is not a resource given to a receiver.

Draw one state with law $\lambda$ and use it as both initial states
$Q^-_0,Q^+_0$. Their equality holds with probability one. At the first
read both indices are $0$. Conditional on the common initial state
$q$, couple $K_{1,0}(q,x^-_0)$ and $K_{1,0}(q,x^+_0)$ by the above
row coupling. By (RC.10) its disagreement probability is at most
$\delta$. Let $G_1=\{Q^-_1=Q^+_1\}$. Then

$$
\mathbb P(G_1^c)\le\delta.
\tag{RC.13}
$$

On $G_1$ the complete state $q$ is common, including the selected
second index. Hence both runs request the same $u\in\{1,2\}$,
although $u$ need not be constant across executions. Conditional on
this common history, couple the actual rows
$K_{2,u}(q,x^-_u)$ and $K_{2,u}(q,x^+_u)$ with disagreement
probability at most $\delta$. On $G_1^c$ use any coupling, for example
the product of the two actual rows at their respective states and
indices. Each run then still has its correct conditional transition
law. For $G_2=G_1\cap\{Q^-_2=Q^+_2\}$ this gives

$$
\mathbb P(G_2^c)
 \le\mathbb P(G_1^c)+\delta\mathbb P(G_1)
 \le2\delta.
\tag{RC.14}
$$

On $G_2$ the state after the second frame, and therefore the selected
third index $v\in\{u+1,\ldots,3\}$, agree. Couple
$K_{3,v}(q,x^-_v)$ and $K_{3,v}(q,x^+_v)$ with conditional
disagreement probability at most $\delta$. On $G_2^c$ again use any
coupling of the actual rows, allowing different lawful indices in
the two runs. With $G_3=G_2\cap\{Q^-_3=Q^+_3\}$,

$$
\mathbb P(G_3^c)
 \le\mathbb P(G_2^c)+\delta\mathbb P(G_2)
 \le3\delta.
\tag{RC.15}
$$

These successive couplings preserve both receivers' marginal path
laws, including their adaptive requests. On every positive-probability
history a row used here is an actual normalized lawful row, so none
of the off-path defaults is invoked. If $\nu_-,\nu_+$ are the final
state laws, the coupling inequality yields

$$
d_{\rm TV}(\nu_-,\nu_+)
 \le\mathbb P(Q^-_3\ne Q^+_3)
 \le\mathbb P(G_3^c)\le3\delta.
\tag{RC.16}
$$

Thus there is no replacement of the adaptive menu by one fixed
triple, and no inference from the first cut alone to the last cut.

Include the arbitrary final probability kernel by writing
$\mu_\pm(D)=\sum_q\nu_\pm(q)H(q,D)$ for Borel
$D\subseteq[-4,1]$. Since $0\le H(q,D)\le1$ and the positive and
negative parts of $\nu_- -\nu_+$ each have mass
$d_{\rm TV}(\nu_-,\nu_+)$,

$$
\begin{aligned}
|\mu_-(D)-\mu_+(D)|&\le d_{\rm TV}(\nu_-,\nu_+),\\
d_{\rm TV}(\mu_-,\mu_+)
 &:=\sup_{D\text{ Borel}}|\mu_-(D)-\mu_+(D)|\le3\delta.
\end{aligned}
\tag{RC.17}
$$

This is the same probability-kernel contraction as Levin--Peres,
Exercise 4.2; the displayed calculation also covers the possibly
continuous output law directly. It imposes no finite support or
determinism on $H$.

For every Borel function $0\le f\le5$, integrating the event
probabilities of $\{f>t\}$ over $0\le t\le5$ gives

$$
\left|\int f\,d\mu_- -\int f\,d\mu_+\right|
 \le5d_{\rm TV}(\mu_-,\mu_+)\le15\delta.
\tag{RC.18}
$$

This is the bounded-loss form of the total-variation dual estimate
(cf. Levin--Peres, Proposition 4.5). On the declared answer interval,
$f_-(t)=|t+4|=t+4$ and $f_+(t)=|t-1|=1-t$ are between $0$ and $5$
and have pointwise sum $5$. Consequently the actual endpoint risks
$r_-=\int f_-\,d\mu_-$ and $r_+=\int f_+\,d\mu_+$ obey

$$
\begin{aligned}
r_-+r_+
 &\ge\int(f_-+f_+)\,d\mu_- -15\delta
   =5-15\delta,\\
\max\{r_-,r_+\}
 &\ge\frac52-\frac{15\delta}{2}
  \ge\frac52-\varepsilon.
\end{aligned}
\tag{RC.19}
$$

This proves (RC.4). In particular (RC.2) is at least
$5/2-\varepsilon$ for every $\varepsilon>0$, so it is at least
$5/2$. This conclusion uses a supremum of expected losses in
complete worlds fixed before the coins. It neither interchanges
supremum and expectation nor fixes a favorable seed and then selects
a source. It also does not require an endpoint world attaining this
supremum for an arbitrary receiver.

Finally choose the indices $0,1,2$, pass over each complete productive
frame with a finite stage controller and output $-3/2$ with probability
one, as in Theorem 15.2. All controller states count toward $Q$.
For every lawful $W$, $|-3/2-\tau|\le5/2$, so this lawful receiver
has risk at most $5/2$. It belongs to Definition 19.1's randomized
class as a deterministic special case. The lower bound just proved
gives equality and attainment in (RC.3). $\square$

**Definition 19.3 (scope of the randomized conclusion).** The
arbitrary-randomness exclusion in Definition 18.2 is qualified exactly
by Theorem 19.2 for the origin experiment of Definition 19.1: fresh
private randomness, with complete finite states at all three
handoffs and a final kernel from the last such state, does not improve
the exact worst-world expected absolute-error value $5/2$.
The classical suppliers used in its proof are the homothetic-copy
result of Definition 18.1 and the cited total-variation and coupling
facts. The additional `repo-derived` deduction connects quantized rows of this
receiver to the two lawful square-pattern worlds and their adaptive
three-read output laws; the suppliers themselves do not state this
clock experiment. This mathematical correspondence makes no claim
of global originality.

Theorem 19.2 leaves unchanged the other boundaries of Definition
18.2. It gives no stochastic first-cut-only minimax value, no noisy
$5/4$ finite-first-cut upper bound, no acquisition memory-growth rate,
no uniform running-time or within-frame-memory bound, and no optimal
scale for the witness integers $a,b$. It supplies no exact-real port,
extra source service or physical realization. It asserts no extension
to the main-coordinate continuation or its consumer, no universal
equivalence of the four views, and no physical memory impossibility.
The original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer,
unchanged-initialization and full relational-process objectives retain
their stated obligations. A receiver with unbounded accessible
records, persistent random backing or a final answer using an erased
frame is outside Definition 19.1; arbitrary terminating transient
work within a frame is inside it.

## 追加锚（本行以下为增补区）
