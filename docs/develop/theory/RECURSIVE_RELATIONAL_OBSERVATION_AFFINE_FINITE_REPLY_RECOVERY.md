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
