# Private randomization for three readings of an uncalibrated quadratic clock

## 1. Complete sources, private seeds and exact compatibility

**Definition 1.1 (complete quadratic-clock source).** Fix $m>0$, $c>0$
and finite $E\ge0$, and put

$$
z=-\frac32,\qquad a=z-E,\qquad b=z+E,\qquad
K=[a,b],\qquad \varepsilon=\frac{mc}{2}.
\tag{1.1}
$$

The source consists of every complete world

$$
W=(\tau,A,B,\eta),\qquad
\tau\in K,\quad m\le A<\infty,\quad B\in\mathbb R,\quad
\eta\in[-\varepsilon,\varepsilon]^4,
\qquad y_i(W)=A(i+\tau)^2+B+\eta_i\quad(0\le i\le3).
\tag{1.2}
$$

All parameters, including all four errors at read and unread coordinates,
are fixed before any private seed. There is no upper bound on the gain,
no additional relation between nuisance parameters, and no source service
other than the requested report. The target is the original $\tau(W)$.
The reports are exact real numbers, and every acquired record remains
accessible to the decision rule.

This is the source of
[Uniform Report Designs, Definitions 30.1, 31.1 and 32.1 and Sections 33--34](FIB_UNCALIBRATED_QUADRATIC_CLOCK_UNIFORM_REPORT_DESIGNS.md),
with the same parameters and original error coordinates. Its chronological
three-reading rights are those of
[Three-Index Design, Definition 23.1](FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN.md),
with $(a,b,m,\varepsilon)$ as in (1.1). Only the admission of private
randomness changes the deterministic experiment.

**Definition 1.2 (private randomized strategies and risk).** A strategy
has one probability space $(\Omega,\mathcal F,\mathbb P)$, chosen
independently of the complete world. The space, its law and the entire
family of history functions are fixed across all worlds; their only
world-dependent operands are actual acquired reports. For each $\omega\in\Omega$, it has
functions

$$
\begin{aligned}
f_\omega&:\mathbb R\longrightarrow\{1,2\},\\
g_\omega&:\{1,2\}\times\mathbb R^2\longrightarrow\{2,3\},\\
\Delta_\omega&:\mathcal P\times\mathbb R^3\longrightarrow\mathbb R,
\qquad \mathcal P=\{(1,2),(1,3),(2,3)\},
\end{aligned}
\tag{1.3}
$$

where $g_\omega(1,r,s)\in\{2,3\}$ and
$g_\omega(2,r,s)=3$ for every real $r,s$. All functions are total on
the displayed domains, and every value of $\Delta_\omega$ is finite.
In world $W$ the actual execution is

$$
\begin{gathered}
\text{read }y_0(W),\qquad
u_\omega(W)=f_\omega(y_0(W)),\qquad
\text{read }y_{u_\omega(W)}(W),\\
v_\omega(W)=g_\omega(u_\omega(W),y_0(W),y_{u_\omega(W)}(W)),
\qquad \text{read }y_{v_\omega(W)}(W),\\
T_\omega(W)=\Delta_\omega
 (u_\omega(W),v_\omega(W),y_0(W),y_{u_\omega(W)}(W),
                                      y_{v_\omega(W)}(W)).
\end{gathered}
\tag{1.4}
$$

Thus exactly three actual readings at integer indices $0,u_\omega,v_\omega$,
with $0<u_\omega<v_\omega\le3$, are acquired. No reset, copy,
extra reading, fractional reading,
source-dependent seed or advice, or reselection of a world during
execution is permitted. For each fixed complete $W$, the two actual
indices and $T_\omega(W)$ must be measurable functions of $\omega$.
No joint measurability in $(W,\omega)$, world-space probability measure,
computability, or further regularity of the history functions is assumed.

Write

$$
\mathcal R(\Gamma)=\sup_{W\text{ satisfying }(1.2)}
                 \mathbb E_\omega|T_\omega(W)-\tau(W)|,
\qquad
R_{\mathrm{private}}(c,E)=\inf_\Gamma\mathcal R(\Gamma).
\tag{1.5}
$$

The expectation may be extended nonnegative. The infimum includes
arbitrary seed probability spaces, rather than only finite mixtures.
The gain lower bound $m$ is suppressed in the notation: dividing every
report and nuisance coefficient by $m$ gives the corresponding
experiment with gain lower bound $1$, without changing $\tau$ or loss.
Let $R_{\mathrm{ad},3}$ denote the same infimum restricted to one-point
seed spaces, namely the entire published deterministic adaptive class.

The order $\sup_W\mathbb E_\omega$ agrees with the worst-input expected
error criterion in Krieg--Novak--Ullrich,
[*On the power of adaption and randomization*, arXiv:2406.07108v2, Sections 1--2](https://arxiv.org/html/2406.07108v2).
Their main setting has a continuous linear target on a convex subset
of a Banach space, and their randomized class additionally imposes
product measurability of the loss. Here, with
$\theta=(\theta_2,\theta_1,\theta_0)=(A,2A\tau,A\tau^2+B)$, the target
$\theta_1/(2\theta_2)$
is a nonlinear ratio. Adding the four errors to the input makes the
reports linear in the augmented coordinates but does not make that
target linear. The permitted information is also the chronological
coordinate menu (1.4), rather than arbitrary linear measurements.
Consequently the cited linear-target comparisons do not supply a
minimax value for (1.5), and their product-measurability assumption is
not imposed here.

**Definition 1.3 (compatible intervals and diameter constants).** For
$(u,v)\in\mathcal P$ and any real history $r=(r_0,r_u,r_v)$, set

$$
C_{uv}(r)=\left\{t\in K:\exists A\ge m,\ B\in\mathbb R,
       \ |r_i-A(i+t)^2-B|\le\varepsilon\quad(i=0,u,v)\right\}.
\tag{1.6}
$$

Every witness of membership has finite gain and offset; its unread
error may be fixed to zero to give a complete world. Conversely,
projection of the complete error cube gives exactly the three
constraints in (1.6). Every nonempty $C_{uv}(r)$ is a compact interval,
by the exact positive-denominator change of variables in
[Three-Index Design, Theorem 3.1](FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN.md):

$$
\lambda=1/A,\qquad \xi=2t,\qquad
\omega_0=(At^2+B)/A,
\qquad
\begin{cases}
0\le\lambda\le1/m,\\
2a\le\xi\le2b,\\
|\lambda r_i-i^2-\xi i-\omega_0|\le\varepsilon\lambda
                                      &(i=0,u,v).
\end{cases}
\tag{1.7}
$$

This is an exact joint feasible set; it is not a box of independent
difference errors. The symbol $\omega_0$ in (1.7) is a real nuisance
coordinate, unrelated to the private seed $\omega$. The compactness
and midpoint suppliers originate in
[Self-Calibrating Relation Mathematics II, Theorem 80.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md).
For $E=0$ compactness is immediate from $C_{uv}(r)\subseteq\{z\}$.

Put

$$
\begin{gathered}
P=\frac{c(1+2E)}{3+2c},\qquad
Q=\frac{cE}{1+c},\qquad
G=\frac{c(1+E)}{3+c},\\
F=\min\{2E,\max(c/3,P,Q,G)\},\qquad
H=\min\{2E,\max(c/3,G,Q)\},\qquad
D_0=\min(2E,c/3).
\end{gathered}
\tag{1.8}
$$

Thus $0\le D_0\le H\le F<\infty$. The reused fixed-design
diameters are $F$ for both $013$ and $023$, and $H$ for the full
grid $0123$, by Three-Index Design, Theorems 3.1 and 18.2.
Here and below $013$ abbreviates the acquired set $\{0,1,3\}$,
and similarly for the other paths. The letter $H$ in (1.8) is a
diameter, not a time-domain endpoint or a prefix-conditioned function
from Uniform Report Designs.

The original separation supplier is Three-Index Design, Theorem 2.1.
Its fixed-pair counterpart is the repository declaration
`QuadraticThreeIndexSeparation.quadratic_three_index_separation`
in [QuadraticThreeIndexSeparation.lean](../../../D5/S3/Observer/MetricGeometry/QuadraticThreeIndexSeparation.lean).
The private helpers `coordinate_bounds`, `right_lower`, `lower`,
`center_le`, `centered_upper`, `centered_minimal`, `value_right`,
`value_reflected`, `reflected_norm`, `upper_right_near`,
`upper_right_far`, and the `attain_*` lemmas concern that fixed-pair
separation and its finite attaining calibrations. They do not state
the simultaneous origin-conditioned decision guarantee below.

The bounded-error feasible-set correspondence is the classical one of
Casini--Garulli--Vicino,
[*A linear programming approach to online set membership parameter estimation for linear regression models*, Section 4, equations (7)--(10)](https://control.dii.unisi.it/~casini/pdf/IJACSP_2017a.pdf):
the regression vector is $(i^2,i,1)$, the coefficient vector is
$(A,2A\tau,A\tau^2+B)$, and the additive error bound is
$\delta=\varepsilon$. Their feasible set is an intersection of
regression strips. Their coordinate linear programs yield bounding
orthotopes; such outer orthotopes do not replace this problem's
joint feasible set or its nonlinear origin target. This classical
method and the cited repository suppliers are intermediate ingredients;
the new deductions are the origin-conditioned reconstruction,
same-world expected bounds and attained family risk in Sections 2--4.
These deductions are repo-derived ordinary mathematical proofs, with
no assertion of global priority or of an exhaustive literature search.

## 2. Simultaneous error budgets conditioned on the origin

**Theorem 2.1 (one answer satisfying both origin-side budgets).** For
every $c>0$ and finite $E\ge0$, define functions on $K$ by

$$
\rho_{13}(t)=
\begin{cases}H/2,&t\le z,\\F/2,&t>z,\end{cases}
\qquad
\rho_{23}(t)=\rho_{13}(-3-t)=
\begin{cases}F/2,&t<z,\\H/2,&t\ge z.\end{cases}
\tag{2.1}
$$

For $j\in\{13,23\}$ and any real history with
$C=C_j(r)\ne\varnothing$, the closed interval

$$
\begin{aligned}
J_j(r)&=[L_j(r),U_j(r)],\\
L_j(r)&=\sup_{t\in C}\bigl(t-\rho_j(t)\bigr),\qquad
U_j(r)=\inf_{t\in C}\bigl(t+\rho_j(t)\bigr)
\end{aligned}
\tag{2.2}
$$

is nonempty and bounded. Its midpoint

$$
d_j(r)=\frac{L_j(r)+U_j(r)}2
\tag{2.3}
$$

therefore satisfies, simultaneously for every $t\in C$,

$$
|d_j(r)-t|\le\rho_j(t).
\tag{2.4}
$$

For an empty compatible set define $d_j(r)=z$. The functions are
total on all real histories. The side of the true origin is an
analysis condition in (2.4), never an extra input to $d_j$.

**Proof.** First record precisely the pair restrictions supplied by
the existing separation and interval theorems. On $013$, the
five-candidate calculation of Three-Index Design, Theorem 3.1,
restricted only for this comparison to the half-prior $[a,z]$, gives

$$
\begin{gathered}
\sup_r\operatorname{diam}\bigl(C_{13}(r)\cap[a,z]\bigr)
       =\min\{E,\max(c/3,G,Q)\}\le H,\\
\text{candidates on }[a,z]:\quad
c/3,\quad c/(3+2c),\quad0,\quad G,\quad Q.
\end{gathered}
\tag{2.5}
$$

Empty intersections are omitted from the supremum. Restriction to
$[z,b]$ instead gives candidates
$c/3,P,Q,c/(3+c),0$ and diameter
$\min\{E,\max(c/3,P,Q)\}\le F$. On the full prior, the
supplier gives $\operatorname{diam}C_{13}(r)\le F$.
These are uses of the existing joint-noise theorem, with no
replacement of its fibers by independent error boxes.

For any $s\le z\le t$ in one compatible interval for either path,
Three-Index Design, Theorem 2.1, gives the cross-center separation
$3m(t-s)$. Since their noiseless triples both lie within
$\varepsilon$ of the same acquired triple,

$$
3m(t-s)\le2\varepsilon=mc,
\qquad t-s\le D_0\le H.
\tag{2.6}
$$

The complete-source reflection

$$
\mathfrak s(W)=(-3-\tau,A,B,(\eta_3,\eta_2,\eta_1,\eta_0))
\tag{2.7}
$$

preserves (1.2) and gives $y_i(\mathfrak s(W))=y_{3-i}(W)$.
It exchanges fixed sets $013$ and $023$ and exchanges the two
origin halves. Thus $C_{23}$ has diameter at most $F$, and its
intersection with $[z,b]$ has diameter at most $H$. Reflection is
only a relation between complete worlds and fixed experiments;
neither actual execution reads in reverse chronological order.

It follows for every $s,t\in C_j(r)$ that

$$
|s-t|\le\rho_j(s)+\rho_j(t).
\tag{2.8}
$$

Indeed, two points in the favorable half have distance at most $H$
and radius sum $H$; two points strictly in the other half have
distance at most $F$ and radius sum $F$. A pair with one point on
each side, including a point equal to $z$, is covered by (2.6),
and its radius sum is at least $H$.

In particular $s-\rho_j(s)\le t+\rho_j(t)$ for every ordered
pair of points. Taking the supremum in $s$ and the infimum in $t$
gives $L_j\le U_j$. Both quantities are finite because
$C_j(r)\subseteq[a,b]$ and $0\le\rho_j\le F/2$.
Every $x\in J_j(r)$ belongs to
$[t-\rho_j(t),t+\rho_j(t)]$ for every $t\in C_j(r)$,
which proves (2.4) for its midpoint.

When $E=0$, every nonempty compatible set is $\{z\}$,
$F=H=0$, and $J_j(r)=\{z\}$. This also proves the degenerate
case without using a positive-length prior in the supplier. The
explicit empty-set convention completes totality. $\square$

## 3. Actual acquisition and expected loss in a fixed world

**Definition 3.1 (a private two-design family).** For $0\le p\le1$,
let $\Gamma_p$ have seed space $\Omega=\{13,23\}$ with its full
power-set sigma-algebra and probabilities $p,1-p$. Set, on all
real first reports,

$$
f_{13}(r_0)=1,\qquad f_{23}(r_0)=2,
\qquad g_j(u,r_0,r_u)=3\quad(j\in\Omega).
\tag{3.1}
$$

On every legal terminal pair, including pairs unreachable for that
seed, define $\Delta_j$ as follows. On pairs $(1,3)$ and $(2,3)$,
use $d_{13}$ and $d_{23}$ from Theorem 2.1, respectively. On pair
$(1,2)$, use the midpoint of $C_{12}$ if it is nonempty, and $z$
otherwise. These terminal rules do not otherwise depend on the seed.
The parameters $p,m,c,E$ are public operands fixed independently of
$W$.

**Theorem 3.2 (origin-conditioned expected loss on the complete source).**
Every $\Gamma_p$ is lawful under Definition 1.2. For every fixed
complete world, it has

$$
\mathbb E_{\Gamma_p}|T-\tau|\le
\begin{cases}
\bigl(pH+(1-p)F\bigr)/2,&\tau<z,\\[2pt]
H/2,&\tau=z,\\[2pt]
\bigl(pF+(1-p)H\bigr)/2,&\tau>z.
\end{cases}
\tag{3.2}
$$

Consequently, throughout $c>0$, $0\le E<\infty$,

$$
\mathcal R(\Gamma_p)\le
\frac{H+(F-H)\max(p,1-p)}2,
\qquad
\mathcal R(\Gamma_{1/2})\le\frac{F+H}{4}.
\tag{3.3}
$$

**Proof.** Each seed executes exactly one of $0,1,3$ and $0,2,3$,
strictly in chronological order. All history functions, including
unused histories, are total by (3.1), Theorem 2.1 and the compact
interval supplier for $012$. Every answer is a finite real number.
For each fixed $W$, actual indices and answer are functions on a
finite power-set probability space, and hence are seed-measurable,
also when $p=0$ or $p=1$. This establishes all acquisition,
totality and measurability requirements.

The true $\tau(W)$ belongs to each of the two compatible intervals
formed from that world's corresponding triple. Applying (2.4) to
this same $W$ gives loss at most $H/2$ on $013$ and $F/2$ on
$023$ when $\tau<z$, and the reverse bounds when $\tau>z$.
At $\tau=z$, both bounds are $H/2$. Averaging these pointwise
bounds gives (3.2) and then (3.3). No execution has access to the
other seed's missing reading. The two losses in this proof are
analytical evaluations on one preselected four-coordinate source,
not a simultaneous acquisition or a seed-dependent choice of
different worst worlds. $\square$

**Theorem 3.3 (all-parameter bounds for arbitrary private seeds).** For
every $c>0$ and finite $E\ge0$,

$$
\boxed{
\frac H2\le R_{\mathrm{private}}(c,E)
\le\min\left\{R_{\mathrm{ad},3}(c,E),\frac{F+H}{4}\right\}.
}
\tag{3.4}
$$

The lower bound holds over all the seed spaces of Definition 1.2.
It uses two complete worlds fixed independently of every seed.

**Proof.** For $E>0$, apply the attained full-grid diameter supplier,
Three-Index Design, Theorem 18.2, at $I=\{0,1,2,3\}$,
$a+b=-3$, $b-a=2E$. Its candidates are $c/3,G,Q,G$,
so it supplies complete legal worlds $W_-,W_+$ with all four
reports equal and origin distance $H$. Both gains and offsets are
finite, and the two four-coordinate errors belong to the original
closed cube. This is the fixed finite-set supplier, also used in
Uniform Report Designs, Sections 30--34; no adaptive branch
certificate is being promoted to a randomized lower bound.

Fix any one admissible private strategy, with an arbitrary seed
space. For each seed, the two worlds give the same $y_0$, the same
first choice, the same acquired second report, the same second
choice, and the same final acquired report. Total deterministic
history rules therefore give the same answer $T_\omega$ in both
worlds. For every seed,

$$
|T_\omega-\tau(W_-)|+|T_\omega-\tau(W_+)|\ge H.
\tag{3.5}
$$

Both losses are measurable by the per-world hypothesis, so finite
additivity of nonnegative integrals gives

$$
\mathbb E|T-\tau(W_-)|+\mathbb E|T-\tau(W_+)|\ge H.
\tag{3.6}
$$

At least one of these two fixed-world expected losses is at least
$H/2$. The assertion remains valid if an expectation is infinite.
There is no integration over the source, no interchange of an
uncountable supremum and expectation, and no appeal to a minimax
or symmetrization theorem. If $E=0$, $H=0$ and the lower bound is
immediate.

Theorem 3.2 supplies the second upper bound. Every deterministic
strategy is an admissible one-point-seed strategy: its functions
need not be measurable in the world, since each fixed-world seed
map is constant. Taking the infimum over them supplies the first
upper bound. $\square$

## 4. Exact risk of the family and a strict deterministic separation

**Theorem 4.1 (attained family risk on a nontrivial closed band).** For
every $c>0$,

$$
\frac c3\le E\le\frac{1+c}{2},\qquad 0\le p\le1,
\tag{4.1}
$$

the family of Definition 3.1 has exact worst-world risk

$$
\boxed{
\mathcal R(\Gamma_p)=
\frac{G+(P-G)\max(p,1-p)}2.
}
\tag{4.2}
$$

In particular its fair member has

$$
\boxed{\mathcal R(\Gamma_{1/2})=\frac{P+G}{4}.}
\tag{4.3}
$$

Two complete worlds specified below attain the maximum in (4.2).
If $E>c/3$, the fair probability uniquely minimizes risk within
this particular family. This assertion is not an optimality claim
over all private strategies.

**Proof.** The relevant comparisons, with positive denominators,
are

$$
\begin{aligned}
E-P&=\frac{3E-c}{3+2c}\ge0,
&E-G&=\frac{3E-c}{3+c}\ge0,\\
G-c/3&=\frac{c(3E-c)}{3(3+c)}\ge0,
&P-G&=\frac{c(3E-c)}{(3+2c)(3+c)}\ge0,\\
G-Q&=\frac{c(1+c-2E)}{(3+c)(1+c)}\ge0.
\end{aligned}
\tag{4.4}
$$

Hence $F=P$, $H=G$ on (4.1), without an active $2E$
truncation. The uniform same-world upper bound in (4.2) follows
from Theorem 3.2. It remains to exhibit simultaneous attainment,
rather than combine two separate worst-world suprema.

Let $b=z+E$ and define the single complete world

$$
W_b=\bigl(b,m,-\varepsilon-mb^2,
                  (\varepsilon,-\varepsilon,-\varepsilon,-\varepsilon)\bigr).
\tag{4.5}
$$

Its complete reports are

$$
(y_0,y_1,y_2,y_3)(W_b)
 =\bigl(0,\ m(2E-2-c),\ m(4E-2-c),\ m(6E-c)\bigr).
\tag{4.6}
$$

Every component of its error vector has magnitude $\varepsilon$;
the gain is $m$, its origin is the prior endpoint, and its offset
is finite. This world is fixed before the coin for every $p$.

For its $013$ reports put

$$
\begin{gathered}
s_P=b-P,\qquad M_P=m(1+2c/3),\\
W_P=\bigl(s_P,M_P,\varepsilon-M_Ps_P^2,
                 (-\varepsilon,\varepsilon,0,\varepsilon)\bigr).
\end{gathered}
\tag{4.7}
$$

The first identity in (4.4) gives $s_P\ge z\ge a$.
The gain is finite and at least $m$, the offset is finite, and
all four specified errors are legal. If $p_P(i),p_b(i)$ denote
the two noiseless reports, direct substitution of $P$ gives

$$
M_Ps_P-mb=-\frac{4mc}{3},\qquad
p_P(i)-p_b(i)=mc+\frac{2mc}{3}(i^2-4i).
\tag{4.8}
$$

At $i=0,1,3$ the latter differences are $mc,-mc,-mc$;
the listed original errors cancel them exactly. Thus $W_P$ and
$W_b$ have the same acquired $013$ history. This is the finite
right-near separation witness of Three-Index Design, Theorem 2.1,
with its unread coordinate explicitly completed.

Since $C_{13}(y(W_b))$ contains $b$ and $b-P$ and its full-prior
diameter is at most $F=P$, its exact endpoints are $b-P,b$.
For $E>c/3$ this whole interval is strictly to the right of $z$,
so $\rho_{13}$ is the constant $P/2$ on it. Formula (2.2)
then gives $d_{13}=b-P/2$. At $E=c/3$, the interval may touch
$z$, but $F=H=P=G=E$, so the same formula still holds.
Therefore in $W_b$ the $013$ loss is exactly $P/2$.

For the very same world's $023$ reports put

$$
\begin{gathered}
s_G=b-G,\qquad M_G=m(1+c/3),\\
W_G=\bigl(s_G,M_G,\varepsilon-M_Gs_G^2,
                    (-\varepsilon,0,\varepsilon,\varepsilon)\bigr).
\end{gathered}
\tag{4.9}
$$

Again (4.4) gives $s_G\ge z$, and every parameter and all four
errors are legal. The original-coordinate identities are

$$
M_Gs_G-mb=-\frac{5mc}{6},\qquad
p_G(i)-p_b(i)=mc+\frac{mc}{3}(i^2-5i).
\tag{4.10}
$$

At $i=0,2,3$ these differences are $mc,-mc,-mc$, exactly
canceled by the displayed errors. The supplier's near-branch
condition here is

$$
0\le s_G-z=E-G=\frac{3E-c}{3+c}\le\frac12,
\tag{4.11}
$$

whose upper endpoint is precisely $E=(1+c)/2$; (4.10) also
verifies the common history directly, including that endpoint.

To identify the entire $023$ interval, first use its global
diameter bound $F=P$ and its member $b$ to conclude that it is
contained in $[b-P,b]\subseteq[z,b]$. Thus every point of this
fiber is in the favorable half, and (2.5) after reflection bounds
its diameter by $H=G$. Since it contains $b-G$ and $b$, its
endpoints are exactly $b-G,b$. Its radius is constantly $G/2$,
so $d_{23}=b-G/2$. The $023$ loss in $W_b$ is exactly $G/2$.
Consequently

$$
\mathbb E_{\Gamma_p,W_b}|T-b|
                  =\frac{pP+(1-p)G}{2}.
\tag{4.12}
$$

For the other origin endpoint take the single complete world

$$
W_a=\mathfrak s(W_b)
 =\bigl(a,m,-\varepsilon-mb^2,
                 (-\varepsilon,-\varepsilon,-\varepsilon,\varepsilon)\bigr).
\tag{4.13}
$$

This is legal by (2.7). The reflection of the compatible sets and
$\rho_{23}(t)=\rho_{13}(-3-t)$ imply

$$
d_{13}(y(\mathfrak s(W)))=-3-d_{23}(y(W)),\qquad
d_{23}(y(\mathfrak s(W)))=-3-d_{13}(y(W)),
\tag{4.14}
$$

where each side uses only its indicated triple. For example the
reflection of (2.2) sends its lower endpoint to $-3$ minus the
old upper endpoint, and conversely. Empty histories have the same
identity since $z=-3-z$. Thus the two branch losses in $W_a$
are $G/2,P/2$, respectively, and

$$
\mathbb E_{\Gamma_p,W_a}|T-a|
                  =\frac{pG+(1-p)P}{2}.
\tag{4.15}
$$

The maximum of (4.12) and (4.15) equals the upper bound (4.2).
Both worlds are complete and independent of the seed; for each
fixed $p$, choose the worse of these two fixed expected losses.
There is no seed-dependent selection of a worst world. If
$P>G$, $\max(p,1-p)$ has its unique minimum at $p=1/2$;
if $P=G$, all probabilities have the same risk. $\square$

**Theorem 4.2 (strict advantage over the entire deterministic adaptive class).**
On the domain

$$
c>0,\qquad \frac c3<E\le\frac{1+2c}{4},
\tag{4.16}
$$

put

$$
\delta(c,E)=\frac{c(3E-c)}{4(3+2c)(3+c)}>0.
\tag{4.17}
$$

Then

$$
\begin{gathered}
R_{\mathrm{ad},3}=P/2,\qquad
\frac G2\le R_{\mathrm{private}}
       \le\mathcal R(\Gamma_{1/2})=\frac{P+G}{4}
       =R_{\mathrm{ad},3}-\delta(c,E)<R_{\mathrm{ad},3},\\
\delta(c,E)\le R_{\mathrm{ad},3}-R_{\mathrm{private}}
                                      \le2\delta(c,E).
\end{gathered}
\tag{4.18}
$$

The certified interval for the unrestricted private minimax value
has positive width $\delta(c,E)$:

$$
0\le R_{\mathrm{private}}-G/2\le\delta(c,E).
\tag{4.19}
$$

In particular (4.19) does not assert that its left inequality is
strict, or that the family's attained value is the unrestricted value.

**Proof.** The exact deterministic value on (4.16) is
[Uniform Report Designs, Theorem 31.4](FIB_UNCALIBRATED_QUADRATIC_CLOCK_UNIFORM_REPORT_DESIGNS.md).
It quantifies over all total deterministic history functions,
including those choosing their indices adaptively from arbitrary
exact-real prefixes. The interval (4.16) is contained in (4.1),
because $(1+2c)/4<(1+c)/2$. Theorems 3.3 and 4.1 therefore
give the two private bounds in (4.18). By (4.4),

$$
\frac{P-G}{4}=\delta(c,E),\qquad
\frac P2-\frac G2=2\delta(c,E),
\tag{4.20}
$$

which proves every assertion.

The lower endpoint $E=c/3$, excluded only for strictness, has
$P=G=E$ and $R_{\mathrm{private}}=E/2$ by (3.4).
At the included upper endpoint $E=(1+2c)/4$,

$$
P=c/2,\qquad
G=\frac{c(5+2c)}{4(3+c)},\qquad
\delta=\frac{c}{16(3+c)}>0.
\tag{4.21}
$$

The complete worlds (4.5), (4.7), (4.9), (4.13) are still legal
at both endpoints: their origins lie in the closed prior, gains
are finite and at least $m$, and every original error is either
$0$ or $\pm\varepsilon$. No limiting or post-coin world is
needed. $\square$

## 5. Unrestricted domains and nontransferable lower certificates

**Definition 5.1 (remaining private minimax question).** For comparison
with the published deterministic classification, retain its constants

$$
\begin{gathered}
c_0=\frac{\sqrt{65}-7}{8},\qquad
q_c=\frac{3+2c+\sqrt{c(3+8c)}}{3+4c},\\
D(c)=
\begin{cases}
\dfrac{c(3+c)}{5+4c},&0<c\le c_0,\\[5pt]
\dfrac{c(3+c-q_c^2)}{3+2c},&c\ge c_0,
\end{cases}
\qquad
E_\star(c)=\frac{(1+c)D(c)}{c}.
\end{gathered}
\tag{5.1}
$$

The two displayed expressions for $D$ agree at $c_0$.
Uniform Report Designs, Sections 31--34, in particular Lemma 32.2,
Theorem 31.4, Corollary 32.6, Theorem 33.4 and Corollary 34.6,
with the wide-prior consequence in Section 34.7, give
$c/3<(1+c)/2<E_\star(c)<1+c$ and the complete deterministic
classification. In the private experiment, Theorem 3.3 together
with those existing results already gives

$$
R_{\mathrm{private}}=
\begin{cases}
\dfrac12\min(2E,c/3),&0\le E\le c/3,\\[4pt]
\dfrac{cE}{2(1+c)},&E\ge E_\star(c).
\end{cases}
\tag{5.2}
$$

These inherited exact regions follow respectively from $F=H$
and from the published deterministic-grid equality; they are not
additional origin-conditioned results. The unrestricted value is
left unresolved here on exactly the intermediate parameter domain

$$
c>0,\qquad c/3<E<E_\star(c).
\tag{5.3}
$$

On that domain the available quantitative conclusion is (3.4),
with the published deterministic value used in its upper bound.
On the subband (4.1) the particular family's exact value is (4.2),
including its upper endpoint $E=(1+c)/2$, where $G=Q=c/2$.
On (4.16) the unrestricted gap between the stated lower and upper
bounds is the explicit positive number (4.17). The remaining
question is to obtain a stronger fixed-pre-coin-world lower
argument, a better lawful strategy, or matching bounds on (5.3).
No reduction of the unrestricted infimum to finite mixtures is
part of that question's definition or of the conclusions above.

**Theorem 5.2 (scope of the lower arguments and of the finite-state comparison).**
The deterministic actual-prefix certificates of Uniform Report
Designs, Lemma 31.3, do not give a lower bound $P/2$ for all
private strategies in (4.16). The randomized value in
Recursive Relational Observation Affine Finite Reply Recovery,
Theorem 19.2, is not an instance of (1.5): both its observation
port and its retained-state restriction differ.

**Proof.** Lemma 31.3 supplies finitely many complete worlds and
selects a pair according to a deterministic strategy's branch.
After fixing a seed, the same conclusion may be applied, but its
selected pair can depend on that seed. If $L_k(\omega)$ denote
the losses on that finite set of worlds, the resulting assertion
has the form

$$
\forall\omega\quad \max_k L_k(\omega)\ge P/2.
\tag{5.4}
$$

Integration gives a bound on $\mathbb E\max_k L_k$, whereas
the required fixed-world assertion concerns $\max_k\mathbb E L_k$.
The inequality between these quantities goes in the other direction:
$\max_k\mathbb E L_k\le\mathbb E\max_k L_k$.
Theorem 4.2 moreover exhibits an admissible private strategy with
worst-world expected risk strictly below $P/2$, so the proposed
universal lower bound itself is false on (4.16). This does not
invalidate the original deterministic certificates. In contrast,
the full-grid pair in (3.5) is the same pair for every seed and
gives a pointwise sum inequality on its two fixed worlds, which
can be integrated as (3.6).

For the other comparison, see
[Recursive Relational Observation Affine Finite Reply Recovery, Definitions 19.1 and 19.3 and Theorem 19.2](RECURSIVE_RELATIONAL_OBSERVATION_AFFINE_FINITE_REPLY_RECOVERY.md).
Its source includes discrete deliveries $k_i$ satisfying
$|k_i/256-y_i|\le1/256$; the receiver acquires canonical finite
frames with those integer payloads, not exact-real $y_i$ ports.
It also has, for each receiver, a fixed finite complete usable
state space $Q$ at all handoffs. All future-usable records,
control, past random information and final operands factor
through $Q$; its final kernel depends on the last state and
public operands rather than an accessible full transcript.
Neither restriction is present in Definition 1.2. An arbitrary
private seed and every acquired exact-real history may remain
accessible here. Changing only memory would still leave the
quantized-port discrepancy, and changing only ports would still
leave the complete-finite-state discrepancy. The value $5/2$
from that different experiment therefore supplies no value for
(1.5). None of the proofs above invokes its finite-state lower
argument, a general Yao principle, or an unverified minimax
exchange. $\square$

## 追加锚（本行以下为增补区）

## 6. Tapered terminal budgets and a smaller private upper bound

**Definition 6.1 (taper and candidate-origin budgets).** Retain the
complete source, compatible sets and unrestricted strategy class of
Definitions 1.1--1.3. Throughout this section's strict band assume

$$
c>0,\qquad \frac c3<E\le\frac{1+c}{2}.
\tag{6.1}
$$

Define

$$
\begin{gathered}
\chi=P-G,\qquad \kappa=\frac{c}{c+6},\qquad
q=E-P,\qquad r=E-G,\\
h(x)=\min\{\chi,(r-x)_+\}\quad(0\le x\le E),\\
U_{\mathrm{new}}=\frac{P+G-\kappa\chi}{4}.
\end{gathered}
\tag{6.2}
$$

Here $(w)_+=\max(w,0)$. For $-E\le x\le E$ set

$$
\widehat\rho_{13}(z+x)=
\begin{cases}
G/2-\kappa h(-x),&-E\le x\le0,\\[2pt]
(P-\kappa\chi)/2+\kappa h(x),&0<x\le E,
\end{cases}
\qquad
\widehat\rho_{23}(t)=\widehat\rho_{13}(-3-t).
\tag{6.3}
$$

These are functions of a candidate origin in the compatible set.
In particular the center convention is the first line of (6.3)
for both designs; the true origin is not a receiver operand.

**Theorem 6.2 (joint-fiber compatibility of the tapered budgets).**
Under (6.1), every real history with $C=C_j\ne\varnothing$,
$j\in\{13,23\}$, satisfies

$$
|s-t|\le\widehat\rho_j(s)+\widehat\rho_j(t)
\qquad(s,t\in C).
\tag{6.4}
$$

All these budgets are positive and bounded. Consequently the interval

$$
\begin{aligned}
\widehat J_j(C)&=[\widehat L_j(C),\widehat U_j(C)],\\
\widehat L_j(C)&=\sup_{t\in C}(t-\widehat\rho_j(t)),\qquad
\widehat U_j(C)=\inf_{t\in C}(t+\widehat\rho_j(t))
\end{aligned}
\tag{6.5}
$$

is nonempty and bounded, and its midpoint $\widehat d_j$ obeys

$$
|\widehat d_j-t|\le\widehat\rho_j(t)\quad(t\in C).
\tag{6.6}
$$

Define $\widehat d_j=z$ when $C_j=\varnothing$. Thus the estimates
are total, finite-valued functions of their three acquired reports.

**Proof.** The identities (4.4) give $F=P$, $H=G$, and

$$
\begin{gathered}
\chi=\frac{c(3E-c)}{(3+2c)(3+c)}>0,\qquad
q=\frac{3E-c}{3+2c},\qquad
r=\frac{3E-c}{3+c},\\
0<q<r<E,\qquad r\le\frac12,\qquad r-q=\chi,\qquad
G=\frac{c(1+r)}3,\\
0<\kappa<1,\qquad
\frac c3-2\kappa=\frac{c^2}{3(c+6)}>0.
\end{gathered}
\tag{6.7}
$$

The bound $r\le1/2$ is equivalent to the included upper endpoint
condition in (6.1). The taper is nonincreasing and has Lipschitz
constant $1$, with

$$
h(x)=\chi\ (0\le x\le q),\qquad
h(x)=r-x\ (q\le x\le r),\qquad
h(x)=0\ (r\le x\le E).
\tag{6.8}
$$

The smallest possible budget in (6.3) is $G/2-\kappa\chi$.
It is positive because

$$
\begin{aligned}
G-2\kappa\chi
&=\frac c3+
  \left(\frac{3+2c}{3}-2\kappa\right)\chi\\
&=\frac c3+
  \frac{2c^2+9c+18}{3(c+6)}\chi>\frac c3.
\end{aligned}
\tag{6.9}
$$

Indeed $G-c/3=(3+2c)\chi/3$ by (4.4). The second line of
(6.3) is also at least this minimum, and every budget is at most
$(P+\kappa\chi)/2$.

We prove (6.4) first for $013$. The exact compatible-set and
joint-noise suppliers in Three-Index Design, Theorems 2.1 and 3.1,
as used in (2.5)--(2.6), give the following restrictions on pairs
in one $C_{13}$:

$$
\begin{gathered}
|s-t|\le P,\\
s,t\le z\ \Longrightarrow\ |s-t|\le G,\\
s\le z\le t\ \Longrightarrow\ t-s\le c/3.
\end{gathered}
\tag{6.10}
$$

A further local consequence of that same separation theorem is
essential here. If $z-y,z-x\in C_{13}$, with $0\le x<y\le E$
and $x<r$, then $x<r\le1/2$. Substitution of $u=1,v=3$
in its left coefficient gives $k_L(x)=3/(1+x)$, including
$k_L(0)=3$. The two compatible noiseless triples are within
$2\varepsilon=mc$ of one another in the original maximum norm.
Their minimum possible distance is $3m(y-x)/(1+x)$, so

$$
y-x\le\frac{c(1+x)}3
     =G-\frac c3(r-x).
\tag{6.11}
$$

The gains and offsets in this comparison are the finite witnesses
of membership in the same exact compatible set. Thus (6.11) uses
the joint original error cube, with no independent relaxation of
shared difference errors. The private `right_lower`, `lower` and
reflection suppliers of `QuadraticThreeIndexSeparation.lean`
are the corresponding fixed-pair separation ingredients identified
in Section 1; (6.11) is their ordinary-mathematical specialization.

Consider first two origins $z-y\le z-x\le z$ in $C_{13}$,
with $0\le x\le y\le E$. If $x\ge r$, both tapers vanish,
so the budget sum is $G$, sufficient by (6.10). If $x<r$,
put $w=r-x>0$. Monotonicity gives
$h(y)\le h(x)\le w$. For distinct origins, (6.11) and (6.7)
therefore give

$$
\begin{aligned}
\widehat\rho_{13}(z-x)+\widehat\rho_{13}(z-y)
 &=G-\kappa(h(x)+h(y))\\
 &\ge G-2\kappa w
 \ge G-\frac c3w
 \ge y-x.
\end{aligned}
\tag{6.12}
$$

Equal origins satisfy the desired inequality by positivity.

Next take $z<z+x\le z+y$ in $C_{13}$, with $0<x\le y\le E$.
If $x\le q$, then $h(x)=\chi$, and their budget sum is
$P+\kappa h(y)\ge P$, sufficient by (6.10). If $x>q$,
(6.8) gives $\chi-h(x)\le x-q$, while the prior gives
$y-x\le E-x=P-(x-q)$. Hence

$$
\begin{aligned}
\widehat\rho_{13}(z+x)+\widehat\rho_{13}(z+y)
 &=P-\kappa\chi+\kappa(h(x)+h(y))\\
 &\ge P-\kappa(x-q)
 \ge P-(x-q)
 \ge y-x.
\end{aligned}
\tag{6.13}
$$

For a pair with $s\le z<t$, each budget is at least
$G/2-\kappa\chi$. Equations (6.9)--(6.10) show that their
sum exceeds $c/3\ge t-s$. This also handles a point exactly
at the center with the stated center convention. These cases
exhaust $C_{13}$. Reflection (2.7) carries a compatible $023$
history to a compatible $013$ history and sends $t$ to $-3-t$.
Together with (6.3), it proves (6.4) for $023$. This is a relation
between fixed experiments, not a reversal of actual acquisition.

Finally apply the scalar budget-intersection argument of Theorem 2.1:
(6.4) implies $s-\widehat\rho_j(s)\le t+\widehat\rho_j(t)$
for every $s,t\in C$. Taking the supremum and infimum yields
$\widehat L_j\le\widehat U_j$. Their finiteness follows from
$C\subseteq[a,b]$ and the bounded budgets. Every point of
$\widehat J_j$ belongs to every interval
$[t-\widehat\rho_j(t),t+\widehat\rho_j(t)]$, proving (6.6).
The empty-set convention completes totality.

The regression-strip comparison is the one of
Casini--Garulli--Vicino, Section 4, equations (7)--(10), cited in
Section 1. The taper and its simultaneous inequalities (6.12)--(6.13)
are deductions from the exact origin fibers, rather than from
coordinate outer boxes. $\square$

**Definition 6.3 (a lawful strategy with tapered terminal rules).**
Under (6.1), let $\widehat\Gamma$ use the source-independent fair
seed space $\{13,23\}$ with its full power-set sigma-algebra.
For every real first report and every legal continuation history set

$$
f_{13}(r_0)=1,\qquad f_{23}(r_0)=2,\qquad
g_j(u,r_0,r_u)=3\quad(j\in\{13,23\}).
\tag{6.14}
$$

On terminal pair $(1,3)$ use $\widehat d_{13}$ from (6.5)--(6.6),
and on $(2,3)$ use $\widehat d_{23}$, for either seed. On pair
$(1,2)$ use the midpoint of $C_{12}$ when nonempty, and $z$ when
empty. These definitions apply also to histories and pairs unreachable
for a given seed. The constants $m,c,E$ and the functions in (6.2)--(6.3)
are public operands fixed independently of the source. At the separate
endpoint $E=c/3$, define $\widehat\Gamma$ instead to be the existing
$\Gamma_{1/2}$ of Definition 3.1.

**Theorem 6.4 (uniform fixed-world bound and exact strategy risk).**
For (6.1), $\widehat\Gamma$ is lawful under Definition 1.2, and
every complete world (1.2) satisfies

$$
\mathbb E_{\widehat\Gamma}|T-\tau|\le
\begin{cases}
U_{\mathrm{new}},&\tau\ne z,\\
G/2-\kappa\chi,&\tau=z.
\end{cases}
\tag{6.15}
$$

Its exact worst-world risk is

$$
\boxed{
\mathcal R(\widehat\Gamma)=U_{\mathrm{new}}
 =\frac{P+G}{4}-\frac{c(P-G)}{4(c+6)}
 =\frac G2+\frac{3(P-G)}{2(c+6)}.
}
\tag{6.16}
$$

At $E=c/3$ the endpoint rule has exact risk $E/2$.

**Proof.** The actual acquired triples are $013$ and $023$,
respectively, each consisting of exactly three increasing integer
reports. The continuation $3$ is legal also when $u=2$.
Theorem 6.2 and the compact-interval supplier for $C_{12}$ make
every terminal rule total with finite output, including empty and
unreachable histories. For each fixed complete world, all choices
and the answer are functions on a two-point power-set probability
space, hence measurable. This requires no measurability in the
world or regularity of history functions.

Fix any one complete $W$, with arbitrary finite $A\ge m$, finite
$B$, and all four original errors in the closed cube. Its true
origin belongs to each corresponding compatible set. Equation (6.6)
therefore bounds both branch losses in this same world. If
$x=|\tau-z|>0$, the two bounds, in an order determined by the
sign of $\tau-z$, are

$$
\frac{P-\kappa\chi}{2}+\kappa h(x),\qquad
\frac G2-\kappa h(x).
\tag{6.17}
$$

Their sum is $2U_{\mathrm{new}}$. At $\tau=z$, both budgets
equal $G/2-\kappa\chi$, which is at most $U_{\mathrm{new}}$
since their difference is $(1+3\kappa)\chi/4>0$. Averaging
proves (6.15) uniformly over all complete $W$. Each execution
uses only its own three acquired reports; the two bounds are
analytical statements about the one preselected four-error world.

For exactness use the complete world already given in (4.5):

$$
W_b=\bigl(b,m,-\varepsilon-mb^2,
       (\varepsilon,-\varepsilon,-\varepsilon,-\varepsilon)\bigr).
\tag{6.18}
$$

It is fixed before the seed. Its gain and offset are finite, its
origin lies in $K$, and all four displayed errors are legal.
The joint-fiber witnesses (4.7)--(4.11) give, for this very same
complete world,

$$
C_{13}(y(W_b))=[b-P,b]=[z+q,z+E],\qquad
C_{23}(y(W_b))=[b-G,b]=[z+r,z+E].
\tag{6.19}
$$

Here each history in (6.19) uses only the indicated triple.
The witnessing complete worlds $W_P,W_G$ have the finite gains
$m(1+2c/3),m(1+c/3)$ and the four legal errors displayed in
(4.7), (4.9). Their shared original-coordinate histories, the
diameter bound $P$, and the favorable-half bound $G$ identify
the entire intervals, as in Theorem 4.1.

On the first interval in (6.19), $q>0$, so the second line of
(6.3) applies throughout. The map
$x\mapsto x-\widehat\rho_{13}(z+x)$ is increasing on $[q,E]$.
The map $x\mapsto x+\widehat\rho_{13}(z+x)$ is also increasing:
for $x_1<x_2$, (6.8) bounds its increment below by
$(1-\kappa)(x_2-x_1)>0$. Since $h(q)=\chi$ and $h(E)=0$,
the two endpoints in (6.5) are therefore

$$
\begin{aligned}
\widehat L_{13}
 &=b-\frac{P-\kappa\chi}{2},\\
\widehat U_{13}
 &=b-P+\frac{P+\kappa\chi}{2}
  =b-\frac{P-\kappa\chi}{2}.
\end{aligned}
\tag{6.20}
$$

Thus the $013$ answer has loss $(P-\kappa\chi)/2$ at $b$.
On the second interval in (6.19), $x\in[r,E]$, so $h(x)=0$
and $\widehat\rho_{23}(z+x)=G/2$. Its budget intersection is
the singleton $\{b-G/2\}$, giving loss $G/2$. The fair expected
loss in the single world (6.18) is consequently

$$
\frac12\left(\frac{P-\kappa\chi}{2}+\frac G2\right)
 =U_{\mathrm{new}}.
\tag{6.21}
$$

Together with the uniform bound this proves (6.16). At the included
upper endpoint $E=(1+c)/2$, one has $r=1/2$; (6.11) uses the
closed near-separation branch, and the complete witnesses in (6.19)
remain legal. At $E=c/3$, $P=G=E$ and the separate existing
rule has risk $E/2$ by Theorem 4.1. $\square$

**Corollary 6.5 (improved unrestricted bound and surviving interval).**
On the unchanged source and the entire arbitrary-seed class of
Definition 1.2, for (6.1),

$$
\boxed{
\frac G2\le R_{\mathrm{private}}
 \le\min\{R_{\mathrm{ad},3},U_{\mathrm{new}}\}.
}
\tag{6.22}
$$

The strict improvement over the old fair-strategy risk and the
remaining width of the interval $[G/2,U_{\mathrm{new}}]$ are

$$
\frac{P+G}{4}-U_{\mathrm{new}}
 =\frac{c(P-G)}{4(c+6)}>0,\qquad
U_{\mathrm{new}}-\frac G2
 =\frac{3(P-G)}{2(c+6)}>0.
\tag{6.23}
$$

On the known deterministic-separation band
$c/3<E\le(1+2c)/4$, with $\delta(c,E)$ from (4.17),

$$
\begin{gathered}
0\le R_{\mathrm{private}}-G/2
 \le\frac{6}{c+6}\,\delta(c,E),\\
\frac{2(c+3)}{c+6}\,\delta(c,E)
 \le R_{\mathrm{ad},3}-R_{\mathrm{private}}
 \le2\delta(c,E).
\end{gathered}
\tag{6.24}
$$

At $E=c/3$, $R_{\mathrm{private}}=E/2$. Equation (6.16)
is exact for the particular strategy $\widehat\Gamma$;
(6.22)--(6.24) leave the unrestricted value unresolved on (6.1),
including whether it equals $G/2$. They do not reduce its infimum
to finite seed spaces. The broader intermediate question (5.3)
retains its original source and strategy quantifiers.

**Proof.** The all-seed lower bound of Theorem 3.3 uses the same
two complete full-grid worlds before every seed; $H=G$ on (6.1).
Theorem 6.4 supplies the new lawful upper bound, and one-point seed
spaces supply the deterministic upper bound. Subtraction gives
(6.23). On the narrower band, the already known deterministic value
is $P/2$ by Uniform Report Designs, Theorem 31.4, and
$\delta=(P-G)/4$ by (4.20). Thus the new certified width is
$6/(c+6)$ times the old width, and the distance from $P/2$ to
$U_{\mathrm{new}}$ is $(1+\kappa)\delta
=2(c+3)\delta/(c+6)$, proving (6.24). The endpoint follows
from Theorems 3.3 and 4.1. No lower-bound argument here averages
a seed-dependent selection of different complete worlds, or invokes
the linear-target/product-measurability comparisons of
Krieg--Novak--Ullrich, Sections 1--2, cited in Section 1. $\square$

## 追加锚（本行以下为增补区）

## 7. Stronger joint-fiber budgets and an unrestricted exact region

**Definition 7.1 (coefficient and terminal budgets).** Use exactly
the complete worlds and private strategies of Definitions 1.1--1.2.
For every $m>0$, $c>0$ and
$c/3<E\le(1+c)/2$, retain $P,G$ from (1.8) and
$\chi,q,r,h$ from (6.2), and put

$$
\gamma=\frac c3,\qquad
\alpha=\min\{1,\gamma\},\qquad
V=\frac G2+\frac{(1-\alpha)\chi}{4}
 =\frac{P+G-\alpha\chi}{4}.
\tag{7.1}
$$

For $-E\le x\le E$ define candidate-origin budgets

$$
\rho^\alpha_{13}(z+x)=
\begin{cases}
G/2-\alpha h(-x),&-E\le x\le0,\\[2pt]
(P-\alpha\chi)/2+\alpha h(x),&0<x\le E,
\end{cases}
\qquad
\rho^\alpha_{23}(t)=\rho^\alpha_{13}(-3-t).
\tag{7.2}
$$

As in (6.3), the center belongs to the first case for each design.
Only candidate origins in the compatible set are arguments of these
budgets; the unknown true origin is not an acquired-history operand.

**Theorem 7.2 (joint-fiber compatibility at the larger coefficient).**
For $m>0$, $c>0$ and $c/3<E\le(1+c)/2$, every real
three-report history with $C=C_j\ne\varnothing$,
$j\in\{13,23\}$, has budgets (7.2) that
are positive and bounded, and satisfy

$$
|s-t|\le\rho^\alpha_j(s)+\rho^\alpha_j(t)
\qquad(s,t\in C).
\tag{7.3}
$$

Consequently the interval and answer

$$
\begin{aligned}
J^\alpha_j(C)&=[L^\alpha_j(C),U^\alpha_j(C)],\\
L^\alpha_j(C)&=\sup_{t\in C}(t-\rho^\alpha_j(t)),\qquad
U^\alpha_j(C)=\inf_{t\in C}(t+\rho^\alpha_j(t)),\\
d^\alpha_j(C)&=\frac{L^\alpha_j(C)+U^\alpha_j(C)}2
\end{aligned}
\tag{7.4}
$$

are well defined and finite, with $J^\alpha_j(C)\ne\varnothing$ and

$$
|d^\alpha_j(C)-t|\le\rho^\alpha_j(t)\qquad(t\in C).
\tag{7.5}
$$

For an empty compatible set set $d^\alpha_j=z$.

**Proof.** The identities (4.4), (6.7) and (6.8) give

$$
\begin{gathered}
0<q<r<E,\qquad r\le\frac12,\qquad r-q=\chi>0,\\
G=\gamma(1+r)=\gamma+(1+2\gamma)\chi,\qquad
0<\alpha\le1,\qquad \alpha\le\gamma.
\end{gathered}
\tag{7.6}
$$

In particular every budget in (7.2) is at least
$G/2-\alpha\chi$ and at most $(P+\alpha\chi)/2$, since
the smallest second-case budget exceeds $G/2-\alpha\chi$ by
$(1+\alpha)\chi/2$. Moreover,

$$
G-2\alpha\chi
 =\gamma+(1+2\gamma-2\alpha)\chi
 \ge\gamma+\chi>\gamma>0.
\tag{7.7}
$$

This proves positivity and boundedness.

For $013$ use the full-prior, favorable-half and cross-center
restrictions (6.10), supplied by Three-Index Design, Theorems 2.1
and 3.1. Its local original-coordinate restriction (6.11) says
that if $z-y,z-x$ belong to this same fiber, $0\le x<y\le E$
and $x<r$, then, with $d=y-x$ and $w=r-x$,

$$
d\le\frac{c(1+x)}3=G-\gamma w.
\tag{7.8}
$$

Indeed $0\le x<r\le1/2$ puts $k_L(x)=3/(1+x)$ in the
near branch of the exact separation theorem for $u=1,v=3$.
The two compatible noiseless triples differ by at most $mc$
in the original maximum norm. Their exact minimum distance is
$3md/(1+x)$, which gives (7.8), including $x=0$.
This uses jointly compatible gains, offsets and original errors;
no independent box for difference errors is used.

Take first $z-y\le z-x\le z$ in $C_{13}$. Equal origins
satisfy (7.3) by positivity. If $x\ge r$, both tapers vanish,
so their radius sum is $G$, sufficient by (6.10). Suppose
$x<r$ and $d>0$. If $d\le\chi$, then $h(x),h(y)\le\chi$
and (7.6) imply

$$
d+\alpha(h(x)+h(y))
 \le(1+2\alpha)\chi
 \le(1+2\gamma)\chi=G-\gamma<G.
\tag{7.9}
$$

If $d\ge\chi$, the two tapers instead satisfy

$$
h(x)+h(y)
 =\min\{\chi,w\}+\min\{\chi,(w-d)_+\}\le w.
\tag{7.10}
$$

For $w\le\chi$ the first term is $w$ and the second is zero,
because $d\ge\chi\ge w$. For $w>\chi$ the first term is
$\chi$, and $(w-d)_+\le w-\chi$. These two cases prove
(7.10). Using (7.8) and $\alpha\le\gamma$ now gives

$$
d+\alpha(h(x)+h(y))
 \le G-\gamma w+\alpha w\le G.
\tag{7.11}
$$

Both (7.9) and (7.11) are precisely
$d\le G-\alpha(h(x)+h(y))$, the required radius sum for
these two origins. The separation by $d\le\chi$ or $d\ge\chi$
is what permits the coefficient in (7.1).

For two origins $z<z+x\le z+y$ in $C_{13}$, if $x\le q$,
then $h(x)=\chi$, so their radius sum is
$P+\alpha h(y)\ge P\ge y-x$. If $x>q$, (6.8) gives
$\chi-h(x)\le x-q$, while the prior gives $y-x\le E-x$.
Thus

$$
\begin{aligned}
\rho^\alpha_{13}(z+x)+\rho^\alpha_{13}(z+y)
 &=P-\alpha\chi+\alpha(h(x)+h(y))\\
 &\ge P-\alpha(x-q)
 \ge P-(x-q)=E-x\ge y-x.
\end{aligned}
\tag{7.12}
$$

Here $\alpha\le1$ is used in the second inequality.
For $s\le z<t$, (6.10) bounds $t-s$ by $\gamma$,
whereas (7.7) bounds the two radii's sum below by
$G-2\alpha\chi>\gamma$. The convention at $z$ is therefore
also covered. These cases prove (7.3) on every $013$ fiber.
The exact complete-source reflection (2.7) and (7.2) prove it
on every $023$ fiber. Reflection relates fixed experiments;
it is not an acquisition operation.

The scalar budget-intersection argument of Theorem 2.1 applies
to (7.3): every $s-\rho^\alpha_j(s)$ is at most every
$t+\rho^\alpha_j(t)$. Its supremum is therefore at most their
infimum. The nonempty compatible set lies in the bounded prior,
and the budgets are bounded, so both endpoints in (7.4) are
finite. Every point of their interval belongs to every
$[t-\rho^\alpha_j(t),t+\rho^\alpha_j(t)]$, giving (7.5).
The empty-set convention completes totality. The fixed-pair
separation, reflection and scalar-intersection ingredients are
the suppliers already identified in Sections 1--2 and 6;
(7.9)--(7.11) supply the stronger joint-fiber estimate.
$\square$

**Definition 7.3 (acquired-history strategy).** Let $\Gamma^\alpha$
use the source-independent fair seed space $\{13,23\}$ with its
power-set sigma-algebra and the total acquisition functions (6.14).
On terminal pairs $(1,3)$ and $(2,3)$, for either seed, use
$d^\alpha_{13}$ and $d^\alpha_{23}$ from (7.4), respectively,
formed solely from that pair's three acquired reports.
On terminal pair $(1,2)$ use the midpoint of $C_{12}$ when
nonempty, and $z$ when empty. These rules apply on every real
history, including histories unreachable under that seed.
All parameters in (7.1)--(7.2) are public and independent of $W$.
At $E=c/3$ use the existing $\Gamma_{1/2}$ of Definition 3.1.

**Theorem 7.4 (fixed-complete-world upper bound and exact strategy risk).**
For $m>0$, $c>0$ and $c/3<E\le(1+c)/2$,
$\Gamma^\alpha$ is lawful under Definition 1.2. Every complete
world of (1.2), with all its original errors fixed before the seed,
satisfies

$$
\mathbb E_{\Gamma^\alpha}|T-\tau|
 \le
 \begin{cases}
 V,&\tau\ne z,\\
 G/2-\alpha\chi,&\tau=z,
 \end{cases}
 \qquad
 \boxed{\mathcal R(\Gamma^\alpha)=V.}
\tag{7.13}
$$

At $E=c/3$ the specified endpoint rule has exact risk $E/2$.

**Proof.** The acquisition functions (6.14) read exactly $013$
or $023$, each consisting of three actual increasing integer
indices. Their second continuation is $3$ on every legal
history, also when the first continuation is $2$.
Theorem 7.2 gives total finite terminal rules for both these
pairs. The compact-interval supplier for $C_{12}$ in Definition
1.3 gives the same property on the unused pair. Thus empty and
unreachable histories have total finite answers. For each fixed
complete world, the actual indices and answer are maps on the
two-point power-set probability space, hence measurable. No world
measurability or history regularity is required.

Fix one complete $W$. Its gain is any finite $A\ge m$,
its offset is any $B\in\mathbb R$, and its four original errors
are any fixed member of the closed cube in (1.2).
Its true origin belongs to each corresponding compatible set.
For $x=|\tau-z|>0$, (7.5) bounds the two branch losses, in the
appropriate order for the sign of $\tau-z$, by

$$
\frac{P-\alpha\chi}{2}+\alpha h(x),
 \qquad \frac G2-\alpha h(x).
\tag{7.14}
$$

Their fair average is $V$. At $\tau=z$ both budgets are
$G/2-\alpha\chi$, smaller than $V$ by
$(1+3\alpha)\chi/4$. This proves the uniform bound using both
losses in the same complete world. Each execution uses only its
own acquired history.

For attainment reuse the complete world $W_b$ of (4.5), with its
gain $m$, finite offset, origin $b$ and all four displayed original
errors fixed before the seed. The original-coordinate witnesses
(4.7)--(4.11) give exactly the fibers (6.19). On its $013$ fiber,
$x=t-z$ runs over $[q,E]$, which is strictly positive.
On this interval
$x\mapsto x-\rho^\alpha_{13}(z+x)$ is nondecreasing because
$h$ is nonincreasing. The map
$x\mapsto x+\rho^\alpha_{13}(z+x)$ is also nondecreasing:
for $x_1<x_2$ its increment is at least
$(1-\alpha)(x_2-x_1)\ge0$ by the Lipschitz bound in (6.8).
Strict monotonicity is unnecessary, so this includes $\alpha=1$.
With $h(q)=\chi$ and $h(E)=0$, (7.4) consequently gives

$$
\begin{aligned}
L^\alpha_{13}
 &=b-\frac{P-\alpha\chi}{2},\\
U^\alpha_{13}
 &=b-P+\frac{P+\alpha\chi}{2}
  =b-\frac{P-\alpha\chi}{2}.
\end{aligned}
\tag{7.15}
$$

The $013$ answer therefore has loss $(P-\alpha\chi)/2$.
On the same world's $023$ fiber, $x\in[r,E]$ and $h(x)=0$,
so $\rho^\alpha_{23}(z+x)=G/2$ throughout. The fiber is
$[b-G,b]$, and its budget intersection is the singleton
$\{b-G/2\}$. This branch's loss is $G/2$. Thus this one
complete world has expected loss
$(P-\alpha\chi+G)/4=V$, proving exactness in (7.13).

At the included upper endpoint $E=(1+c)/2$, one has $r=1/2$;
the near-branch separation used in (7.8) and the finite original
witnesses (4.7)--(4.11) remain valid. The cases $x=q,r,E$ in
the taper are closed in (6.8), so no additional endpoint convention
is needed. At $E=c/3$, the reused endpoint rule has risk $E/2$
by Theorem 4.1. $\square$

**Theorem 7.5 (unrestricted improvement and a matching region).**
On exactly the source and arbitrary-seed class of Definitions
1.1--1.2, for every $m>0$, $c>0$ and
$c/3<E\le(1+c)/2$,

$$
\boxed{
\frac G2\le R_{\mathrm{private}}
 \le\min\{R_{\mathrm{ad},3},V\},\qquad
V=\frac G2+\frac{(1-\min\{1,c/3\})(P-G)}4.
}
\tag{7.16}
$$

On this entire strict band $V<U_{\mathrm{new}}$.
Wherever $U_{\mathrm{new}}\le R_{\mathrm{ad},3}$,
(7.16) strictly improves the upper bound in (6.22).
In particular this holds on the nonempty band
$c/3<E\le(1+2c)/4$ for every $c>0$.
For $c\ge3$, including $c=3$, the unrestricted value is

$$
\boxed{
R_{\mathrm{private}}(c,E)=\frac G2
 =\frac{c(1+E)}{2(3+c)}
 \quad\left(\frac c3\le E\le\frac{1+c}{2}\right).
}
\tag{7.17}
$$

The endpoint $E=c/3$ has the already known value $E/2$ for
every $c>0$. For $0<c<3$ the remaining certified width on the
strict band is

$$
0\le R_{\mathrm{private}}-\frac G2
 \le\frac{(3-c)(P-G)}{12}.
\tag{7.18}
$$

**Proof.** Theorem 3.3 applies to every permitted seed probability
space and supplies the lower bound $H/2=G/2$ on this band.
Its same two complete legal full-grid worlds are fixed before
every seed; the original pointwise sum inequality (3.5) is
integrable using only per-world measurability. Theorem 7.4
supplies a lawful upper strategy, and one-point seed spaces
still supply the upper bound $R_{\mathrm{ad},3}$. This proves
(7.16) for the whole competitor class.

With $\kappa=c/(c+6)$ as in Section 6, one has
$\alpha>\kappa$: if $c\le3$, $c/3>c/(c+6)$, and if
$c\ge3$, $1>c/(c+6)$. Therefore

$$
U_{\mathrm{new}}-V
 =\frac{(\alpha-\kappa)\chi}{4}>0.
\tag{7.19}
$$

When the old upper bound is active, its value is
$U_{\mathrm{new}}$, and
$\min\{R_{\mathrm{ad},3},V\}\le V<U_{\mathrm{new}}$.
On the specified narrower band, Uniform Report Designs,
Theorem 31.4, gives $R_{\mathrm{ad},3}=P/2$ and

$$
\frac P2-U_{\mathrm{new}}
 =\frac{(1+\kappa)\chi}{4}>0.
\tag{7.20}
$$

That band has positive length
$(1+2c)/4-c/3=(3+2c)/12$, and its upper endpoint is included.
This verifies strict improvement on a nonempty active-bound
domain without requiring a classification of every active domain.

For $c\ge3$ one has $\alpha=1$, so (7.16) matches the
unrestricted lower bound, proving (7.17) on the strict band.
At $E=c/3$, $P=G=E$, and the inherited endpoint result
completes its closed lower boundary. For $0<c<3$,
$\alpha=c/3$, and subtraction gives (7.18).
The threshold $c\ge3$ is sufficient for this matching argument;
no necessity assertion about that threshold follows.

The comparison literature remains exactly scoped as in Section 1:
Krieg--Novak--Ullrich, Sections 1--2, concerns a linear target and
a class with additional product measurability, and
Casini--Garulli--Vicino, Section 4, equations (7)--(10), supplies
regression strips rather than this nonlinear target's minimax value.
The deductions (7.9)--(7.19) use the cited repository separation,
joint fibers, scalar feasibility and complete-world witnesses.

For $0<c<3$ and $c/3<E\le(1+c)/2$, (7.18) has positive
right-hand width; it determines no unrestricted equality there.
For every $c>0$ the intermediate domain
$(1+c)/2<E<E_\star(c)$ from Definition 5.1 also remains beyond
this matching argument. In that domain $r>1/2$, so (7.8) is no
longer supplied on all of the tapered region by the same
near-separation branch. Determining these remaining values requires
stronger lawful fixed-world upper or lower estimates on the original
class. The inherited exact regions (5.2) remain available.
The two-point seed used to construct $\Gamma^\alpha$ gives no
reduction of the unrestricted infimum to finite seeds; unrestricted
equality in (7.17) follows from matching an upper strategy to the
arbitrary-seed lower certificate. $\square$

## 追加锚（本行以下为增补区）

## 8. Outside-band budgets and further unrestricted exact regions

**Definition 8.1 (outside-band coefficient and budgets).** Retain
exactly the complete source, exact-real ports, full acquired histories
and arbitrary-seed competitor class of Definitions 1.1--1.3. Fix
$m>0$, $c>0$ and

$$
\frac{1+c}{2}\le E<1+c.
\tag{8.1}
$$

Keep $P=c(1+2E)/(3+2c)$ and $Q=cE/(1+c)$, and define

$$
\begin{gathered}
\chi_o=P-Q,\qquad q_o=E-P,\qquad r_o=E-Q=\frac{E}{1+c},\\
\beta=c\left(1-\frac{1+c}{3E}\right)
      =c\left(1-\frac{1}{3r_o}\right),\qquad
\vartheta=\min\{1,\beta\},\qquad \gamma=\frac c3,\\
h_o(x)=\min\{\chi_o,(r_o-x)_+\}\quad(0\le x\le E),\\
V_o=\frac Q2+\frac{(1-\vartheta)\chi_o}{4}
   =\frac{P+Q-\vartheta\chi_o}{4}.
\end{gathered}
\tag{8.2}
$$

On candidate origins, rather than as additional receiver inputs, put

$$
\rho^o_{13}(z+x)=
\begin{cases}
Q/2-\vartheta h_o(-x),&-E\le x\le0,\\[2pt]
(P-\vartheta\chi_o)/2+\vartheta h_o(x),&0<x\le E,
\end{cases}
\qquad
\rho^o_{23}(t)=\rho^o_{13}(-3-t).
\tag{8.3}
$$

The center uses the first case for both designs.

The feasible strip intersection in (1.6)--(1.7) has the mathematical
correspondence in Casini--Garulli--Vicino,
[*A linear programming approach to online set membership parameter estimation for linear regression models*, Section 4, equations (7)--(10)](https://control.dii.unisi.it/~casini/pdf/IJACSP_2017a.pdf),
with known regressors and componentwise bounded additive errors.
Here the regressor is $(i^2,i,1)$, the coefficient vector is
$(A,2A\tau,A\tau^2+B)$ and the error bound is $\varepsilon$.
Coordinate bounding orthotopes do not supply the nonlinear target
$\tau=\theta_1/(2\theta_2)$ or the estimate (8.10).

**Theorem 8.2 (joint compatibility across both separation branches).**
For every parameter in (8.1), the budgets (8.3) are positive and
bounded. Every nonempty exact compatible set $C=C_j(r)$, for
$j\in\{13,23\}$ and any real triple $r$, satisfies

$$
|s-t|\le\rho^o_j(s)+\rho^o_j(t)\qquad(s,t\in C).
\tag{8.4}
$$

Thus the following interval is nonempty and has finite endpoints:

$$
\begin{aligned}
J^o_j(C)&=[L^o_j(C),U^o_j(C)],\\
L^o_j(C)&=\sup_{t\in C}(t-\rho^o_j(t)),\qquad
U^o_j(C)=\inf_{t\in C}(t+\rho^o_j(t)),\\
d^o_j(C)&=\frac{L^o_j(C)+U^o_j(C)}2,
\qquad |d^o_j(C)-t|\le\rho^o_j(t)\quad(t\in C).
\end{aligned}
\tag{8.5}
$$

For an empty compatible set define $d^o_j=z$.

**Proof.** First check the suppliers' parameter ranges and the
active diameter candidates. On (8.1), $3E>c$ and

$$
\begin{gathered}
P-Q=\frac{c(1+c-E)}{(3+2c)(1+c)}>0,\qquad
Q-G=\frac{c(2E-1-c)}{(1+c)(3+c)}\ge0,\\
Q\ge\frac c2>\frac c3,\qquad P<E,\qquad Q<E.
\end{gathered}
\tag{8.6}
$$

The separation and finite-attainment formulas are those of
[Three-Index Design, Theorems 2.1, 3.1 and 18.2](FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN.md).
The scalar feasibility and compact-interval correspondences are in
[Self-Calibrating Relation Mathematics II, Sections 80--81](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md).

Consequently the fixed-design and full-grid formulas in (1.8)
give $F=P$, $H=Q$, without prior truncation. The exact
three-coordinate supplier, Three-Index Design, Theorems 2.1--3.1,
applies with $u=1,v=3$, $a=z-E<b=z+E$, gain lower bound $m$
and original error bound $\varepsilon=mc/2$. Its full-prior,
left-half and cross-center consequences, as in (2.5)--(2.6), are

$$
\begin{gathered}
|s-t|\le P\quad(s,t\in C_{13}),\\
s,t\le z\ \Longrightarrow\ |s-t|\le Q,\qquad
s\le z\le t\ \Longrightarrow\ t-s\le\gamma.
\end{gathered}
\tag{8.7}
$$

For the left-half statement its five candidates are
$c/3,c/(3+2c),0,G,Q$, and the half-prior length is $E$;
(8.6) verifies the stated upper bound $Q$ directly.

The new local estimate uses both closed branches of that separation
supplier. Let $z-y,z-x\in C_{13}$ with $0\le x<y\le E$,
$x<r_o$, and set $d=y-x$. Their compatible noiseless triples
are within $2\varepsilon=mc$ in the original maximum norm.
For this ordered origin pair the exact separation is $md k_L(x)$,
where, at $u=1,v=3$,

$$
k_L(x)=
\begin{cases}3/(1+x),&0\le x\le1/2,\\1/x,&x\ge1/2.
\end{cases}
\quad\Longrightarrow\quad
 d\le
\begin{cases}c(1+x)/3,&0\le x\le1/2,\\cx,&x\ge1/2.
\end{cases}
\tag{8.8}
$$

Both expressions agree at $x=1/2$; the first includes $x=0$.
Every finite compatible gain and offset is allowed in this
comparison. It is a restriction on two members of one exact fiber,
with the original independent-coordinate cube, not a relaxation
into independent difference errors.

Since $1/2\le r_o<1$, the identities

$$
Q=cr_o=\gamma+\beta r_o,\qquad
\gamma\le\beta<c,\qquad 0<\vartheta\le1,\quad\vartheta\le\beta
\tag{8.9}
$$

hold. For $0\le x\le1/2$, subtracting the first bound in
(8.8) from $Q-\beta(r_o-x)=\gamma+\beta x$
gives $(\beta-\gamma)x\ge0$. For $1/2\le x<r_o$,
subtracting $cx$ gives $(c-\beta)(r_o-x)\ge0$.
Thus throughout the required taper support,

$$
d\le Q-\beta(r_o-x)\qquad(0\le x<r_o).
\tag{8.10}
$$

In particular no near-branch formula is extrapolated beyond its
junction.

The taper identities are

$$
\begin{gathered}
\chi_o=\frac{c(1-r_o)}{3+2c},\qquad
0<q_o=r_o-\chi_o<r_o<E,\\
h_o(x)=\chi_o\ (0\le x\le q_o),\quad
h_o(x)=r_o-x\ (q_o\le x\le r_o),\quad
h_o(x)=0\ (r_o\le x\le E).
\end{gathered}
\tag{8.11}
$$

Here $q_o>0$ also follows from $P<E$ in (8.6).
Moreover $\chi_o<\gamma$ and $2\chi_o<r_o$: the latter follows
from $2c/(3+2c)<1$ and $1-r_o\le r_o$. Hence

$$
Q-2\vartheta\chi_o
\ge\gamma+\beta(r_o-2\chi_o)>\gamma>\chi_o>0.
\tag{8.12}
$$

Every radius in (8.3) is at least $Q/2-\vartheta\chi_o$
and at most $(P+\vartheta\chi_o)/2$. This proves positivity
and boundedness.

For two origins $z-y\le z-x\le z$ in $C_{13}$, let
$d=y-x\ge0$. If $x\ge r_o$, the radius sum is $Q$, sufficient
by (8.7). If $x<r_o$ and $d\le\chi_o$, its radius sum is at
least $Q-2\vartheta\chi_o>\chi_o\ge d$ by (8.12).
In the remaining case put $w=r_o-x>0$, $d\ge\chi_o$.
The elementary taper inequality (7.10), with these parameters, is

$$
h_o(x)+h_o(y)
=\min\{\chi_o,w\}+\min\{\chi_o,(w-d)_+\}\le w.
\tag{8.13}
$$

Indeed for $w\le\chi_o$ the second term vanishes; for
$w>\chi_o$ it is at most $w-\chi_o$. Therefore (8.10) gives

$$
d+\vartheta(h_o(x)+h_o(y))
\le Q-\beta w+\vartheta w\le Q,
\tag{8.14}
$$

exactly the required inequality for these two budgets.

For two origins $z<z+x\le z+y$ in $C_{13}$, if $x\le q_o$
then $h_o(x)=\chi_o$ and their radius sum is
$P+\vartheta h_o(y)\ge P\ge y-x$. If $x>q_o$, (8.11)
gives $\chi_o-h_o(x)\le x-q_o$, and consequently

$$
\begin{aligned}
\rho^o_{13}(z+x)+\rho^o_{13}(z+y)
&=P-\vartheta\chi_o+\vartheta(h_o(x)+h_o(y))\\
&\ge P-\vartheta(x-q_o)
 \ge P-(x-q_o)=E-x\ge y-x.
\end{aligned}
\tag{8.15}
$$

For $s\le z<t$, (8.7) gives $t-s\le\gamma$, whereas
(8.12) bounds the radius sum strictly above $\gamma$.
This includes the center convention. Equal origins are covered by
positivity. The complete-source reflection (2.7) carries $023$
fibers to $013$ fibers and exchanges the budgets in (8.3), proving
(8.4) for the other design without changing acquisition rights.
Finally (8.4) implies $s-\rho^o_j(s)\le t+\rho^o_j(t)$ for all
$s,t\in C$. Supremum and infimum give $L^o_j\le U^o_j$;
boundedness of $C\subseteq K$ and of the budgets gives finite
endpoints. Every point of $J^o_j$ belongs to every interval
$[t-\rho^o_j(t),t+\rho^o_j(t)]$, proving (8.5). $\square$

**Definition 8.3 (total three-reading rule).** Let $\Gamma^o$ have
the source-independent fair seed space $\{13,23\}$ with its
power-set sigma-algebra. For every real history use
$f_{13}(r_0)=1$, $f_{23}(r_0)=2$, and
$g_j(u,r_0,r_u)=3$ for both seeds and both legal values of $u$.
For either seed, on terminal pair $(1,3)$ output $d^o_{13}$ from
(8.5) using only $(r_0,r_1,r_3)$; on pair $(2,3)$ output
$d^o_{23}$ using only $(r_0,r_2,r_3)$. On pair $(1,2)$ output
the midpoint of $C_{12}$ if nonempty, and $z$ otherwise.
The rules include every legal real history, including unreachable
ones. All constants depend only on the public $m,c,E$.

The chronological acquisition order is that of
[Three-Index Design, Definition 23.1](FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN.md),
with the complete worlds and parameters of Definitions 1.1--1.2.

**Theorem 8.4 (outside-band unrestricted quantitative bound).**
For every $m>0$, $c>0$ and $(1+c)/2\le E<1+c$, on exactly
Definitions 1.1--1.2,

$$
\boxed{
\frac Q2\le R_{\mathrm{private}}(c,E)
\le\min\left\{R_{\mathrm{ad},3}(c,E),
 \frac Q2+
 \frac{\bigl(1-\min\{1,c(1-(1+c)/(3E))\}\bigr)(P-Q)}4
\right\}.
}
\tag{8.16}
$$

The upper strategy $\Gamma^o$ bounds its two analytical branch
losses in each one complete world; the lower bound holds against
every permitted arbitrary seed space.

The worst-input expected-error order agrees with Krieg--Novak--Ullrich,
[*On the power of adaption and randomization*, Sections 1--2](https://arxiv.org/html/2406.07108v2).
Their comparisons assume a continuous linear target and a randomized
class with product-measurable loss. Augmenting this clock's input by
its errors makes the reports linear, while the target remains a ratio
and only per-complete-world seed measurability is imposed here.
Those comparison theorems do not directly apply to this strategy class.

**Proof.** Each seed of $\Gamma^o$ actually reads exactly $013$
or $023$, in increasing integer order. Continuation $3$ is legal
for either $u$. Theorem 8.2 supplies finite total estimates for
these two terminal pairs. For the unused pair $012$, the compact
interval supplier is Three-Index Design, Theorem 3.1, with
$u=1,v=2$, the same nondegenerate prior and original error bound;
its positive-denominator feasible set gives finite endpoints.
The empty-set conventions give finite answers on every remaining
history. Indices and answers are measurable in each fixed world
because the seed space is finite with its power-set sigma-algebra.
No regularity of history functions or measurability in the world
is used.

Fix one arbitrary complete $W=(\tau,A,B,\eta)$ satisfying (1.2).
Its finite $A\ge m$, finite $B$ and all four errors, including
unread coordinates, remain fixed for both seed evaluations.
The true $\tau$ belongs to both corresponding exact compatible
sets. If $x=|\tau-z|>0$, (8.5) bounds the two losses, in the
order determined by the sign of $\tau-z$, by

$$
\frac{P-\vartheta\chi_o}{2}+\vartheta h_o(x),
\qquad \frac Q2-\vartheta h_o(x).
\tag{8.17}
$$

Their fair average is $V_o$. At $\tau=z$ both are bounded by
$Q/2-\vartheta\chi_o\le V_o$, since the difference is
$(1+3\vartheta)\chi_o/4>0$. Thus
$\mathcal R(\Gamma^o)\le V_o$ uniformly on the whole source.
The other triple in (8.17) is only an analytical evaluation of
this same complete world; neither execution acquires its missing
coordinate.

For the unrestricted lower bound reuse the full-grid witness of
Uniform Report Designs, (32.23) and (34.36), explicitly completed
in the original four coordinates. With $t=b$, $s=b-Q=z+r_o$,
put

$$
\begin{aligned}
W_s&=(s,m(1+c),\varepsilon-m(1+c)s^2,
                 (-\varepsilon,\varepsilon,\varepsilon,-\varepsilon)),\\
W_t&=(t,m,-\varepsilon-mt^2,
                 (\varepsilon,-\varepsilon,-\varepsilon,\varepsilon)).
\end{aligned}
\tag{8.18}
$$

Because $0<Q<E$, both origins lie in $K$; all gains, offsets
and four errors are finite and legal. Both worlds depend only on
$m,c,E$. The difference of their noiseless reports is
$mc(i^2-3i+1)$, taking the values $mc,-mc,-mc,mc$ at
$0,1,2,3$, exactly canceled by their error difference.
Thus their complete four-report vectors coincide.

Fix any admissible strategy on any source-independent seed space.
For each seed its deterministic history functions see the same
$y_0$ in these two fixed worlds, select the same $u$, see the
same next report, select the same $v$, and see the same last
report. Their finite answers are therefore equal, say $T_\omega$.
Pointwise in the seed,

$$
|T_\omega-s|+|T_\omega-t|\ge t-s=Q.
\tag{8.19}
$$

Both loss maps are measurable by the stipulated per-world
hypothesis. Additivity of nonnegative integrals yields a sum of
the two fixed-world expected losses at least $Q$, even if one
is infinite. At least one is at least $Q/2$, proving the lower
bound before taking the infimum over the full strategy class.
The same complete pair is used for every seed; no branchwise
choice of witnesses is averaged. Finally every total deterministic
strategy is admissible on a one-point seed space, so
$R_{\mathrm{private}}\le R_{\mathrm{ad},3}$. Together with the
upper strategy this proves (8.16), without a minimax exchange,
world probability law, compactness reduction of strategies or
normal-form assumption. $\square$

**Theorem 8.5 (matching region and all finite priors for $c\ge3$).**
On (8.1), $\beta\ge1$ is sufficient for
$R_{\mathrm{private}}=Q/2$. Its exact parameter description is

$$
\begin{cases}
c\ge3,&(1+c)/2\le E<1+c,\\[2pt]
3/2<c<3,&\displaystyle
 \frac{c(1+c)}{3(c-1)}\le E<1+c.
\end{cases}
\tag{8.20}
$$

For $0<c\le3/2$ there are no points of (8.1) with
$\beta\ge1$. Combining inherited exact regions gives, for every
$c\ge3$ and every finite $E\ge0$,

$$
\boxed{
R_{\mathrm{private}}(c,E)=\frac H2=
\begin{cases}
\frac12\min\{2E,c/3\},&0\le E\le c/3,\\[3pt]
\dfrac{c(1+E)}{2(3+c)},&c/3\le E\le(1+c)/2,\\[5pt]
\dfrac{cE}{2(1+c)},&E\ge(1+c)/2.
\end{cases}}
\tag{8.21}
$$

**Proof.** If $\beta\ge1$, then $\vartheta=1$ and both
sides of (8.16) are $Q/2$. For $c\le1$, $\beta<c\le1$.
For $c>1$, positive-denominator multiplication gives

$$
\beta\ge1\quad\Longleftrightarrow\quad
E\ge T(c):=\frac{c(1+c)}{3(c-1)}.
\tag{8.22}
$$

The condition $T(c)<1+c$ is equivalent to $c>3/2$, and
$T(c)\le(1+c)/2$ is equivalent to $c\ge3$.
This proves (8.20), including the equality $c=3$, where
$T(3)=2=(1+3)/2$, and the excluded endpoint $c=3/2$,
where $T(c)=1+c$ lies outside (8.1).

For (8.21), on $0\le E\le c/3$ the five-candidate formulas
give $F=H=\min\{2E,c/3\}$, and Theorem 3.3 matches.
In particular $E=0$ is the singleton prior, with risk zero;
no supplier requiring $a<b$ is needed there. For $E>0$ in
this interval, Uniform Report Designs, Theorem 31.4, is also
within its stated domain because $c/3<(1+2c)/4$.
On $c/3\le E\le(1+c)/2$, Theorem 7.5 applies for $c\ge3$
and gives $H/2=G/2$, with its separately proved endpoint at
$E=c/3$. On $(1+c)/2\le E<1+c$, (8.20) gives $H/2=Q/2$.
For $E\ge1+c$, the candidate comparisons $Q\ge P,G,c/3$
and $Q<E$ give $F=H=Q$ directly, so Theorem 3.3 again matches.
This includes $E=1+c$, where $P=Q=c$.
At $E=c/3$ the adjoining values are $c/6$; at
$E=(1+c)/2$ they are $G/2=Q/2=c/4$.
All statements use finite complete-world suppliers or the total
strategies already specified, with closed endpoint conventions.

The inherited wide-prior region (5.2) also remains exact for all
$c>0$: for $0<c\le1/2$, Uniform Report Designs, Lemma 32.2,
gives $E_\star>E_{\mathrm{fit}}$ and
$(1+c)/2<E_\star<1+c$, so its Theorem 32.4 applies at every
$E_\star\le E\le1+c$; for $c>1/2$, Lemma 34.2 and
Theorem 34.5 give precisely that same interval of equality.
Beyond $1+c$ the fixed-design comparison just given suffices.
Thus neither the small-$c$ domain of Section 32 nor the
high-noise domain of Section 34 is extended by assumption.
In particular $c\ge3$ now includes the entire formerly unresolved
outside interval $(1+c)/2<E<E_\star(c)$. $\square$

**Theorem 8.6 (rational interior improvement over the previous minimum).**
For every $m>0$, take

$$
c=\frac{299}{100}<3,\qquad E=2,\qquad
K=[-7/2,1/2],\qquad \varepsilon=\frac{299m}{200}.
\tag{8.23}
$$

This point lies strictly in
$(1+c)/2<E<E_\star(c)$ and $\beta>1$. Its new exact value is

$$
\boxed{R_{\mathrm{private}}(299/100,2)=\frac{299}{399}.}
\tag{8.24}
$$

The previously certified minimum upper bound at this point is
$D(299/100)/2$, and its decrease is strictly greater than
$116311/14332080$.

**Proof.** Direct rational substitution gives

$$
P=\frac{1495}{898},\qquad Q=\frac{598}{399},\qquad
\beta=\frac{20033}{20000}>1,\qquad
\frac{1+c}{2}=\frac{399}{200}<2<\frac{399}{100}=1+c.
\tag{8.25}
$$

To certify the active old bound, use the actual deterministic
classification, not the fixed-path risk $P/2$. Since $c>1/2$
and $E_0=(1+2c)/4<2<1+c$, Uniform Report Designs,
Theorem 34.5, applies. Let $q_c$ be its larger root of

$$
f_c(q)=(3+4c)q^2-2(3+2c)q+3-c=0.
\tag{8.26}
$$

At the rational $c$ in (8.23),

$$
f_c(7/6)=-\frac{523}{900}<0,
\qquad f_c(6/5)=\frac1{2500}>0.
\tag{8.27}
$$

The quadratic has positive leading coefficient. A point where it
is negative lies strictly between its roots, so its larger root
satisfies $7/6<q_c<6/5$. Therefore its exact constant
$D=c(3+c-q_c^2)/(3+2c)$ obeys the rational certificate

$$
D_{\mathrm{lo}}:=\frac{27209}{17960}
 <D<\frac{622817}{404100}=:D_{\mathrm{hi}}.
\tag{8.28}
$$

Two exact positive differences are

$$
D_{\mathrm{lo}}-Q=\frac{116311}{7166040}>0,
\qquad
\frac{P+Q}{2}-D_{\mathrm{hi}}
 =\frac{1089257}{26872650}>0.
\tag{8.29}
$$

Since $Q<P$, these imply $Q<D<(P+Q)/2<P$.
Theorem 34.5 consequently gives
$R_{\mathrm{ad},3}=\max\{Q,\min\{P,D\}\}/2=D/2$.
Also $Q<D$ is exactly $E<E_\star=(1+c)D/c$.
The point is outside the domains of Sections 6--7, whose upper
endpoint is $(1+c)/2$, and outside the wide exact region (5.2).
The old all-parameter bound (3.4), with $F=P,H=Q$, therefore
has actual minimum

$$
U_{\mathrm{previous}}
 =\min\left\{R_{\mathrm{ad},3},\frac{P+Q}{4}\right\}
 =\frac D2>\frac Q2=\frac{299}{399}.
\tag{8.30}
$$

Equations (8.25) and (8.16) prove (8.24), and (8.29) gives

$$
U_{\mathrm{previous}}-R_{\mathrm{private}}
 =\frac{D-Q}{2}>\frac{116311}{14332080}>0.
\tag{8.31}
$$

This certifies improvement over the active previous minimum,
including its deterministic adaptive supplier.

There is also a nonempty open region of new exactness below $3$:

$$
\mathcal O=\left\{(c,E):\frac32<c<3,\quad
 \max\left\{\frac{1+c}{2},T(c)\right\}<E<E_\star(c)\right\}.
\tag{8.32}
$$

On $c>3/2$ the rational $T$ and the radical expression
$E_\star$ from (5.1) are continuous, with positive denominators;
hence the displayed strict inequalities define an open set.
The point (8.23) belongs to it by (8.25), (8.29) and (8.22),
so it is nonempty. Every point of $\mathcal O$ has $\beta>1$
and lies below $E_\star$, and (8.20) gives $R_{\mathrm{private}}=Q/2$
there. In this open set, Lemma 34.2 gives $E_1<(1+c)/2<E$,
so Theorem 34.5 gives $R_{\mathrm{ad},3}=D/2>Q/2$. Also
$(P+Q)/4>Q/2$. Thus the previous minimum of these two upper
bounds strictly exceeds the new exact value throughout $\mathcal O$.
$\square$

**Theorem 8.7 (remaining intervals).** The sufficient criterion
$\beta\ge1$ makes no necessity assertion. On the remaining
outside domain

$$
\frac{1+c}{2}\le E<E_\star(c),\qquad \beta<1,
\tag{8.33}
$$

the certified conclusion is

$$
0\le R_{\mathrm{private}}-\frac Q2
\le\min\left\{R_{\mathrm{ad},3}-\frac Q2,
                 \frac{(1-\beta)(P-Q)}4\right\}.
\tag{8.34}
$$

It asserts no positive actual gap and no unrestricted equality
on (8.33). The small-$c$ original-band question also remains:
for $0<c<3$, $c/3<E\le(1+c)/2$, the inherited estimate is

$$
0\le R_{\mathrm{private}}-\frac G2
 \le\frac{(3-c)(P-G)}{12},
\tag{8.35}
$$

without a proof that either inequality is attained. These statements
retain the arbitrary-seed infimum, full histories and unchanged
complete source.

**Proof.** Subtract the arbitrary-seed lower bound from (8.16)
when $\vartheta=\beta<1$ to get (8.34). Equation (8.35) is
exactly Theorem 7.5 on its stated domain. At the common boundary
$E=(1+c)/2$, $Q=G$, $r_o=1/2$, $\beta=c/3$ and the
budgets (8.3) coincide with (7.2), so the two estimates agree.
For $E\ge E_\star$, (5.2) remains available even if $\beta<1$;
those points are excluded from (8.33). Neither constructing one
two-point-seed upper strategy nor integrating (8.19) restricts
the competitor class to finite seeds. $\square$

## 追加锚（本行以下为增补区）

## 9. Common-endpoint localization and complementary signed budgets

**Definition 9.1 (one-sided complementary budgets).** Retain precisely
Definitions 1.1--1.3. In this section assume

$$
c>0,\qquad \frac c3<E<1+c,
\qquad \gamma=\frac c3,\quad r=E-H,\quad q=E-P,\quad \chi=P-H.
\tag{9.1}
$$

Define the public coefficient

$$
\lambda=
\begin{cases}
\min\{1,c/3\},&E\le(1+c)/2,\\[2pt]
\min\{1,c(1-(1+c)/(3E))\},&E\ge(1+c)/2.
\end{cases}
\tag{9.2}
$$

The two definitions agree at their common endpoint. Choose a public
number $w$ satisfying

$$
\chi\le w\le r,\qquad
r+\lambda w\le H,\qquad
\bigl[w=r\ \text{or}\ \lambda(1+4\gamma)\ge1\bigr].
\tag{9.3}
$$

Put

$$
\begin{gathered}
q_w=r-w,\qquad s_w=\frac{(1-\lambda)w}{2},\qquad
\ell_w=E-(1+\lambda)w,\qquad
\nu=\frac{1-\lambda}{1+\lambda},\\
\psi(x)=\min\{w,(r-x)_+\}-s_w+\nu(x-\ell_w)_+
\quad(0\le x\le E),\\
\mathsf b_L(x)=H/2-\psi(x),\qquad
\mathsf b_R(x)=H/2+\psi(x).
\end{gathered}
\tag{9.4}
$$

Here $L$ labels the favorable separation coefficient $k_L$ of the
$013$ experiment, and $R$ its other coefficient. These are budgets
on a single origin half, with
$\mathsf b_L(x)+\mathsf b_R(x)=H$. They impose no
cross-center budget inequality. When $0<\lambda<1$, the correction
has $\psi(r)=-s_w$ and $\psi(E)=s_w$; the radii themselves
will be nonnegative. Candidate origins, rather than an unknown
true origin supplied to the receiver, are the arguments of (9.4).

**Theorem 9.2 (one-sided joint-fiber certificate).** Under
(9.1)--(9.3), the budgets in (9.4) belong to $[0,H]$.
If two origins $z-y\le z-x\le z$, $0\le x\le y\le E$,
belong to one exact $013$ compatible set, then

$$
y-x\le\mathsf b_L(x)+\mathsf b_L(y).
\tag{9.5}
$$

If $z\le z+x\le z+y$ belong to one such set, then

$$
y-x\le\mathsf b_R(x)+\mathsf b_R(y).
\tag{9.6}
$$

For $023$, the corresponding positive-half budget is
$\mathsf b_L$ and the negative-half budget is $\mathsf b_R$.
All assertions concern the full joint original-coordinate fibers
(1.6), with every finite gain $A\ge m$ allowed.

**Proof.** The comparisons (4.4), (8.6) and the fixed-set
suppliers give, throughout (9.1),

$$
\begin{gathered}
F=P<E,\qquad
H=\begin{cases}G,&E\le(1+c)/2,\\Q,&E\ge(1+c)/2,\end{cases}
\qquad H>\gamma,\\
0<q<r<1,\qquad \chi=r-q>0,\qquad 0<\lambda\le1.
\end{gathered}
\tag{9.7}
$$

In particular no prior-length truncation is active. On the first
band $r=(3E-c)/(3+c)\le1/2$; on the second
$r=E/(1+c)\in[1/2,1)$. Also
$q=(3E-c)/(3+2c)<1$.

The joint feasible-set correspondence being used is exactly
(1.6)--(1.7), supplied by Three-Index Design, Theorem 3.1.
For a selected triple its variables satisfy
$\lambda_0=1/A$, $\xi=2t$,
$\omega_0=(At^2+B)/A$, with the three original strip
constraints imposed together. Conversely, in that closed strip
polytope $\lambda_0=0$ would make the monic polynomial
$i^2+\xi i+\omega_0$ vanish at three distinct indices.
Thus every feasible point has $\lambda_0>0$ and gives the finite
witness

$$
A=1/\lambda_0,\quad t=\xi/2,\quad
B=\omega_0/\lambda_0-At^2,\quad
\eta_i=r_i-A(i+t)^2-B.
\tag{9.8}
$$

The strip inequalities say jointly that all selected
$|\eta_i|\le\varepsilon$; setting the one unread error to zero
completes a world. The reverse construction follows by substitution.
The bounds on $\lambda_0,\xi$, together with the index-zero
constraint bounding $\omega_0$, make the polytope compact.
Consequently its origin projection is the same compact interval
$C_j$, without an upper gain assumption or independent difference
errors. This is the existing scalar-recovery correspondence, not
an additional observation channel.

For two members of one $013$ fiber, their noiseless triples differ
by at most $2\varepsilon=mc$ in the original maximum norm.
Theorem 2.1 of Three-Index Design therefore gives, on the favorable
half, for $d=y-x$,

$$
d\le H,\qquad
x<r\ \Longrightarrow\ d\le H-\lambda(r-x).
\tag{9.9}
$$

The first inequality is the half-prior bound (2.5), with
$H=G$ or $H=Q$ as in (9.7). For completeness the exact local
restriction is

$$
d\le L(x):=
\begin{cases}c(1+x)/3,&0\le x\le1/2,\\cx,&x\ge1/2.
\end{cases}
\tag{9.10}
$$

On the first band, $x<r\le1/2$ gives
$L(x)=G-\gamma(r-x)$ and $\lambda\le\gamma$.
On the second put $\beta=c(1-1/(3r))$. Then
$H=cr=\gamma+\beta r$ and $\beta\ge\gamma$.
For $x\le1/2$,
$H-\beta(r-x)-L(x)=(\beta-\gamma)x\ge0$;
for $1/2\le x<r$ that difference is
$(c-\beta)(r-x)\ge0$. Since $\lambda\le\beta$,
this proves (9.9) on both closed separation branches, including
$x=0$ and $x=1/2$ wherever applicable. On the other origin half
the same exact supplier gives

$$
d\le R(x):=
\begin{cases}c(1+2x)/3,&0\le x\le1,\\cx,&x\ge1.
\end{cases}
\tag{9.11}
$$

Only its first branch will be needed below. These restrictions
are necessary conditions on pairs of finite witnesses in the same
joint fiber; no independent realizability of separate error
differences is asserted.

From (9.3), $H\ge r+\lambda w\ge(1+\lambda)w$ and hence

$$
0\le q_w\le r\le\ell_w\le E,\qquad
0\le\nu<1,\qquad
\psi(r)=-s_w,\quad \psi(E)=s_w.
\tag{9.12}
$$

The successive slopes of $\psi$ on the intervals separated by
$q_w,r,\ell_w$ are $0,-1,0,\nu$, omitting intervals of
zero length. In particular

$$
-s_w\le\psi(x)\le w-s_w=\frac{(1+\lambda)w}{2}\le H/2.
\tag{9.13}
$$

Since $s_w\le w-s_w$, this proves both radii nonnegative
and at most $H$. The functions $x+\psi(x)$ and
$x-\psi(x)$ are nondecreasing on $[0,E]$.

To prove (9.5), it suffices to show
$d+\psi(x)+\psi(y)\le H$ for favorable pairs. First suppose
$y\le r$. Write $h(v)=\min\{w,(r-v)_+\}$.
Then $y+h(y)\le r$ and $x-h(x)\ge-w$, so

$$
d+\psi(x)+\psi(y)
=d+h(x)+h(y)-2s_w
\le r+w-2s_w=r+\lambda w\le H.
\tag{9.14}
$$

If $x<r<y$, put $v=r-x>0$. By (9.9),
$d\le H-\lambda v$, or equivalently
$y\le E-(1+\lambda)v$. If $y\le\ell_w$, the correction
sum is $\min(w,v)-(1-\lambda)w$. This is at most
$\lambda v$: for $v\ge w$ use $\lambda w\le\lambda v$,
and for $v\le w$ use
$v-(1-\lambda)w\le\lambda v$.
If $y>\ell_w$, the same upper bound for $y$ implies $v<w$
and

$$
\nu(y-\ell_w)\le(1-\lambda)(w-v),\qquad
\psi(x)+\psi(y)
\le v-(1-\lambda)w+(1-\lambda)(w-v)=\lambda v.
\tag{9.15}
$$

Combining either estimate with (9.9) gives (9.5).
Finally if $r\le x\le y$, monotonicity on that outer interval
gives

$$
d+\psi(x)+\psi(y)
=(y+\psi(y))-(x-\psi(x))
\le(E+s_w)-(r+s_w)=H.
\tag{9.16}
$$

These cases include $x=r$, $y=r$ by their closed alternatives
and prove the favorable inequality, also for equal origins.

For (9.6) we need $d-\psi(x)-\psi(y)\le H$.
If $x\ge q_w$, monotonicity and
$q_w+\psi(q_w)=r-s_w$ give directly

$$
d-\psi(x)-\psi(y)
=(y-\psi(y))-(x+\psi(x))
\le(E-s_w)-(r-s_w)=H.
\tag{9.17}
$$

If $x<q_w$, then $q_w>0$ and therefore $w<r$.
The last condition in (9.3) now supplies

$$
\nu(1+2\gamma)\le2\gamma.
\tag{9.18}
$$

Set $\delta=q_w-x>0$. Since $q_w=r-w\le r-\chi=q<1$,
the near branch of (9.11) applies. At $q$ its value is
$R(q)=P=H+\chi$, so

$$
\begin{aligned}
R(q_w)&=H+\chi-2\gamma(w-\chi)\le H+w,\\
d&\le H+w-2\gamma\delta,\qquad
y\le Y:=E-(1+2\gamma)\delta.
\end{aligned}
\tag{9.19}
$$

For an actual pair $0\le y\le Y\le E$. If $Y\ge\ell_w$,
(9.12) gives
$\psi(Y)=s_w-\nu(1+2\gamma)\delta
\ge s_w-2\gamma\delta$.
If $Y<\ell_w$, then
$(1+2\gamma)\delta>(1+\lambda)w$.
Together with (9.18), this implies
$2\gamma\delta\ge(1-\lambda)w=2s_w$, so (9.13) gives
the same lower bound $\psi(Y)\ge s_w-2\gamma\delta$.
This argument includes $\lambda=1$, where $s_w=\nu=0$.
Since $y-\psi(y)$ is nondecreasing and
$\psi(x)=w-s_w$, we conclude

$$
\begin{aligned}
d-\psi(x)-\psi(y)
&\le Y-\psi(Y)-(q_w-\delta+w-s_w)\\
&\le E-s_w-\delta-(r-s_w-\delta)=H.
\end{aligned}
\tag{9.20}
$$

If $w=r$, the case $x<q_w=0$ is empty, and no condition
(9.18) is needed. This completes all pair cases.

The complete-world reflection (2.7) exchanges the two fixed
experiments and the two origin halves. Applying it to these
inequalities gives the stated $023$ budgets. It only relates
compatible experiments, and grants no reversed execution.
All estimates are nonstrict; zero radii and singleton intervals
are allowed. $\square$

**Definition 9.3 (a terminal rule using the common acquired endpoints).**
Assume (9.1)--(9.3). For either terminal design $j=13,23$ and
any real triple, form its exact set $C=C_j$ and the acquired
endpoint difference $D=r_3-r_0$. If $C$ is empty, output $z$.
If $C$ is nonempty and $|D|\le mc$, output its ordinary midpoint.
For the remaining histories, define on $C$ the budget $B_j$ by

$$
\begin{array}{c|cc}
 &j=13&j=23\\ \hline
D>mc&B_j(t)=\mathsf b_R(t-z)&B_j(t)=\mathsf b_L(t-z)\\
D<-mc&B_j(t)=\mathsf b_L(z-t)&B_j(t)=\mathsf b_R(z-t).
\end{array}
\tag{9.21}
$$

Output the midpoint of the scalar budget intersection

$$
\left[
\sup_{t\in C}(t-B_j(t)),\quad
\inf_{t\in C}(t+B_j(t))
\right].
\tag{9.22}
$$

Let $\Gamma^{\mathrm{end}}_w$ use a source-independent fair
seed on $\{13,23\}$, with its power-set sigma-algebra.
For every real history set $f_{13}=1$, $f_{23}=2$ and
$g_j(u,r_0,r_u)=3$. On terminal pairs $(1,3)$ and $(2,3)$
use the preceding respective rules, for either seed. On $(1,2)$
use the ordinary midpoint of $C_{12}$ if nonempty and $z$ otherwise.
These prescriptions include every legal unreachable history.

**Theorem 9.4 (same-world exact minimax value from the certificate).**
For every public choice satisfying (9.1)--(9.3), Definition 9.3
is a finite-valued total strategy under Definition 1.2 and

$$
\boxed{
\mathcal R(\Gamma^{\mathrm{end}}_w)
=R_{\mathrm{private}}(c,E)=H/2.
}
\tag{9.23}
$$

The lower bound holds for every independent seed probability
space in that definition, with only per-world seed measurability.

**Proof.** For every member $t=z+x$ of either exact compatible
set, its finite witness (9.8) gives the original-coordinate identity

$$
D=6Ax+\eta_3-\eta_0,\qquad
A\ge m,\qquad |\eta_3-\eta_0|\le mc.
\tag{9.24}
$$

If $|D|\le mc$, then for $x\ge0$ one has
$6mx\le D+mc$; for $x\le0$ one has
$6mx\ge D-mc$. Thus the whole compatible set is contained in

$$
K\cap\left[z+\frac{D-mc}{6m},\quad
             z+\frac{D+mc}{6m}\right],
\tag{9.25}
$$

whose length is at most $c/3=\gamma<H$. Its midpoint rule
therefore has loss at most $\gamma/2$ on every member of $C$.
This is an outer interval consequence of the original joint
constraints, used only for its valid diameter bound. It is not
asserted to equal $C$ or to certify feasibility.

If $D>mc$, (9.24) forces $x>0$ in every compatible world;
if $D<-mc$, it forces $x<0$. Hence all arguments in (9.21)
are in $[0,E]$ and the whole compatible set is on that one side.
Theorem 9.2 gives
$|s-t|\le B_j(s)+B_j(t)$ for all its pairs.
The scalar intersection argument of Theorem 2.1 now shows that
(9.22) is nonempty: each $s-B_j(s)$ is at most every
$t+B_j(t)$. The endpoints are finite because
$C\subseteq K$ is nonempty and $0\le B_j\le H$.
Every point of this intersection has loss at most $B_j(t)$
simultaneously for every $t\in C$. This reasoning requires
neither positive radii nor an interior point; it covers a zero
radius forcing a singleton intersection.

The source's scalar-recovery supplier also makes the $012$
midpoint finite. Thus every terminal prescription is total on
all real histories, with the explicit empty-set convention.
Each seed actually reads exactly $013$ or $023$, in increasing
integer order, with continuation $3$ legal after either choice
of $u$. In particular the difference $D$ is formed from two
reports that have actually been acquired in that execution.
No test of the true origin is a receiver input. All actual
indices and answers are measurable for each fixed complete world
on this two-point power-set probability space.

Fix one complete $W$ of (1.2), including its finite gain, offset
and all four original errors, before the seed. Both analytical
triples have the same $D=y_3(W)-y_0(W)$.
If $|D|\le mc$, both losses are at most $\gamma/2\le H/2$.
Otherwise put $x=|\tau(W)-z|>0$. The two losses are bounded,
in the order specified by the sign of $D$, by
$\mathsf b_R(x)$ and $\mathsf b_L(x)$. Their fair average is
$H/2$. This proves the fixed-world bound uniformly over every
$A\ge m$, every $B$ and the complete original cube. The other
seed's triple is only an analytical evaluation on this same
world; it is not an extra acquired report.

For the lower bound reuse the finite attained full-grid pair of
Theorem 3.3, supplied by Three-Index Design, Theorem 18.2.
Its two complete worlds have origins at distance $H$ and equal
reports at all four indices, with finite gains and offsets and
legal errors in the original four-coordinate cube. They are fixed
before any seed of any candidate strategy. For each seed, equality
of actual reports successively forces the same choices, same
terminal history and same answer in the two worlds. The sum of
their two losses is therefore at least $H$ pointwise. Each loss
is measurable by the individual world's hypothesis, so additivity
of nonnegative integrals gives a sum of fixed-world expected
losses at least $H$, even if one is infinite. At least one is
at least $H/2$. This applies before taking the infimum over all
allowed seed spaces and gives the reverse inequality in (9.23).
No source law, joint measurability, finite-seed reduction or
minimax exchange occurs. $\square$

## 10. Closed small-parameter bands and an all-prior matching family

**Theorem 10.1 (endpoint-width criterion and a small-$c$ curve).**
For the original complete-source problem, every $c>0$ and finite
$E\ge0$ with $E\le3H/2$ satisfy

$$
\boxed{R_{\mathrm{private}}(c,E)=H/2.}
\tag{10.1}
$$

More generally, in the strict middle domain (9.1),
$H\ge(1+\lambda)(E-H)$ is sufficient for the same equality.
In particular, for every

$$
0<c<2,\qquad \frac c3\le E\le\frac{3c}{6-c},
\tag{10.2}
$$

there is the closed-band value

$$
\boxed{
R_{\mathrm{private}}(c,E)=\frac{c(1+E)}{2(3+c)}.
}
\tag{10.3}
$$

**Proof.** On $E\le c/3$ the inherited identity is
$F=H=\min\{2E,c/3\}$, so Theorem 3.3 matches; this includes
$E=0$. On $E\ge1+c$, $F=H=Q$ and the same theorem matches.
In the remaining domain (9.1), choose $w=r=E-H$.
Then (9.3) requires only $(1+\lambda)r\le H$, and
Theorem 9.4 applies. If $E\le3H/2$, then $r\le H/2$;
since $\lambda\le1$, this sufficient inequality holds.
This proves (10.1) and the more general assertion with the actual
single-trajectory consumer $\Gamma^{\mathrm{end}}_r$.

For (10.2), $6-c>0$ and

$$
\frac{3c}{6-c}-\frac c3=\frac{c(3+c)}{3(6-c)}>0,
\qquad
\frac{1+c}{2}-\frac{3c}{6-c}
=\frac{(2-c)(c+3)}{2(6-c)}>0.
\tag{10.4}
$$

Thus this band is contained in
$c/3\le E<(1+c)/2$, where $H=G$. Positive-denominator
multiplication gives

$$
E\le3H/2
\quad\Longleftrightarrow\quad
(6-c)E\le3c.
\tag{10.5}
$$

Equations (10.1) and (10.5) prove (10.3). At the lower endpoint
$E=c/3$, use the already supplied $\Gamma_{1/2}$ and value
$E/2=c/6$; no positive $r$ or $w$ is required there.
At the included upper endpoint, $r=H/2$ and all inequalities
in (9.3) remain nonstrict. At $c=2$ the two upper boundaries in
(10.4) meet at $E=3/2$; that point is covered by (10.1).
The displayed parameter restriction $c<2$ merely isolates the
stated smaller-$c$ curve. $\square$

**Theorem 10.2 (signed-budget all-prior family).** Define

$$
c_\dagger=\frac{3(\sqrt{17}-1)}8.
\tag{10.6}
$$

For every $c\ge c_\dagger$ and every finite $E\ge0$, on the
unrestricted strategy class of Definition 1.2,

$$
\boxed{
R_{\mathrm{private}}(c,E)=\frac H2=
\begin{cases}
\frac12\min\{2E,c/3\},&0\le E\le c/3,\\[3pt]
\dfrac{c(1+E)}{2(3+c)},&c/3\le E\le(1+c)/2,\\[5pt]
\dfrac{cE}{2(1+c)},&E\ge(1+c)/2.
\end{cases}}
\tag{10.7}
$$

In particular this holds throughout $c\ge\sqrt{3/2}$.
The number $c_\dagger$ is a sufficient threshold, with no
necessity assertion.

**Proof.** For $c\ge3$, (10.7) is already Theorem 8.5.
The inherited regions $E\le c/3$ and $E\ge1+c$ were also
settled in the proof of Theorem 10.1. It remains to treat
$c_\dagger\le c<3$ and (9.1). We choose $w=\chi$ in
(9.3). The new threshold is the positive root of

$$
4c^2+3c-9=0.
\tag{10.8}
$$

Hence $c>1$, $\gamma=c/3<1$, and

$$
\gamma(1+4\gamma)\ge1,\qquad
5c^2+3c-9\ge c^2>0.
\tag{10.9}
$$

On the first band $\lambda=\gamma$. On the second,
$\beta\ge\gamma$ and $\lambda=\min(1,\beta)\ge\gamma$.
Thus the last condition of (9.3) holds, including its equality
at the threshold on the first band.

To check the width condition first suppose
$c/3<E\le(1+c)/2$. Then

$$
0<r\le1/2,\qquad
\chi=\frac{\gamma r}{1+2\gamma},\qquad
H=\gamma(1+r).
\tag{10.10}
$$

Since $0<\gamma<1$, the affine function
$H-r-\gamma\chi=
\gamma+r(\gamma-1-\gamma^2/(1+2\gamma))$
decreases in $r$. Its minimum on $0\le r\le1/2$ is

$$
\frac{5\gamma^2+\gamma-1}{2(1+2\gamma)}
=\frac{5c^2+3c-9}{6(3+2c)}>0.
\tag{10.11}
$$

Therefore $r+\lambda\chi<H$ on this band.

Next suppose $(1+c)/2\le E<1+c$. Now
$1/2\le r<1$, $H=cr$ and
$\chi=c(1-r)/(3+2c)$. Put $u=1/r\in(1,2]$.
Using $\lambda\le\beta=c(1-u/3)$ gives

$$
\frac{\lambda\chi}{r}
\le\frac{c^2(u-1)(3-u)}{3(3+2c)}
\le\frac{c^2}{3(3+2c)},
\tag{10.12}
$$

because $(u-1)(3-u)=1-(u-2)^2\le1$.
Consequently

$$
H-r-\lambda\chi
\ge r\left(c-1-\frac{c^2}{3(3+2c)}\right)
=\frac{r(5c^2+3c-9)}{3(3+2c)}>0.
\tag{10.13}
$$

This calculation does not extrapolate the near separation branch
past $r=1/2$; the coefficient $\beta$ uses both branches as
proved in (9.9)--(9.10). Since $0<\chi<r$, all conditions in
(9.3) hold for $w=\chi$. Theorem 9.4 supplies the same-world
upper strategy and arbitrary-seed lower bound on the whole
remaining domain, proving (10.7).

All boundaries are included. At $c=c_\dagger$, (9.18) can be
an equality, while the strict width bounds (10.11)--(10.13)
still hold; no inverse of $4c^2+3c-9$ was used. The positive
root in (10.8) is less than $\sqrt{3/2}$: the polynomial is
strictly increasing on $c>0$ and at $c=\sqrt{3/2}$ its value
is $3(\sqrt{3/2}-1)>0$. Thus $c=\sqrt{3/2}$ and every
larger $c$ lie in the proved family.

At $E=0$, the constant answer $z$ has risk zero. At
$E=c/6$, the minimum $\min(2E,c/3)$ has matching values
on its two branches. At $E=c/3$, adjoining values are $c/6$;
at $E=(1+c)/2$, both are $c/4$. At this latter junction
$r=1/2$, $G=Q$, $\chi=P-G=P-Q$ and the two definitions
of $\lambda$ agree, so the endpoint rule and its pair estimates
also agree. At $E=1+c$, $P=Q=c$ and the inherited
$F=H$ rule gives $c/2$; the strict middle certificate need
not be extended to its vanishing $\chi$. Every prior in (10.7)
is finite, and all attaining lower worlds have finite nuisance
parameters. $\square$

**Theorem 10.3 (nonempty additional small-$c$ domain and remaining scope).**
For every $0<c<c_\dagger$, the interval

$$
\frac c3<E\le\frac{3c}{6-c}
\tag{10.14}
$$

has positive length, lies in the previously unmatched domain
of (8.35), and has the exact value (10.3).
Neither (10.7) nor (10.14) changes the deterministic conclusions
of Uniform Report Designs or the attained risks of the particular
strategies in Sections 4, 6 and 7.

On $0<c<c_\dagger$, the equalities of (5.2), Theorem 10.1,
and every valid certificate (9.3) remain available. For other
points of $c/3<E<E_\star(c)$ these results do not determine
the unrestricted value. In particular the sufficient thresholds
and the failures of their budget conditions imply neither a
positive actual gap above $H/2$ nor a necessary threshold.

**Proof.** Since $c_\dagger<\sqrt{3/2}<2$, both strict
comparisons in (10.4) apply and give a nonempty interval above
$c/3$ and below $(1+c)/2$. The inherited relation
$(1+c)/2<E_\star(c)$ puts it below the other inherited exact
region. The right-hand width in (8.35) is positive there because
$c<3$ and $P-G>0$; (8.35) itself made no claim that the
actual gap was positive. Theorem 10.1 now settles the value
with the lawful consumer of Definition 9.3, without changing
any source or strategy quantifier. Earlier lower and upper bounds
and exact risks on their own stated domains remain valid.

The comparison with existing mathematics is scoped as follows.
The exact separations, finite full-grid witnesses, joint fibers,
reflection and scalar interval-intersection steps are the suppliers
in Three-Index Design, Sections 2, 3, 18 and 23, and Uniform
Report Designs, Sections 30--34, already identified in Sections
1--8. The common-endpoint localization combined with the signed
transfer (9.14)--(9.20) supplies the complementary decision
guarantee used here. Casini--Garulli--Vicino,
[*A linear programming approach to online set membership parameter estimation for linear regression models*, Section 4, equations (7)--(10)](https://control.dii.unisi.it/~casini/pdf/IJACSP_2017a.pdf),
supplies the classical intersection of known-regressor bounded-error
strips. Its coordinate bounding orthotopes do not supply the
joint ratio-target conclusion (9.23). Krieg--Novak--Ullrich,
[*On the power of adaption and randomization*, Sections 1--2](https://arxiv.org/html/2406.07108v2),
studies continuous linear targets and imposes product measurability
on randomized loss. The clock target
$\theta_1/(2\theta_2)$ remains nonlinear even after including
the four errors in the input, and Definition 1.2 requires only
per-world seed measurability. Neither comparison theorem is used
as a substitute for the same-fixed-world upper proof or the
two-fixed-world lower proof. These are ordinary mathematical
deductions in the declared clock model, without a claim of
literature priority or of empirical clock realization. $\square$

## 追加锚（本行以下为增补区）
