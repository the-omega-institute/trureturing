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

## 11. Actual-prefix continuation and the unrestricted first-order value

**Definition 11.1 (three-path continuation and terminal ratios).** Retain
exactly Definitions 1.1--1.2. For this section fix
$m>0$, $0<E\le1/2$, $0<c<1$, and set

$$
\begin{gathered}
r_E=\frac{1+E}{2(1+2E)},\qquad
p_E=\frac{E}{2(1+2E)},\qquad k_E=1-r_E,
\\
p(h)=\min\{k_E,\max\{p_E,k_E(h^{-1}-1)\}\}\quad(h>0).
\end{gathered}
\tag{11.1}
$$

Thus $p_E+r_E=1/2$, $0<p_E<k_E<1$, and
$p_E\le p(h)\le k_E$. Use the independent seed space $[0,1]$
with its Borel sigma-algebra and uniform probability. For each seed
$u\in[0,1]$, on every real first history choose index $2$ if
$u<r_E$ and index $1$ otherwise. After index $2$, choose $3$.
After the actual prefix $(r_0,r_1)$ at indices $01$, put

$$
\widehat h=\frac{r_0-r_1}{2m},\qquad
\bar h=\max\{1/2,\widehat h\},
\tag{11.2}
$$

and choose index $2$ if $r_E\le u<r_E+p(\bar h)$, and index
$3$ otherwise. These prescriptions define the history functions
also on unreachable legal histories.

For any real triple at the indicated indices, define

$$
\begin{array}{c|c|c}
 j&\widehat A_j&\widehat x_j\quad(\widehat A_j>0)\\ \hline
012&(r_0-2r_1+r_2)/2&1/2+(r_2-r_0)/(4\widehat A_{012})\\
013&(2r_0-3r_1+r_3)/6&(r_3-r_0)/(6\widehat A_{013})\\
023&(r_0-3r_2+2r_3)/6&(r_3-r_0)/(6\widehat A_{023}).
\end{array}
\tag{11.3}
$$

The terminal answer is the projection of $z+\widehat x_j$ onto
$K=[z-E,z+E]$ when $\widehat A_j>0$, and is $z$ when
$\widehat A_j\le0$. The same terminal prescription is used for
every seed and every legal terminal pair. Denote this strategy by
$\Gamma^{\mathrm{prefix}}$.

**Lemma 11.2 (joint original-error inequality for the continuation).**
For $-E\le x\le E$, $\alpha\ge1$, put $h=\alpha(1-x)$,
$p=p(h)$, $q=1-r_E-p$. In the original coordinate order $0123$, set

$$
\begin{aligned}
w_{012}(x)&=(-3x,\ 6x-3,\ 3-3x,\ 0),\\
w_{013}(x)&=(-1-2x,\ 3x,\ 0,\ 1-x),\\
w_{023}(x)&=(-1-x,\ 0,\ 3x,\ 1-2x).
\end{aligned}
\tag{11.4}
$$

Then for every $e\in[-1,1]^4$,

$$
p|w_{012}(x)\cdot e|+q|w_{013}(x)\cdot e|
 +r_E|w_{023}(x)\cdot e|
\le2\alpha(1+E).
\tag{11.5}
$$

In particular, all three terms are evaluated on the same four
original errors.

**Proof.** Write $r=r_E$, $k=k_E$, $p_0=p_E$. The left side is a
convex function of $e$. Every point of the cube is a convex
combination of its vertices, so it suffices to bound the vertices.
Since each row in (11.4) sums to zero and simultaneous sign reversal
does not change the expression, its nonzero vertex values, divided
by $2$, are the following seven quantities:

$$
\begin{aligned}
M_1&=q(1-x)+r(1-2x),\\
M_2&=3p(1-x)+3r|x|,\\
M_3&=(3p+q)(1-x)+r(1+x),\\
M_4&=3p(1-2x)+3q|x|,\\
M_5&=3p(1-2x)+q(1+2x)+r(1-2x),\\
M_6&=3|x|,\\
M_7&=3p|x|+q(1+2x)+r(1+x).
\end{aligned}
\tag{11.6}
$$

The remaining sign pair gives zero. The assumptions $|x|\le1/2$
justify all signs used in (11.6).

If $x\le0$, then $h\ge1$ and $p=p_0$, $q=1/2$.
Each $M_i$ is convex as a function of $x$ on $[-E,0]$.
At $x=0$ their maximum is $1+2p_0\le1+E$.
At $x=-E$, the first, third and fifth equal $1+E$; the
second is $3E(1+E)/(1+2E)\le1+E$; the fourth and sixth
are $3E\le1+E$. For the seventh use

$$
M_7=1-p_0-E(2-5p_0-r)\le1,
\qquad 2-5p_0-r=\frac{3+2E}{2(1+2E)}>0.
\tag{11.7}
$$

Convexity therefore bounds all seven by $1+E$, and hence by
$\alpha(1+E)$, on this half.

Suppose $x\ge0$. We always have $p\ge p_0$, $q\le1/2$.
Direct subtraction in (11.6), using $0\le x\le1/2$, gives

$$
M_1\le M_3,\quad M_2\le M_3,\quad M_4\le M_5\le M_3.
\tag{11.8}
$$

For the last comparison,
$M_3-M_5=3x(1-2q)\ge0$. It remains to bound
$C=M_3$, $J=M_7$ and $3x$. Define

$$
h_0=\frac{k}{k+p_0}=\frac{1+3E}{1+4E},\qquad
x_0=1-h_0=\frac{E}{1+4E}.
\tag{11.9}
$$

Since $h\ge1-x\ge1/2$, the upper truncation in (11.1) does
not alter $k(h^{-1}-1)$. For $h\ge h_0$ one has $p=p_0$.
If also $x\le x_0$, then

$$
C=1+2p_0-4p_0x\le1+E,
\qquad
J=1-p_0+x(3/2+2p_0)\le1+x\le1+E.
\tag{11.10}
$$

The second inequality uses $x_0=p_0/(1/2+2p_0)$.
Also $3x\le1+x\le1+E$, and $\alpha\ge1$.

For $h\le h_0$, use $p=k(h^{-1}-1)$ and
$h=\alpha(1-x)$. Elementary substitution gives

$$
\frac C\alpha=(1+x-2k)v+2kv^2,
\qquad
\frac J\alpha=(1+k+x)v-kv^2,
\qquad v=1/\alpha\in(0,1].
\tag{11.11}
$$

The first polynomial is convex in $v$, with endpoint values
$0$ and $1+x$, so it is at most $1+x$. For the second,

$$
1+x-\frac J\alpha=(1-v)(1+x-kv)\ge0.
\tag{11.12}
$$

Thus both are at most $1+x\le1+E$; also
$3x/\alpha\le3x\le1+x$. This includes $h=h_0$.
Finally, if $x>x_0$ and $h>h_0$, keep $x,p_0,q,r$ fixed
and decrease $h$ to $h_0$. This is admissible since
$h_0>1-x$. Every nonnegative $M_i/\alpha=M_i(1-x)/h$
can only increase under that change, and its value at $h_0$
was just bounded. These cases exhaust $x\ge0$ and prove
(11.5). $\square$

**Theorem 11.3 (a lawful upper bound on every small prior).** For every
$m>0$, $0<E\le1/2$ and $0<c<1$, Definition 11.1 is an
admissible strategy on the original complete source, and

$$
\begin{aligned}
R_{\mathrm{private}}(c,E)
&\le\mathcal R(\Gamma^{\mathrm{prefix}})
\le U_*(c,E):=\frac{c[1+E+4k_Ec]}{6(1-c)}\\
&\le U(c,E):=\frac{c[1+E+3c(1+3E)]}{6(1-c)}.
\end{aligned}
\tag{11.13}
$$

All preceding upper bounds can still be included in the minimum.
For fixed $0<E\le1/2$, on $0<c<\min\{1,3E\}$,

$$
\boxed{
0\le R_{\mathrm{private}}-\frac H2
\le\frac{c^2[13+31E+c(3+9E)]}{6(1-c)(3+c)},
\qquad
\lim_{c\downarrow0}\frac{R_{\mathrm{private}}(c,E)}c
 =\frac{1+E}{6}.
}
\tag{11.14}
$$

**Proof.** Fix one complete world before the seed, and write
$x=\tau-z$, $\alpha=A/m\ge1$. Its noiseless $01$ difference is
$2A(1-x)$. Consequently the actual prefix satisfies

$$
h=\alpha(1-x)\ge1/2,\qquad
|\widehat h-h|\le c/2,\qquad |\bar h-h|\le c/2.
\tag{11.15}
$$

The clamp onto $[p_E,k_E]$ is nonexpansive, so

$$
|p(\bar h)-p(h)|
\le\frac{k_E|\bar h-h|}{\bar h h}
\le\frac{k_Ec}{h}.
\tag{11.16}
$$

All denominators here are positive. In this fixed world the actual
path probabilities are $p(\bar h)$, $1-r_E-p(\bar h)$ and
$r_E$ for $012,013,023$, respectively. The conditional decision
after $01$ uses its two acquired reports alone.

Quadratic interpolation gives the exact identities, before projection,

$$
\widehat x_j-x=\frac{w_j(x)\cdot\eta}{6\widehat A_j},
\qquad
|\widehat A_{012}-A|\le mc,\qquad
|\widehat A_{013}-A|,|\widehat A_{023}-A|\le mc/2.
\tag{11.17}
$$

For example, subtracting $A$ from the first column of (11.3)
yields the original linear combinations of the three selected errors;
substitution in the ratio gives exactly (11.4). Thus
$\widehat A_j\ge A(1-c)>0$ on every actual triple.
Projection onto $K$ cannot increase error at $\tau\in K$.
The four errors in (11.17) remain the one fixed vector of the
world; no independent error bounds on report differences are used.

Put $S(v)=v|w_{012}\cdot\eta|+(1-r_E-v)|w_{013}\cdot\eta|
+r_E|w_{023}\cdot\eta|$. Lemma 11.2 gives
$S(p(h))\le2\varepsilon\alpha(1+E)$. Moreover,

$$
w_{012}(x)-w_{013}(x)=(1-x)(1,-3,3,-1)
\tag{11.18}
$$

implies
$\big||w_{012}\cdot\eta|-|w_{013}\cdot\eta|\big|
\le8\varepsilon(1-x)$. Combining this with (11.16)--(11.17)
bounds the expected loss on this same complete world by

$$
\begin{aligned}
\frac{S(p(\bar h))}{6A(1-c)}
&\le\frac{2\varepsilon\alpha(1+E)
       +8\varepsilon(1-x)k_Ec/h}{6A(1-c)}\\
&=\frac{c(1+E)}{6(1-c)}
  +\frac{2k_Ec^2}{3\alpha^2(1-c)}
\le U_*(c,E).
\end{aligned}
\tag{11.19}
$$

Since $4k_E=2(1+3E)/(1+2E)\le3(1+3E)$, this is at most
$U(c,E)$. No gain upper bound was used.

The rules in Definition 11.1 are total: on arbitrary histories their
clamped probability is defined, all choices are chronological, and
(11.3) either has a strictly positive denominator or uses the finite
answer $z$. The projection is finite. For each fixed world, the
actual path events are intervals of the seed and the answer is one
of three fixed real numbers. Hence indices and answer are measurable
on the displayed seed space, including zero-probability branches and
the boundary seeds. Each seed acquires exactly three reports; the
other two possible triples in (11.19) are analytical evaluations on
this same world, without additional acquisitions. This proves
admissibility and the uniform upper bounds.

For $c<3E$ and $E\le1/2$, the constants (1.8) have
$H=G=c(1+E)/(3+c)$ and $F=P$. Indeed $G>c/3$,
$G\ge Q$, and $G<E<2E$. The arbitrary-seed full-grid pair in
Theorem 3.3 supplies $R_{\mathrm{private}}\ge G/2$. Subtracting
$G/2$ from $U$ gives precisely the fraction in (11.14), whose
denominators are positive. Dividing these lower and upper bounds by
$c$ and letting $c\downarrow0$ proves the limit for every fixed
positive $E$ in the stated interval. $\square$

**Proposition 11.4 (strict improvement over the active published minimum).**
At $E=1/10$ and every $0<c\le1/200$, the minimum of the
upper bounds in Sections 1--10 is

$$
V(c,1/10)=\frac{c(10c+69)}{120(2c+3)},
\tag{11.20}
$$

and the admissible bound in Theorem 11.3 satisfies

$$
U(c,1/10)=\frac{c(11+39c)}{60(1-c)}<V(c,1/10).
\tag{11.21}
$$

**Proof.** This range has $c/3<E<(1+c)/2$ and
$E\le(1+2c)/4$. Uniform Report Designs, Theorem 31.4,
therefore gives $R_{\mathrm{ad},3}=P/2$; Theorem 7.5 makes
$V=G/2+(1-c/3)(P-G)/4$ smaller than the other upper bounds
from Sections 1--7. Substitution gives (11.20).
The outside-prior domain of Section 8 is absent. The wide exact
region starts at $E_\star>(1+c)/2$, and $c<c_\dagger$.
In Section 9 the necessary width condition for its certificate is
$E-H\le H$, whereas here

$$
2H=\frac{11c}{5(3+c)}\le\frac{11}{3000}<\frac1{10}.
\tag{11.22}
$$

So no choice of its $w$ is admissible; the narrower sufficient
condition of Theorem 10.1 is absent as well. Thus none of the
additional upper consumers in Sections 8--10 lowers (11.20).
Finally direct subtraction gives

$$
V-U=\frac{c(3-337c-166c^2)}{120(1-c)(2c+3)}>0.
\tag{11.23}
$$

The numerator factor decreases on $c\ge0$ and at $1/200$ is
$26217/20000>0$. All denominators in (11.20)--(11.23) are
positive. This is an improvement over the active prior minimum,
without an assertion that $U$ is an exact finite-$c$ value. $\square$

## 12. Finite complete worlds, endpoint-only loss and actual path occupation

**Definition 12.1 (endpoint-only subclass and finite witnesses).**
For any strategy of Definition 1.2, let

$$
\pi_\Gamma(W)=\mathbb P\{(u_\omega(W),v_\omega(W))=(1,2)\}.
\tag{12.1}
$$

The event is measurable by that definition. Let $R_{\mathrm{end}}(c,E)$
be the infimum of $\mathcal R(\Gamma)$ over the entire subclass
satisfying $\pi_\Gamma(W)=0$ for every complete world. The seed
space and all history functions remain unrestricted as in
Definition 1.2; the exceptional seed set may depend on the world.

For $m>0$, $0<E\le1/2$, $0<c<3E$ and any integer $N\ge1$,
put $t=c/3$. Define complete worlds $X_0,\ldots,X_N$ and
$Y_0,\ldots,Y_{N-1}$ by the following finite parameters, where
$J=A(\tau-z)$:

$$
\begin{array}{c|c|c|c}
 &A&J&\eta/\varepsilon\\ \hline
X_j&m(1+jt)&mE&(1,-1,-1,-1)\\
Y_j&m(1+(j+2)t)&m(E-t)&(-1,1,1,1).
\end{array}
\tag{12.2}
$$

In each row set $\tau=z+J/A$ and
$B=-A\tau^2-\eta_0$. Let $D=6mE-mc$. For any of these worlds
$W=(\tau,A,B,\eta)$ also define

$$
W^\dagger=(-3-\tau,A,B-D,\eta^\dagger),
\qquad \eta^\dagger_i=\eta_{3-i}.
\tag{12.3}
$$

These are mathematical choices of complete worlds; the superscript
is not an operation available during a strategy's execution.

**Theorem 12.2 (a finite pre-seed occupation inequality).** All worlds
(12.2)--(12.3) belong to the original source. Define the positive
distances

$$
\begin{aligned}
d_{13,j}&=t\frac{1+2E+jt}{(1+jt)(1+(j+2)t)},\\
d_{23,j}&=t\frac{1+E+(j+1)t}{(1+(j+1)t)(1+(j+2)t)},\\
S_{13}&=\sum_{j=0}^{N-1}d_{13,j},\qquad
S_{23}=\sum_{j=0}^{N-1}d_{23,j}.
\end{aligned}
\tag{12.4}
$$

For every original arbitrary-seed strategy $\Gamma$, with
$\ell(W)=\mathbb E|T(W)-\tau(W)|$, the finite inequality is

$$
\begin{aligned}
&\sum_{j=0}^{N}\bigl[\ell(X_j)+\ell(X_j^\dagger)\bigr]
 +\sum_{j=0}^{N-1}\bigl[\ell(Y_j)+\ell(Y_j^\dagger)\bigr]\\
&\quad\ge S_{13}+S_{23}
 -\sum_{j=0}^{N-1}\left[
 d_{13,j}\pi_\Gamma(X_j)
 +d_{23,j}\pi_\Gamma(X_{j+1}^\dagger)\right].
\end{aligned}
\tag{12.5}
$$

In particular the left side is at most
$2(2N+1)\mathcal R(\Gamma)$. No source probability law is required.

**Proof.** Since $0<t<E$, the centered origins of $X_j,Y_j$ lie
in $(0,E]$; the reflected ones lie in $[-E,0)$. Every gain is
finite and at least $m$, every offset displayed above is finite,
and all four errors are fixed signs of $\varepsilon$. Thus all
worlds are legal. In the original coordinates the report differences
are

$$
\begin{aligned}
y_1-y_0&=2(J-A)+\eta_1-\eta_0,\\
y_2-y_0&=4J-2A+\eta_2-\eta_0,\\
y_3-y_0&=6J+\eta_3-\eta_0.
\end{aligned}
\tag{12.6}
$$

Substitution shows that every world in (12.2) has $y_0=0$,
$y_3=D$, and gives the exact equalities

$$
\begin{aligned}
(y_0,y_1,y_3)(X_j)&=(y_0,y_1,y_3)(Y_j),\\
(y_0,y_2,y_3)(Y_j)&=(y_0,y_2,y_3)(X_{j+1}).
\end{aligned}
\tag{12.7}
$$

For example, from $X_j$ to $Y_j$ the changes in $A,J$ are
$2mt,-mt$, so the noiseless $01$ difference changes by
$-6mt=-2mc$, while its original error difference changes by
$2mc$. From $Y_j$ to $X_{j+1}$ these changes are $-mt,mt$,
so the corresponding $02$ changes are $2mc$ and $-2mc$.
The $03$ difference is $D$ in both cases. This verifies the
joint original-error realizations, including the unread coordinates.

Subtracting the centered origins in each pair gives exactly
$d_{13,j}=\tau(X_j)-\tau(Y_j)$ and
$d_{23,j}=\tau(X_{j+1})-\tau(Y_j)$ in (12.4).
Their numerators and denominators are positive. Reflection obeys

$$
y_i(W^\dagger)=y_{3-i}(W)-D,
\tag{12.8}
$$

so the reflected worlds still have $y_0=0,y_3=-D$. Their
$013$ pairs are $(Y_j^\dagger,X_{j+1}^\dagger)$ at distance
$d_{23,j}$, and their $023$ pairs are
$(X_j^\dagger,Y_j^\dagger)$ at distance $d_{13,j}$.

Fix any seed of any candidate strategy. All these worlds have the
same initial report zero. Therefore the event
$I=\{f_\omega(0)=1\}$ is common to them all. It is measurable
because it is the actual first-index event in, for example, $X_0$.
On $I$, the pair $(X_j,Y_j)$ supplies the same actual prefix
$01$. Its third-index decision is consequently the same in both
worlds. If it is $3$, their entire acquired histories and their
answers agree, and the sum of their losses is at least $d_{13,j}$.
If it is $2$, their nonnegative losses are still at least zero.
The excluded event is exactly the actual $012$ event in $X_j$
(and also in $Y_j$), rather than a hypothetical path choice.
On $I^c$, the pair $(Y_j,X_{j+1})$ must execute $023$ in both
worlds by chronology; (12.7) forces equal answers and a sum of
losses at least $d_{23,j}$.

For each of the two alternatives these are disjoint pairs among
$X_0,Y_0,X_1,\ldots,Y_{N-1},X_N$, leaving one world unpaired.
Summing their triangle inequalities pointwise and then integrating
therefore gives, with $q=\mathbb P(I)$,

$$
\sum_{j=0}^{N}\ell(X_j)+\sum_{j=0}^{N-1}\ell(Y_j)
\ge qS_{13}+(1-q)S_{23}
 -\sum_{j=0}^{N-1}d_{13,j}\pi_\Gamma(X_j).
\tag{12.9}
$$

The reflected pairs give in the same way

$$
\sum_{j=0}^{N}\ell(X_j^\dagger)
 +\sum_{j=0}^{N-1}\ell(Y_j^\dagger)
\ge qS_{23}+(1-q)S_{13}
 -\sum_{j=0}^{N-1}d_{23,j}\pi_\Gamma(X_{j+1}^\dagger).
\tag{12.10}
$$

Adding cancels $q$ and proves (12.5). Every integral used is of
a measurable loss or actual path event for one fixed world; only
finitely many such functions are added. If a loss expectation is
infinite the asserted inequality still holds. Thus no joint
world--seed measurability, finite-seed reduction or minimax
interchange enters the proof. The worlds were all fixed before
the seed, without selecting a different witness after execution.
$\square$

**Theorem 12.3 (exact first-order endpoint-only penalty).** For every
fixed $0<E\le1/2$, over the complete original endpoint-only
subclass of Definition 12.1,

$$
\boxed{
\lim_{c\downarrow0}\frac{R_{\mathrm{end}}(c,E)}c
 =\frac{2+3E}{12},\qquad
\lim_{c\downarrow0}\frac{R_{\mathrm{end}}(c,E)
                     -R_{\mathrm{private}}(c,E)}c
 =\frac E{12}.
}
\tag{12.11}
$$

In particular the restriction is substantive at every fixed positive
prior width in this interval.

**Proof.** Let $a_N=1+(N+1)c/3$. The denominators in (12.4)
are at most $a_N^2$, while their respective numerators are at
least $1+2E$ and $1+E$. If the strategy is endpoint-only,
all occupation terms in (12.5) vanish, including when its null
sets differ between worlds. Consequently, for every $N\ge1$,

$$
R_{\mathrm{end}}(c,E)
\ge\frac{Nc(2+3E)}{6(2N+1)a_N^2}
\qquad(0<c<3E).
\tag{12.12}
$$

For fixed $N$ take the lower limit as $c\downarrow0$, obtaining
$N(2+3E)/[6(2N+1)]$. This holds for every integer $N$;
letting $N$ increase gives $(2+3E)/12$ as a lower bound for
that lower limit. This order of two scalar limits uses only the
finite inequalities already proved.

For the upper bound, the fair $013/023$ strategy of Section 3 is
endpoint-only and has risk at most $(F+H)/4$. For sufficiently
small $c$ at fixed positive $E\le1/2$, $F=P,H=G$, whence

$$
\limsup_{c\downarrow0}\frac{R_{\mathrm{end}}(c,E)}c
\le\lim_{c\downarrow0}\frac14
 \left(\frac{1+2E}{3+2c}+\frac{1+E}{3+c}\right)
=\frac{2+3E}{12}.
\tag{12.13}
$$

This matches (12.12). Subtract the unrestricted limit (11.14)
to obtain the second limit in (12.11). The lower argument here
is a restricted-class conclusion; it does not give a positive
unrestricted gap above $H/2$. $\square$

**Corollary 12.4 (a necessary nonzero actual $012$ occupation).**
For every $m>0$ and $0<E\le1/2$, define the public finite numbers

$$
\begin{gathered}
N=\left\lceil\frac{4(1+E)}E\right\rceil,\\
B_{N,E}=\frac{2(2+3E)(N+1)}3
       +2(2+1/N)(4+10E),\\
c_E=\min\{1/2,E/(4B_{N,E})\}>0.
\end{gathered}
\tag{12.14}
$$

For every $0<c\le c_E$ and every strategy on the original
arbitrary-seed class with $\mathcal R(\Gamma)\le U(c,E)$,
the explicit worlds (12.2)--(12.3) satisfy

$$
\boxed{
\Pi_N(\Gamma):=\frac1{2N}\sum_{j=0}^{N-1}
 [\pi_\Gamma(X_j)+\pi_\Gamma(X_{j+1}^\dagger)]
 \ge\frac{E}{4(1+2E)}>0.
}
\tag{12.15}
$$

Thus at least one of these $2N$ fixed complete worlds must
actually use $012$ with at least that probability.

**Proof.** The range (12.14) is contained in $0<c<\min\{1,3E\}$,
so all the witnesses and bounds apply. Cancellation of one
positive denominator in (12.4) gives

$$
d_{13,j}\le\frac{c(1+2E)}3,
\qquad d_{23,j}\le\frac{c(1+E)}3
\le\frac{c(1+2E)}3.
\tag{12.16}
$$

For example $1+2E+jt\le(1+2E)(1+jt)$;
the other inequality uses $1+E+(j+1)t\le(1+E)(1+(j+1)t)$.
Combining (12.5), its finite count of losses, the lower bound
for $S_{13}+S_{23}$ used in (12.12), and (12.16) gives for
any finite-risk strategy

$$
\Pi_N(\Gamma)\ge\frac1{2(1+2E)}
\left[\frac{2+3E}{a_N^2}
 -\frac{6(2N+1)\mathcal R(\Gamma)}{Nc}\right].
\tag{12.17}
$$

Under the stated risk bound the second term in brackets is at most

$$
(2+1/N)\frac{1+E+3c(1+3E)}{1-c}
=(2+1/N)\left[1+E+\frac{c(4+10E)}{1-c}\right].
\tag{12.18}
$$

The elementary inequality $(1+s)^{-2}\ge1-2s$ for $s\ge0$
follows, for example, by multiplying by $(1+s)^2$; the
resulting difference is $s^2(3+2s)\ge0$. With
$s=(N+1)c/3$, and using $c\le1/2$, the bracket in (12.17)
is therefore at least

$$
E-\frac{1+E}{N}-cB_{N,E}\ge E-E/4-E/4=E/2.
\tag{12.19}
$$

This proves (12.15). A finite average of probabilities cannot
exceed their largest value, giving the stated actual-world
consequence. Theorem 11.3 supplies an admissible strategy meeting
the hypothesis, so the implication has a nonempty class of
consumers. $\square$

**Proposition 12.5 (endpoints, degeneracies and the remaining finite-noise scope).**
At $E=1/2$, all assertions of Sections 11--12 include the endpoint,
and their first-order coefficients are respectively $1/4$ and
$7/24$, with endpoint-only penalty $1/24$. At $E=0$ both risks
are zero for every $c\ge0$. In the noiseless extension $c=0$,
both risks are zero for every finite $E\ge0$. For every fixed
$0<E\le1/2$, (11.14) bounds the unrestricted excess above
$H/2$ by a quantity of order $c^2$. These statements do not
identify that excess at a positive finite $c$ outside the inherited
exact regions, nor determine its second-order coefficient.

**Proof.** At $E=1/2$, $p_E=1/8$, $r_E=3/8$ and $k_E=5/8$.
The only potentially vanishing factors in (11.6) are $1-2x$ at
$x=1/2$; they occur as nonnegative summands and were never
divided by. The prefix bound remains $h\ge1/2$, the interpolated
gains remain strictly positive for $c<1$, and every denominator
in (12.2)--(12.19) is positive. Substituting $E=1/2$ in the
two limits gives the stated coefficients.

If $E=0$, the original target is the single known origin $z$;
the constant terminal rule $z$ has zero loss and may use only
$013$. Thus both nonnegative risks are zero. The fixed-positive-$E$
limits (11.14) and (12.11) are not asserted uniformly through
$E=0$. If $c=0$, any three distinct acquired reports determine
the common quadratic polynomial, whose leading coefficient is
$A\ge m>0$; its linear coefficient divided by $2A$ is the
original $\tau$. The ratios (11.3), or the exact-fiber supplier
of Three-Index Design, Theorem 3.1, therefore give zero loss.
No infinite gain or offset is needed in any boundary argument.

The error interval (11.14) has nonnegative lower endpoint and
an explicit positive upper endpoint for $c>0,E>0$ in its scope.
Neither the finite-world endpoint-only lower bound nor the
occupation consequence changes that lower endpoint to a positive
unrestricted gap. All earlier exact values and all upper consumers
remain valid on their original domains; their minimum with
(11.13) is an available upper bound. The unresolved question at
other finite-$c$ points is whether a lawful strategy attains $H/2$
or a stronger same-world lower argument excludes it.

The interpolation identities, convexity on a cube, triangle
inequalities and finite counting used here are intermediate
classical facts. The fixed-design separations, joint original
fibers and full-grid lower pair are the suppliers in
[Three-Index Design, Sections 2, 3 and 18](FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN.md),
with the chronological history contract in its Definition 23.1;
[Uniform Report Designs, Sections 30--34](FIB_UNCALIBRATED_QUADRATIC_CLOCK_UNIFORM_REPORT_DESIGNS.md)
supplies the deterministic comparison. The joint error calculation
(11.5), its actual-prefix consumer and the finite complete-world
inequality (12.5) are clock-specific deductions in the original
source model. They are repo-derived ordinary mathematical results,
without a claim of literature priority or empirical clock realization.

The literature correspondence remains limited to the hypotheses
actually shared. Casini--Garulli--Vicino,
[*A linear programming approach to online set membership parameter estimation for linear regression models*, Section 4, equations (7)--(10)](https://control.dii.unisi.it/~casini/pdf/IJACSP_2017a.pdf),
uses known regressors and bounded-error strips; here these are
$(i^2,i,1)$ and the coefficient vector $(A,2A\tau,A\tau^2+B)$.
Its orthotope construction bounds coordinate parameters and does
not provide the nonlinear ratio target's private minimax value.
Krieg--Novak--Ullrich,
[*On the power of adaption and randomization*, Sections 1--2](https://arxiv.org/html/2406.07108v2),
studies a continuous linear target on a convex Banach-space input
class and additionally requires product measurability of randomized
loss. Including the four original errors as input coordinates
makes the reports linear but leaves $\tau=\theta_1/(2\theta_2)$
nonlinear, and the chronological coordinate menu and per-world
measurability in Definition 1.2 remain unchanged. Consequently
those linear-target comparisons do not replace either (11.19)
or the finite integration proof (12.9)--(12.10). $\square$

## 追加锚（本行以下为增补区）

## 13. The projected prefix consumer at second order

**Definition 13.1 (normalized loss on one complete world).** Fix
$m>0$ and $E=1/10$. Throughout this section the consumer is exactly
$\Gamma^{\mathrm{prefix}}$ of Definition 11.1, including its terminal
projection. Put

$$
\begin{gathered}
r=\frac{11}{24},\qquad k=\frac{13}{24},\qquad
p_0=\frac1{24},\qquad L=\frac{11}{60},\\
x=\tau-z\in[-1/10,1/10],\qquad \alpha=A/m\ge1,\qquad
\eta_i=\frac{mc}{2}e_i,\quad e\in[-1,1]^4,\\
h=\alpha(1-x),\qquad v=\frac{e_0-e_1}{4},\\
d_{012}=\frac{e_0-2e_1+e_2}{4},\qquad
d_{013}=\frac{2e_0-3e_1+e_3}{12},\qquad
d_{023}=\frac{e_0-3e_2+2e_3}{12},\qquad
b_j=w_j(x)\mathbin{\cdot}e.
\end{gathered}
\tag{13.1}
$$

Here $w_j$ and $p$ are the original functions (11.4) and (11.1).
For $0<c\le1/200$, $h+cv\ge359/400>1/2$, so the lower
clamp in (11.2) is inactive on every complete world. The actual
path probabilities and unprojected errors are

$$
\begin{gathered}
(\lambda_{012},\lambda_{013},\lambda_{023})
 =\bigl(p(h+cv),\ k-p(h+cv),\ r\bigr),\\
\delta_j=\widehat x_j-x=\frac{c b_j}{12(\alpha+cd_j)}.
\end{gathered}
\tag{13.2}
$$

All denominators are positive: $|d_{012}|\le1$ and
$|d_{013}|,|d_{023}|\le1/2$. Write $\Pi$ for projection onto
$[-1/10,1/10]$, and define

$$
\ell_c(x,\alpha,e)=\sum_j\lambda_j|\Pi(x+\delta_j)-x|,
\qquad
\widetilde\ell_c(x,\alpha,e)=\sum_j\lambda_j|\delta_j|.
\tag{13.3}
$$

These are respectively the expected projected and unprojected
losses in the one fixed world. They are independent of its finite
offset $B$. Conversely every displayed $(x,\alpha,e)$ is realized
by a complete world with $A=m\alpha$, $\tau=z+x$, $B=0$ and
the four errors in (13.1). Thus the consumer risk is exactly
$\sup_{x,\alpha,e}\ell_c(x,\alpha,e)$ over the displayed domain.
The three summands are analytical evaluations in that same world;
each seed still acquires just its actual triple.

**Theorem 13.2 (all first-order equality faces).** Define

$$
\Phi(x,\alpha,e)=\frac{
 p(h)|b_{012}|+(k-p(h))|b_{013}|+r|b_{023}|}{12\alpha}.
\tag{13.4}
$$

Its maximum is $L$. Equality holds precisely when $\alpha=1$
and $(x,e)$ belongs to the following faces or their simultaneous
error sign reversals, with $-1\le u\le1$:

$$
\begin{array}{c|c|c}
\text{face}&x&e\\ \hline
\mathsf L_1&-1/10&(1,1,u,-1)\\
\mathsf L_2&-1/10&(1,u,1,-1)\\
\mathsf R&1/10&(1,u,-1,-1).
\end{array}
\tag{13.5}
$$

**Proof.** Lemma 11.2 gives $\Phi\le L$. We first track strictness
in its proof, before considering the errors. If $x\le0$, then
$p(h)=p_0$. The seven supports $M_i$ in (11.6) are convex in
$x$ on $[-1/10,0]$. At the left endpoint their maximum is
$11/10$, while at zero it is $13/12<11/10$. Consequently
$\Phi<L$ unless $x=-1/10$ and $\alpha=1$.

For $x\ge0$, use (11.8) to reduce to $C=M_3$, $J=M_7$ and
$3x$. Here $h_0=13/14$ and $x_0=1/14$. On the floor branch
with $x\le x_0$, (11.10) gives $C\le13/12$ and
$J\le1+x\le15/14$, both strictly below $11/10$.
On $h\le h_0$, (11.11)--(11.12) give
$C/\alpha,J/\alpha\le1+x$. Both inequalities are strict when
$\alpha>1$: the polynomial for $C/\alpha$ is strictly convex
in $1/\alpha$, and the positive factor $1+x-k/\alpha$ in
(11.12) cannot vanish. Also $3x/\alpha\le3/10<11/10$.
Thus equality on this branch requires $\alpha=1$ and $x=1/10$.
In the remaining case $x>x_0$, $h>h_0$, decrease $h$ to $h_0$
at fixed $x$. The resulting gain
$\alpha_0=h_0/(1-x)>1$ gives strict inequalities just established.
Each $M_i/\alpha$ can only increase under this decrease of $h$,
so the original point is strict as well. This exhausts $x\ge0$.

At either remaining endpoint set $P=(p(h),k-p(h),r)$. The
identity

$$
12\Phi(x,1,e)=
\max_{s\in\{-1,1\}^3}\left(\sum_j P_js_jw_j(x)\right)
 \mathbin{\cdot}e
\tag{13.6}
$$

allows an exhaustive equality calculation on the entire error cube.
Simultaneous reversal of $s$ reverses the coefficient vector, so
it suffices to put $s_{012}=1$. The cube maxima of the four
linear forms, divided by $12$, are

| $(s_{012},s_{013},s_{023})$ | $x=-1/10$ | $x=1/10$ |
|---|---|---|
| $(1,1,1)$ | $11/60$ | $11/60$ |
| $(1,1,-1)$ | $1/20$ | $11/720$ |
| $(1,-1,1)$ | $0$ | $8/135$ |
| $(1,-1,-1)$ | $11/60$ | $49/270$ |

These maxima are the sums of the absolute coefficients divided by
$12$. The coefficient vectors for the entries equal to $L$ are,
respectively,

$$
\begin{array}{c|c|c}
x&s&\sum_jP_js_jw_j(x)\\ \hline
-1/10&(1,1,1)&(-4/5,-3/10,0,11/10)\\
-1/10&(1,-1,-1)&(33/40,0,11/40,-11/10)\\
1/10&(1,1,1)&(-11/10,0,3/10,4/5).
\end{array}
\tag{13.7}
$$

Equality in a cube support forces every coordinate with nonzero
coefficient to have its coefficient's sign; a zero coefficient
leaves exactly that coordinate free. The other entries are strictly
below $L$. Including reversed signs therefore gives exactly (13.5),
and each displayed face attains $L$. This uses a signed-linear-form
identity for the first-order function, not a vertex reduction for
the finite-$c$ rational loss. $\square$

**Theorem 13.3 (uniform local expansion and inward penalties).** In
neighborhoods of the faces (13.5), let $p_h$ denote the derivative
of $p$ at $h$. It is zero near the left faces and $-k/h^2$ near
the right face. Define

$$
\Psi(x,\alpha,e)=\frac1{12}\left\{
 \frac{p_hv}{\alpha}(|b_{012}|-|b_{013}|)
 -\frac{p(h)|b_{012}|d_{012}
       +(k-p(h))|b_{013}|d_{013}+r|b_{023}|d_{023}}
       {\alpha^2}\right\}.
\tag{13.8}
$$

Uniformly on sufficiently small closed neighborhoods of these faces,

$$
\widetilde\ell_c=c\Phi+c^2\Psi+O(c^3).
\tag{13.9}
$$

For a limit point $e_*$ on a displayed face, put $t=x+1/10$
on the left and $t=1/10-x$ on the right, and $g=\alpha-1$.
As $(t,g,e)\longrightarrow(0,0,e_*)$ within the source domain,

$$
\Phi(x,\alpha,e)=\Phi(x_*,1,e)-D(u)t-Q(u)g+o(t+g),
\tag{13.10}
$$

where the coefficients and face values of $\Psi$ are

| face | $D(u)$ | $Q(u)$ | $\Psi(x_*,1,e_*)$ |
|---|---|---|---|
| $\mathsf L_1$ | $(15u+19)/144$ | $11/60$ | $11(3u^2+8u+13)/5760$ |
| $\mathsf L_2$ | $(15u+19)/144$ | $11/60$ | $-(3u^2-30u-17)/960$ |
| $\mathsf R$ | $1/6$ | $(195u+329)/1440$ | $(351u^2+39u-290)/8640$ |

Both penalty coefficients are strictly positive on $[-1,1]$.
Error sign reversal preserves $\Phi,D,Q$ and negates $\Psi$.

**Proof.** The left limiting prefix is $11/10>h_0$, and the
right one is $9/10<h_0$. These are separated from the probability
kink and from its upper truncation. Expand the actual probability
as $p(h+cv)=p(h)+cvp_h+O(c^2)$ and each positive reciprocal as
$(\alpha+cd_j)^{-1}=\alpha^{-1}-cd_j\alpha^{-2}+O(c^2)$.
All operands and the required derivatives are uniformly bounded
on the chosen closed neighborhoods and the whole error cube.
Substitution in (13.2)--(13.3) gives (13.8)--(13.9); in
particular the expansion is uniform also when some $b_j$ vanishes.

The signed values needed for the derivatives and for (13.8) are

$$
\begin{array}{c|c|c|c}
 &b_{012}/12&b_{013}/12&b_{023}/12\\ \hline
\mathsf L_1&11(u-1)/40&-11/60&-(u+7)/40\\
\mathsf L_2&3(1-u)/10&-(3u+19)/120&-1/5\\
\mathsf R&-(4u+5)/20&(u-7)/40&-11/60.
\end{array}
\tag{13.11}
$$

For the two left faces use $p=p_0$, $k-p=1/2$; differentiating
(13.4) gives $-\partial_x\Phi=(15u+19)/144$ and
$-\partial_\alpha\Phi=L$. For the right face use
$p=k/[\alpha(1-x)]-k$; the same differentiation gives
$\partial_x\Phi=1/6$ and
$-\partial_\alpha\Phi=(195u+329)/1440$.
For example on that face

$$
(d_{012},d_{013},d_{023})
 =(-u/2,(1-3u)/12,1/6),\qquad v=(1-u)/4,
$$

and substitution of these quantities and (13.11) into (13.8)
gives $(351u^2+39u-290)/8640$. On the left $p_h=0$,
and substitution gives the two other displayed quadratics.

For nonzero $b_j$ the derivatives used in (13.10) vary continuously
as $e$ approaches $e_*$. The only zero in (13.11) occurs when
$u=1$ on a left face, where $e_*=(1,1,1,-1)$ and
$b_{012}(x,e_*)=0$ for every $x$. Since $b_{012}$ is affine in
$x$,

$$
\bigl||b_{012}(x,e)|-|b_{012}(x_*,e)|\bigr|
 \le |x-x_*|\,|\partial_x b_{012}(x,e)|
 =o(|x-x_*|)
$$

as $e\to e_*$, and the corresponding gain derivative tends to
zero as well. This proves (13.10) even at the intersection of the
left faces, without assuming a rate for $e-e_*$. Finally $d_j$
and $v$ reverse sign while $|b_j|$ does not, proving the reversal
assertion. $\square$

**Theorem 13.4 (sharp projected-consumer second-order coefficient).**
For every $m>0$, at the fixed prior $E=1/10$,

$$
\boxed{
\mathcal R(\Gamma^{\mathrm{prefix}})
 =\frac{11c}{60}+\frac{5c^2}{432}+o(c^2)
 \qquad(c\downarrow0).
}
\tag{13.12}
$$

The supremum here is over all original complete worlds with finite
$A\ge m$, finite $B$ and the original four-error cube.

**Proof.** First fix, before the seed, the complete world

$$
\tau=z+1/10,\qquad A=m,\qquad B=0,\qquad
\eta=\frac{mc}{2}(1,1,-1,-1).
\tag{13.13}
$$

Its actual prefix perturbation is $v=0$, so its probabilities are
$13/216,13/27,11/24$. Its three errors point into the prior, and
for $0<c\le4/11$ their absolute values are at most $1/5$.
Indeed the largest constraint, from $012$, is
$9c/[20(1-c/2)]\le1/5$, equivalent to $11c\le4$; the
other two constraints are $c\le12/11$ and $c\le4/3$.
All three therefore hold on this interval. Projection
therefore leaves all three answers unchanged. The exact expected
loss in this complete world is

$$
\begin{aligned}
W(c)&=\frac{13}{216}\frac{9c}{20(1-c/2)}
 +\frac{13}{27}\frac{3c}{20(1-c/6)}
 +\frac{11}{24}\frac{11c}{60(1+c/6)}\\
&=Lc+\frac{5c^2}{432}+O(c^3).
\end{aligned}
\tag{13.14}
$$

This proves the required lower limit for this particular consumer's
worst-world risk, without a lower claim for other consumers.

For the upper limit we first control the unbounded gain domain.
For $|x|\le1/10$, every row in (11.4) has sum of absolute
coefficients at most $36/5$. Hence for every $\alpha\ge4$,

$$
\ell_c\le\widetilde\ell_c
 \le\frac{3c}{5(\alpha-c)}
 \le\frac{3c}{5(4-c)}<Lc
 \qquad(0<c\le1/200).
\tag{13.15}
$$

The lower witness tends to $Lc$ after division by $c$, with a
strictly larger limit than the right-hand side of (13.15) divided
by $c$. For all sufficiently small $c$, the risk supremum is
therefore attained in $1\le\alpha\le4$: on this compact domain
(13.3) is continuous in $(x,\alpha,e)$. This is a tail estimate,
not a restriction of the source gains.

Uniformly on that compact domain,
$\widetilde\ell_c=c\Phi+O(c^2)$, by the Lipschitz continuity
of the clamped probability and the positive denominator bounds.
Take any sequence $c\downarrow0$ of maximizers and pass to a
convergent subsequence in $(x,\alpha,e)$. Since
$\ell_c\ge W(c)$ and $\ell_c\le\widetilde\ell_c$, its limit
must satisfy $\Phi=L$. Theorem 13.2 places that limit on exactly
one of the faces (13.5) or a sign reversal.

Let $t,g$ be its inward distance and gain excess as in Theorem
13.3. The two strictly positive penalties in (13.10), the bound
$\Phi(x_*,1,e)\le L$, and the boundedness of $\Psi$ imply

$$
t+g=O(c).
\tag{13.16}
$$

To see the rate explicitly, in a sufficiently small neighborhood
(13.10) gives $\Phi\le L-\gamma(t+g)$ for some
$\gamma>0$. Equations (13.9) and (13.14) then give
$Lc-O(c^2)\le\ell_c\le Lc-\gamma c(t+g)+O(c^2)$.
This proves (13.16) without a rate assumption on the errors'
distance to their limiting face. Pass to a further subsequence
so that $t/c\to s\ge0$ and $g/c\to a\ge0$.

Projection now imposes an additional necessary condition on $s$.
The preceding bounds give both $\ell_c/c\to L$ and
$\widetilde\ell_c/c\to L$. Thus the projection loss, divided
by $c$, tends to zero. Every limiting path probability is strictly
positive. At the left endpoint, a path with limiting coefficient
$b_j/12<0$ would lose a positive first-order amount if
$s<-b_j/12$; at the right endpoint the same holds when
$b_j/12>0$ and $s<b_j/12$. This follows directly from clipping
an outward error of magnitude $c|b_j|/12+o(c)$ at distance
$t=cs+o(c)$ from that endpoint. The opposite endpoint is a
fixed distance $1/5+o(1)$ away and cannot be crossed by these
$O(c)$ errors. In particular (13.11) yields the necessary bounds
in the second column below. Some use just one path and need not
be the strongest necessary bound.

Dropping the nonpositive term
$[\Phi(x_*,1,e)-L]/c$ from (13.9)--(13.10), and dropping
the nonpositive gain penalty, gives

$$
\limsup\frac{\ell_c-Lc}{c^2}
 \le\Psi(x_*,1,e_*)-D(u)s-Q(u)a
 \le\Psi(x_*,1,e_*)-D(u)s.
\tag{13.17}
$$

All six possibilities are consequently bounded as follows:

| limiting errors | necessary $s\ge$ | upper expression in (13.17) | its maximum on $[-1,1]$ |
|---|---|---|---|
| $\mathsf L_1$ | $11/60$ | $11(3u-1)^2/17280$ | $11/1080$ |
| $-\mathsf L_1$ | $0$ | $-11(3u^2+8u+13)/5760$ | $-11/720$ |
| $\mathsf L_2$ | $1/5$ | $-(3u-5)^2/2880$ | $-1/720$ |
| $-\mathsf L_2$ | $3(1-u)/10$ | $11(u+1)(3u-5)/960$ | $0$ |
| $\mathsf R$ | $0$ | $(351u^2+39u-290)/8640$ | $5/432$ |
| $-\mathsf R$ | $11/60$ | $65/20736-13(18u+1)^2/103680$ | $65/20736$ |

For the first and third rows the bounds follow from
$|3u-1|\le4$ and $|3u-5|\ge2$. In the second row the
quadratic in parentheses is increasing on $[-1,1]$ with minimum
$8$. The fourth row is nonpositive because $u+1\ge0$ and
$3u-5<0$. The fifth row is convex, with endpoint values
$11/4320$ and $5/432$. The last row is a constant minus a
square, attaining that constant at $u=-1/18$.
All six maxima are at most $5/432$.

Every sequence realizing a limiting upper quotient has a
subsequence of the form just treated. The uniform expansions,
the gain tail and the inward-rate argument cover perturbations
off the equality faces as well as points on them. They therefore
give the global upper limit $5/432$. Together with the actual
complete-world lower witness (13.14), this proves (13.12).
Only finitely many seed-interval probabilities in one fixed world
were used at each step; no world-space integration or additional
measurability assumption is involved. $\square$

**Theorem 13.5 (explicit finite-noise improvement for the same consumer).**
For every $m>0$, $E=1/10$ and $0<c\le1/200$, put

$$
D_c=\frac9{10}-\frac c2,\qquad
B_{\mathrm{prefix}}(c)
 =\frac{11c}{60(1-c)}
   +\frac{13c^2}{72D_c(1-c)}
 =\frac{c(297+160c)}{180(1-c)(9-5c)}.
\tag{13.18}
$$

Then, on the entire original complete-world source,

$$
\begin{gathered}
R_{\mathrm{private}}(c,1/10)
 \le\mathcal R(\Gamma^{\mathrm{prefix}})
 \le B_{\mathrm{prefix}}(c),\\
U_*(c,1/10)-B_{\mathrm{prefix}}(c)
 =\frac{13c^2(4-5c)}{36(1-c)(9-5c)}>0.
\end{gathered}
\tag{13.19}
$$

In particular this is a strict improvement over the full preceding
minimum on an explicit nonempty interval, not just over $U$.

**Proof.** In one arbitrary complete world, $h\ge9/10$ and
$\widehat h=h+cv\ge D_c\ge359/400$. Clamping onto the
probability interval is nonexpansive, so

$$
|p(\widehat h)-p(h)|
 \le k\frac{|\widehat h-h|}{h\widehat h}
 \le\frac{kc}{2D_ch}.
\tag{13.20}
$$

The exact row difference (11.18) gives
$\bigl||b_{012}|-|b_{013}|\bigr|\le8(1-x)$ on the common
four-error cube. Applying Lemma 11.2 at the noiseless prefix and
then (13.20), with no change of world, yields

$$
\begin{aligned}
\sum_j\lambda_j|b_j|
 &\le2\alpha(1+E)
       +8(1-x)\frac{kc}{2D_ch}\\
 &=2\alpha(1+E)+\frac{4kc}{D_c\alpha}.
\end{aligned}
\tag{13.21}
$$

Using $\alpha+cd_j\ge\alpha(1-c)>0$ and projection's
nonincrease of error in (13.2)--(13.3) gives

$$
\ell_c\le\frac{c(1+E)}{6(1-c)}
 +\frac{kc^2}{3D_c\alpha^2(1-c)}
 \le B_{\mathrm{prefix}}(c).
\tag{13.22}
$$

The bound is uniform for every finite $\alpha\ge1$ and every
finite offset. The consumer, its independent uniform seed, its
total history rules, its three actual chronological acquisitions
and its per-world measurability are unchanged from Definition
11.1 and Theorem 11.3. Direct subtraction of (13.18) from
$U_*=[11c/60+13c^2/36]/(1-c)$ gives (13.19), with all
denominators positive on the closed upper endpoint $c=1/200$.
Proposition 11.4 gives the Sections 1--10 minimum $V>U$, while
$U_*\le U$. Thus $U_*$ is the full preceding minimum on this
band and (13.19) improves it strictly. $\square$

**Corollary 13.6 (unrestricted upper envelope and its scope).** Retain
every earlier applicable upper consumer in the minimum, adding
(13.18) only on its stated band. At $E=1/10$ and
$0<c\le1/200$ this gives

$$
\begin{gathered}
\frac{11c}{20(3+c)}\le R_{\mathrm{private}}(c,1/10)
 \le B_{\mathrm{prefix}}(c),\\
0\le R_{\mathrm{private}}(c,1/10)-\frac H2
 \le\frac{c^2(2163-335c)}
 {180(1-c)(9-5c)(3+c)},\\
0\le\liminf_{c\downarrow0}
 \frac{R_{\mathrm{private}}(c,1/10)-H/2}{c^2}
 \le\limsup_{c\downarrow0}
 \frac{R_{\mathrm{private}}(c,1/10)-H/2}{c^2}
 \le\frac{157}{2160}.
\end{gathered}
\tag{13.23}
$$

The sharp coefficient (13.12) is a statement about the specified
projected consumer. It does not identify the unrestricted
second-order coefficient or its finite-positive-$c$ exact minimax
value. No uniformity in a varying prior width is asserted.

**Proof.** On the band in question $c<3E$ and $H=G$, so the
original arbitrary-seed lower bound is
$H/2=11c/[20(3+c)]$. Subtracting it from (13.18) gives the
finite expression in (13.23). For the limiting bound use the
stronger consumer expansion (13.12) and

$$
\frac H2=\frac{11c}{60}-\frac{11c^2}{180}+O(c^3),
\qquad \frac5{432}+\frac{11}{180}=\frac{157}{2160}.
$$

The lower endpoint remains the all-strategy lower bound of Theorem
3.3; no endpoint-only obstruction is used to strengthen it.
All worlds in the proofs are complete and fixed before the seed,
all gains and offsets are finite, and all four errors remain
coordinates of the same original cube. The parameter endpoints
$x=\pm1/10$, $\alpha=1$ and $e_i=\pm1$ are included.
The finite bound includes $c=1/200$; its zero-noise extension has
value zero by exact quadratic interpolation as in Proposition
12.5. All preceding results retain their original scopes.

The intermediate tools are the classical signed support formula
for absolute values, Taylor expansion with uniform reciprocal
bounds, compactness and scalar projection. The interpolation and
joint-error suppliers are (11.4), Lemma 11.2 and (11.17), in the
original chronological experiment of Definitions 1.1--1.2.
The equality-face exhaustion, inward clipping analysis and the
complete-world family (13.13) give the clock-specific deduction.
This is a repo-derived ordinary mathematical result, with no
literature-priority or empirical-realization claim.

The literature correspondence is limited to the shared hypotheses.
Casini--Garulli--Vicino,
[*A linear programming approach to online set membership parameter estimation for linear regression models*, Section 4, equations (7)--(10)](https://control.dii.unisi.it/~casini/pdf/IJACSP_2017a.pdf),
uses known-regressor bounded-error feasible strips. Here the
regressors are $(i^2,i,1)$, the coefficient vector is
$(A,2A\tau,A\tau^2+B)$, and the target is its nonlinear ratio
$\tau=\theta_1/(2\theta_2)$. Coordinate orthotope bounds do
not supply (13.12). Krieg--Novak--Ullrich,
[*On the power of adaption and randomization*, Sections 1--2](https://arxiv.org/html/2406.07108v2),
studies continuous linear targets on convex Banach-space input
classes and requires product measurability of randomized loss.
Its comparison results do not instantiate this nonlinear target,
chronological coordinate menu and per-world-only measurability.
Neither source is used as a minimax or boundary-layer theorem
for the present experiment. $\square$

## 追加锚（本行以下为增补区）

## 14. An affine continuation with zero second-order risk coefficient

**Definition 14.1 (affine continuation).** Retain the complete source,
chronology, target and risk of Definitions 1.1--1.2, with $m>0$ and
$E=1/10$. Put

$$
\begin{gathered}
r=\frac{11}{24},\qquad k=\frac{13}{24},\qquad
p_0=\frac1{24},\qquad L=\frac{11}{60},\\
a_0=\frac{389}{1080},\qquad \beta=\frac{25}{648},\qquad
P_c(t)=\min\{k,\max\{p_0,a_0-t/3-\beta c\}\}
\quad(t\ge1/2),\\
P(t)=P_0(t),\qquad h_0=\frac{43}{45},\qquad x_0=\frac2{45}.
\end{gathered}
\tag{14.1}
$$

For each $c>0$, use the independent uniform seed $u\in[0,1]$.
After the first report choose index $2$ when $u<r$ and index $1$
otherwise; after index $2$ choose $3$. At every real $01$ history
$(r_0,r_1)$ put $\bar h=\max\{1/2,(r_0-r_1)/(2m)\}$ and
choose $2$ when $r\le u<r+P_c(\bar h)$, and $3$ otherwise.
Use exactly the terminal ratios, positive-gain test, fallback $z$,
and projection onto $K$ in (11.3) and Definition 11.1. Denote this
strategy by $\Gamma^{\mathrm{aff}}$.

For the analysis use exactly the coordinates $(x,\alpha,e,h,v,d_j,b_j)$
in (13.1), with the rows $w_j(x)$ in (11.4), and the projection
$\Pi$ in (13.3). For $0<c\le1/200$, $h\ge9/10$ and
$h+cv\ge359/400>1/2$. The actual path probabilities and errors
before projection are therefore

$$
\begin{gathered}
\lambda_c=(P_c(h+cv),\ k-P_c(h+cv),\ r),\qquad
\delta_j=\frac{cb_j}{12(\alpha+cd_j)},\\
\ell_c=\sum_j\lambda_{c,j}|\Pi(x+\delta_j)-x|,\qquad
\widetilde\ell_c=\sum_j\lambda_{c,j}|\delta_j|,\\
\Phi=\frac{P(h)|b_{012}|+(k-P(h))|b_{013}|+r|b_{023}|}
 {12\alpha}.
\end{gathered}
\tag{14.2}
$$

The errors here are the original four coordinates
$\eta_i=mc e_i/2$. The identity for $\delta_j$ is (11.17) with
$A=m\alpha$ and these errors, and so does not depend on the
continuation probability. Every $(x,\alpha,e)$ in
$[-1/10,1/10]\times[1,\infty)\times[-1,1]^4$ is realized by
$\tau=z+x$, $A=m\alpha$, $B=0$ and this error vector.
The loss is independent of arbitrary finite $B$.

**Lemma 14.2 (global support and equality exhaustion).** On the entire
coordinate domain in Definition 14.1, $\Phi\le L$. Equality holds
exactly at $\alpha=1$ and the following faces, or their simultaneous
error sign reversals, where $-1\le u\le1$:

$$
\begin{array}{c|c|c}
 &x&e\\ \hline
\mathsf L_1&-1/10&(1,1,u,-1)\\
\mathsf L_2&-1/10&(1,u,1,-1)\\
\mathsf R&1/10&(1,u,-1,-1).
\end{array}
\tag{14.3}
$$

**Proof.** Set $p=P(h)$ and $q=k-p$. Since $h\ge9/10$,
the upper truncation is inactive, $p\ge p_0$ and $q\le1/2$.
The convex cube support calculation (11.6) applies with exactly
these $p,q,r$, the same $x$ and the same four errors: each row
sums to zero, and the seven nonzero vertex values of
$\sum_j(P(h),q,r)_j|b_j|$, divided by $2$, are its $M_i$.
Thus it suffices to bound $M_i/\alpha$ by $11/10$.

When $x\le0$, $h\ge1>h_0$, hence $p=p_0$ and $q=1/2$.
The seven functions are precisely the left-half functions in the
proof of Lemma 11.2 at $E=1/10$. They are convex in $x$;
their maxima at $x=-1/10$ and $x=0$ are respectively $11/10$
and $13/12$. Convex interpolation is strictly below $11/10$
for $x>-1/10$. Division by $\alpha\ge1$ then shows that
equality on this half requires $x=-1/10$, $\alpha=1$.

For $x\ge0$, the subtractions (11.8) use only
$p\ge p_0$, $q\le1/2$, $p+q+r=1$ and $0\le x\le1/2$;
these conditions hold here. It remains to bound

$$
C=M_3=1-x/12+2p(1-x),\qquad
J=M_7=1-p+x(2-r+p),\qquad M_6=3x.
\tag{14.4}
$$

If $x\le x_0$, then $h\ge1-x\ge h_0$, so $p=p_0$ and

$$
C=13/12-x/6\le13/12<11/10,\qquad
J=23/24+19x/12\le1111/1080<11/10.
\tag{14.5}
$$

For $x>x_0$ on the affine branch $h\le h_0$, put
$w=1/\alpha$. Substitution of $p=a_0-\alpha(1-x)/3$ gives

$$
\begin{aligned}
C/\alpha&=\left(\frac{929}{540}-\frac{217x}{270}\right)w
 -\frac23(1-x)^2,\\
J/\alpha&=\left(\frac{691}{1080}+\frac{1027x}{540}\right)w
 +\frac13(1-x)^2.
\end{aligned}
\tag{14.6}
$$

Both coefficients of $w$ are positive for $0\le x\le1/10$.
Each expression is therefore strictly smaller than its value at
$\alpha=1$ when $\alpha>1$. At $\alpha=1$, direct subtraction
gives

$$
\begin{aligned}
11/10-C&=\frac{(1-10x)(25-36x)}{540},\\
11/10-J&=\frac{(1-10x)(36x+137)}{1080}.
\end{aligned}
\tag{14.7}
$$

Both are nonnegative and vanish only at $x=1/10$.
If instead $x>x_0$ and $h>h_0$, decrease the gain to
$\alpha_0=h_0/(1-x)>1$. Along this decrease $p=p_0$
and each nonnegative $M_i/\alpha$ increases; at the boundary
(14.6) gives a strict bound. Finally $3x/\alpha\le3/10<11/10$.
This proves the global bound and confines all equality to the two
endpoints with $\alpha=1$.

At the left endpoint the probability triple is
$(p_0,1/2,r)$; at the right it is
$(13/216,13/27,r)$, since $P(9/10)=13/216$.
These are exactly the endpoint triples in (13.6)--(13.7).
The signed-support identity (13.6) concerns only the endpoint
rows and these triples, so its four signed linear forms and
coefficient vectors (13.7) apply without a change of parameters.
Their only supports equal to $12L$ have one free error coordinate
and force all other coordinates to their displayed signs.
Consequently their equality sets are exactly (14.3) and their
reversals. Every other signed support is strictly smaller.
This proves equality exhaustion on the whole cube, rather than
only at its vertices. $\square$

**Lemma 14.3 (uniform expansion at all equality faces).** Near the
left faces put $\rho=0$, $P_h=0$; near the right face put
$\rho=-\beta$, $P_h=-1/3$. Define

$$
\Psi=\frac1{12}\left\{
\frac{P_hv+\rho}{\alpha}(|b_{012}|-|b_{013}|)
-\frac{P(h)|b_{012}|d_{012}+(k-P(h))|b_{013}|d_{013}
 +r|b_{023}|d_{023}}{\alpha^2}\right\}.
\tag{14.8}
$$

Uniformly on sufficiently small closed neighborhoods of the faces,
including their reversals and intersections,

$$
\widetilde\ell_c=c\Phi+c^2\Psi+O(c^3).
\tag{14.9}
$$

For a limiting face point $e_*$, let $t=x+1/10$ on the left,
$t=1/10-x$ on the right, and $g=\alpha-1$. Within the source
domain, as $(t,g,e)\to(0,0,e_*)$,

$$
\Phi(x,\alpha,e)=\Phi(x_*,1,e)-D(u)t-Q(u)g+o(t+g),
\tag{14.10}
$$

with strictly positive coefficients

$$
\begin{array}{c|c|c}
 &D(u)&Q(u)\\ \hline
\mathsf L_1,\mathsf L_2&(15u+19)/144&11/60\\
\mathsf R&(917-489u)/6480&(81u+247)/1200.
\end{array}
\tag{14.11}
$$

Sign reversal preserves $D,Q$. The values of $\Psi$ on the
positive faces and the reversed right face are

$$
\begin{array}{c|c}
 &\Psi(x_*,1,e_*)\\ \hline
\mathsf L_1&11(3u^2+8u+13)/5760\\
\mathsf L_2&-(3u^2-30u-17)/960\\
\mathsf R&(u-1)(282u+391)/12960\\
-\mathsf R&-(141u^2+167u-158)/6480.
\end{array}
\tag{14.12}
$$

On a reversed left face $\Psi$ is the negative of its positive-face
value.

**Proof.** The limiting prefixes are $11/10$ on the left and
$9/10$ on the right. They are separated from $h_0=43/45$,
the lower history clamp, and the upper probability truncation.
For all small $c$, the same branches remain active on fixed closed
neighborhoods of the faces. There
$P_c(h+cv)=P(h)+c(P_hv+\rho)$ exactly. Expanding
$(\alpha+cd_j)^{-1}=\alpha^{-1}-cd_j\alpha^{-2}+O(c^2)$
uniformly gives (14.8)--(14.9). The $b_j$ remain bounded, and
the expansion does not differentiate $|b_j|$; it is uniform even
where $b_j=0$.

For the face derivatives and substitutions, the three signed
values $b_j/12$ are exactly (13.11), since the $x,e$ coordinates
and terminal ratios are unchanged. The left first-order
probabilities and their local derivatives also coincide with those
in Theorem 13.3, so its left values of $D,Q,\Psi$ apply with
$E=1/10$, $\alpha=1$, $p=p_0$, $q=1/2$, and $r=11/24$.
On the right set

$$
\begin{gathered}
(a_{012},a_{013},a_{023})
 =\left(-\frac{4u+5}{20},\frac{u-7}{40},-\frac{11}{60}\right),\\
(d_{012},d_{013},d_{023})
 =\left(-\frac u2,\frac{1-3u}{12},\frac16\right),\qquad
v=\frac{1-u}{4},\qquad
f=|a_{012}|-|a_{013}|=\frac{9u+3}{40}.
\end{gathered}
\tag{14.13}
$$

All $a_j$ here are strictly negative on $[-1,1]$.
Differentiating the explicit rows in (11.4), with
$p=13/216$, $q=13/27$, gives

$$
\begin{aligned}
D&=\frac f3-p\frac u2+q\frac{1-3u}{12}+\frac r6
 =\frac{917-489u}{6480},\\
Q&=L+\frac3{10}f=\frac{81u+247}{1200},\\
\Psi_{\mathsf R}&=(-v/3-\beta)f
 +\sum_j(p,q,r)_j a_jd_j
 =\frac{(u-1)(282u+391)}{12960}.
\end{aligned}
\tag{14.14}
$$

Upon reversing all errors, $v,d_j$ reverse while $|a_j|$ do
not. The probability correction $-\beta$ is unchanged.
Thus the reversed value is
$(v/3-\beta)f-\sum_j(p,q,r)_j a_jd_j$, giving the last
row of (14.12). The left reversal rule follows because its
correction $\rho$ is zero.

The smallest possible values of $D,Q$ are positive: on the left
$D\ge1/36$, $Q=L$; on the right
$D\ge107/1620$, $Q\ge83/600$.
For nonzero $b_j$ the derivatives in (14.10) are continuous as
the errors approach $e_*$. The only zero face value is
$b_{012}=0$ at the left intersection $e_*=(1,1,1,-1)$,
or its reversal. At this vector $b_{012}(x,e_*)=0$ for every
$x$. The affine dependence on $x$ consequently gives

$$
\bigl||b_{012}(x,e)|-|b_{012}(x_*,e)|\bigr|
 \le |x-x_*|\,|\partial_x b_{012}(x,e)|=o(|x-x_*|)
\tag{14.15}
$$

as $e\to e_*$. Its gain derivative also tends to zero.
The other terms have continuous derivatives. Integration of these
local derivatives proves (14.10) with remainder $o(t+g)$,
without a rate assumption on $e-e_*$, including intersections
and all sign faces. $\square$

**Theorem 14.4 (global risk of the affine continuation).** For every
$m>0$, Definition 14.1 is a total lawful strategy for the original
three chronological readings. At $E=1/10$,

$$
\boxed{\mathcal R(\Gamma^{\mathrm{aff}})
 =\frac{11c}{60}+o(c^2)\qquad(c\downarrow0).}
\tag{14.16}
$$

Moreover, for every $0<c\le1/200$,

$$
R_{\mathrm{private}}(c,1/10)
 \le\mathcal R(\Gamma^{\mathrm{aff}})
 \le B_{\mathrm{new}}(c):=
 \frac{c(132+121c)}{720(1-c)}.
\tag{14.17}
$$

**Proof.** The probability $P_c$ always lies in $[p_0,k]$.
The history rules are total on all real legal histories. The
terminal rule uses a positive denominator or the finite fallback,
and then projection onto the finite prior. Thus it is defined even
on unreachable histories or when $c$ is outside the band of the
bounds. Every seed acquires exactly $012$, $013$ or $023$ in
chronological order. For each fixed complete world, the path events
are seed intervals and the terminal answer is one of three fixed
real numbers. This proves per-world measurability, including
boundary seeds; no world-space measure is required.

To prove the finite bound, clamping is nonexpansive and the affine
part has slope $-1/3$, so on each complete world

$$
|P_c(h+cv)-P(h)|\le c|v|/3+\beta c\le\frac{133c}{648}.
\tag{14.18}
$$

The exact row difference (11.18) uses our same $x,e$, and gives
$\bigl||b_{012}|-|b_{013}|\bigr|\le8(1-x)$.
Lemma 14.2 therefore yields

$$
\sum_j\lambda_{c,j}|b_j|
 \le\frac{11\alpha}{5}+8(1-x)\frac{133c}{648}.
\tag{14.19}
$$

As in (13.1), $|d_{012}|\le1$ and
$|d_{013}|,|d_{023}|\le1/2$, so
$\alpha+cd_j\ge\alpha(1-c)>0$. Projection cannot increase
error. Using $1-x\le11/10$ and $\alpha\ge1$ in (14.2) gives

$$
\ell_c\le\frac{Lc}{1-c}
 +\frac{1463c^2}{9720(1-c)}
 \le\frac{Lc}{1-c}+\frac{121c^2}{720(1-c)}
 =B_{\mathrm{new}}(c),
\tag{14.20}
$$

where $121/720-1463/9720=341/19440>0$.
This estimate is uniform over all finite gains and offsets and the
entire original error cube, proving (14.17).

For the matching second-order lower limit for this consumer, fix
before the seed the legal complete world

$$
\tau=z+1/10,\qquad A=m,\qquad B=0,\qquad
\eta=\frac{mc}{2}(1,1,-1,-1).
\tag{14.21}
$$

Its prefix has $v=0$ and $h=9/10$, and its path probabilities
are $(13/216-\beta c,13/27+\beta c,r)$ throughout the band.
Its three interpolation errors are exactly those in (13.14):
all point inward and their largest magnitude is
$9c/[20(1-c/2)]\le1/5$ for $c\le4/11$.
Thus projection is inactive. If $W(c)$ denotes the exact rational
loss (13.14), its new expected loss is

$$
\begin{aligned}
W_{\mathrm{aff}}(c)
 &=W(c)-\beta c\left\{
 \frac{9c}{20(1-c/2)}-\frac{3c}{20(1-c/6)}\right\}\\
 &=Lc+\left(\frac5{432}-\frac{3\beta}{10}\right)c^2+O(c^3)
 =Lc+O(c^3).
\end{aligned}
\tag{14.22}
$$

The parameter correspondence to (13.13)--(13.14) is exact:
$x=1/10$, $\alpha=1$, $e=(1,1,-1,-1)$ and the same
terminal estimates; only the $012/013$ probabilities transfer
mass $\beta c$. Hence this is a fixed-before-seed complete-world
witness for this consumer, and gives its lower limiting quotient
zero after subtracting $Lc$ and dividing by $c^2$.

For the upper limit, first retain the full unbounded gain domain.
The rows (11.4) have absolute coefficient sums at most $36/5$.
For all $\alpha\ge4$ and $0<c\le1/200$, any probability
triple in (14.2) consequently satisfies

$$
\ell_c\le\widetilde\ell_c\le\frac{3c}{5(\alpha-c)}
 \le\frac{3c}{5(4-c)}<Lc.
\tag{14.23}
$$

After division by $c$, this tail has a uniform strict gap from
$L$, whereas $W_{\mathrm{aff}}(c)/c\to L$. For all sufficiently
small $c$ the supremum is attained on the compact set
$|x|\le1/10$, $1\le\alpha\le4$, $e\in[-1,1]^4$,
since the projected loss is continuous there. This removes no
source worlds from the definition of risk.

On this compact set, the global Lipschitz bound (14.18) and the
uniform reciprocal bounds give
$\widetilde\ell_c=c\Phi+O(c^2)$ uniformly, including at the
probability kink. For any sequence $c\downarrow0$, choose
maximizers and pass to a convergent subsequence. By (14.22),
$\ell_c/c$ has lower limit at least $L$, while
$\ell_c\le\widetilde\ell_c$ and Lemma 14.2 give upper limit
at most $L$. Its limit point therefore satisfies $\Phi=L$ and
belongs to exactly the faces (14.3) or their reversals.

Let $t,g$ be its inward distance and gain excess in Lemma 14.3.
Since $\Phi(x_*,1,e)\le L$ for every $e$ and the two
penalties in (14.10) are positive, a sufficiently small neighborhood
has $\Phi\le L-\gamma(t+g)$ for some $\gamma>0$.
Combining (14.9) with the lower witness
$\ell_c\ge Lc-O(c^3)$ proves $t+g=O(c)$.
Pass to a further subsequence with $t/c\to s\ge0$,
$g/c\to a\ge0$. No rate for the errors' distance to the
limiting face has been assumed or deduced.

The projected and unprojected losses divided by $c$ both tend to
$L$, so their difference divided by $c$ tends to zero. Every
limiting path probability is positive. An outward path with limiting
absolute error coefficient $M$ therefore requires $s\ge M$:
otherwise its projection loss divided by $c$ tends to its positive
path probability times $M-s$. The other endpoint remains a
positive distance away and cannot clip these $O(c)$ errors.
This argument uses the exact scalar projection in each one fixed
world and supplies all the necessary bounds below.

Dropping the nonpositive error-support deficit and gain penalty
in (14.9)--(14.10) gives

$$
\limsup\frac{\ell_c-Lc}{c^2}
 \le\Psi(x_*,1,e_*)-D(u)s-Q(u)a
 \le\Psi(x_*,1,e_*)-D(u)s.
\tag{14.24}
$$

The following table exhausts its upper bounds. Each displayed
expression is nonpositive on its stated interval.

| limiting face | interval | necessary $s\ge$ | upper expression in (14.24) |
|---|---|---|---|
| $\mathsf L_1$ | $[-1,1/3]$ | $11(1-u)/40$ | $11(u+1)(3u-1)/960$ |
| $\mathsf L_1$ | $[1/3,1]$ | $(u+7)/40$ | $(3u-5)(3u-1)/2880$ |
| $-\mathsf L_1$ | $[-1,1]$ | $0$ | $-11(3u^2+8u+13)/5760$ |
| $\mathsf L_2$ | $[-1,1]$ | $1/5$ | $-(3u-5)^2/2880$ |
| $-\mathsf L_2$ | $[-1,1]$ | $3(1-u)/10$ | $11(u+1)(3u-5)/960$ |
| $\mathsf R$ | $[-1,1]$ | $0$ | $(u-1)(282u+391)/12960$ |
| $-\mathsf R$ | $[-1,-1/3]$ | $(7-u)/40$ | $-(3u+1)(227u+11)/28800$ |
| $-\mathsf R$ | $[-1/3,1]$ | $(4u+5)/20$ | $-(3u+1)(96u+475)/43200$ |

Indeed, on $\mathsf L_1$ all nonzero path errors point outward
at the left endpoint, and their maximum absolute coefficient is
$11(1-u)/40$ for $u\le1/3$ and $(u+7)/40$ for $u\ge1/3$;
all three coefficients meet at $11/60$ when $u=1/3$.
On $\mathsf L_2$, path $023$ gives $1/5$; on its reversal,
path $012$ gives $3(1-u)/10$. The reversed $\mathsf L_1$
errors point inward. On $\mathsf R$ the errors point inward;
on its reversal they point outward, and (14.13) has largest
absolute coefficient $(7-u)/40$ for $u\le-1/3$ and
$(4u+5)/20$ for $u\ge-1/3$. All three meet at $11/60$
when $u=-1/3$. These facts give the third column directly.
Substitution of (14.11)--(14.12) gives the fourth column.
For its third row, $3u^2+8u+13\ge8$ on $[-1,1]$.
In its sixth row $282u+391\ge109$; in the seventh both
$3u+1$ and $227u+11$ are nonpositive; in the eighth both
$3u+1$ and $96u+475$ are nonnegative. The signs of the
other factorizations are immediate from their interval endpoints.

Thus every limiting face, every sign reversal and their intersections
have upper quotient at most zero. The compactness argument, the
uniform expansion, the inward-rate estimate and the discarded
nonpositive support deficit also cover arbitrary off-face sequences.
The gain tail (14.23) covers escaping gains. Every sequence of
maximizers therefore has limiting upper quotient at most zero.
Together with (14.22), this proves (14.16) for the complete source.
The simultaneous summands always evaluate one pre-seed world's
four original errors; the strategy acquires only its actual triple.
$\square$

**Corollary 14.5 (comparisons and unrestricted residual envelope).**
On $0<c\le1/200$, $B_{\mathrm{new}}$ is strictly below the
Section 13 bound, with

$$
B_{\mathrm{prefix}}(c)-B_{\mathrm{new}}(c)
 =\frac{c^2(211+605c)}{720(1-c)(9-5c)}>0.
\tag{14.25}
$$

For all sufficiently small positive $c$, the actual risks satisfy
$\mathcal R(\Gamma^{\mathrm{aff}})
 <\mathcal R(\Gamma^{\mathrm{prefix}})$.
All earlier applicable consumers remain available in the upper
minimum, with (14.17) added on its stated band. The original
arbitrary-seed lower bound remains $H/2$; specifically,

$$
\begin{gathered}
\frac H2=\frac{11c}{20(3+c)}
 \le R_{\mathrm{private}}(c,1/10)\le B_{\mathrm{new}}(c)
 \qquad(0<c\le1/200),\\
0\le\liminf_{c\downarrow0}
 \frac{R_{\mathrm{private}}(c,1/10)-H/2}{c^2}
 \le\limsup_{c\downarrow0}
 \frac{R_{\mathrm{private}}(c,1/10)-H/2}{c^2}
 \le\frac{11}{180}.
\end{gathered}
\tag{14.26}
$$

**Proof.** Subtracting (14.17) from (13.18) gives (14.25),
whose denominators are positive on the entire stated band.
Theorem 13.4 concerns exactly the unchanged old consumer, and
(14.16) concerns the affine consumer; their difference is
$5c^2/432+o(c^2)>0$ eventually. Proposition 11.4 and Theorem
13.5 compare all earlier applicable published upper bounds on
this band, so (14.25) also improves their minimum. Outside this
band the earlier domains and conclusions remain unchanged.

Theorem 3.3 applies to all strategies of Definition 1.2, including
the present one; $H/2=11c/[20(3+c)]$ here because $c<3E$
and $E=1/10$. Expanding it gives
$H/2=Lc-11c^2/180+O(c^3)$. Use the sharper actual-consumer
expansion (14.16), rather than the finite majorant, for the last
inequality in (14.26). The witness (14.21) supports the exact
coefficient of this specified consumer only. Neither equality in
the last inequality, existence of an unrestricted second-order
coefficient, nor a finite-noise unrestricted minimax value follows.
The finite band includes its upper endpoint. At $c=0$ the
terminal quadratic interpolation recovers the origin exactly for
all finite gains and offsets. No uniformity in a varying $E$ is
asserted.

The intermediate methods are joint cube supports, reciprocal
expansion, compactness and scalar projection. Their clock inputs
are the original interpolation identities (11.4), (11.17) with
$\eta=mc e/2$, $A=m\alpha$, $x=\tau+3/2$, and the
endpoint signed supports (13.6)--(13.7). The new affine probability
requires its own global support proof (14.4)--(14.7); the old
probability's global maximizer assertion is not transferred.
The endpoint-only results of Section 12 retain their restricted
scope and are not used as unrestricted second-order lower bounds.

The bounded-error regression correspondence in Casini--Garulli--Vicino,
[*A linear programming approach to online set membership parameter estimation for linear regression models*, Section 4, equations (7)--(10)](https://control.dii.unisi.it/~casini/pdf/IJACSP_2017a.pdf),
uses known regressors and feasible strips. Its parameters correspond
to $(i^2,i,1)$, $(A,2A\tau,A\tau^2+B)$ and noise bound
$mc/2$ here; its coordinate orthotope bounds do not identify the
nonlinear ratio $\tau=\theta_1/(2\theta_2)$ under the present
chronological choices. Krieg--Novak--Ullrich,
[*On the power of adaption and randomization*, Sections 1--2](https://arxiv.org/html/2406.07108v2),
uses continuous linear targets on convex Banach-space input classes
and product measurability of randomized loss. The augmented clock
reports are linear, but the target remains the displayed nonlinear
ratio and Definition 1.2 requires only per-world seed measurability.
Those hypotheses therefore do not supply (14.16), a minimax
interchange, or an unrestricted second-order lower certificate.
The affine continuation and its global risk calculation are
repo-derived mathematical deductions; no literature-priority or
empirical-realization assertion is made. $\square$

## 追加锚（本行以下为增补区）
