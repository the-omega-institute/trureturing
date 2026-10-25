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
