# Third-germ whole-child scalar-retention threshold

> This volume is append-only mathematical reference input for `generic-v1`.
> It contains ordinary conditional mathematics, not a new Lean certification.
> Published definitions and statements remain fixed; corrections and additions
> belong after the final append anchor.

## 1. The bounded recovery question and its suppliers

**Convention 1.1 (scope and evidence).** The question is exact recovery of
one complete original world after the original clock-seven $J$ acquisition,
when the acquired base $(p,v)$ remains exact and only retention of the last
scalar is changed. The change is the full closed error relation of
Definition 5.1, with a known common radius. The source, initialization,
gain, drift, clock convention and actual action word are unchanged.

The complete-child inventories, analytic germ and source jets below are
reused results. So are noiseless inversion on a $J$-injective child and
the interval-disjointness/midpoint recovery principle. The additional
source-specific conclusions are the attained whole-child minimum, its
rate relative to the original acquired coordinates, and the resulting
sharp retention condition. They are `repo-derived` deductions under the
stated supplier interfaces; no worldwide-originality claim is made.

**Convention 1.2 (fixed ordinary sources).** The following abbreviations
refer to the complete original volumes at the indicated revisions.

| Name | Source and fixed scope |
| --- | --- |
| O | [Common Parent Geometry and Mixed Children](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), at `4442fb66c4d7017bb7b932cc63f058b46c83b71c`; Definitions 1.1–1.3 and Theorem 2.1 supply the complete original parent and its zero-safe converse. |
| III | [Strict Real Joint Incidence Support III](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md), at `4442fb66c4d7017bb7b932cc63f058b46c83b71c`; its full-parent and source-exhaustion results retain their original strata and guards. |
| VI | [Strict Real Joint Incidence Support VI](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VI.md), at `4442fb66c4d7017bb7b932cc63f058b46c83b71c`; §§13–24 also have their historical pin `0c3db7ce36b940d4c751fb35810a8d7c9cf7cbeb`. The exact critical world, jets, germ, remote companion and entire-child inventory are reused from §§13–23. Sections 25–26 have the separate scope described in §7. |
| V | [Strict Real Joint Incidence Support V](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md), including the complete §§13–18, at `e3dfce7cb69bdd30394ce5268eb47b829856ad28`; its second-region exclusion is assessed in §7. |
| X | [Strict Real Joint Incidence Support X](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_X.md), §§7–11, at `42bd459809a2d44a7fb0f8a76de8da32ec90774e`. Its own supplier revision `403741dec0c5df912168c53ed1cdce6707041300` remains distinct. |

Source attribution is part of the hypotheses of the deductions here.
Reading ordinary sources or declaration text does not establish current
Lean certification. In particular the numerical interval and elimination
certificates underlying the reused inventory are not new computations
of this volume.

## 2. The complete source, actual history and recovery target

**Definition 2.1 (original complete worlds).** An original world is
$W=(P(r,b),g,d)$, where

$$
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad d\in\mathbb R,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3.
\tag{2.1}
$$

There is one whole polynomial $g$ and one fixed drift $d$ on the entire
run. Put $c=r(1-r)/b$ and

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP).
\tag{2.2}
$$

The original history through clock four is

$$
H_4=(0,J,24,M,147/5,J,24,M,18).
\tag{2.3}
$$

Let $\mathcal H$ be the set of **all** complete worlds realizing this
literal history. No regular-chart, gain-sign, degree-exactly-three,
nonzero-sample, distinct-root or nonzero-drift condition is added.
Singular sources, lower degrees, repeated roots and zero samples remain
in the original domain. The only excluded gain is the identically zero
polynomial, already impossible from the unequal readings $0$ and $24$.

**Definition 2.2 (the actual continuation and entire child).** Write

$$
j=b+c,\qquad n=j+r,\qquad T=1+b,\qquad U=1+2b.
$$

The actual fifth and sixth actions are $M,M$, giving

$$
p(W)=d+(U+n)g(5),\qquad v(W)=d+(2U+n)g(6).
\tag{2.4}
$$

The actual seventh action in this volume is $J$, with acquired value

$$
a(W)=d+(T+2j+4r)g(7).
\tag{2.5}
$$

The function

$$
m(W)=d+(3U+2n)g(7)
\tag{2.6}
$$

denotes the alternative seventh-$M$ reply on that same world. It is
**not acquired** on this run. Set

$$
\Phi(W)=(p(W),v(W)),\qquad
C(y)=\{W\in\mathcal H:\Phi(W)=y\},\quad y\in\mathbb R^2.
\tag{2.7}
$$

Thus an entire child includes every original complete-world companion,
whether or not it belongs to the local chart used to construct a germ.
The recovery target is the complete triple $W$, in the same sense as O
and VI. It determines the original clock-seven source $Q_7P$, its whole
gain and drift, and all readings of the fixed run. It does not include a
new future invocation right or an extra source label.

**Convention 2.3 (zero-safe membership).** The following convenient
description is O, Theorem 2.1, specialized to the present $H_4$. For
$e=d-24$, put

$$
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\qquad
\kappa=\frac6T-\frac2U>0.
$$

The full parent is in bijection with the triples $(r,b,e)$ satisfying

$$
0<r<1,\quad b>0,\qquad
e\Lambda+\frac{24}{5}(b-1/8)\kappa=0.
\tag{2.8}
$$

The corresponding entire gain is uniquely fixed by its samples

$$
(g(0),g(1),g(2),g(3))
=\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right).
\tag{2.9}
$$

Fixed-node interpolation supplies the degree-at-most-three polynomial;
(2.8) is exactly the remaining clock-four compatibility condition.
The positive denominators $T,U,j,n$ do not exclude zero gain samples.
There is no division here by $e$, $\Lambda$, a gain coefficient or a
root difference. Later regular coordinates describe the particular
local worlds, rather than replacing this definition of $C(y)$.

## 3. Reused third-germ interface

**Convention 3.1 (exact center and analytic coordinates).** Let $W_3$ be
the exact algebraic complete world of VI, Definition 13.1, with
$b_3$ the specified unique root of its polynomial $F$ in
$(12758053/10^8,12758054/10^8)$ and the source's specified algebraic
lift. This referenced algebraic definition, not a rounded decimal,
fixes $W_3$. Put $y_3=(p_3,v_3)=\Phi(W_3)$ and $t_3=r_3/b_3$.
VI, Lemma 13.2, gives

$$
\begin{gathered}
0.9005088162<r_3<0.9005088163,\qquad
0.1275805397<b_3<0.1275805398,\\
y_3\in\operatorname{int}K_3,\qquad
K_3=[7.283036,7.283037]\times[61.494372,61.494373].
\end{gathered}
\tag{3.1}
$$

This $y_3$ is different from the original target $(p_*,v_*)$ of III,
§26.12. The statements below are not a settlement of that target.

In the independent source coordinates $(t,b)$, $t=r/b$, VI, Lemma
14.2, gives $p_b(W_3)\ne0$. Set

$$
s_3=\frac{p_t(W_3)}{p_b(W_3)},\quad
K=\partial_t-s_3\partial_b,\quad
A=a_K(W_3),\quad 4<A<5.
\tag{3.2}
$$

VI, §15, uses the analytic coordinates $x=p-p_3$, $w=t-t_3$.
Their inverse has $t=t_3+w$, $b=\beta(x,w)$ and the original complete
world lift, denoted $\mathcal L(x,w)$. Write

$$
(p,v,m)\circ\mathcal L(x,w)
=(p_3+x,V(x,w),\mathcal M(x,w)),\qquad
\mathcal A(x,w)=a(\mathcal L(x,w)).
\tag{3.3}
$$

The reused jet identities are

$$
V_w(0,0)=\mathcal M_w(0,0)=0,\qquad
V_{ww}(0,0)=\chi\in(0.140,0.141),\qquad
\mathcal A_w(0,0)=A.
\tag{3.4}
$$

Here $\chi$ is the original-source jet of VI, (14.3), transported by
its explicit derivative identity (15.5). No metric coefficient is
being transported from a Whitney normal form.

**Convention 3.2 (actual germ and remote companion).** VI, Theorem 15.1,
supplies real analytic functions $X(q),\zeta(q)$, with
$X(0)=\zeta(0)=0$, for which

$$
W_\pm(h)=\mathcal L\bigl(X(h^2),\zeta(h^2)\pm h\bigr)
\tag{3.5}
$$

are actual complete worlds. For sufficiently small nonzero real $h$,
they are distinct, have the same $\Phi$ value $y(h)$ and the same
alternative $m$ value, and satisfy $p\ne24$. They exchange under
$h\mapsto-h$ and converge to $W_3$. The equal-$m$ condition describes
the mathematical domain; it is not a measurement or an input to recovery.
The entire polynomial and drift in each branch are its own lawful
whole-world lift, not a newly fitted gain at each clock.

VI, Theorem 16.1, already proves

$$
a(W_+(h))-a(W_-(h))=2Ah+O(h^3).
\tag{3.6}
$$

VI, Theorem 18.1, supplies one analytic remote branch $Z(y)$ over an
open rectangle containing $K_3$, with source in the square of radius
$10^{-8}$ centered at $(r,b)=(0.048472239114,0.046421593505)$.
Its $J$ response obeys

$$
a(Z(y))\in[220.955521,220.976926]\qquad(y\in K_3).
\tag{3.7}
$$

**Convention 3.3 (entire-child inventory).** The following facts are
VI, Theorems 23.1–23.2 and Corollary 23.3, not new inventory claims:

1. $C(y_3)=\{W_3,Z(y_3)\}$ consists of exactly two distinct worlds.
   A double eliminant root at $W_3$ counts as one world.
2. There exists an open $V_3\subset\operatorname{int}K_3$ containing
   $y_3$ on which every entire child has at most three worlds and $a$
   is injective on that entire child. No numerical radius or effective
   membership recognizer for $V_3$ is supplied.
3. For all sufficiently small nonzero $h$,

$$
C(y(h))=\{W_+(h),W_-(h),Z(y(h))\},\qquad |C(y(h))|=3.
\tag{3.8}
$$

The source proof exhausts singular and regular parent strata before
concluding (3.8). These conclusions therefore do not introduce
regular-only guards on the original child. In the same sufficiently
small domain $313<a(W_\pm(h))<314$. With

$$
L=\frac{46011537}{500000}>92.02,
\tag{3.9}
$$

each local–remote reply distance is strictly greater than $L$, by
(3.7). The center also satisfies this separation. All subsequent
shrinking of the parameter interval preserves these source conclusions.

## 4. Displacement and the attained whole-child minimum

**Definition 4.1 (original-coordinate coefficients).** In the analytic
coordinates of §3 put

$$
\xi=X'(0),\qquad \nu=V_x(0,0),\qquad
\mathbf c=\left(\xi,\nu\xi+\frac\chi2\right),\qquad
B=\|\mathbf c\|_\infty.
\tag{4.1}
$$

These are fixed germ coefficients. They are not additional acquired
data or source-dependent decoder advice. Big-$O$ statements below refer
to $h\to0$ in this fixed germ, with constants independent of the two
signs of $h$.

**Lemma 4.2 (nonzero quadratic acquired displacement).** There is a
positive parameter radius such that

$$
y(h)-y_3=\mathbf c h^2+O(h^4),\qquad
\mathbf c\ne0,\qquad B>0,
\tag{4.2}
$$

and hence

$$
\|y(h)-y_3\|_\infty=Bh^2+O(h^4)>0
\quad\text{for sufficiently small }h\ne0.
\tag{4.3}
$$

**Proof.** Analyticity and $X(0)=\zeta(0)=0$ give
$X(h^2)=\xi h^2+O(h^4)$ and
$\zeta(h^2)=\zeta'(0)h^2+O(h^4)$. Thus the first acquired coordinate
has displacement $\xi h^2+O(h^4)$.

Let
$H(h)=V(X(h^2),\zeta(h^2)+h)$. This is analytic. Equal $v$ values
in (3.5) give
$H(h)=V(X(h^2),\zeta(h^2)-h)=H(-h)$ for nonzero small $h$, and
continuity gives the same identity at zero. Its power series is even.
In its quadratic coefficient the linear $x$ term contributes
$\nu\xi$, and the $w^2$ term contributes $\chi/2$. The linear $w$
term contributes zero by $V_w(0,0)=0$; $xw$ and $x^2$ have order at
least three and four, respectively. Therefore

$$
H(h)=v_3+(\nu\xi+\chi/2)h^2+O(h^4).
$$

Evenness justifies the fourth-order remainder, without claiming that
each unsymmetrized Taylor term has that order. This proves (4.2)'s
expansion. If $\xi\ne0$, $\mathbf c$ has nonzero first coordinate.
If $\xi=0$, its second coordinate is $\chi/2\ne0$. Thus $B>0$.
Finally the reverse triangle inequality for the maximum norm bounds
the difference between $\|\mathbf c h^2+O(h^4)\|_\infty$ and
$Bh^2$ by $O(h^4)$. Its leading coefficient is positive, so the
norm is positive for every sufficiently small nonzero $h$. $\square$

**Theorem 4.3 (attained complete-child minimum).** There exists $h_0>0$
such that for every real $h$ with $0<|h|<h_0$ the quantity

$$
\delta(h)=\min_{\substack{W,W'\in C(y(h))\\W\ne W'}}
                 |a(W)-a(W')|
\tag{4.4}
$$

is positive, is attained by the pair $W_+(h),W_-(h)$, and satisfies

$$
\delta(h)=|a(W_+(h))-a(W_-(h))|
         =2A|h|+O(|h|^3).
\tag{4.5}
$$

In the original acquired coordinates it has the positive rate

$$
\lim_{h\to0,\ h\ne0}
\frac{\delta(h)}{\sqrt{\|y(h)-y_3\|_\infty}}
=\frac{2A}{\sqrt B}>0.
\tag{4.6}
$$

**Proof.** Shrink the interval so that the entire inventory (3.8),
the local response bounds and the two local–remote gaps $>L$ hold.
The local difference in (3.6) tends to zero; shrink again so that
its absolute value is less than $L$. Of the three unordered
distinct-world pairs in (3.8), the two involving $Z(y(h))$ have
distance $>L$, whereas the remaining pair has distance $<L$.
Consequently it attains the minimum over the entire child.

The inequality $\bigl||u+r|-|u|\bigr|\le|r|$ applied to
$u=2Ah$ and (3.6) gives (4.5), with $A>0$. It also gives
positivity after another shrinking. This proves the claimed attained
minimum, rather than a lower bound for a selected local pair.
By (4.3),

$$
\sqrt{\|y(h)-y_3\|_\infty}
=\sqrt B\,|h|\bigl(1+O(h^2)\bigr).
$$

Dividing (4.5) gives (4.6). Only the original $(p,v)$ norm is used;
an arbitrary target diffeomorphism in a normal-form theorem would
not supply this coefficient. $\square$

## 5. The retained record and a common compatibility decoder

**Definition 5.1 (full closed scalar-retention relation).** Fix a public
known radius $\varepsilon\ge0$. The original exact scalar $a(W)$ is
actually acquired by $J$. Its retained substitute may be **any** real
$z$ satisfying

$$
|z-a(W)|\le\varepsilon.
\tag{5.1}
$$

The decoder's complete variable input is exactly

$$
(p,v,z,\varepsilon).
\tag{5.2}
$$

The model and literal history $H_4$ are fixed public parameters. The
base $(p,v)$ is retained exactly and can be an infinite-precision
reference. The radius is common to every world compared within a
child; it cannot carry a branch label. A radius depending on the
acquired base is allowed in Corollary 6.2, with the same value for
all worlds having that base.

There is no retained original $a$, error residue, $m$, germ parameter,
sign, local/remote flag, source coordinate or world-dependent lookup
table in (5.2). The full relation (5.1) is substantive: a particular
quantizer or channel with a proper subset of these allowed outputs
has a different necessity question.

**Definition 5.2 (one source-independent decoder).** For any $y=(p,v)$,
$z\in\mathbb R$ and $\varepsilon\ge0$, define mathematically

$$
\operatorname{Comp}(y,z,\varepsilon)
=\{W\in C(y):|z-a(W)|\le\varepsilon\}.
\tag{5.3}
$$

On the domain

$$
\mathscr D=\{(y,z,\varepsilon):\varepsilon\ge0,
                         |\operatorname{Comp}(y,z,\varepsilon)|=1\},
$$

let $D(y,z,\varepsilon)$ be that unique compatible complete world.
This is one mathematical partial function, defined using the fixed
original model on its actual compatible domain. Its input contains
neither $h$ nor an enumeration of $C(y)$; the set in (5.3) specifies
the function, not a newly supplied reply oracle. Correctness means it
is defined and returns $W$ for every actual $W$ and every allowed $z$
in the declared domain. No algorithm for evaluating (5.3) is asserted.

**Lemma 5.3 (reused interval and midpoint principle).** Let $C$ be a
finite set with at least two elements and let $a:C\to\mathbb R$ be
injective. Put
$\Delta=\min_{W\ne W'\in C}|a(W)-a(W')|>0$. For a common
radius $\varepsilon\ge0$, exact recovery of every $W\in C$ from
every $z$ satisfying (5.1) is possible if and only if

$$
2\varepsilon<\Delta.
\tag{5.4}
$$

Here the common base identifying $C$ is fixed in all inputs. The
unique-compatible-world decoder supplies sufficiency. At equality,
as well as above it, recovery fails.

**Proof.** If two distinct worlds were compatible with the same $z$,
the triangle inequality would give
$|a(W)-a(W')|\le2\varepsilon<\Delta$, a contradiction. An actual
allowed record has at least its generating world compatible, so its
compatible set is a singleton.

Conversely take a pair attaining $\Delta$ and set
$z_*=(a(W)+a(W'))/2$. Its distance to each reply is $\Delta/2$.
When $2\varepsilon\ge\Delta$, the same input consisting of the
common base, $z_*$ and the common radius is permitted for both
distinct worlds. No single-valued decoder can return both. Closed
endpoints make this argument valid at equality. $\square$

This principle, including the need to inspect attainment, is reused
mathematics. In particular `CriticalPrefixSeparation.result` has a
different critical equality behavior on finite-tail addresses: its
different-prefix reply distances are strictly greater than $t/2$
with unattained infimum $t/2$, and its closed-error prefix recovery
holds for $\varepsilon\le t/4$. On its complete infinite-address
domain, different-prefix reply sets do attain distance $t/2$.
Neither domain nor its equality convention
can replace the attained three-world minimum of Theorem 4.3.

## 6. The sharp threshold, variable radii and the center

**Theorem 6.1 (whole-child exact terminal-world recovery).** Choose $h_0$
as in Theorem 4.3. For every $h$ with $0<|h|<h_0$ and every common
known $\varepsilon\ge0$, the following are equivalent:

1. There exists a single-valued decoder of (5.2) which returns $W$
   for every complete world $W\in C(y(h))$ and every real $z$ with
   $|z-a(W)|\le\varepsilon$.
2. $2\varepsilon<\delta(h)$.

The **same** function $D$ of Definition 5.2 realizes recovery for all
such safe children and radii simultaneously. The admissible radii
for the fixed child are exactly

$$
[0,r_*(h)),\qquad
r_*(h)=\frac{\delta(h)}2
      =A|h|+O(|h|^3),
\tag{6.1}
$$

where the supremum is not admissible. Moreover

$$
\lim_{h\to0,\ h\ne0}
\frac{r_*(h)}{\sqrt{\|y(h)-y_3\|_\infty}}
=\frac A{\sqrt B}>0.
\tag{6.2}
$$

**Proof.** The entire child is exactly the three-world set (3.8).
Theorem 4.3 supplies its positive attained minimum. Lemma 5.3 proves
the equivalence, including a midpoint counterexample whenever
$2\varepsilon\ge\delta(h)$. All compatible sets in that argument
are formed from the **entire** $C(y(h))$, including the remote
companion, so the sufficient decoder is precisely $D$.

The definition of $D$ is independent of $h$, the branch and the
generating world. Different bases occupy different input fibers
because both $p$ and $v$ are retained. Thus its simultaneous use
does not require distinguishing children from $z$ alone. Equation
(6.1) follows from (4.5), and (6.2) from (4.6). At zero radius this
recovers the already supplied noiseless inverse; it is not a new
noiseless inversion theorem. $\square$

**Corollary 6.2 (punctured nonuniform-radius consequence).** Let

$$
Y_* =\{y(h):0<|h|<h_0\}.
$$

No fixed positive radius permits exact recovery of every world and
every permitted stored value over all sufficiently small nonzero
parameters. More strongly, for every $\varepsilon_0>0$ there is
$\rho\in(0,h_0)$ such that recovery at radius $\varepsilon_0$
fails in every child $C(y(h))$ with $0<|h|<\rho$.

For a known radius function $e:Y_*\to[0,\infty)$, exact recovery
over the whole promised family, with radius $e(y)$ supplied as in
(5.2), is possible if and only if

$$
2e(y(h))<\delta(h)\qquad(0<|h|<h_0).
\tag{6.3}
$$

The definition is consistent if different parameters have the same
base: $\delta(h)$ is determined by that entire child. Every successful
radius function obeys $e(y(h))=O(|h|)$ and tends to zero. A permissible
strictly positive mathematical choice is one quarter of its minimum
reply separation; it tends to zero at rate $|h|$. This is an
existence statement for radii, not an effective evaluation procedure.

**Proof.** Equation (4.5) gives $\delta(h)\to0$. Hence it is less
than $2\varepsilon_0$ for every sufficiently small nonzero $h$;
Theorem 6.1 gives failure at each such child. If (6.3) holds, the
same $D$ gives correctness for every allowed record in the family.
If it fails at even one child, the midpoint input for that child's
nearest pair has the same $y$, $z$ and $e(y)$ for two worlds, so
every proposed family decoder fails there. For a successful function,
$0\le e(y(h))<\delta(h)/2$ and (4.5) give the stated bound and
zero limit. Finally $e=\delta/4$
is positive and satisfies (6.3); (4.5) proves its stated rate.
$\square$

**Proposition 6.3 (the different child at the center).** Put
$Z_3=Z(y_3)$ and

$$
\delta_{\rm c}=|a(W_3)-a(Z_3)|>L>92.02.
\tag{6.4}
$$

At the center, exact recovery of every complete world in $C(y_3)$
for every allowed stored value holds exactly when
$2\varepsilon<\delta_{\rm c}$, again with equality failure. Its
positive critical supremum is $\delta_{\rm c}/2$. In contrast,
the punctured critical suprema in (6.1) tend to zero.

**Proof.** Convention 3.3 gives exactly two distinct center worlds.
Their response distance is greater than $L$ by the same local and
remote bounds. Apply Lemma 5.3 to this two-world child. The two local
germ endpoints have coalesced into the single world $W_3$; they are
not a distinct-world pair at $h=0$. Thus setting the center minimum
equal to the limit of $\delta(h)$ would count a nonexistent pair.
The claimed discontinuity follows from (4.5) and (6.4). $\square$

## 7. Exact overlap and common-source boundaries

**Convention 7.1 (VI25–26, X7–11 and V13–18).** The threshold above
does not replace these results or extend their regions.

VI, §§25–26, treats a reflected pair near $b=1/8$ of width
$1/30000$. Its first $r$ interval is $[.267,.277]$, its reflected
interval is $[25439/30000,25741/30000]$, and both $b$ values are in
$[3749/30000,3751/30000]$. It proves an ordered comparator and an
off-$24$ exclusion for the selected equal-$M$ pair, preserving its
zero-safe cases. The third local world has $r$ near $.9005$ and the
remote companion has $r$ near $.04847$, outside those intervals.
Shrinking this germ keeps them outside. Those sections do not give
the attained entire-child $J$ margin or its retention threshold.

X, §9, proves $p$-only separation on its exceptional layer
$n/U=\kappa_X$, where $5/8<\kappa_X<313/500<2/3$; §10 separately
exhausts and proves $p$-only separation on the golden layer
$n/U=(\sqrt5-1)/2$. Section 11 permits at most one world from
each layer per child. For $p\ne24$, its conditional fixed-$(p,v,m)$
count is six when its polynomial satisfies
$N(\kappa_X;p,v,m)=0$; its unconditional fixed-$(p,v,m)$ bound is
seven and its entire $C(p,v)$ bound is twenty-four. The counting
bounds are not asserted at $p=24$. These are layer and counting results,
not cross-layer $J$ distances or third-germ error thresholds. Its
auxiliary $m$ in an inverse remains unacquired on the present $J$
run. Here the stronger source-specific inventory (3.8) is directly
reused; no layer is removed from the definition of the entire child.

V, §§13–18, keeps the same original model and proves all-companion
localization and $J$ injectivity over

$$
K_2=[1.83048,1.83049]\times[175.91204,175.91206],
$$

with source rectangle
$R_2=[.517,.522]\times[.04227,.04230]$ and collar
$B_2=[.519535942,.519535944]\times[.0422838305,.0422838320]$.
Its zero-safe elimination and finite closed cover lead to a
quantitative fixed-$p$ response order; its collar excludes the
original second-sector joint configurations. Section 18 explicitly
limits that exclusion to the second region. The rectangles $K_2$
and $K_3$ are disjoint, and neither the local third source nor its
remote companion lies in $R_2$. V's earlier fourth-region results
also have their own separate scope. The complete V result therefore
neither absorbs nor contradicts the present third-germ retention
deduction, and changes no acquisition or retention premise used here.
No missing result in another region is inferred from V's scope note.

**Convention 7.2 (formal suppliers and their exact contribution).**
The following declaration sources and their owning Scribes supply
reusable mathematical principles; source text is not a current build.
The `Blueprint/` path corresponding to each displayed `D5/` path,
with suffix `.scribe.cs`, is its owning narrative source.

| Declaration source and revision | Reused content and limitation |
| --- | --- |
| `D5/S3/ObserverMemory/Refinement/InterfaceKernelCriterion.lean`, `interface_refinement_iff_kernel_inclusion`, at `e2665d9f06157453325ad4e1064681b41db63625` | Exact refinement is kernel inclusion. The identity target here requires singleton compatible-world fibers; the criterion supplies no error margin or acquired source. |
| `D5/S3/ObserverMemory/Refinement/EffectiveImageKernelCriterion.lean`, `refinement_iff_kernel_inclusion_on_effective_images`, at `4442fb66c4d7017bb7b932cc63f058b46c83b71c` | Unique range-to-range factorization on actual images under kernel inclusion. Its range splitting/choice is not an installed numerical algorithm. |
| `D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.lean`, `predictive_memory_minimal_quotient`, at `e2665d9f06157453325ad4e1064681b41db63625`, with owning Scribe available at `4442fb66c4d7017bb7b932cc63f058b46c83b71c` | Predictive memory requires both readout and update factorization. A terminal inverse alone does not establish that continuation contract. |
| `D5/S1/Digit/Infinite/CriticalPrefixSeparation.lean`, `result` and its private separation, infimum and midpoint helpers, with owning Scribe at `4442fb66c4d7017bb7b932cc63f058b46c83b71c` | Closed-error all-compatible recovery and the distinction between an attained minimum and an unattained infimum. The different finite-tail prefix equality case is stated after Lemma 5.3. |
| `D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/OnlineDecoderCoordinates.lean`, with owning Scribe, at the supplied `e2665d9f06157453325ad4e1064681b41db63625` source and `4442fb66c4d7017bb7b932cc63f058b46c83b71c` narrative retrieval | The actual OperationOmega grouped legal digits and support recurrence have their own coordinate bridge. They do not transport this real observation relation, retention errors or callable rights. |

The additional work here is not a renamed kernel theorem, a new
generic quotient, or the creation of an inverse by definition.
The substantive inputs specific to this source are (3.4), (3.6),
the complete inventory and remote gap. Their combination proves
the nonzero original-coordinate rate and the attained margin used
in the threshold.

**Convention 7.3 (NCR, PVC, PR57, PG and Atlas).** These ordinary
contracts are taken at the documentary revision
`e2665d9f06157453325ad4e1064681b41db63625`, preserving each volume's
own internal supplier pins: NCR uses
`b7d37ca0fee9638f28af45d4a63f7f0eb974c972`, PVC uses
`82c9eb9c1462af91333b7038a93488c8b9b8bdc7`, Atlas uses
`a683624403f0c22bc441dc3171f5e181bfd709f6`, and PR57's immutable
supplier revision is `17b26a61db5577d2f67031c777e9d86e91c3e617`.

| Contract | Precise distinction |
| --- | --- |
| [NCR: Native Clocked Recovery and Order](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md), §§2–6 | Its fixed installed controller, atomic Native tree source, actually acquired seed, receipt clocks and owned callable records give separate view/task kernels. Its fence-at-$n+1$ readout requires the stated authorization. The present cubic-gain real experiment supplies neither that controller nor its clock-reading mechanism. |
| [PVC: Native Paid View Conversion](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md), §§1–2, 5–7 | It constructs a finite $D_2$ conversion program on a fixed-$H$ alpha/beta entrance, unused lanes and an explicitly added once-only owner-authorized Install. Its serialized $S\to B\to M\to T\to S$ cycle has actual copying and return. This volume adds no such installation or conversion service, and does not change PVC's original CAP-consumer boundary. |
| [PR57: Transport Memory Completion, §57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) | Its padded finite source packet, constructed tapes, local opcodes, meter, masks and ideal owner/token primitives are runtime assumptions with their own schedules and bills. They are not consequences of an exact-real inverse or a wire representation. No PR57 source-acquisition or bit-operation tariff is imported here. |
| [PG: Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md), §§1–3 | Complete partial-action transport must preserve actual joint source, legality, labels, root readouts and successors, with selector descent for adaptive use. The terminal recovery theorem does not by itself prove those conditions for a future installed process. |
| [Atlas: Native Callable Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md), §§1–2 and 7 | It preserves initialization, partial-source/control phases, retained backing, actual selectors, packages and invocation rights. Lemma 7.2 distinguishes reversible wire interpretation from installing additional serializers; Theorem 7.3 keeps the old target and later Call return separate. Reconstructing $W$ here issues no package, token or late-target reference. |

These results remain stronger on their own operational subjects.
The gain here is a sharp terminal retention condition on another
explicitly supplied actual source, without an unproved transplantation
of their machinery. A promised-domain conditional theorem does not
require a digital implementation as a premise; claiming that stronger
implementation would require its own acquisition and execution bridge.

## 8. Same-run resources, remaining programme and literature limits

**Convention 8.1 (same actual run).** The action word is exactly
$J,M,J,M,M,M,J$. There are seven actions and eight readings including
the initial one at zero. Their values are

$$
(0,24,147/5,24,18,p,v,a).
$$

Every world uses one $P$, one $g$ and one $d$ on these clocks.
There is no reset, extra preparation, copy, skipped read, rebased
clock or extra port. The last $J$ is an original lawful choice, not
a new acquisition primitive; the alternative last $M$ is unexecuted.
The retained variable record consists of exact $p,v$, the single
substitute $z$, and the known common radius. The fixed history and
model are public references. Recovering $W$ and recomputing its
responses agrees with this same acquired base and yields an $a$
inside the reported interval by (5.3).

This is a count of original actions/readings and a declaration of
retained mathematical fields, not a finite-bit storage bound or a
priced numerical implementation. In particular exact retention of
$(p,v)$ is a potentially infinite-precision resource, and $z$ and
$\varepsilon$ are real inputs as declared. No minimum memory,
arithmetic complexity, physical realization, installed decoder,
effective $V_3$ recognizer, or future post-terminal access is proved.
The midpoint failure concerns the full channel (5.1), not every
quantizer satisfying an error upper bound. The vanishing margin
rules out a common positive radius only on this punctured family;
it is not a universal observer obstruction or an all-target result.

**Convention 8.2 (remaining original and four-expression obligations).**
The original source and initialization in §§2–3 are preserved. The
original fixed-$G_{gc}$, original-$Q$, stationary and parked-consumer
questions retain their own sources, interfaces, readouts and unresolved
obligations. No new construction here changes an old target or counts
as its solution. The original global joint-incidence sentence still
asks for independent distinct equal-$J$ and equal-$M$ pairs in one
entire off-$24$ child, permits cross-pair overlap, and imposes no
equality between their two common terminal values. No global truth
value is inferred from this third-sector exclusion or threshold.

The independently meaningful source geometry, actual ordered clock
events, acquired boundary replies and retained memory belong to one
run here. The event word alone has no numerical source information,
and the memory theorem concerns the specified terminal task only.
No four individual task-kernel equalities, four-way route agreement,
or complete continued dynamics representation is proved. In particular
there is no reduction of every source to alpha/beta generation.
The common space/time/boundary/memory programme, actual implementation
bridges and all untouched model-specific obligations remain open in
their original scopes.

**Convention 8.3 (ordinary literature and unavailable contexts).**
The source-specific deduction in §§4–6 uses the named supplier
identities, elementary analytic power series, norm inequalities and
closed intervals. The general inverse, kernel and midpoint principles
are credited reuse. The following source/version restrictions remain
explicit; unavailable texts are not replaced by snippets or another
edition.

| Source | Evidence and use boundary |
| --- | --- |
| Basu–Pollack–Roy, *Algorithms in Real Algebraic Geometry*, second edition, Chapters 2, 8 and 9 | `UNVERIFIED-CITATION`: the complete cited book contexts are unavailable. They provide no separately checked load-bearing theorem body here. |
| Rudin, *Principles of Mathematical Analysis*, Theorem 2.41 | `UNVERIFIED-CITATION`: edition unspecified and complete cited context unavailable. |
| Krantz–Parks, *The Implicit Function Theorem*, Chapters 1–2 | `UNVERIFIED-CITATION`: edition unspecified and complete cited contexts unavailable. The analytic parametrization is the explicit VI supplier, not an assertion of having checked this book. |
| Cox–Little–O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 3 | `UNVERIFIED-CITATION`: edition unspecified and complete cited context unavailable. |
| Basu, [author-linked real-algebraic-geometry survey PDF](https://www.math.purdue.edu/~sbasu/raag_survey2011_final-sep4-2014.pdf), SHA-256 `4d32f328179a354e8ad19b5fd07233581f8d0408ed39fc2a175d7461f9b949e4` | The supplied complete PDF matches its requested title and literal page/section locators. Identity with the exact earlier copy is not uniquely certified, and equivalence to an arXiv revision or publisher edition is unverified. PDF creation metadata and the author-page 2017 publication entry are distinct. This does not independently certify the source eliminations. |
| Hasegawa–Honda–Naokawa–Umehara–Yamada, *Intrinsic Invariants of Cross Caps*, [arXiv:1207.3853v2](https://arxiv.org/abs/1207.3853v2) | `literature-attested` at this version only: the Whitney criterion cited by VI. Complete TeX and original PDF are supplied; the PDF derivative has 96 fontTools/CFF encoding notices, and mathematical glyph/formula/layout fidelity is not certified. The criterion supplies no metric retention constant; (4.2) uses the original-source jets directly. |
| Jelonek, the 1993 paper at [DOI 10.4064/ap-58-3-259-266](https://doi.org/10.4064/ap-58-3-259-266) | The complete original PDF and text derivative preserve their extraction limits; unchanged strings do not certify formulas or layout. Dominant complex polynomial nonproperness is not a substitute for the strict-real complete-world exhaustion used here. Publisher metadata labels CC-BY without an exact license-version link; no version-specific license is certified. |
| [Affine Finite Reply Recovery](RECURSIVE_RELATIONAL_OBSERVATION_AFFINE_FINITE_REPLY_RECOVERY.md), complete §§2 and 7 at `4442fb66c4d7017bb7b932cc63f058b46c83b71c` | Reused separation of finite closed values from exact/analog data, approximate task guarantees from exact source recovery, and numerical inverses from chronology and rights. Its affine source, noise model and native response task are not the present cubic-gain experiment. |

Independent PGP signature trust is unvalidated. Documentary byte,
version, index and seal checks certify neither source completeness
nor mathematical correctness, novelty or applicability. In particular
the finite source certificates for O, III, V, VI and X are attributed
to those sources; no execution or independent recomputation of them,
and no new Lean/axiom-closure verification, is asserted here. The
ordinary conditional proofs above establish their displayed deduction
from those inputs, not a new certification of the inputs themselves.

## 追加锚（本行以下为增补区）
