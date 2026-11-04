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

## 9. Clock-eight response separation on the complete third child

**Convention 9.1 (source and action correspondence).** Retain the complete
worlds, the history $H_4$, the actual continuation $M,M,J$ after $H_4$, followed by the
entire-child definition $C(y)$ of §§2–3. The seventh action remains the
actual $J$; $m(W)$ is the unacquired alternative seventh-$M$ value. In
VI at the pinned revision 4442fb66c4d7017bb7b932cc63f058b46c83b71c, direct
multiplication of the chronological products gives

$$
 Q_6=\begin{pmatrix}3&1\\5&2\end{pmatrix},\qquad
 Q_7=JQ_6=\begin{pmatrix}5&2\\3&1\end{pmatrix},
$$

and therefore

$$
 JQ_7=\begin{pmatrix}3&1\\5&2\end{pmatrix},\qquad
 MQ_7=\begin{pmatrix}3&1\\8&3\end{pmatrix}.
\tag{9.1}
$$

Put

$$
 c=\frac{r(1-r)}b,\qquad U=1+2b,\qquad n=b+c+r,
 \qquad \theta=\frac nU.
\tag{9.2}
$$

For a complete world define $q_k=Ug(k)$. The unchanged readings at
clocks $3,4,5,6$ and the source-determined alternative $m$ give

$$
 q_3=\frac{24-d}{\theta},\quad q_4=18-d,
 \quad q_5=\frac{p-d}{1+\theta},\quad
 q_6=\frac{v-d}{2+\theta},\quad
 q_7=\frac{m-d}{3+2\theta}.
\tag{9.3}
$$

The alternative $m$ occurs only in this source identity. It is not an
observer input. The four values in (9.3) are samples of one whole polynomial
of degree at most three, so fixed-node interpolation gives

$$
\begin{aligned}
 F&:=q_3-4q_4+6q_5-4q_6+q_7=0,\\
 q_0&:=35q_4-84q_5+70q_6-20q_7=-Ud,\\
 q_8&:=-q_4+4q_5-6q_6+4q_7=Ug(8).
\end{aligned}
\tag{9.4}
$$

The identities follow by checking the weights on $1,s,s^2,s^3$, hence
remain valid for every lower degree, zero sample, repeated root and other
allowed gain specialization. From (9.1), the two possible actual clock-eight
scalars are

$$
 f_J=d+(2U+n)g(8)=d+(2+\theta)q_8,
 \qquad
 f_M=d+(3+8b+c)g(8).
\tag{9.5}
$$

They are responses of the same $W$, with one fixed $g$ and one fixed $d$
throughout the run.

At $W_3$, VI Lemma 13.2 gives

$$
27.263115<d<27.263116,\qquad
1.2551610794<U<1.2551610796,
$$

and $g(4)=(18-d)/U$, hence

$$
-7.381<g(4)<-7.379.
\tag{9.6}
$$

Using the same source intervals in (9.4), with outward rational endpoint
substitution, gives $139.8<q_8<139.9$ and $111<g(8)<112$. The response
conclusion below uses (9.4).

**Lemma 9.2 (nonzero response tangents at $W_3$).** At the exact algebraic
world $W_3$ of VI Definition 13.1, both $Kf_J$ and $Kf_M$ are nonzero,
where $K$ is the VI tangent in the independent $(t,b)$ chart with
$t=r/b$, $Kp=Kv=Km=0$, $Kt=1$, and $p_b(W_3)\ne0$.

**Proof.** All partial derivatives below hold $p,v,m$ fixed. Differentiating
(9.4) gives

$$
\begin{aligned}
F_d&=-\frac1\theta+4-\frac6{1+\theta}+\frac4{2+\theta}-\frac1{3+2\theta},\\
F_\theta&=-\frac{24-d}{\theta^2}-\frac{6(p-d)}{(1+\theta)^2}
 +\frac{4(v-d)}{(2+\theta)^2}-\frac{2(m-d)}{(3+2\theta)^2},\\
(q_8)_d&=1-\frac4{1+\theta}+\frac6{2+\theta}-\frac4{3+2\theta},\\
(q_8)_\theta&=-\frac{4(p-d)}{(1+\theta)^2}+\frac{6(v-d)}{(2+\theta)^2}
 -\frac{8(m-d)}{(3+2\theta)^2},\\
(q_0)_d&=-35+\frac{84}{1+\theta}-\frac{70}{2+\theta}+\frac{20}{3+2\theta},\\
(q_0)_\theta&=\frac{84(p-d)}{(1+\theta)^2}-\frac{70(v-d)}{(2+\theta)^2}
 +\frac{40(m-d)}{(3+2\theta)^2}.
\end{aligned}
\tag{9.7}
$$

The exact VI boxes imply the following weaker rational box:

$$
\begin{gathered}
1.3785\le\theta\le1.3787,\quad 1.25516\le U\le1.25517,
\quad27.2631\le d\le27.2632,\\
7.2830\le p\le7.2831,\quad61.4943\le v\le61.4944,
\quad351.0575\le m\le351.0576.
\end{gathered}
\tag{9.8}
$$

Every terminating decimal in (9.8) and below denotes the corresponding
exact rational. Since all denominators in (9.7) are positive, signed
endpoint products give

$$
\begin{array}{c|c@{\qquad}c|c}
F_d&[1.761,1.764]&F_\theta&[15.34,15.39]\\
(q_8)_d&[.399,.400]&(q_8)_\theta&[-46.1,-45.9]\\
(q_0)_d&[-16.94,-16.91]&(q_0)_\theta&[-116.1,-115.4]\\
q_8&[139.8,139.9]&&
\end{array}
\tag{9.9}
$$

For example, the two $q_8$ endpoint inequalities are

$$
9.2631-\frac{4(19.9802)}{2.3785}-\frac{6(34.2313)}{3.3785}
 +\frac{4(323.7943)}{5.7574}>139.8,
$$

and

$$
9.2632-\frac{4(19.9800)}{2.3787}-\frac{6(34.2311)}{3.3787}
 +\frac{4(323.7945)}{5.7570}<139.9.
$$

The analogous signed endpoint expressions in (9.7) give (9.9); no floating
point evaluation is used. In particular

$$
 d':=\frac{Kd}{K\theta}=-\frac{F_\theta}{F_d}\in[-8.75,-8.69].
\tag{9.10}
$$

Here $K\theta\ne0$. Indeed, if $K\theta=0$, then $F_d>0$ and
$KF=0$ give $Kd=0$. Differentiating $q_0=-Ud$, using $d>0$, gives
$KU=0$, hence $Kb=0$. Differentiating $n=b+c+r$ then gives $Kn=0$;
with $n_r=1+(1-2r)/b\in[-5.29,-5.27]$, this forces $Kr=0$, contradicting
$Kt=1$.

Set $q_8'=(q_8)_\theta+(q_8)_d d'$. From (9.9)–(9.10),

$$
q_8'\in[-49.7,-49.3],\qquad
U':=\frac{KU}{K\theta}\in[-.81,-.72].
\tag{9.11}
$$

The second bound follows by differentiating $q_0=-Ud$. Further source
identities give

$$
\begin{gathered}
 n_r\in[-5.29,-5.27],\quad n_b=1-c/b\in[-4.51,-4.50],
 \quad r'\in[.25,.33],\\
 H:=3+8b+c\in[4.722,4.724],\quad H'\in[-3.04,-2.50],\\
 g_8:=q_8/U\in[111,112],\quad g_8'\in[24,34].
\end{gathered}
\tag{9.12}
$$

For clarity, $n'=U+\theta U'$, $b'=U'/2$,
$r'=(n'-n_b b')/n_r$, and
$H=(7/2+\theta)U-r-1/2$. These formulas, together with the signed
endpoint convention, prove (9.12).

Finally, (9.5), (9.11), and (9.12) give

$$
-38<\frac{Kf_J}{K\theta}=d'+q_8+(2+\theta)q_8'<-34,
\tag{9.13}
$$

and

$$
-240<\frac{Kf_M}{K\theta}=d'+Hg_8'+g_8H'<-120.
\tag{9.14}
$$

For instance the $J$ bounds use
$-8.75+139.8-3.3787(49.7)>-38$ and
$-8.69+139.9-3.3785(49.3)<-34$; the $M$ bounds use
$-8.75+4.722(24)-112(3.04)>-240$ and
$-8.69+4.724(34)-111(2.50)<-120$.
Since $K\theta\ne0$, both response tangents are nonzero. $\square$

**Lemma 9.3 (local and remote response bands).** At $W_3$,

$$
499.5<f_J(W_3)<500,\qquad 551<f_M(W_3)<557.
\tag{9.15}
$$

For every $y\in K_3$, the remote branch $Z(y)$ of VI Theorem 18.1
satisfies

$$
493.9<f_J(Z(y))<494.4,\qquad 646<f_M(Z(y))<648.
\tag{9.16}
$$

**Proof.** The local bounds follow from
$27.2631+3.3785(139.8)>499.5$,
$27.2632+3.3787(139.9)<500$,
$27.2631+4.722(111)>551$, and
$27.2632+4.724(112)<557$.
For the remote square, VI Theorem 18.1 gives the complete source bounds
that imply

$$
\theta\in[.9959,.9961],\quad U\in[1.0928431,1.0928433],
$$

$$
q_5\in[-14.153,-14.149],\quad q_6\in[8.665,8.668],
\quad q_7\in[61.027,61.042],\quad q_8\in[153.01,153.12],
$$

and hence $g_8\in[139.99,140.12]$ and
$3+8b+c\in[4.3649,4.3650]$. The endpoint sums

$$
17.527142-4(14.153)-6(8.668)+4(61.027)>153.01,
$$

$$
17.529885-4(14.149)-6(8.665)+4(61.042)<153.12
$$

then give (9.16) by (9.5). $\square$

**Theorem 9.4 (open-base entire-child separation).** There is an open set
$V\subset\operatorname{int}K_3$, containing $y_3$, such that for every
$y\in V$ each of $f_J$ and $f_M$ is injective on the entire child
$C(y)$. The set $V$ is existential; no numerical radius or effective
membership recognizer is asserted.

**Proof.** By Lemma 9.2 and $p_b(W_3)\ne0$, the Jacobian of
$(p,f_e)$ in $(t,b)$ coordinates is

$$
\det D(p,f_e)=-p_b(W_3)Kf_e(W_3)\ne0,
\qquad e\in\{J,M\}.
\tag{9.17}
$$

The inverse-function theorem supplies neighborhoods $N_J,N_M$ of $W_3$
on which $(p,f_J)$ and $(p,f_M)$ are injective. Let $N=N_J\cap N_M$,
and shrink it so that its two response images remain in the local bands
(9.15). Let $N_Z$ be a relatively open complete-world neighborhood of
$Z(y_3)$ inside VI's remote source square. VI Theorem 18.1 supplies one
and only one remote world over each base in $K_3$, and (9.16) holds on it.

By VI Theorem 17.2, the complete strict-world inverse image of $K_3$ is
compact. VI Theorem 23.1 gives $C(y_3)=\{W_3,Z(y_3)\}$. Hence there is an
open neighborhood $V_0$ of $y_3$, inside $\operatorname{int}K_3$, for
which

$$
\Phi^{-1}(V_0)\subset N\cup N_Z.
\tag{9.18}
$$

If not, choose $y_i\to y_3$ and $W_i\in\Phi^{-1}(y_i)$ outside
$N\cup N_Z$. Compactness gives a convergent complete-world subsequence.
Its limit lies in $C(y_3)$, hence is $W_3$ or $Z(y_3)$, both in the open
union; the complement is relatively closed, a contradiction. Intersect
$V_0$ with VI Theorem 23.2's at-most-three neighborhood and with the
off-$p=24$ domain, obtaining $V$.

For $y\in V$, two local worlds with equal $f_e$ have equal $p$ and
therefore coincide by the injectivity of $(p,f_e)$ on $N$. Two remote
worlds coincide by VI's uniqueness, and a local and remote response cannot
agree by the disjoint bands (9.15)–(9.16). Since (9.18) exhausts the entire
child, $f_e$ is injective on $C(y)$. This includes all unused companions
and all singular, lower-degree, zero-sample and repeated-root strata in the
original definition of $C(y)$. $\square$

**Corollary 9.5 (germ and center cardinalities).** After shrinking the
original germ radius so that its bases lie in $V$, for every sufficiently
small $0<|h|$,

$$
C(y(h))=\{W_+(h),W_-(h),Z(y(h))\},
$$

and both $f_J$ and $f_M$ have three singleton response classes. At the
center,

$$
C(y_3)=\{W_3,Z(y_3)\}
$$

and each response has two singleton classes. There is no assertion of three
worlds, or constant cardinality, at every base in $V$. $\square$

## 10. Old-record prediction, actual execution and acquired identification

**Definition 10.1 (response separation margin).** For $e\in\{J,M\}$, define

$$
\Delta_e(y)=\min_{\substack{W,W'\in C(y)\\ f_e(W)\ne f_e(W')}}
 |a(W)-a(W')|,
\tag{10.1}
$$

with value $+\infty$ when the indexing set is empty. The $a$ in this
margin is exactly the original seventh-$J$ source response from (2.5).

On a punctured germ child, Corollary 9.5 gives

$$
\Delta_J(y(h))=\Delta_M(y(h))=\delta(h),
\tag{10.2}
$$

because every distinct-world pair has a different new response. In the
original germ coordinates, this is the attained quantity $\delta(h)=2A|h|+O(|h|^3)$
from (4.5). At the center both margins equal

$$
\Delta_J(y_3)=\Delta_M(y_3)=\delta_{\rm c}
 =|a(W_3)-a(Z(y_3))|>L>92.02.
\tag{10.3}
$$

**Theorem 10.2 (exact old-record prediction condition).** Let
$R=(p,v,z,\varepsilon)$ be precisely the pre-action record of Definition
5.1, with every real $z$ satisfying $|z-a(W)|\le\varepsilon$ permitted.
For either fixed $e\in\{J,M\}$, an $R$-only predictor can return the exact
$f_e(W)$ for every complete world and every permitted $z$ in a punctured
germ child if and only if

$$
2\varepsilon<\delta(h).
\tag{10.4}
$$

At the center, the corresponding condition is exactly

$$
2\varepsilon<\delta_{\rm c}.
\tag{10.5}
$$

Equality fails in both statements.

**Proof.** This is Lemma 5.3 applied to the newly computed response
partition. If $2\varepsilon<\Delta_e$, two worlds compatible with one
record have $a$-distance at most $2\varepsilon$, hence cannot have
different $f_e$; the common response is the predictor. If
$2\varepsilon\ge\Delta_e$, an attaining pair and the midpoint of its two
$a$-values give the same permitted record for two different responses.
On the punctured germ (10.2) applies, and at the center (10.3) applies.
Closed endpoints give failure at equality. The accessible input contains only
$p,v,z,\varepsilon$; $h$, the sign, branch, $m$, source coordinates and
unacquired alternatives remain absent. A record-only selector choosing $e$
sees the same midpoint record for both worlds and therefore chooses the same
action, so the same necessity argument applies. $\square$

**Definition 10.3 (legitimate one-step same-source port).** For a fixed public
action $e\in\{J,M\}$, or for an action selected only from $R$, grant the
following conditional interface on the actual run:

$$
\operatorname{Clock8Read}_e(W,7,Q_7,R)
 =\bigl(W,8,eQ_7,R\mathbin{\|}(8,e,f_e(W))\bigr),
\tag{10.6}
$$

and let the returned scalar be the exact $f_e(W)$. The port preserves the
same $W,g,d$, grants no reset, second source, simultaneous counterfactual
reply, unknown seed, decoder oracle or future-call right. It is an action/read/
retention premise, not a record-only computation of $f_e$.

**Theorem 10.4 (one actual read identifies the complete world).** Under the
port (10.6), for every allowed old $\varepsilon$ the extension adds exactly
one action and one exact scalar. The original run has seven actions and eight
readings, including the initial zero; the extended run has eight actions and
nine scalar readings, with one appended event record $(8,e,f_e)$. The old
record remains $R$, and no simultaneous $J/M$ reply is acquired.

For $y\in V$, if two actual worlds produce the same new subrecord
$(p,v,e,f_e)$, then they are equal. Consequently the exact newly acquired
response identifies $W$ on the entire child over $V$, including any old
retention error. This is a mathematical inverse on the actual image; it is
not an installed, effective, finite-bit or cost-optimal decoder.

**Proof.** Equality of the subrecords places both worlds in the same $C(y)$
and gives equal $f_e$. Theorem 9.4 makes $f_e$ injective there, so the
worlds coincide. The port supplies an actual source response even when the
old midpoint condition fails; it does not manufacture that response from
$R$. Conversely, with no new read and $2\varepsilon\ge\delta(h)$ (or
$\delta_{\rm c}$ at the center), Theorem 10.2's midpoint gives two worlds
with the same old record, so uniform identification cannot hold. $\square$

## 11. Source overlap and exact scope

**Convention 11.1 (later published sources).** The later StrictRealVIII source
at commit 359d2aae09512cbeb61749f99d5589f2f494e2f8, §§21–27, evaluates a
closed rectangle centered at $p=20$, $v\approx117.0985$. It proves exactly
four complete worlds there and separates all original clock-seven $M$ replies
by more than $1/3$, while locating an existing clock-seven $J$ pair. That
rectangle, its carrier roots, and its $J/M$ question are distinct from the
third target $K_3$, the exact $W_3$, and the clock-eight responses (9.5).
Its §§17–20 lower-face/unit-$j$ exclusion is likewise a separate boundary
incidence statement. It neither proves nor contradicts Theorem 9.4.

The historical StrictRealVI source at 4442fb66c4d7017bb7b932cc63f058b46c83b71c
and the c88 Third-Germ source at c88f466a3ad621f86b563d5179675ace7505b8a3 remain the suppliers for $W_3$, $K_3$, the
remote branch, the complete-child compactness argument, and $\delta(h)$ and
$\delta_{\rm c}$. The later 359d source is not substituted for either pin.

The independently published Atomic Holographic Boundary Geometry Continuation
VIII source at commit 4b07e9740ce998ee7cf899f4b1897bf61a3bf713 proves a
critical-temperature obstruction for a common completely positive map on a
native Gibbs preparation. Its source, fixed register, filter, and conversion
contract are different from the strict-real clock source and its one-step
scalar port. It supplies no $W_3$ response, no $C(y)$ child, and no
retention or prediction margin, so it does not absorb this deduction.

At the separate fixed revision `b0bba854178edce6540fb1ad1d8b3461925d5f11`,
that [Atomic VIII source, Corollary 241.2](https://github.com/the-omega-institute/trureturing/blob/b0bba854178edce6540fb1ad1d8b3461925d5f11/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_VIII.md),
also proves a positive conditional trace-distance approximation gap over
nonzero common completely positive trace-nonincreasing maps with positive
success for every native source, without an imposed success floor. It retains
the same fixed critical temperature, two full Gibbs preparations, coherent
filter, spectator populations and success-only record. This conversion
contract supplies no strict-real child or scalar-retention hypothesis.

The [Gaussian Source Attainer, Theorem 2.1 and §3.2](https://github.com/the-omega-institute/trureturing/blob/b0bba854178edce6540fb1ad1d8b3461925d5f11/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_GAUSSIAN_SOURCE_ATTAINER.md),
at that same fixed revision, selects preparations from its historical $K_J$
with $10\le p\le34$ and proves a five-label Gaussian record law and an
invertible whole-record relabelling preserving the complete instrument.
Its source means reuse the original cubic-gain equations, but its supplied
Gaussian preparation and seven stochastic acquisitions through clock six
give a different acquisition and retention contract. Its selected sources
are outside $K_3$; it proves neither the clock-eight entire-child separation
nor the closed-error prediction condition or one-read identification here.

The [Task–Partition Galois and Whitebox source](https://github.com/the-omega-institute/trureturing/blob/b0bba854178edce6540fb1ad1d8b3461925d5f11/docs/develop/theory/FIB_TASK_PARTITION_GALOIS_AND_WHITEBOX.md),
also at that fixed revision, gives arbitrary-set static task-kernel
factorization and coverage criteria in §10. Its §11 fixes finite deterministic
occurrence forests, root initialization, common legal terminal continuations,
and explicit initial-label or carried-state contracts. Its root-conflict
feasibility and state/label counts do not instantiate the continuous
complete-world source, exact-real record or clock-eight port here. The
generic kernel/factorization principles are credited reuse in §7.2; these
results supply no clock-eight response separation or acquisition bridge.

The [Analytic Frontier Interfaces source, §477](https://github.com/the-omega-institute/trureturing/blob/7fabc7c4a11b70908bf64aee4896cb7c38f9ee0d/docs/develop/theory/FIBONACCI_ANALYTIC_FRONTIER_INTERFACES.md),
at `7fabc7c4a11b70908bf64aee4896cb7c38f9ee0d`, derives bounds on actual lcm
Robin witnesses from Mertens cumulative peaks, with a conditional zero-height
application. Its integer and analytic hypotheses contain no strict-real clock
source, entire child, response map or retention relation. These pinned
comparison results neither prove nor contradict §§9–10 and add no premise
to them; this is a bounded source comparison.

The source-specific delta here is only the pair of actual response maps
(9.5), their nonzero W3 tangents, their disjoint local/remote bands, and the
resulting entire-child injectivity and one-read consequence. Fixed-node
interpolation, the VI/c88 child inventory, the old $a$-margin and midpoint
criterion are reused. The checked source correspondence supports no
literature-wide priority claim.

**Convention 11.2 (remaining scope).** The result preserves all original
fixed-$G_{gc}$, original-$Q$, parked-consumer and unchanged-initialization
questions. It does not settle the global independent equal-$J$/equal-$M$
incidence problem, any base outside $V$, or any all-depth continuation. It
does not construct unknown-source preparation, an effective neighborhood
recognizer, an installed inverse, finite-precision storage, a resource optimum,
or a universal alpha/beta reduction. Independently meaningful space, time,
boundary and memory views, mutual recovery, route agreement, dynamics
compatibility, actual continued callable use and the alpha/beta foundation
therefore remain open in their original scopes.

The interpolation weights used in (9.4) are the distinct-node Lagrange
formula; see Berrut and Trefethen, “Barycentric Lagrange Interpolation”,
§2, DOI 10.1137/S0036144502417715. The inverse-function, compactness and
midpoint steps are used only in the source hypotheses and the retained
whole-child lemma of §§3–6; no stronger global source theorem is inferred.

## 追加锚（本行以下为增补区）

## 12. One additional acquired reply and two different retention channels

**Convention 12.1 (unchanged world and changed last retention field).**
Throughout §§12–17, $\mathcal H$, $\Phi=(p,v)$, $a$, $f_J$, $f_M$,
$W_3$, $y_3$ and $Z$ have exactly their meanings in §§2–3 and 9.
The supplier for §§9–11 is the published volume at
`b2670c974a4d5042331fa7027fc722d0669ead1f`; the VI supplier remains
`4442fb66c4d7017bb7b932cc63f058b46c83b71c`, including its complete
original-world topology and exhaustion results. In particular $a$ is
acquired at clock seven by $J$. The alternative seventh response $m$
is never acquired. No calibration of the drift is supplied.

The old record is precisely

$$
 R_7=(p,v,z_7,\varepsilon_7),\qquad
 \varepsilon_7\ge0,\qquad |z_7-a(W)|\le\varepsilon_7.
\tag{12.1}
$$

A public fixed eighth choice $e\in\{J,M\}$ invokes the same-source
exact acquisition of Definition 10.3. Only its final retention field
is changed here: the exact acquired $f_e(W)$ is discarded after producing
its retained substitute. In the additive version, the complete variable
record after this event is

$$
 R_{8,e}^{\rm add}=(p,v,z_7,\varepsilon_7,z_8,\varepsilon_8),
 \qquad \varepsilon_8\ge0,
\tag{12.2}
$$

and the jointly allowed output relation on each one $W$ is exactly

$$
 |z_7-a(W)|\le\varepsilon_7,\qquad
 |z_8-f_e(W)|\le\varepsilon_8.
\tag{12.3}
$$

Every pair $(z_7,z_8)$ satisfying these inequalities is permitted.
The alternative positive logarithmic version has record

$$
 R_{8,e}^{\log}=(p,v,z_7,\varepsilon_7,z_8,\eta_8),\qquad
 \eta_8\ge0,\quad z_8>0,
\tag{12.4}
$$

and its full joint relation is

$$
 |z_7-a(W)|\le\varepsilon_7,\qquad
 |\log z_8-\log f_e(W)|\le\eta_8.
\tag{12.5}
$$

This version is used only where $f_e(W)>0$. All radii are finite,
public and common to the worlds being compared. The fixed history,
model, channel type, chronological labels $(7,J),(8,e)$, references and
current rights are the same public metadata in every comparison.
The relation is a specification of permitted outputs, with no probability
law or probabilistic independence premise.

Neither record retains an exact $a$ or $f_e$, an error residue, $m$,
a branch or germ sign, a source parameter, an acquired list of possible
worlds or a response oracle. In particular (12.2) is a different retention
contract from the exact appended event in (10.6); it does not retain that
exact event alongside its substitute. The public constant $e$ needs no
world-dependent selector. In §§15–16 it is always $M$.

**Definition 12.2 (one actual old-record-compatible set).** For an actual
old record $R=R_7$ let

$$
 S_R=\{W\in C(p,v):|z_7-a(W)|\le\varepsilon_7\}.
\tag{12.6}
$$

This is the same set for both possible eighth laws and both last-retention
models. It is nonempty because the record is actual. In the neighborhoods
below it is finite, of cardinality at most three. This set specifies a
mathematical compatibility relation; it is not an additional observer
input or a claim that its elements have been enumerated internally.

## 13. Strict additive and logarithmic advantages on the entire child

**Theorem 13.1 (whole-child eighth-response gap comparison).** There is
an open neighborhood $V_*\subset\operatorname{int}K_3$ of $y_3$, contained
in the neighborhood of Theorem 9.4 and Convention 3.3, such that every
$f_J,f_M$ value on $\Phi^{-1}(V_*)$ is positive. For every $y\in V_*$ and
every two distinct complete worlds $W,W'\in C(y)$,

$$
\begin{aligned}
 |f_M(W)-f_M(W')|&>3|f_J(W)-f_J(W')|,\\
 |\log f_M(W)-\log f_M(W')|
   &>2|\log f_J(W)-\log f_J(W')|.
\end{aligned}
\tag{13.1}
$$

The quantifiers include the remote companion and every original permitted
source stratum; they impose no common drift or common gain between
possible worlds.

**Proof.** Use $K$ only for the tangent of (3.2) in this proof. Lemma 9.2
proves $K\theta\ne0$ and $p_b(W_3)\ne0$. Consequently

$$
 \det D(p,\theta)(W_3)=-p_b(W_3)K\theta(W_3)\ne0.
\tag{13.2}
$$

Thus $(p,\theta)$ are genuine local coordinates on the original complete
parent near $W_3$. They come with the regular whole-world lift, including
all padded gain coefficients, from VI, Lemma 2.2. At the center,
$d/d\theta$ while holding $p$ fixed equals $K/(K\theta)$. Equations
(9.13)–(9.15) therefore give

$$
 \partial_\theta f_J<0,\quad \partial_\theta f_M<0,\quad
 \frac{|\partial_\theta f_M|}{|\partial_\theta f_J|}>
 \frac{120}{38}>3,
\tag{13.3}
$$

and

$$
 \frac{|\partial_\theta\log f_M|}
      {|\partial_\theta\log f_J|}>
 \frac{120\cdot499.5}{38\cdot557}>2.
\tag{13.4}
$$

All the quantities are analytic where these positive responses occur.
Continuity gives a product rectangle in $(p,\theta)$ about the center
on which both derivatives in (13.3) remain negative, the two strict
factor inequalities remain true, and the local response bands
$499.5<f_J<500$, $551<f_M<557$ hold. Denote its lifted neighborhood by
$N$. For two different points of $N$ with the same $p$, their $\theta$
coordinates differ. The interval between them at this fixed $p$ stays
inside the rectangle. Integrating the derivatives with their common
negative sign proves both strict inequalities in (13.1). This covers
all local/local pairs with the same base, without requiring the two
points to be a distinguished equal-$m$ pair.

For a local/remote pair, Lemma 9.3 and the local bands give

$$
 |f_M(W)-f_M(Z(y))|>89,
 \qquad |f_J(W)-f_J(Z(y))|<61/10.
\tag{13.5}
$$

Since $89>3(61/10)$, the additive assertion holds. Integrating $1/s$
between the positive response endpoints also gives

$$
 |\log f_M(W)-\log f_M(Z(y))|>\frac{89}{648},\qquad
 |\log f_J(W)-\log f_J(Z(y))|<\frac{61}{4939}.
\tag{13.6}
$$

The rational inequality $89/648>2(61/4939)$ proves the logarithmic
assertion. The reversed order of a pair changes none of these absolute
values. There is at most one remote world at any one base, by VI,
Theorem 18.1.

Finally choose a relatively open remote neighborhood $N_Z$ of $Z(y_3)$
inside that theorem's source square. VI, Theorems 17.2 and 23.1, imply
that the entire inverse image of some open neighborhood of $y_3$ is
contained in $N\cup N_Z$: otherwise a sequence of omitted worlds with
bases tending to $y_3$ would have a strict complete-world limit in
$C(y_3)=\{W_3,Z(y_3)\}$ outside that open union. This is the compactness
argument of (9.18), with the present smaller $N$.
Intersect this base neighborhood with the neighborhoods in Theorem 9.4
and Convention 3.3 to obtain $V_*$. Local/local, local/remote and the
unique-remote case exhaust every pair in every entire child there.
All values lie in the positive bands just used. No stratum is removed
by declaring a local chart: exhaustion is proved in the original world
space before the pair comparison is made. $\square$

**Definition 13.2 (last-retention gaps on the same set).** For an actual
$R$ with $(p,v)\in V_*$ and $|S_R|\ge2$, put

$$
\begin{aligned}
 \gamma_e(R)&=\min_{\substack{W,W'\in S_R\\W\ne W'}}|f_e(W)-f_e(W')|,\\
 \lambda_e(R)&=\min_{\substack{W,W'\in S_R\\W\ne W'}}
                   |\log f_e(W)-\log f_e(W')|.
\end{aligned}
\tag{13.7}
$$

For $|S_R|=1$ set both quantities to $+\infty$. For nonsingletons they
are positive attained minima, by Theorem 9.4 and finiteness. Theorem
13.1 gives, on exactly this same nonsingleton set,

$$
 \gamma_M(R)>3\gamma_J(R),\qquad
 \lambda_M(R)>2\lambda_J(R).
\tag{13.8}
$$

Indeed take a pair attaining the $M$ minimum and apply (13.1), then
bound the $J$ gap of that pair below by its own minimum. The two
minimizing pairs need not be equal. No comparison of two separately
chosen old-record sets occurs here.

## 14. The resulting complete closed-channel retention conditions

**Proposition 14.1 (new-retention thresholds at an actual old record).**
Fix an actual $R$ with base in $V_*$ and a public $e\in\{J,M\}$.
Recovery of every complete $W\in S_R$ from every allowed new retained
value is possible precisely under the following conditions:

$$
\begin{array}{c|c|c}
\text{last retention}&\text{condition}&\text{admissible finite radii}\\ \hline
\text{additive}&2\varepsilon_8<\gamma_e(R)&[0,\gamma_e(R)/2)\\
\text{positive logarithmic}&2\eta_8<\lambda_e(R)&[0,\lambda_e(R)/2).
\end{array}
\tag{14.1}
$$

For a singleton every finite nonnegative radius is admissible. For a
nonsingleton the finite upper endpoint is inadmissible, including
at equality. Thus the additive critical supremum for $M$ is strictly
more than three times that for $J$, and the logarithmic critical
supremum is strictly more than twice as large, whenever $S_R$ is a
nonsingleton. These are consequences of the source-specific gaps;
the interval recovery principle itself is the reused Lemma 5.3.

**Proof.** With the old record fixed, the compatible set after an
additive retained value is exactly

$$
 \{W\in S_R:|z_8-f_e(W)|\le\varepsilon_8\}.
\tag{14.2}
$$

Under the strict inequality in (14.1), two different elements cannot
both satisfy this constraint, by the triangle inequality and (13.7).
An actual allowed value has at least its generating world compatible.
Selecting the unique element defines one mathematical partial inverse
on all singleton compatibility sets, using only the displayed record
and public model. It therefore works simultaneously for all actual
records in the stated safe domain; neither an acquired enumeration
nor the parameter $h$ is needed as an extra input to its definition.

If the inequality fails, a pair attaining $\gamma_e(R)$ and the
midpoint of its two $f_e$ values give the same new retained value
for both worlds. Both worlds already admit this very same old $R$.
The full joint relation (12.3) therefore permits the same complete
record for both, including at equality. No single-valued inverse can
return both distinct worlds.

For the logarithmic channel apply the same interval principle to
$\log f_e$. A midpoint in logarithmic coordinates is the positive
value

$$
 z_8=\exp\!\left(\frac{\log f_e(W)+\log f_e(W')}{2}\right),
\tag{14.3}
$$

which is permitted for both at equality and above it. For a singleton,
compatibility with the old record alone has already fixed the target,
so every allowed new value leaves that target unique. The comparisons
of suprema are exactly (13.8) divided by two. $\square$

**Proposition 14.2 (joint-channel condition and coalescing pairs).**
For a fixed $y\in V_*$ and common radii, uniform exact recovery for all
old and new records on the entire $C(y)$ holds in the additive model
if and only if there is no distinct pair $W,W'\in C(y)$ satisfying
both

$$
 |a(W)-a(W')|\le2\varepsilon_7,\qquad
 |f_e(W)-f_e(W')|\le2\varepsilon_8.
\tag{14.4}
$$

In the logarithmic model replace the second inequality by
$|\log f_e(W)-\log f_e(W')|\le2\eta_8$. The same pair must satisfy
both inequalities. In particular the separate minima of the two
coordinate gaps cannot be combined unless their common-pair
compatibility has been checked.

For the actual pair $W_\pm(h)$ of (3.5), both eighth additive gaps
and both eighth logarithmic gaps tend to zero. Hence no positive
lower bound for these gaps holds uniformly over the punctured germ.
For any fixed $\varepsilon_7>0$, old midpoint records exist on every
sufficiently small nontrivial germ child for which these new-retention
critical suprema tend to zero as well.

**Proof.** Two closed equal-radius intervals intersect precisely when
the distance of their centers is at most twice the radius. Applying
this separately to the two coordinates for one fixed pair, and then
using the full joint output relation, proves necessity and sufficiency
of (14.4). The common base is exact and already equal. The intersection
can use the midpoint in each coordinate, so equality is included.
For the log version use logarithmic coordinates and exponentiate
their midpoint. If no pair is jointly compatible, every actual
complete record has a unique world, which proves sufficiency.

Both germ worlds converge in original complete-source coordinates to
$W_3$. Continuity of the positive responses and their logarithms proves
the asserted zero limits. Their seventh gap also tends to zero by
(3.6). For fixed $\varepsilon_7>0$, take
$z_7=(a(W_+(h))+a(W_-(h)))/2$. This is allowed for both for all
sufficiently small $h\ne0$. Then $S_R$ contains that pair, so each
minimum in (13.7) is at most its corresponding pair gap and tends to
zero. This assertion concerns these ambiguous old records, not every
old record or the exact-old-retention endpoint. $\square$

Theorem 10.2 remains the separate old-$a$ prediction theorem:
its old-record-only criterion uses seventh-$a$ distances. Equations
(13.7)–(14.1) concern the newly retained eighth scalar after the actual
additional read. They do not rename the old-$a$ margin or change its
equality case.

## 15. Full-preimage source stability and common-word future responses

**Definition 15.1 (original complete-source coordinates and future task).**
For $g(s)=\sum_{j=0}^3k_js^j$, padded through degree three, use

$$
 \omega(W)=(r,b,c,d,k_0,k_1,k_2,k_3)\in\mathbb R^8,
 \qquad \|\cdot\|_\infty,
 \qquad B_M(W)=(p(W),v(W),f_M(W)).
\tag{15.1}
$$

These are the original coefficients and source entries, without a
normal-form change of metric. The tuple is injective on complete
worlds. From now on the eighth action is the public constant $M$, and

$$
 Q_8=MQ_7=\begin{pmatrix}3&1\\8&3\end{pmatrix}.
\tag{15.2}
$$

For a chronological word $u=(E_1,\ldots,E_n)\in\{J,M\}^n$ put
$T_u=E_n\cdots E_1$, with $T_\varnothing=I$, and define its terminal
numerical response at the absolute clock by

$$
 Y_u(W)=d+g(8+n)\operatorname{tr}(T_uQ_8P).
\tag{15.3}
$$

This is a task of mathematical response evaluation from the frozen
clock-eight boundary. It does not grant execution of $u$, a new read,
access to a discarded value or a future invocation right.

**Theorem 15.2 (inverse Lipschitz bound on an entire original preimage).**
There exist a compact base rectangle $\mathcal K$ and a finite $L>0$,
with $y_3\in\operatorname{int}\mathcal K$ and
$\mathcal K\subset V_*$, such that, for
$\mathcal D=\Phi^{-1}(\mathcal K)$ taken in the original $\mathcal H$,

$$
 \|\omega(W)-\omega(W')\|_\infty
 \le L\|B_M(W)-B_M(W')\|_\infty
 \qquad(W,W'\in\mathcal D).
\tag{15.4}
$$

All pairs are covered, including different acquired bases, the remote
companion and every permitted stratum in this full preimage. Neither
$\mathcal K$ nor $L$ is supplied effectively.

**Proof.** At $W_3$, (9.17) gives an invertible differential for
$(p,f_M)$ in the genuine $(t,b)$ coordinates. The inverse-function
theorem gives a local inverse. Choose a convex open rectangle $A$ in
its $(p,f_M)$ image, containing the center image, whose compact closure
is inside the inverse domain. Composing this inverse with VI's
analytic whole-world lift gives an analytic map
$H:A\to\mathbb R^8$ returning exactly $\omega(W)$.
Its derivative is bounded on $\overline A$, because it extends
analytically to a neighborhood of that closure. The mean value
inequality on the convex rectangle supplies a finite $L_N$ with

$$
 \|H(q)-H(q')\|_\infty\le L_N\|q-q'\|_\infty
 \qquad(q,q'\in A).
\tag{15.5}
$$

Choose a complete-world neighborhood $N$ of $W_3$ lying in this lifted
rectangle and in the local neighborhood used in Theorem 13.1.
Equation (15.5) bounds every local/local pair in $N$ by its
$(p,f_M)$ difference, hence by its $B_M$ difference. This explicitly
uses derivative regularity of the inverse on a convex image; compact
injectivity alone would not justify (15.5).

The remote branch $Z(y)$ is analytic over the open rectangle
$\widehat K_3$ of VI, Theorem 18.1. On a compact rectangle about $y_3$
inside that open rectangle, the derivative of $\omega\circ Z$ is
bounded. The same convex mean value inequality gives a finite $L_Z$
bounding every remote/remote source difference by $\|y-y'\|_\infty$,
and therefore by the full $B_M$ difference.

Using the full compact set $\Phi^{-1}(K_3)$ and its exact two-world
fiber over $y_3$, shrink the base as in the exhaustion argument of
Theorem 13.1 until every world belongs either to $N$ or to the remote
branch. Choose $\mathcal K$ to be a compact rectangle about $y_3$
inside this base neighborhood, $V_*$ and the remote derivative domain.
The set $\mathcal D$ is compact by VI, Theorem 17.2, since it is the
inverse image of the closed subset $\mathcal K\subset K_3$.
Let $D_\omega$ be its finite diameter in the norm of (15.1).

For a local world and a remote world, even at different bases in
$\mathcal K$, the uniform bands (9.15)–(9.16) give
$|f_M(W)-f_M(W')|>89$. Thus

$$
 \|\omega(W)-\omega(W')\|_\infty
 \le D_\omega\le\frac{D_\omega}{89}
                         \|B_M(W)-B_M(W')\|_\infty.
\tag{15.6}
$$

Taking $L=\max\{1,L_N,L_Z,D_\omega/89\}$ proves (15.4) in all
three cases. The full-preimage exhaustion, rather than a restriction
of the model to two selected parametrizations, is what makes these
cases exhaustive. $\square$

**Theorem 15.3 (uniform numerical sensitivity for every common word).**
For the same $\mathcal D$, there is a finite $C>0$ such that, for all
$W,W'\in\mathcal D$, every $n\ge0$ and every common chronological
$u\in\{J,M\}^n$,

$$
 |Y_u(W)-Y_u(W')|
 \le C\varphi^n(1+n)^3\|B_M(W)-B_M(W')\|_\infty,
 \qquad \varphi=\frac{1+\sqrt5}{2}.
\tag{15.7}
$$

The same right-hand side bounds the maximum difference over all prefix
responses $Y_{u_{\le k}}$, $0\le k\le n$, so every intermediate
immediate read is included in the numerical statement.

**Proof.** Use the Euclidean operator norm for matrices and the maximum
norm (15.1) for sources. Since $J$ is orthogonal and $M$ is symmetric
with eigenvalues $\varphi$ and $-\varphi^{-1}$,

$$
 \|J\|_2=1,\qquad\|M\|_2=\varphi,
 \qquad \|T_uQ_8\|_2\le\varphi^n\|Q_8\|_2.
\tag{15.8}
$$

Choose $H\ge1$ bounding both $\|P\|_2$ and each $|k_j|$ on the compact
$\mathcal D$. Put $\delta_\omega=\|\omega(W)-\omega(W')\|_\infty$
and $A_0=4\cdot8^3$. Since $8+n\le8(1+n)$,

$$
\begin{aligned}
 |g(8+n)|&\le A_0H(1+n)^3,\\
 |g(8+n)-g'(8+n)|&\le A_0\delta_\omega(1+n)^3,\\
 \|P-P'\|_2&\le2\delta_\omega,\qquad |d-d'|\le\delta_\omega.
\end{aligned}
\tag{15.9}
$$

Here primes label the second world, not derivatives. The coefficient
bounds cover lower-degree polynomials without changing this padded
coordinate system. For two-by-two real matrices,
$|\operatorname{tr}(AB)|\le2\|A\|_2\|B\|_2$. Splitting the difference
in (15.3) into its drift, gain and source terms now gives

$$
 |Y_u(W)-Y_u(W')|
 \le\{1+6A_0H\|Q_8\|_2\}
             \varphi^n(1+n)^3\delta_\omega.
\tag{15.10}
$$

For the drift term we used $\varphi^n(1+n)^3\ge1$.
Apply (15.4) and absorb its constant $L$ to obtain (15.7).
The estimate uses the one entire polynomial of each world at the
absolute clock $8+n$, and the same future word in both worlds. It
fits no new polynomial to a later prefix and supplies no later
measurement. Applying the estimate to every prefix and using the
monotonicity of $\varphi^k(1+k)^3$ proves the prefix maximum assertion.
$\square$

## 16. Actual frozen-record witnesses with an uncancelled growing mode

**Lemma 16.1 (growing polynomial changes along the original third germ).**
Put $\psi=-\varphi^{-1}$ and use the spectral projectors

$$
 \Pi_+=\frac{M-\psi I}{\varphi-\psi},\qquad
 \Pi_-=I-\Pi_+,\qquad
 A_\pm(W)=\operatorname{tr}(\Pi_\pm Q_8P).
\tag{16.1}
$$

For every sufficiently small nonzero $h$, the actual pair $W_\pm(h)$
of (3.5) has a nonzero polynomial

$$
 D_{+,h}(s)=A_+(W_+(h))g_+(s)-A_+(W_-(h))g_-(s).
\tag{16.2}
$$

Its nonvanishing concerns the actual original-source lift, not merely
an eighth-response tangent.

**Proof.** Every entry of $\Pi_+=(M+\varphi^{-1}I)/\sqrt5$ is positive.
Both $Q_8$ and $P$ have positive entries. Hence $A_+(W)>0$ on the
entire original world domain. The projector is an algebraic proof
tool, not an extra allowed acquisition action.

At $W_3$ use the tangent $K$ of (3.2), and write
$D_\theta=K/(K\theta)$ at this point. Lemma 9.2 gives
$K\theta\ne0$, $Kp=Kv=0$, and

$$
 d_\theta:=D_\theta d\in[-8.75,-8.69]<0.
\tag{16.3}
$$

The source bands give $p<d<v$ at this exact world. The genuine
same-source samples (9.3) imply

$$
 \frac{g(5)}{g(6)}=
 \frac{p-d}{v-d}\frac{2+\theta}{1+\theta},
 \qquad g(5)g(6)\ne0.
\tag{16.4}
$$

Differentiating while $D_\theta p=D_\theta v=0$ yields

$$
 D_\theta\log\left|\frac{g(5)}{g(6)}\right|
 =-d_\theta\left(\frac1{p-d}-\frac1{v-d}\right)
   -\frac1{(1+\theta)(2+\theta)}<0.
\tag{16.5}
$$

The first parenthesis is negative, $-d_\theta>0$, and the last
term is strictly negative. This proves the sign without a new
numerical approximation or a separate gain fit.

If both $K(A_+g(5))$ and $K(A_+g(6))$ were zero at $W_3$, their
nonzero values would give

$$
 K\log|A_+g(5)|=K\log|A_+g(6)|=0,
$$

and hence $K\log|g(5)/g(6)|=0$. This contradicts (16.5) and
$K\theta\ne0$. Choose $s_0\in\{5,6\}$ for which
$K(A_+g(s_0))\ne0$.

VI, Theorem 15.1, gives analytic complete-world branches with derivatives
$+K,-K$ at zero and $W_-(h)=W_+(-h)$. The same whole gain coefficients
are part of that lift. The odd analytic difference at this fixed sample
therefore satisfies

$$
 D_{+,h}(s_0)=2hK(A_+g(s_0))(W_3)+O(h^3).
\tag{16.6}
$$

Its nonzero linear coefficient makes it nonzero for every sufficiently
small nonzero $h$. Thus the polynomial (16.2) is nonzero for each
such pair, proving actual growing-mode noncancellation. $\square$

**Theorem 16.2 (arbitrarily close worlds, one complete frozen record,
and unbounded all-$M$ response difference).** Fix any
$\varepsilon_7>0$ and $\varepsilon_8>0$ in the full additive joint
relation (12.3), with eighth choice $M$. In every complete-source
neighborhood of $W_3$ there are distinct actual $W_+(h),W_-(h)\in
\mathcal D$ and one complete record $R_{8,M}^{\rm add}$ allowed for
both, such that for every real $1\le\rho<\varphi$,

$$
 \lim_{n\to\infty}
 \frac{|Y_{M^n}(W_+(h))-Y_{M^n}(W_-(h))|}
      {\rho^n(1+n)^3}=+\infty.
\tag{16.7}
$$

In particular their unweighted future difference is unbounded. The
same chosen pair works for every $\rho$ in the displayed range.

**Proof.** The actual germ worlds have the same exact $p,v$ and converge
to $W_3$ in every coordinate (15.1). Their bases tend to the interior
point $y_3$ of $\mathcal K$, so both belong to $\mathcal D$ for every
sufficiently small $h$. Both $a$ and $f_M$ differences tend to zero.
Choose an arbitrarily small nonzero $h$ for which Lemma 16.1 applies
and both half-differences are strictly below the stipulated positive
radii. Set

$$
 z_7=\frac{a(W_+(h))+a(W_-(h))}{2},\qquad
 z_8=\frac{f_M(W_+(h))+f_M(W_-(h))}{2}.
\tag{16.8}
$$

The common exact base, these two real substitutes, the same public
radii and the fixed event metadata constitute one complete frozen
record permitted by (12.3) on each of these two actual worlds.
No coupling of two separately chosen pairs is involved. Each witness
has its own one source, its original whole $g_\pm$ and its fixed
$d_\pm$ on every clock, including the original $H_4$ and actual
$M,M,J,M$ extension. The values in (16.8) witness allowed channel
outputs, not an observer's access to the two exact replies.

The elementary spectral identity
$M^n=\varphi^n\Pi_++\psi^n\Pi_-$ gives exactly

$$
\begin{aligned}
 Y_{M^n}(W_+(h))-Y_{M^n}(W_-(h))
  ={}&d_+-d_-+\varphi^nD_{+,h}(8+n)\\
    &+\psi^nD_{-,h}(8+n),
\end{aligned}
\tag{16.9}
$$

where $D_{-,h}(s)=A_-(W_+(h))g_+(s)-A_-(W_-(h))g_-(s)$ also has
degree at most three. The original same-source clock is $8+n$;
there is no clock reset or newly fitted polynomial in (16.9).

By Lemma 16.1, $D_{+,h}$ is a nonzero polynomial. If its degree is
$k\in\{0,1,2,3\}$, its nonzero leading coefficient supplies $c_h>0$
and $N_h$ with $|D_{+,h}(8+n)|\ge c_h n^k$ for $n\ge N_h$.
The other polynomial times $\psi^n$ tends to zero because
$|\psi|<1$, while $d_+-d_-$ is constant. The reverse triangle
inequality in (16.9), after enlarging $N_h$, therefore gives

$$
 |Y_{M^n}(W_+(h))-Y_{M^n}(W_-(h))|
 \ge\frac{c_h}{2}\varphi^n n^k.
\tag{16.10}
$$

For every fixed $1\le\rho<\varphi$, an exponential with ratio
$\varphi/\rho>1$ dominates the factor $(1+n)^3/n^k$.
Dividing (16.10) proves (16.7). The unweighted assertion follows
as well, for example from the case $\rho=1$. Arbitrarily small
$h$ were available under all the preceding strict requirements.
$\square$

**Corollary 16.3 (reused two-point prediction inequality on the witness).**
For the common record in Theorem 16.2, any sequence of numerical
predictions $q_n$ depending only on that record and public data obeys

$$
 \max_{\sigma\in\{+,-\}}
 |q_n-Y_{M^n}(W_\sigma(h))|
 \ge\frac12|Y_{M^n}(W_+(h))-Y_{M^n}(W_-(h))|.
\tag{16.11}
$$

Consequently it has no uniform finite error bound on that record
fiber, even after the smaller-exponential normalization in (16.7).
For each such normalization at least one of the two worlds has
unbounded normalized error.

**Proof.** Apply the triangle inequality to the two errors and their
common $q_n$, then use (16.7). If both individual normalized errors
were bounded, their maximum would be bounded, a contradiction.
$\square$

Both positive radii and the full joint allowed relation are essential
to this witness. Nothing here extends it to exact retention endpoints,
a restricted channel omitting the common outputs, adaptive later
observations, or an observer with additional lawful acquired data.
Theorem 15.3 uses the larger weight $\varphi^n(1+n)^3$ and an exact
boundary-coordinate distance; it is consistent with (16.7). The lower
bound establishes no impossibility for every physical observer and
no universal memory or acquisition lower bound.

## 17. Geometry, ordered clocks, readout and memory on the same process

**Definition 17.1 (four independently specified expressions).** The
source geometry is the positive rank-one projector $P(r,b)$ on
$\mathbb R^2$, or equivalently its image line and complementary kernel
line with its trace-one normalization. At a clocked event its transported
relation is $H_i=Q_iP$. These definitions use linear incidence and the
actual left action, not an inverse of a desired observation.

The ordered action/clock expression consists of the absolute clock $i$
and the chronological action word actually executed, with its ordered
product $Q_i$. The boundary expression at that event is the single
actual read $d+g(i)\operatorname{tr}H_i$. The retained expression is
exactly (12.1) before the eighth event and (12.2), or (12.4), after
its declared retention relation. It contains its specified references
and event labels; it does not contain the rest of the history as
unrestricted variable data. The stipulated $H_4$, already acquired
exact $p,v$, and the conditional one-step port are premises of this
process. No procedure acquiring this initialization from an unknown
source is asserted.

**Proposition 17.2 (source, readout and clock correspondence).** On
$\mathcal D$, the exact acquired boundary subrecord $B_M=(p,v,f_M)$
mathematically determines one complete original $W$. Reconstructing
that world, forming its transported geometry and then evaluating its
readout agrees with the original forward route at every stipulated
clock, and with (15.3) for every mathematical common continuation
word. The same route agreement holds from a retained record on each
of the singleton compatibility domains of Proposition 14.1.

The original clock-seven run uses exactly seven actions and eight
scalar readings including clock zero. Its eighth-event extension
uses exactly eight actions and nine scalar readings. The extension
acquires only its one chosen eighth scalar.

**Proof.** The original $P$ has trace one and determinant zero, hence
$P^2=P$ by the two-by-two characteristic identity. Its rank is one,
so its image and kernel are complementary lines. Conversely the
projection onto a line along its specified complementary line is
unique: it fixes every vector in the image and annihilates every
vector in the kernel, which together span $\mathbb R^2$. This
justifies the independent geometric description.

For an actual state write

$$
 \mathsf S_i=(i,H_i,g,d),\qquad
 F_E(\mathsf S_i)=(i+1,EH_i,g,d),\qquad
 q(\mathsf S_i)=d+g(i)\operatorname{tr}H_i.
\tag{17.1}
$$

The initial state is $(0,P,g,d)$. Induction using $Q_i=E_iQ_{i-1}$
proves $H_i=Q_iP$ after each actual action and therefore reproduces
exactly every stipulated original reading, including $H_4$, the
fifth/sixth $p,v$, seventh $a$, and chosen eighth $f_M$. The state
recursion preserves the whole $g$ and fixed $d$; it does not replace
them by samples. It is an equation for the actual process and a
mathematical continuation law, not an extra retained register.

If two worlds of $\mathcal D$ have the same $B_M$, (15.4) makes their
complete-source coordinates equal, hence the worlds equal. Thus on
the actual image the recovered world is exactly the generating one.
Reapplying (17.1) to this same world reproduces the original prefix.
For a future word $u$ the induction gives state
$(8+n,T_uQ_8P,g,d)$, whose readout is (15.3). For chronological words
$u,w$, $T_{uw}=T_wT_u$; therefore direct evaluation of their
concatenation and successive state updates agree, using the same
absolute gain argument $8+|u|+|w|$. This proves the claimed dynamics
compatibility and route agreement without changing the source.

For a record in a safe domain of Proposition 14.1, its unique
compatible world is likewise the actual one. Applying the preceding
construction to it gives identical geometry and numerical responses.
Its reconstructed exact $a$ and $f_e$ satisfy the reported retention
inequalities; they are computed mathematical consequences of the
unique world, not additional surviving error residues. In the $J$
version the same induction uses $Q_{8,J}$ of (9.1).

Finally the chronological prefix is $J,M,J,M,M,M,J$ after clock zero,
with readings $(0,24,147/5,24,18,p,v,a)$. Appending its single chosen
$e$ adds exactly one action and one immediate read. There is no second
specimen, reset, skipped read, alternative seventh $m$ acquisition
or simultaneous acquisition of both eighth laws. $\square$

**Convention 17.3 (resources, suppliers and remaining scope).** The
retained variable numerical fields are four reals before the extension
and six after it, with their displayed constraints; action/channel
labels and the fixed model are public. Exact $p,v$ remain potentially
infinite-precision references, as do the declared real substitutes
and radii. These field and action/read counts are not bounded-bit
memory, arithmetic, execution-time or optimality claims. In particular
a compatible set is not an acquired list, a partial mathematical
inverse is not a finite-input decoder, and response evaluation in
(15.3) is not an authorized future call. Neither the inverse Lipschitz
estimate nor the noise relation installs source acquisition, selection,
retained accessibility or continued callable use. No future rights
are added to the original one-step port.

The new quantitative deductions are (13.1), their last-retention
consequences on the same $S_R$, the full-preimage estimate (15.4),
the uniform clocked response estimate (15.7), and the actual
noncancelling common-record witnesses (16.2)–(16.10). They are
`repo-derived` ordinary mathematics. The exact germ and its derivatives,
compact exhaustion, center inventory, remote analytic branch, original
eighth responses and their tangent/response bands are reused from
§§3 and 9 and the pinned VI. Closed intervals and their midpoint
criterion are reused from Lemma 5.3. The inverse-function theorem,
convex mean value inequality, polynomial interpolation, spectral
decomposition and domination of polynomials by exponentials are
classical tools, not additional source-specific discoveries.

For the calculus suppliers, the repository's pinned mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` contains
`HasStrictFDerivAt.to_localInverse` in
`Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`,
`ApproximatesLinearOn.antilipschitzWith` in its
`ApproximatesLinearOn.lean` companion, and
`Convex.norm_image_sub_le_of_norm_fderiv_le` in
`Mathlib/Analysis/Calculus/MeanValue.lean`. Their inverse-derivative and
convex derivative-bound hypotheses are met here by the displayed
nonzero Jacobians and the analytic lifts on neighborhoods of compact
rectangles. The kernel/effective-image and predictive-memory
suppliers of Convention 7.2 remain general factorization tools;
they supply neither these source-specific estimates nor an acquisition
or update implementation. The distinct-node interpolation attribution
in §11 is unchanged, as are the unavailable book contexts in §8.3.
These deductions assert no literature-wide priority.

The later VII, §§36–39, and VIII, §§30–34, at
`c8ae6f747aeb40c61f9d135f171011de99a12c99` retain their own exact
source contracts. VII's fixed-drift exclusion does not identify the
clock-eight response or impose a calibrated drift on this domain.
VIII's distinguished H/L arc has $10\le p\le34$, whereas this domain
has $p$ near $7.283036$. Its endpoint classification does not restrict
the entire children here to that arc or remove the remote companion.
The moving-trace recovery and polynomial-gain shear-calibration
volumes at `e1a5759d74d7b8f1b6faad61f47a85859b385fd1` likewise
have their stated calibration histories and, for the latter, a different
read-clock/compound-word contract. Their recovery constructions are
not a retention or future-sensitivity theorem for this fixed prefix.
The finite-start predictive-memory volume at that revision uses a
passive five-mode stochastic source and future-law distance; its
exact ambiguous-branch metric is not the numerical-response metric
of (15.3).

The precise gain over NCR/PVC/PR57/PG/Atlas in Convention 7.3 is this
source-specific quantitative boundary/retention/dynamics bridge under
the original clock law, not an additional installation or serialization
service. A clock word alone is not a source identifier. Under positive
retention errors the common record of Theorem 16.2 does not determine
the future responses; at a safe record the proved reconstruction is
only the stated conditional mathematical one. Thus no four isolated
view kernels are asserted equal, and no four-way mutual recovery or
universal alpha/beta generation of this process follows. All earlier
fixed-$G_{gc}$, original-$Q$, parked-consumer, initialization-specific
and global incidence questions keep their original scopes and
settlements. Unknown-source acquisition, finite-input recovery,
installed lawful continuation and the full four-expression objective
remain unresolved.

## 追加锚（本行以下为增补区）

## 18. An explicit common-bound estimate in original source coordinates

**Theorem 18.1 (conservative common-coordinate sensitivity).** Let
$W=(P(r,b),g,d)$ and $W'=(P(r',b'),g',d')$ be any two original complete
worlds of Definition 2.1. Use the coordinates and chronological response
of Definition 15.1, so
$\omega(W)=(r,b,c,d,k_0,k_1,k_2,k_3)$ with $c=r(1-r)/b$ and
$g(s)=\sum_{j=0}^3k_js^j$, and likewise for $W'$. For every real $H\ge1$
satisfying

$$
 |\omega_j(W)|\le H,\qquad |\omega_j(W')|\le H
 \qquad(j=0,\ldots,7),
$$

every $n\in\mathbb N_0$ and every common chronological word
$u=(E_1,\ldots,E_n)\in\{J,M\}^n$, with $T_u=E_n\cdots E_1$ and
$T_\varnothing=I$, obey

$$
 |Y_u(W)-Y_u(W')|
 \le (1+1048576H)\varphi^n(1+n)^3
                  \|\omega(W)-\omega(W')\|_\infty,
 \qquad \varphi=\frac{1+\sqrt5}{2}.
\tag{18.1}
$$

Here $Y_u(W)=d+g(8+n)\operatorname{tr}(T_uQ_8P(r,b))$ uses the
original whole cubic at the absolute clock $8+n$ and the actual
$Q_8=\begin{pmatrix}3&1\\8&3\end{pmatrix}$, with the same conventions
for $W'$. The bound assumes no acquired-prefix constraint. It is a
conservative source-coordinate estimate and does not replace (15.7)
or the tighter operator-norm constant in (15.10).

Proof. Put $v=(1,\varphi)^{\mathsf T}$. Both native actions have
nonnegative entries, $Jv\le\varphi v$ coordinatewise, and
$Mv=\varphi v$, since $\varphi^2=1+\varphi$. Induction on the word
therefore preserves nonnegativity and gives the cone invariant

$$
 (T_u)_{i0}+\varphi(T_u)_{i1}\le\varphi^n v_i
 \qquad(i=0,1).
\tag{18.2}
$$

Since $1\le v_i<2$, every entry of $T_u$ has absolute value at most
$2\varphi^n$. Every entry of $Q_8$ is at most $8$, so every entry of
$A=T_uQ_8$ has absolute value at most $32\varphi^n$. Consequently,
for any two-by-two matrix $S$ whose entries have absolute value at
most $K\ge0$, the four terms of the trace pairing give
$|\operatorname{tr}(AS)|\le128\varphi^nK$.

Write $P=P(r,b)$, $P'=P(r',b')$ and
$\delta=\|\omega(W)-\omega(W')\|_\infty$. Every entry of $P$ has
absolute value at most $2H$: this follows directly from the coordinate
bounds for $r,b,c$, and $|1-r|\le1+|r|\le2H$. Every entry of $P-P'$
has absolute value at most $\delta$, including
$|(1-r)-(1-r')|=|r-r'|$. Thus

$$
 \begin{aligned}
 |\operatorname{tr}(AP)|&\le256\varphi^nH,\\
 |\operatorname{tr}(AP)-\operatorname{tr}(AP')|
   &\le128\varphi^n\delta.
 \end{aligned}
\tag{18.3}
$$

Put $q=(1+n)^3$. For each $0\le j\le3$,
$(8+n)^j\le512q$, since $8+n\le8(1+n)$ and $n\ge0$.
Applying the sum of these four monomial bounds to the ordinary
coefficients of $g'$ and of $g-g'$ yields

$$
 |g'(8+n)|\le2048Hq,\qquad
 |g(8+n)-g'(8+n)|\le2048\delta q.
\tag{18.4}
$$

Primes label the second world, not derivatives. The exact difference
splits as

$$
 \begin{aligned}
 Y_u(W)-Y_u(W')={}&(d-d')
 +(g(8+n)-g'(8+n))\operatorname{tr}(AP)\\
 &+g'(8+n)\bigl(\operatorname{tr}(AP)-\operatorname{tr}(AP')\bigr).
 \end{aligned}
$$

Using $|d-d'|\le\delta$, (18.3) and (18.4), its absolute value is at
most

$$
 \delta+(2048\delta q)(256\varphi^nH)
        +(2048Hq)(128\varphi^n\delta)
 =\delta+786432H\varphi^nq\delta.
$$

Finally $\varphi^nq\ge1$ absorbs the drift term, and
$786432H\le1048576H$ gives (18.1). $\square$

## 追加锚（本行以下为增补区）
