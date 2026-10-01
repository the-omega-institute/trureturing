# Even mixed corners transport actual query-weighted overlap

A covered canonical fibre with a private target point forces actual
overlap at an even nonempty mixed corner. On a cut with more than two
axes, that corner need not be the point outside every target root.
The exact positive replacement is a family of reset measures transported
from the same actual private set. Their densities give a lower bound for
an arbitrary nonnegative joint query payoff on actual overlap.

More generally, one chosen probability law supported on the actual
private set gives the same transport, with cost determined by its
projection densities rather than the private set's total mass. For three
axes only its three one-coordinate marginals are needed. Uniform marginal
bounds can
therefore give a positive conditional overlap bound even when private
mass tends to zero. A symbolic distinct-odd tagged-fibre construction
below shows that this premise is nonempty. It does not establish it for
an arbitrary cover or supply a uniform global source mass.

These are ordinary finite set and measure proofs. No numerical campaign,
Lean verification, or unrestricted Erdős #7 noncoverage theorem is
claimed. The finite-difference cancellation and private-mass baseline
are reused mechanisms; the result here records actual overlap location,
the exact same-source reset densities, and their joint-payoff consumer.

Section 7 gives the complementary limitation using only four fixed odd
primes. A globally irredundant distinct-modulus family can have a
covered, genuinely three-cut fibre whose outside-target overlap tends
to zero as heights grow. The same occurs after conditioning on the
avoidance of actual original prime classes. These families have global
holes; their full overlap on the selected fibre does not tend to zero.
Thus the local fibre premises and irredundance do not supply the
projection or weighted-mass input needed for a uniform positive
outside-target bound.

## 1. One actual canonical fibre and its original labels

Fix a finite original family $A_i=[a_i]_{d_i}$ with distinct odd moduli
$d_i>1$, a divisibility-maximal selected original $C=[a]_d$, and a common
finite CRT period $N$. For each other original put

$$
D_i=\{p:p\mid d,\ p\text{ prime},\ v_p(d_i)<v_p(d)\}.
$$

Let $T\subseteq\{p:p\text{ prime},\ p\mid d\}$ be a hitting set for all
$D_i$, with $k=|T|\ge2$.
The canonical boundary from
[report 838](838-weighted-primitive-overlap-on-admissible-prime-boundaries.md)
is

$$
b=q_T=
\prod_{p\in T}p^{v_p(d)-1}
\prod_{p\mid N,\ p\notin T}p^{v_p(N)}.                 \tag{EC1}
$$

Condition on one literal fibre modulo $b$ where the target is active,
using the original phases and their exact affine pullback. Index the
axes in $T$ by $1,\ldots,k$. The residual carrier and relative Haar law
are

$$
X=\prod_{i=1}^kX_i,\qquad
X_i=\mathbb Z/p_i^{\alpha_i}\mathbb Z,\qquad
\mu=\bigotimes_i\mu_i,
\quad \alpha_i=v_{p_i}(N)-v_{p_i}(d)+1\ge1.
$$

The target is $C=\prod_i C_i$, where $C_i$ fixes one first residual
digit and $\mu_i(C_i)=1/p_i$. Every other active original cylinder omits
at least one cut axis. Keep original tags even when residual numerical
labels coincide. No global-top-height premise is being imposed on the
target.

Assume that this actual fibre is covered by these originals and that
the target-private set is nonempty:

$$
\Pi=C\setminus\bigcup_{j\ne *}A_j,\qquad
\theta=\mu(\Pi)>0.                                     \tag{EC2}
$$

All subsequent assertions are conditional on this fibre. A whole odd
cover is not a premise. Let

$$
L_-(y)=\sum_{j\ne *}\mathbf1_{A_j}(y),\qquad
O=\{y\in C^c:L_-(y)\ge2\}.                            \tag{EC3}
$$

Thus $O$ consists of points covered by at least two actual other
original labels. It is not an intersection of preimages referring to
two different points.

The original-owner partition and private-shell supplier capacities in
the [coset library](../../../../../../Library/Arith/lettlsun2008cosets.md)
remain reusable. A pair of shell suppliers can cover two different
modified points; EC3 requires both originals to cover one actual reset
corner. The transport below preserves the query at that point.

## 2. The even-corner location lemma

Choose $x\in\Pi$ and, independently for the present pointwise argument,
any $z_i\in C_i^c$. For $J\subseteq T$, let $y^J$ use $z_i$ on $J$ and
$x_i$ on $J^c$. Each other cylinder has zero alternating sum on this
Boolean cube: it omits an axis, along which the terms cancel in pairs.
Consequently

$$
\sum_{J\subseteq T}(-1)^{|J|}L_-(y^J)=0.
$$

The empty corner has $L_-(x)=0$. Every nonempty corner lies outside the
target, so local coverage gives $L_-(y^J)\ge1$. With
$e_J=L_-(y^J)-1\ge0$ for nonempty $J$, the cancellation reads

$$
\boxed{
\sum_{\substack{J\ne\varnothing\\|J|\text{ even}}}e_J
-\sum_{|J|\text{ odd}}e_J=1.
}                                                       \tag{EC4}
$$

At least one even nonempty corner therefore belongs to $O$. Write

$$
\mathcal E=\{J\subseteq T:J\ne\varnothing,\ |J|\text{ even}\}.
$$

For every nonnegative joint function $h:X\to\mathbb R_{\ge0}$,

$$
\sum_{J\in\mathcal E}h(y^J)\mathbf1_O(y^J)
\ge\min_{J\in\mathcal E}h(y^J).                         \tag{EC5}
$$

The minimum is essential. The overlap corner may depend on the entire
private point and the jointly chosen outside coordinates. Separately
optimized phases, a mean corner payoff, or unrelated marginal queries
cannot replace the right side of EC5.

This is the usual mixed finite-difference cancellation for proper-support
functions. With one cut it would give an impossibility, recovering the
existing sibling obstruction. With two cuts there is one even nonempty
corner, giving the complementary rectangle in
[report 839](839-two-cut-private-fibres-force-query-weighted-overlap-rectangles.md).

## 3. Exact reset densities and the arbitrary-payoff bound

For each $J\in\mathcal E$, take the unnormalized measure $\mu|_\Pi$ and
replace precisely the coordinates in $J$ by independent laws
$\mu_i(\,\cdot\mid C_i^c)$. Denote the pushforward by $\nu_J$. Define

$$
\begin{aligned}
\beta_J&=\prod_{i\in J}(1-1/p_i),\\
a_J(v)&=\int\mathbf1_\Pi(u_J,v)\,d\mu_J(u_J),\\
Q_J&=\prod_{i\in J}C_i^c\times\prod_{i\notin J}C_i.
\end{aligned}
$$

For any test function $g$, finite Fubini applied to the definition of
$\nu_J$ gives

$$
\int g\,d\nu_J
=\int g(y)\mathbf1_{Q_J}(y)
\frac{a_J(y_{J^c})}{\beta_J}\,d\mu(y).
$$

In particular

$$
\boxed{
\frac{d\nu_J}{d\mu}(y)
=\mathbf1_{Q_J}(y)\frac{a_J(y_{J^c})}{\beta_J}.
}                                                       \tag{EC6}
$$

Each reset measure has mass $\theta$. The $Q_J$ are pairwise disjoint,
since different $J$ give different inside/outside first-digit patterns.
Therefore the density of the sum of reset measures has the exact cap

$$
\begin{aligned}
D(y)&=\sum_{J\in\mathcal E}
 \mathbf1_{Q_J}(y)\frac{a_J(y_{J^c})}{\beta_J},\\
M&=\|D\|_\infty
 =\max_{J\in\mathcal E}\frac{\|a_J\|_\infty}{\beta_J}>0.
\end{aligned}                                           \tag{EC7}
$$

There is no factor $|\mathcal E|$ in this supremum. Integrate EC5 over
$x$ with the same unnormalized $\mu|_\Pi$, and over all $z_i$ with the
product of the outside-root laws. Put

$$
R_h=\int_\Pi
 \mathbb E_z\min_{J\in\mathcal E}h(y^J)\,d\mu(x).
$$

The integrated left side is exactly $\mu(h\mathbf1_OD)$. Hence

$$
\boxed{
\mu(h\mathbf1_OD)\ge R_h,
\qquad
\mu(h\mathbf1_O)\ge\frac{R_h}{M}.
}                                                       \tag{EC8}
$$

For $h=1$, $R_1=\theta$. Since
$a_J\le\prod_{i\in J}1/p_i$, if $p_{(1)}<p_{(2)}$ are the two
smallest cut primes, EC7 implies

$$
M\le\frac1{(p_{(1)}-1)(p_{(2)}-1)},\qquad
\mu(O)\ge(p_{(1)}-1)(p_{(2)}-1)\theta.                  \tag{EC9}
$$

EC9 is the familiar private-mass baseline. The finer information in
EC6--EC8 is the location of actual overlap, the exact projection-density
cost, and preservation of the entire query payoff.

## 4. One supported private law and three-cut amplification

Choose any one probability law $\pi$ supported on the actual private
set $\Pi$, and put $g_{J^c}=d\pi_{J^c}/d\mu_{J^c}$. Resetting $\pi$
instead of $\mu|_\Pi$ has density
$\mathbf1_{Q_J}(y)g_{J^c}(y_{J^c})/\beta_J$, by the same finite Fubini
calculation as EC6. Disjoint corner supports therefore give the cap
$M_\pi=\max_{J\in\mathcal E}\|g_{J^c}\|_\infty/\beta_J$.
Integrating EC5 with this single law proves

$$
\boxed{
\mu(h\mathbf1_O)\ge
\frac{\displaystyle
 \mathbb E_{x\sim\pi,z}\min_{J\in\mathcal E}h(y^J)}
{\displaystyle
 \max_{J\in\mathcal E}
 \left\|d\pi_{J^c}/d\mu_{J^c}\right\|_\infty/\beta_J}.
}                                                       \tag{EC10}
$$

All corner marginals must come from this one supported law. Independently
favorable projection laws do not supply such a witness. For an empty
complement the density is the scalar 1. The choice
$\pi=\mu(\,\cdot\mid\Pi)$ has
$g_{J^c}=a_J/\theta$, recovering EC8 with cancellation of $\theta$.
Other certified laws on the same private relation may have better
projection bounds; their existence and construction are additional
certificate obligations, not a free property of a covered fibre.

Equivalently, a finite nonnegative witness measure $\lambda$ supported
on $\Pi$ with
$\lambda_{J^c}\le\beta_J\mu_{J^c}$ for every $J\in\mathcal E$
has summed reset density at most 1, and hence directly certifies
$\mu(h\mathbf1_O)\ge\int\mathbb E_z\min_{J\in\mathcal E}h(y^J)
\,d\lambda(x)$. This is a fractional packing certificate on the actual
private relation. Scaling the chosen $\pi$ by $1/M_\pi$ supplies exactly
this homogeneous form.

When $k=3$, the even nonempty sets are $12,13,23$, whose complements
are the three single axes. If the chosen supported private law obeys
$d\pi_i/d\mu_i\le c_i$, then

$$
\boxed{
\mu(h\mathbf1_O)\ge
\frac{\mathbb E_{\pi,z}\min\{h(y^{12}),h(y^{13}),h(y^{23})\}}
{\max\{c_3/\beta_{12},c_2/\beta_{13},c_1/\beta_{23}\}}.
}                                                       \tag{EC11}
$$

In particular

$$
\mu(O)\ge
\min\{\beta_{12}/c_3,\beta_{13}/c_2,\beta_{23}/c_1\}.
                                                               \tag{EC12}
$$

If each marginal is uniform on its target root, then $c_i=p_i$.
For the primes $3,5,7$, EC12 gives $8/105$. Under Haar conditioned
only on avoiding $C$, this becomes $1/13$, because
$O\subseteq C^c$ and $\mu(C)=1/105$.
These constants require the stated supported-law marginal premise; arbitrary
proper-support coverage has not been proved to supply it.

For general $k$, EC10 needs caps on the complementary projections
$J^c$, $J\in\mathcal E$. Their largest dimension is $k-2$.
An unrestricted joint private density can be much larger than all
these lower-dimensional density caps.

### A symbolic family with vanishing private mass and bounded marginals

Fix three distinct odd primes $p_1,p_2,p_3$ and an integer $m\ge2$.
Set

$$
n_i=p_i^{\lceil\log_{p_i}m\rceil},\qquad
X_i=\mathbb Z/(p_i n_i)\mathbb Z,
$$

and let $C_i$ be its zero first-digit root. Then
$m\le n_i<p_i m$, and $|C_i|=n_i$. Choose distinct
$u_i(1),\ldots,u_i(m)$ in each root. Use the target $C$, together with
the following literal proper-support cylinders:

1. Every nonzero first-root strip, on each axis.
2. Each full-coordinate value in $C_i\setminus\{u_i(1),\ldots,u_i(m)\}$,
   on axis $i$ alone.
3. Each pair of full-coordinate values $(u_i(s),u_j(t))$ with $i<j$
   and $s\ne t$, leaving the third axis free.

Outside $C$, a first-root strip covers. Inside $C$, a point with an
unselected coordinate is covered by the second group. If all coordinates
are selected but their indices differ, the third group covers. No
other cylinder meets a common-index point. Consequently this fibre is
covered, with exact private set

$$
\Pi=\{(u_1(t),u_2(t),u_3(t)):1\le t\le m\},\qquad
\theta=\frac{m}{\prod_i(p_i n_i)}\longrightarrow0.
$$

The normalized private law is uniform on these $m$ diagonal points.
Its one-coordinate density cap is

$$
\left\|\frac{d\pi_i}{d\mu_i}\right\|_\infty
=\frac{p_i n_i}{m}\le p_i^2.                            \tag{EC13}
$$

EC12 therefore gives a fixed positive conditional overlap lower bound
independent of $m$, despite $\theta\to0$. This is a nonemptiness witness
for the projection-density premise, not a claim about all covers.

The example can be realized inside an actual distinct-odd original
family. Attach to every other literal cylinder a distinct positive
exponent of one fresh odd prime $\ell$, with tag residue zero; leave
the target modulus $p_1p_2p_3$ untagged. Choose phases by CRT to give the
stated cylinders in the transported residual coordinates. The resulting
original moduli are all distinct. On the zero fibre modulo the largest $\ell$-power
their residuals are exactly those above. Every other original omits at
least one of the three target primes, so the target is divisibility
maximal and this is a canonical cut. Pair cylinders exist for each
omitted axis when $m\ge2$, making the three-axis cut inclusion-minimal.
A CRT point with tag residue one and a nonzero first root on one cut
axis is a global hole. No irredundance claim is made for the suppliers.
The Haar mass of the selected tag fibre is not uniform in $m$ and may
vanish. Thus conditional amplification does not become a uniform global
covering contradiction.

## 5. Exact recovery of two cuts and the three-cut geometry guard

For $k=2$, $\mathcal E=\{T\}$, $a_T=\theta$, and
$M=\theta/\beta_T$. All coordinates are reset, so

$$
R_h=\theta\mathbb E_{z\in C_1^c\times C_2^c}h(z).
$$

EC8 becomes exactly

$$
\mu(h\mathbf1_O)\ge
\mu(h\mathbf1_{C_1^c\times C_2^c}),                     \tag{EC14}
$$

the arbitrary-payoff rectangle consumer of report 839. No private-mass
factor remains.

For three cuts, the analogous all-outside inclusion is false. Consider
the target root box $C$ and proper-support sets

$$
\begin{aligned}
B_1&=C_1^c\times X_2\times X_3,\\
B_2&=C_1\times C_2^c\times X_3,\\
B_3&=X_1\times C_2\times C_3^c,\\
B_4&=C_1\times X_2\times C_3^c.
\end{aligned}
$$

These sets and $C$ cover the fibre; $C$ is private. The all-outside
corner belongs only to $B_1$. Overlap occurs instead on mixed corners,
including patterns $13$ and $23$. Expanding complements into their
literal nonzero first-digit cylinders keeps every support proper.
The pair supports of $B_2,B_3,B_4$ require all three cut axes in a
hitting cut. Distinct original odd labels can be supplied by the same
fresh-prime tagging construction above. Thus even an inclusion-minimal
three-cut interface does not force overlap at the all-outside corner.
EC4 locates overlap at at least one even corner and makes no stronger
pointwise location assertion.

## 6. Actual owners, desired buckets, and non-Haar sources

Fix one ordering of the actual original labels. Partition $O$ by the
first two labels covering the point, writing the cells as $P_{ij}$.
Then, with no double counting,

$$
\mu(h\mathbf1_OD)=\sum_{i<j}\mu(h\mathbf1_{P_{ij}}D).
$$

For a desired original subfamily $\mathcal J$, let
$W_{\mathcal J}=\bigcup_{i\in\mathcal J}A_i$. Pairs containing at least
one label in $\mathcal J$ lie inside this actual union. If a certified
$B_{\rm bad}$ satisfies

$$
B_{\rm bad}\ge
\sum_{\substack{i<j\\i,j\notin\mathcal J}}
 \mu(h\mathbf1_{P_{ij}}D),
$$

then EC8 gives

$$
\boxed{
\mu(h\mathbf1_{W_{\mathcal J}})
\ge\frac{[R_h-B_{\rm bad}]_+}{M}.
}                                                       \tag{EC15}
$$

The same partition proof applies to the reset density, cap, and corner
floor obtained from any chosen supported $\pi$ in EC10.

The ordering can place desired labels first. The partner test still
uses original labels and actual overlap points. Residual axis support
does not determine an original ending-prime bucket; for example all
tagged suppliers in the construction can have the fresh prime as their
largest prime. EC15 requires its own original-bucket accounting.

Every finite nonnegative source measure on this fibre has a density
$\xi=f\mu$. Apply EC8 or EC15 to the entire payoff
$h=f h_{\rm query}$. This yields an actual $\xi$-weighted bound, with
the same source density evaluated at the actual reset corners inside
the minimum. Neither $f$ nor the query is assumed to factor, be shallow,
or remain constant under reset.

If $\xi$ is Haar conditioned only outside the target, every reset corner
lies in its support. The target may have zero $\xi$-mass while the corner
lower bound remains positive. Further deletions can make the corner
minimum zero, and no positive constant survives without checking it.

Finally, integration over coarse fibres must retain their actual source
masses and conditional densities. Existence of one private fibre does
not provide a uniform positive source mass, the projection-density caps,
or a positive weighted corner floor. Those are the remaining premises
for a quantitative Erdős #7 consumer; the report proves their exact
conditional transport, not their universal availability.

## 7. Three necessary cuts can have arbitrarily little outside-target overlap

The two-cut conclusion EC14 has no height-independent three-cut analogue,
even for a covered canonical fibre in a globally irredundant family of
distinct odd originals. The following construction also shows that the
supported-law premise of EC10 is additional information: its optimal
projection packing tends to zero, and the actual overlap it would pay
for tends to zero as well.

Fix three distinct odd primes $p,q,r$ and heights $A,B\ge1$. On the
selected fibre use

$$
X=\mathbb Z/p^A\mathbb Z\times\mathbb Z/q^B\mathbb Z
  \times\mathbb Z/r\mathbb Z,
\qquad
C=\{p\mid x,\ q\mid y,\ z=0\}.
$$

Besides the target, use the four unions of proper-support cylinders

$$
\begin{aligned}
B_1&=\{x\ne0\},&
B_2&=\{x=0,\ y\ne0\},\\
B_3&=\{y=0,\ z\ne0\},&
B_4&=\{x=0,\ z\ne0\}.
\end{aligned}
\tag{EC16}
$$

Here $x=0$ means the full residue modulo $p^A$, and similarly for
$y$. Expand every nonzero condition into its disjoint first-nonzero
digit cylinders. The resulting literal core conditions are

| Group | Literal core conditions | Number |
| --- | --- | ---: |
| $B_1$ | $x=c p^{j-1}\bmod p^j$, $1\le j\le A$, $1\le c<p$ | $(p-1)A$ |
| $B_2$ | $x=0\bmod p^A$, $y=c q^{j-1}\bmod q^j$, $1\le j\le B$, $1\le c<q$ | $(q-1)B$ |
| $B_3$ | $y=0\bmod q^B$, $z=c\bmod r$, $1\le c<r$ | $r-1$ |
| $B_4$ | $x=0\bmod p^A$, $z=c\bmod r$, $1\le c<r$ | $r-1$ |

### 7.1 Literal odd originals and their actual private points

Choose one further odd prime $\ell$, different from $p,q,r$. Order
the literal suppliers group by group as $B_2,B_4,B_3,B_1$, with any
fixed order inside each group. Give supplier $i$ the additional
condition $0\bmod\ell^i$, for $1\le i\le K$, where

$$
K=(p-1)A+(q-1)B+2(r-1).
$$

The original target is $0\bmod pqr$ without a tag. CRT fixes one
residue for each original modulus, once and for all. Every modulus is
odd and greater than one, and different $\ell$-exponents make the
supplier moduli numerically distinct. No supplier contains all three
target primes, so the target is divisibility-maximal. All four primes
can stay fixed as the heights grow.

The full period and canonical three-cut boundary are

$$
N=p^Aq^Br\ell^K,\qquad b=\ell^K.
\tag{EC17}
$$

On the actual $0\bmod b$ fibre the suppliers are exactly the cylinders
in the table. They and $C$ cover it: use $B_1$ if $x\ne0$, $B_2$ if
$x=0,y\ne0$, $B_3$ if $x=y=0,z\ne0$, and $C$ at the origin.
The target's private set on this fibre is exactly

$$
\Pi=\{(0,0,0)\},\qquad \theta=p^{-A}q^{-B}r^{-1}.
\tag{EC18}
$$

The three pair-support groups omit precisely $r,p,q$, respectively.
Their missing-prime sets are singletons. Any hitting set for the
target therefore contains all three primes; this is an
inclusion-minimal three-cut interface, with no two-cut alternative for
this target and original inventory.

The entire original family is irredundant, although some suppliers are
redundant on the selected fibre alone. For supplier $i<K$, take tag
coordinate $\ell^i\bmod\ell^K$, so exactly the suppliers with index
at most $i$ are active. At $i=K$, take tag zero. Use the following
actual core point, with $s$ the supplier's own nonzero shell value
or nonzero $r$-residue:

| Supplier group | Private core point |
| --- | --- |
| $B_2$ | $(0,s,1)$ |
| $B_4$ | $(0,0,s)$ |
| $B_3$ | $(1,0,s)$ |
| $B_1$ | $(s,1,0)$ |

Every point misses $C$. Earlier suppliers in its own group have
disjoint shell conditions. At a $B_4$ point, earlier $B_2$ suppliers
miss $y=0$; at a $B_3$ point, the earlier $B_2,B_4$ groups miss
$x=1$; at a $B_1$ point, $B_2,B_4$ miss $x\ne0$ and $B_3$ misses
$y=1$. Later suppliers are inactive at its tag. CRT therefore gives
one globally private point for each original supplier. The full origin
is private to the target. Finally, tag one and any core point outside
$C$ give a global hole. These are irredundant noncovers with a covered
canonical fibre, not odd whole covers.

### 7.2 Exact outside-target overlap and the projection cost

The literal cylinders within each group are disjoint. Therefore on
the selected fibre the multiplicity of other originals is

$$
L_-=\mathbf1_{x\ne0}
 +\mathbf1_{x=0,y\ne0}
 +\mathbf1_{y=0,z\ne0}
 +\mathbf1_{x=0,z\ne0}.
$$

If $z=0$, every nonorigin point has $L_-=1$. If $z\ne0$, this load
is two exactly when $x=0$ or $y=0$, and is one otherwise. Since
$z\ne0$ already lies outside $C$, the actual event EC3 is exactly

$$
\begin{aligned}
O&=\{z\ne0\}\cap\bigl(\{x=0\}\cup\{y=0\}\bigr),\\
\mu(O)&=(1-r^{-1})
 \bigl(p^{-A}+q^{-B}-p^{-A}q^{-B}\bigr)
 \longrightarrow0\quad(A,B\longrightarrow\infty).
\end{aligned}
\tag{EC19}
$$

The cut primes stay fixed. Conditioning Haar only outside the target
divides this mass by the fixed number $1-1/(pqr)$, so it does not
restore a uniform positive bound. Nor does existence of a private point
or global irredundance supply that bound.

The only probability law supported on $\Pi$ is its point mass. Its
single-coordinate densities relative to Haar are $p^A,q^B,r$.
Equivalently, every nonnegative witness measure in the homogeneous
packing formulation after EC10 has the form $s\delta_{(0,0,0)}$.
The three projection constraints are exactly

$$
s\le\frac{\beta_{12}}r,\qquad
s\le\frac{\beta_{13}}{q^B},\qquad
s\le\frac{\beta_{23}}{p^A}.
$$

Consequently its optimum is attained and equals

$$
s_*=
\min\left\{\frac{\beta_{12}}r,
             \frac{\beta_{13}}{q^B},
             \frac{\beta_{23}}{p^A}\right\}
\longrightarrow0.
\tag{EC20}
$$

This is the direct evaluation of the existing packing interface, not
a new linear-programming duality theorem. The small-capacity witness
uses full-depth singleton projections; it does not change which cut
primes are necessary. Thus failure of a uniform projection packing
cannot, under these local and irredundance premises, be repaired by
asserting that the target must instead admit a smaller cut.

The distinction between outside-target overlap and all overlap is
essential. Every point of $C\setminus\Pi$ has one supplier as well as
the target. The actual excess on the selected fibre is therefore

$$
\mu((L-1)_+)=\mu(O)+\frac1{pqr}-\frac1{p^Aq^Br}.
\tag{EC21}
$$

It does not tend to zero. These identities refute a uniform
outside-target amplification from the stated three-cut premises;
they do not refute a whole-cover forcing theorem using oddness,
a different original-bucket allocation, or the full excess account.
No numerical experiment or Lean verification is claimed for this
symbolic construction.

### 7.3 The obstruction survives an actual pure-prime prefilter

One can also include original prime classes and retain their actual
avoidance law. Add the four originals $1\bmod p$, $1\bmod q$,
$1\bmod r$, $1\bmod\ell$. Delete precisely the suppliers contained
in one of these classes: the $j=1,c=1$ cylinder in each of $B_1,B_2$,
and the $z=1$ cylinders in $B_3,B_4$. Give the remaining suppliers
successive tag heights in the same group order. All four groups remain
nonempty, since every prime is odd. Use the resulting maximum tag
height $K'$ and actual $0\bmod\ell^{K'}$ fibre.

The deleted cylinders are covered by the added pure classes, so this
fibre is still covered and its target-private set is still the origin.
The pair-support groups still force the same three-cut interface.
For each remaining supplier the private-point table remains valid
after replacing its free coordinate value $1$ by $2$. Its prescribed
shell avoids the relevant prime class by the stated deletion rule,
and all other coordinates also avoid the four pure classes. The tag
valuation still excludes later suppliers. Each core prime original
has a private point with its own core coordinate one, the other core
coordinates zero, and tag two. The prime-$\ell$ original has a private
point with tag one and core $(2,0,0)$. Thus global irredundance and
numerical distinctness are retained. Tag two with core $(2,0,0)$ is a
global hole.

On the selected fibre, condition Haar on avoiding the actual prime
originals. Its support is

$$
U=\{x\not\equiv1\pmod p,\quad
      y\not\equiv1\pmod q,\quad z\ne1\},
\qquad \mu_U=\mu(\,\cdot\mid U).
$$

The tag-prime original is already absent on this fibre. At every point
of $U$ all added pure originals and all deleted cylinders are absent,
so the other-original load is exactly the same formula as before.
Writing

$$
a_A=\frac1{(p-1)p^{A-1}},\qquad
b_B=\frac1{(q-1)q^{B-1}},
$$

direct counting under this one actual conditioned law gives

$$
\mu_U(O)=\frac{r-2}{r-1}
          (a_A+b_B-a_Ab_B)\longrightarrow0.
\tag{EC22}
$$

This is a calculation under the modified family's original prime
prefilter, not a substitution of its density into a Haar identity.
The family is still a noncover and is not asserted to be divisor-closed
or globally minimum in class count. Those stronger whole-cover
restrictions remain available for a future positive forcing argument.
