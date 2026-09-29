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
