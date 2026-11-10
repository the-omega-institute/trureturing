---
bibkey: miyaderaimai2007landaupollak
authors: T. Miyadera and H. Imai
year: 2007
title: Generalized Landau-Pollak Uncertainty Relation
doi: 10.48550/arXiv.0707.4450
url: https://arxiv.org/abs/0707.4450v3
claim: The weak Landau-Pollak inequality bounds the sum of two projection probabilities by one plus the operator norm of their product.
strata_touched: []
license: citation-only
triage: anchor
---

# Two pure states, comparison bounds and Jordan geometry

[Miyadera–Imai, arXiv:0707.4450v3](https://arxiv.org/pdf/0707.4450v3),
Section 2, equation (1), states the weak Landau–Pollak bound for rank-one
quantum projections. Theorem 2 gives, for arbitrary orthogonal projections
$P,Q$ on a Hilbert space and any density operator $\rho$,

$$
\operatorname{tr}(\rho P)+\operatorname{tr}(\rho Q)
\le 1+\|PQ\|.
$$

For rank-one $P,Q$, $\|PQ\|=\sqrt{\operatorname{tr}(PQ)}$.
The source already assumes Hilbert-space quantum mechanics. Its theorem
therefore cannot establish the same bound in a general ordered model.
The argument below relates this numerical bound to two-state face
geometry in the project's comparison reconstruction. It is a
paper derivation and an application of attributed classification results;
no claim of literature priority or Lean verification is made.

## Carrier, comparison and two-state faces

Use the nonzero finite-dimensional ordered carrier, full proper-effect
interval and Principle S from the
[least-confirmation note](niestegge2023transition.md#carrier-and-the-retained-condition).
For a pure state $p$ and a normalized state $x$, define

$$
T_p(x)=\inf\{f(x):0\le f\le u,\ f(p)=1\}.
$$

S requires that $T_p$ preserve probability mixtures and that
$T_p(q)=T_q(p)$ for pure $p,q$. Mixture preservation is equivalent to
one least proper confirming effect. The first endpoint in this infimum
remains pure. These are conditions on comparisons and preparation
relations, not an assertion that successive measurements commute.

The cited note's paper derivation gives the positive definite pairing
$B$, a vector $U$ with $u=B(U,\cdot)$, signed spectral decompositions in
complete orthonormal pure frames, and projectivity with canonical
orthogonal face projections. Write

$$
\tau(p,q)=T_p(q)=B(p,q),\qquad B(p,p)=1.
$$

A complete frame $(a_i)$ satisfies $\sum_i a_i=U$. Each cone face $F$
has unit $s_F=P_FU$ and capacity
$\operatorname{cap}(F)=u(s_F)=B(s_F,s_F)$, equal to its frame length.
The face lattice is atomic and orthomodular. These supplied bridges
remain paper results, including when used below.

Let $p\vee q$ denote the smallest cone face containing the two pure
rays. The geometric property of interest is

$$
\operatorname{cap}(p\vee q)\le2\qquad(p,q\text{ pure}).
\tag{J2}
$$

It says that the smallest face containing two pure possibilities cannot
contain any three pure states perfectly distinguished by one common
measurement. The triple need not include either original state. This concerns that
entire face; testing only the straight line segment between $p$ and $q$
would be a different, weaker statement. The
[maximum-impurity argument](niestegge2023transition.md#least-confirmation-forces-face-filter-purity)
derives purity of all face projections from S on the stated carrier.
The following construction consequently derives J2 without a separate
two-state or covering assumption. These are paper arguments, not a
formalization of the full chain.

## A capacity-two face from two pure states

For distinct pure $p,q$, put $t=B(p,q)<1$ and
$D=C\cap p^{\perp_B}$. Properness of $e_p$ gives $U-p\in D$;
since $p\perp\operatorname{span}D$, $P_DU=U-p$. Therefore
$u(P_Dq)=1-t>0$. Face-filter purity makes

$$
r=\frac{P_Dq}{1-t}
$$

a pure state in $D$. Orthogonal projection gives $B(q,r)=1-t$.
The vector

$$
w=U-p-r=P_D(U-r)\in C
$$

is orthogonal to $p,q,r$. Positivity follows from $U-r\in C$ and
positivity of $P_D$. The exposed face $H=C\cap w^{\perp_B}$ contains
$p,q,r$, and its unit is $s_H=P_HU=p+r$. Hence its capacity is two,
and $p\vee q\subseteq H$ proves J2. A face of capacity one is a pure
ray, so two distinct pure states in fact generate capacity exactly two.
When $p=q$, the capacity is one. The case $w=0$ is allowed.

If the whole system has capacity three, $u(w)=1$ and
$\|w\|^2=B(w,U-p-r)=u(w)=1$, so $w$ is pure. It is the unique pure
state having zero comparison with both $p$ and $q$. Indeed any such
$h$ lies in $D$ and satisfies
$B(h,r)=B(h,P_Dq)/(1-t)=0$, whence $B(h,w)=1$; unit norms force
$h=w$. Thus $T_w=0$ is a supporting hyperplane containing the entire
line segment $[p,q]$. Distinctness of $p,q$ is essential to uniqueness.

## A three-comparison expression of exactly the same condition

In this geometry, J2 is equivalent to

$$
\tau(p,r)+\tau(q,r)\le1+\sqrt{\tau(p,q)}
\qquad(p,q,r\text{ pure}).
\tag{WLP}
$$

To prove the equivalence, fix $p,q$, put $t=\tau(p,q)$ and take a
positive spectral expansion $p+q=\sum_i\lambda_i a_i$ in a complete
frame. Then

$$
\sum_i\lambda_i=2,\qquad
\sum_i\lambda_i^2=2+2t,
\qquad\lambda_i\ge0.
\tag{1}
$$

Let $M=\max_i\lambda_i$ and label a maximal term by $i=1$.
For any pure $r$, the numbers $B(a_i,r)$ are nonnegative and sum to one.
Their weighted average is $B(p+q,r)$, with value $M$ attained at
$r=a_1$. In particular

$$
M=\max_{r\text{ pure}}[\tau(p,r)+\tau(q,r)]\ge1+t\ge1.
\tag{2}
$$

Equations (1) give

$$
2+2t=M^2+\sum_{i\ge2}\lambda_i^2
\le M^2+(2-M)^2.
$$

Thus S already gives the reverse bound $M\ge1+\sqrt t$. If WLP also
holds, equality forces at most one nonzero coefficient after $\lambda_1$.
The support of $p+q$ is precisely $p\vee q$, so its capacity is at most
two. Conversely J2 permits at most two nonzero spectral terms in (1).
Their values are $1\pm\sqrt t$, giving WLP by (2). This includes $p=q$.

The exact defect can be written without any new primitive objects:

$$
\delta(p,q)=M-1-\sqrt t\ge0,\qquad
\sum_{2\le i<j}\lambda_i\lambda_j
=\delta(p,q)(2\sqrt t+\delta(p,q)).
\tag{3}
$$

Consequently $p\vee q$ has capacity greater than two precisely when
$\delta(p,q)>0$. A maximal spectral state $a_1$ then gives an explicit
third pure state violating WLP in the supplied spectral geometry.
The moment identities alone supply the lower bound; face-filter purity
and the two-state construction supply the upper bound, so in S the
defect is zero. WLP is an equivalent expression of J2 within this
geometry, not an additional independent assumption in the paper route.

## From the two-state condition to purity-preserving filters

The relevant established interface is
[Barnum–Müller–Ududec, arXiv:1403.4147v4](https://arxiv.org/html/1403.4147v4),
Theorem 16: finite-dimensional projectivity, symmetric transition
probabilities and purity-preserving filters characterize formally real
Jordan state spaces. Theorem 17 has additional symmetry assumptions
and is not used here. The equivalence of filter purity and the covering
law in the projective setting is also discussed at the end of its
Section V, with references to Guz's filter theory.

For completeness, the required lattice bridge can be proved in the
present geometry. The covering law says that $F\vee a$ has no strict
intermediate face above $F$ whenever $a$ is an atom outside $F$.
Suppose J2 holds and write $F=d_1\vee\cdots\vee d_k$ using an
orthogonal face frame. Starting with $a_0=a$, successively make the atom
orthogonal to each $d_i$. If it already is, keep it. Otherwise replace it
inside $H_i=d_i\vee a_{i-1}$ by
$a_i=H_i\wedge d_i^\perp$. J2 makes this relative complement an atom.
The case $a_{i-1}=d_i$ is excluded by the invariant
$F\vee a_{i-1}=F\vee a\ne F$.

At every step $d_i\vee a_i=d_i\vee a_{i-1}$. Earlier orthogonality
persists because both generators of $H_i$ lie in each earlier
$d_j^\perp$. The final atom $b$ is orthogonal to $F$ and
$F\vee b=F\vee a$. Orthomodularity gives an interval isomorphism
$[F,F\vee b]\simeq[0,b]$ by intersecting with $F^\perp$; its inverse
is joining with $F$. The latter interval has two elements, proving
covering. Conversely covering makes the join of two distinct atoms
have capacity two, giving J2.

For an arbitrary face $F$ and pure $p$, the support face of its positive
projection obeys the Sasaki formula

$$
\operatorname{face}(P_Fp)=F\wedge(F^\perp\vee p).
\tag{4}
$$

Indeed $B(y,P_Fp)=B(y,p)$ for $y\in F$. The relative orthogonal
complement of the support is therefore $F\wedge p^\perp$; taking its
relative orthogonal complement and using De Morgan's law gives (4).
The support of zero is the zero face. Covering and the interval
isomorphism above make (4) either zero or an atom. Thus all face
projections preserve pure rays. Conversely that preservation makes
$F^\perp\wedge(F\vee p)$ an atom for $p\not\le F$, and
orthomodularity gives $F\vee p=F\vee[F^\perp\wedge(F\vee p)]$.
The same interval argument proves covering.

Proposition 3.1 of
[arXiv:1508.03107v2](https://arxiv.org/pdf/1508.03107v2)
identifies filters uniquely with faces. Hence purity of these canonical
projections supplies exactly the filter hypothesis of Theorem 16.
Within the supplied S geometry this proves the paper-level chain

$$
\mathrm{WLP}\iff\mathrm{J2}\iff\text{covering law}
\iff\text{all filters preserve pure rays}
\iff\text{finite-dimensional Jordan state geometry}.
\tag{5}
$$

The last reverse implication uses the usual positive spectral and
purity-preserving compression properties of Euclidean Jordan algebras.
It includes finite direct sums and classical simplices.

## The two-state picture is a ball

S already makes the normalized base of any capacity-two face a Euclidean
ball. To see this, let $s=s_F$, so $B(s,s)=2$. Every pure $a\in F$
has a complementary pure state $s-a$, giving
$\|a-s/2\|_B^2=1/2$. Each nonzero direction
$v\in\operatorname{span}F\cap s^\perp$ has a signed two-term
face expansion $v=\lambda a-\lambda(s-a)$. Thus every direction reaches
that pure-state sphere. Taking its convex hull gives

$$
K\cap F=\frac{s}{2}+
\left\{v\in\operatorname{span}F\cap s^\perp:
\|v\|_B\le\frac1{\sqrt2}\right\}.
\tag{6}
$$

The one-dimensional ball is a line segment. J2 makes the smallest face
of every two distinct pure states such a ball. This does not force the
whole state space to be a ball or choose a three-dimensional Bloch ball.
If the whole system has capacity three, J2 is equivalent to saying
that every pure-state midpoint $(p+q)/2$ lies on the relative boundary
of $K$: its support is $p\vee q$, and a proper face has smaller
capacity. The construction of $w$ above excludes an interior midpoint
and supplies its unique pure zero-comparison witness when $p\ne q$.
This uses the global face-filter argument, not local ball geometry alone.

## Complete conditional candidate and its scope

On the stated finite-dimensional full-effect carrier, the complete
candidate is S: the carrier-defined comparison preserves mixtures and
exchanging its pure endpoints preserves its value. The
[preparation-comparison equation](niestegge2023transition.md#one-preparation-comparison-equation)
combines these two requirements. The preceding paper bridges and
Theorem 16 give precisely general finite-dimensional Euclidean Jordan
state spaces; their usual trace pairing satisfies S conversely. Filter
purity, J2 and WLP are consequences on this route. The full bridge and
maximum argument remain unformalized in Lean; the positive-dual theorem
alone does not certify this classification.

For the converse, in an EJA's trace representation a primitive idempotent
$p$ represents a pure state. If $0\le a\le U$ and $B(a,p)=1$, then
$U-a$ belongs to the complementary face $p^\perp$. Its positive face
projection fixes $U-a$ and maps $U$ to $U-p$. Applying that projection
to $U-a\le U$ gives $U-a\le U-p$, or $a\ge p$. Thus $p$ is the least
proper confirming effect, and its trace pairing is affine and reciprocal.

This permits classical simplices, real, complex and quaternionic matrix
systems, spin factors, the Albert algebra, and finite direct sums. It
does not supply the composite, tomography and process conditions needed
to select complex quantum mechanics and its allowed instruments.
Existence of mathematical filters does not assert physical availability
of every filter. No clock or Hamiltonian is selected.

In ordinary words: use the least possible false-acceptance probability
as the comparison reading. Comparing after a random pure preparation
gives the same result as reversing each comparison first and then
averaging. In the stated model the paper argument makes a face filter
preserve pure inputs, and makes every two pure states generate a local
ball-shaped face. Those local parts fit into Jordan geometry. This is
an explicit mathematical candidate with the displayed carrier and
effect assumptions, not a claim that all physical measurement orders
commute or that complex quantum dynamics has been reconstructed.
