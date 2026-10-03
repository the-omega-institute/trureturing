[Index](../../../marked_head_profile.md) · [Source-global collision moment](../350-399/388-source-global-substitution-collision-moment.md) · [Private liability](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md)

# The source-global collision moment needs a cofactor-packing theorem

The common-source substitution of report 388 gives, for every safe
coordinate and every common rooted-tree embedding, at least one pair of
original labels with the same **numerical** output modulus.  Averaging gives

\[
\Psi_{r,s}=\mathbb E X\geq 1.
\]

This is a genuine whole-source statement, but it is not yet an
Erdős--Selfridge contradiction.  A positive summand does not mean that the
pulled-back phases agree, so it does not supply an EB1 replacement.  The
missing estimate is a bound on the sum over all remaining cofactor groups,
or a phase-compatible repair of their complete liability.

Here “survives together” means that both individual pullback classes are
nonempty under the same source map; it does not require one source point to
satisfy both original congruences.  The remaining cofactor phase changes the
output phase, while the numerical-modulus collision is still present.

## 1. A positive term is not a phase collision

For a pair

\[
d=r^a s^b m,\qquad d'=r^{a'}s^b m,\qquad a<a',
\]

comparable-class disjointness forces their original phases to disagree at a
common divisor.  A common source map can nevertheless retain both labels and
produce the same numerical modulus \(r^b m\).  If their pulled-back phases
were equal, injectivity of the tree map would give equality of the original
\(s^b\)-prefixes, while the common safe coordinate gives equality of the
\(r^a\)-prefixes.  Equality of the \(m\)-components would then imply
\(\alpha\equiv\alpha'\pmod d\), contradicting disjointness.

Thus the moment records repeated numerical labels with different phases.  It
does not permit deleting the pair and inserting one class: a valid repair
must preserve the original phases on retained labels, use an unused odd
nonunit modulus, and cover the complete finite-period liability of every
deleted class.

## 2. The bound that is available for one cofactor group

Fix \((b,m)\), and let \(U_r\) be the safe \(r\)-coordinate set.  Put

\[
\eta_r=\frac{|U_r|}{r^A}.
\]

Divisor closure and disjoint pure \(r\)-power classes give

\[
\eta_r>1-\sum_{j\geq1}r^{-j}=\frac{r-2}{r-1}.
\]

For a pair whose larger \(r\)-exponent is \(k\), the safe-coordinate
factor is at most \(r^{-k}/\eta_r\), and there are at most \(k\) such pairs
in this fixed \((b,m)\)-group.  Hence

\[
\sum_{\text{pairs in }(b,m)}\rho
\leq \frac1{\eta_r}\sum_{k\geq1}kr^{-k}
 =\frac{r}{(r-1)^2\eta_r}
 <\frac{r}{(r-1)(r-2)}.
\]

The common-tree factor is at most \((r/s)^b\).  Therefore the group
contribution satisfies

\[
\boxed{
\Psi_{r,s}^{(b,m)}
 <\frac{r}{(r-1)(r-2)}\left(\frac rs\right)^b.
}
\]

For \((r,s,b)=(3,5,1)\), this is the conservative bound
\(\Psi_{3,5}^{(1,m)}<9/10\).  It is not a bound for the sum over distinct
cofactors \(m\).  Nothing in divisor closure, comparable disjointness, or
the top-layer condition currently supplies the required packing inequality

\[
\sum_{(b,m)}\left(\frac rs\right)^b
<\frac{(r-1)(r-2)}r.
\]

## 3. A divisor-closed local family defeats the attempted global estimate

The obstruction survives the local conditions that are most useful in an EB1
argument.  Take \(r=3,s=5,b=1\), retain the pure labels
\(3,5,15\), and let \(U_3=\{1,2\}\) by assigning phase \(0\pmod3\) to
the pure 3-class.  For each of the two safe colours and each edge of the
complete graph on the four nonzero 5-children, use a fresh odd prime
cofactor \(m>5\) and include the divisor-closed packet

\[
 m,\quad 3m,\quad 5m,\quad 15m.
\]

The phases are fixed by CRT. For a chosen safe colour \(c\in\{1,2\}\)
and oriented nonzero edge \((x,y)\), the \(m\)-class has phase zero, and
every proper \(m\)-multiple has phase one modulo \(m\). The remaining
coordinates are
\[
 3m:\ 3-c\pmod3,\qquad
 5m:\ x\pmod5,\qquad
 15m:\ c\pmod3,\ y\pmod5.
\]
Only prime coordinates dividing the numerical modulus are imposed. In
particular, \(3m\) and \(15m\) differ modulo three, while \(5m\) and
\(15m\) differ modulo five.
The edge orientation is chosen so that the colour-one \(15m\)-phase is not
the pure \(15\)-phase.  The resulting 51 numerical moduli are pairwise
distinct, odd, and divisor-closed; every comparable pair is phase-disjoint.

There are \(2\cdot\binom42=12\) designated \((5m,15m)\) pairs.  A common
three-child embedding contains an edge of the nonzero four-vertex graph in
every selected 3-subset of the five children.  Therefore every one of the 20
common source maps (two safe coordinates times ten embeddings) retains at
least one designated pair.  Each pair has

\[
\rho=\frac12,\qquad
\kappa=\frac{3\cdot2}{5\cdot4}=\frac3{10},
\qquad
\rho\kappa=\frac3{20},
\]

so their designated subfamily has collision moment

\[
\Psi_{\mathrm{designated}}=12\cdot\frac3{20}=\frac95>1.
\]

The complete collision count also includes twelve \((m,3m)\) pairs,
each surviving with probability \(1/2\), and the pure \((5,15)\) pair,
surviving with probability \(3/20\). These exhaust the repeated numerical
output columns. Hence the full moment of report 388 is
\[
 \Psi_{3,5}=\frac95+12\cdot\frac12+\frac3{20}=\frac{159}{20}>1.
\]

This family is a local incidence model: the integer two avoids every
listed class, so it is not a whole cover. It carries no claim about the existence of an unrestricted
counterexample.  Its role is sharper than a bare pair example: even
distinctness, divisor closure, comparable disjointness, a common source, and
the pointwise collision condition do not yield a global \(\Psi<1\) estimate.

## 4. Exact status of the route

The collision moment remains a useful necessary condition because it keeps one
safe coordinate, one common source, the original phases, and the whole source
image.  It does not close the problem.  A successful continuation must supply
one of the following genuinely new bridges:

1. a whole-cover cofactor-group packing theorem strong enough to force
   \(\Psi_{r,s}<1\) for some support-prime pair; or
2. a phase-compatible, unused-label replacement chain covering the complete
   finite-period liability of every deleted collision and strictly decreasing
   the EB1 objective.

Neither the first-moment collision, its one-group bound, nor the local family
provides either bridge.  The unrestricted odd distinct-modulus problem remains
open at this boundary.

For a conditional second-moment route,
[report 848](../800-849/848-common-old-coordinate-refines-collision-moments.md)
filters same-column pairs by their actual old cofactor phase and obtains the
smaller coefficient \(r/((r-2)(s-1))\). Its common-old-coordinate
replica weight contains \(1/m\), not \(1/m^2\). That bound controls one
part of a conditional labelled-load moment, not the full \(\Psi_{r,s}\)
or the cross-column budget.

## 5. Exact finite check

The [accompanying checker](../../../frontier/cover-geometry/source-global-collision-moment/collision_moment_no_cap.py)
and its [result](../../../frontier/cover-geometry/source-global-collision-moment/collision_moment_no_cap.json) verify, with exact integer and rational arithmetic,
the 51-label divisor-closed construction, distinctness, all 122 comparable
pairs using actual CRT residues and numerical gcds, and all 20 common source
maps. Its 76,500 literal source-to-output membership comparisons retain
the same safe coordinate and child subset for all labels. The designated
moment is \(9/5\), and the full collision moment is \(159/20\).
The results retain all 51 numerical moduli and CRT phases, together with
the uncovered witness two. Negative controls reject a coordinate absent
from its modulus and a genuinely contained comparable class. These checks
remain active under Python optimization. The program checks only the finite
obstruction and makes no whole-cover claim.
