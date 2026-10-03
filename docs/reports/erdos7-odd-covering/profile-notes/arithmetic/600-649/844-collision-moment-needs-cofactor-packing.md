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

## 6. Whole output classes admit an exact divisor-matching test

Collision-free output is sufficient for report 388's descent, but it is
stronger than necessary. Fix an odd period \(N>1\) and a finite labelled
family
\[
 C_i=c_i\pmod{n_i},\qquad 1<n_i\mid N,\qquad i\in I.
 \tag{DM1}
\]
Different original identities remain different demands, even when their
numerical moduli coincide. Put \(\mathcal P_N=\{h>1:h\mid N\}\).
A subset \(J\subseteq\mathcal P_N\) is downward closed if it contains
every nonunit divisor of each of its elements. Define
\[
 L_J=\#\{i\in I:n_i\in J\},\qquad
 \Delta=\max_{J\text{ downward closed}}(L_J-|J|).
 \tag{DM2}
\]
The empty set is allowed, so \(\Delta\ge0\). The maximum number of
labels admitting distinct assignments \(i\mapsto h_i\in\mathcal P_N\)
with \(h_i\mid n_i\) is exactly
\[
 \boxed{|I|-\Delta.} \tag{DM3}
\]
This applies Hall's marriage theorem to divisor neighborhoods; it is not
a new matching theorem. The pinned Mathlib provides
`Finset.all_card_le_biUnion_card_iff_existsInjective'` in
`Mathlib/Combinatorics/Hall/Finite.lean`.
[Report 385, section 69](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#69-cross-cofactor-divisor-payment-reduces-exactly-to-nonconcentrated-ancestors)
already uses Hall deficiency for original payer labels. Those payers do
not automatically cover transported demands; this application instead
replaces the complete output classes in (DM1).

Give label \(i\) the neighborhood \(\{h>1:h\mid n_i\}\). For a
label subset \(S\), its union \(J_S\) is downward closed and
\(|S|-|J_S|\le L_{J_S}-|J_S|\le\Delta\). Conversely, all neighbors
of \(S_J=\{i:n_i\in J\}\) lie in \(J\), so every matching leaves
at least \(L_J-|J|\) labels unmatched. Adding \(\Delta\) universally
adjacent dummy slots makes Hall's condition hold for every nonempty label
subset. A saturating matching followed by deletion of dummy assignments
proves (DM3).

For every assigned label use
\[
 B_i=c_i\pmod{h_i}. \tag{DM4}
\]
Its phase is forced by the original output and \(C_i\subseteq B_i\).
Containment \((c\bmod n)\subseteq(b\bmod h)\) holds exactly when
\(h\mid n\) and \(b\equiv c\pmod h\): test \(c\) and \(c+n\)
for necessity. Thus \(\Delta=0\) exactly characterizes repairs that
assign a different containing nonunit coset to every label. It does not
characterize arbitrary covers of their union or grouping several
compatible labels into one coset.

Apply this to **all** nonempty pullbacks of one actual common source
\((u,\theta)\) in report 388. Under the hypothetical EB1 whole-cover
assumption they cover the complete output period and have fewer identities
than the original cover. Therefore
\[
 \boxed{\Delta(u,\theta)\ge1
 \quad\text{for every safe }u\text{ and common }\theta.} \tag{DM5}
\]
Otherwise (DM4) supplies a distinct odd nonunit whole cover with fewer
classes. This replaces the entire output family; it does not append new
classes to an unchanged inventory whose slots could already be occupied.

The criterion is strictly broader than numerical collision-freeness. For
distinct odd primes \(r,q\), output moduli \(q,rq,rq\) can be assigned
slots \(q,r,rq\), inheriting every phase by (DM4). If \(k_n\) is the
number of outputs at modulus \(n\), matching one label to each occupied
modulus gives
\[
 0\le\Delta\le\sum_n(k_n-1)_+
 \le\sum_n\binom{k_n}{2}=X. \tag{DM6}
\]
Hence \(\mathbb E\Delta<1\), under any specified law on actual common
sources, would contradict (DM5). No unrestricted bound of this strength
has been established. Bounds on each fixed \(\mathbb E L_J\) do not
bound the expectation of the maximum in (DM2).

## 7. Every averaged Hall constraint can hold while every tree fails

Fix odd primes \(r\ge3\), \(s>2r\), and arbitrary finite heights
\(A,B\ge1\). Let \(V=\{1,\ldots,s-1\}\), and choose a distinct
prime \(q_e>s\) for each pair \(e=\{i,j\}\subset V\), with
\(i<j\). Use the original numerical moduli
\[
 D=\{r^a:1\le a\le A\}\cup\{s^b:1\le b\le B\}
 \cup\{rs\}\cup\bigcup_e\{q_e,rq_e,sq_e,rsq_e\}.
 \tag{DM7}
\]
For each pure power \(p^k\), \(p\in\{r,s\}\), prescribe the
least-significant-first digit word \(1^{k-1}0\). All remaining phases
are fixed by this CRT table; a dash means the coordinate is absent from
that modulus.

| Original modulus | Modulo \(r\) | Modulo \(s\) | Modulo \(q_e\) |
| --- | ---: | ---: | ---: |
| \(rs\) | 2 | 1 | — |
| \(q_e\) | — | — | 0 |
| \(rq_e\) | 2 | — | 2 |
| \(sq_e\) | — | \(i\) | 1 |
| \(rsq_e\) | 1 | \(j\) | 1 |

These are distinct odd nonunit moduli and \(D\) is divisor closed.
The pure-power words are prefix incompatible. Each mixed class has
nonzero first \(r\)- or \(s\)-digit whenever that coordinate is
present, so it is disjoint from the comparable pure-prime class. The
\(q_e\)-class has phase zero, unlike all its proper extensions;
\(rq_e,rsq_e\) disagree modulo \(r\), and \(sq_e,rsq_e\) disagree
modulo \(s\). The classes at \(rs,rsq_e\) disagree modulo \(r\).
Mixed moduli from different cofactor packets are incomparable. These
checks account for every comparable pair.

Every class has a private integer. For a class in the \(e\)-packet,
set all other cofactor coordinates to 3 and use the triples
\((x\bmod r,x\bmod s,x\bmod q_e)\)
\[
 (1,1,0),\quad(2,2,2),\quad(1,i,1),\quad(1,j,1)
 \tag{DM8}
\]
for \(q_e,rq_e,sq_e,rsq_e\), respectively. Fill higher \(r\)- and
\(s\)-digits with ones. For \(rs\), use first digits \((2,1)\),
higher digits one and all cofactor coordinates 3. For the pure
\(r^a\)-class, use its designated prefix followed by ones, the
\(s\)-word \(2^B\), and all cofactor coordinates 3. For the pure
\(s^b\)-class, use the \(r\)-word \(1^A\), its designated
\(s\)-prefix followed by ones, and all cofactor coordinates 3. CRT
realizes every prescription. The table and prefix incompatibility show
that each point meets exactly its named class.

### One fixed safe coordinate and the actual output inventory

Fix \(u=1^A\) at \(r\), which avoids every pure \(r\)-power class.
It also kills \(rs\) and every \(rq_e\). Sample one common uniform
\(r\)-branch subtree of the \(s\)-ary tree through height \(B\), as
in report 388. Its root subset is
\(S\subseteq\{0,\ldots,s-1\}\), \(|S|=r\); put
\(z_a=\mathbf1_{\{a\in S\}}\). Every original uses this same tree.
The output period is \(N=r^B\prod_e q_e\), and the nonzero numerical
loads are
\[
 k_{q_e}=1,\qquad k_{rq_e}=z_i+z_j,\qquad k_r=z_0.
 \tag{DM9}
\]
For each \(2\le b\le B\), there is additionally one output at
\(r^b\) exactly when its pure \(s^b\)-prefix survives. With
\(\rho=r/s\),
\[
 \mathbb E k_{q_e}=1,\qquad
 \mathbb E k_{rq_e}=2\rho<1,\qquad
 \mathbb E k_{r^b}=\rho^b<1\quad(1\le b\le B).
 \tag{DM10}
\]
Every other output modulus has load zero. Thus \(\mathbb E L_J\le|J|\)
for **every fixed** downward-closed \(J\subseteq\mathcal P_N\).
These inequalities hold simultaneously as inequalities of expectations;
they do not assert that one tree satisfies them all.

### The exact pointwise deficit

Put \(T=S\setminus\{0\}\), \(t=|T|=r-z_0\), and let \(E_T\)
be the pairs contained in \(T\). For \(k=|E_T|=\binom t2\), the
set
\[
 J_S=\{r\}\cup\bigcup_{e\in E_T}\{q_e,rq_e\}
 \tag{DM11}
\]
is downward closed. Every selected pair contributes three labels to
\(L_{J_S}\), and the pure \(r\)-output contributes \(z_0\). Hence
\[
 L_{J_S}-|J_S|=(3k+z_0)-(2k+1)=k+z_0-1.
 \tag{DM12}
\]
This lower bound is attained. Match each \(q_e\)-label to \(q_e\),
one label in each nonempty \(rq_e\)-bin to \(rq_e\), and each
surviving pure-power label of exponent at least two to its own modulus.
If \(0\in S\), the pure output occupies \(r\), leaving \(k\)
unmatched labels. Otherwise put one of the \(k\) extra double-bin
labels at \(r\), leaving \(k-1\). Therefore
\[
 \boxed{\Delta(\theta)=
 \begin{cases}
 \binom{r-1}{2},&0\in S,\\
 \binom r2-1,&0\notin S.
 \end{cases}} \tag{DM13}
\]
Both values are positive for \(r\ge3\). Higher tree choices do not
change the deficit: the deficient ideal contains no higher pure power,
and no higher pure-power modulus can divide \(q_e\) or \(rq_e\).
This proves the assertion uniformly in both finite heights.

Since \(\Pr(0\in S)=r/s\),
\[
 \boxed{
 \max_J\mathbb E(L_J-|J|)=0,\qquad
 \mathbb E\Delta=\binom r2-1-\frac{r(r-2)}s>0.
 } \tag{DM14}
\]
For \(r=3,s=7\), 15 root subsets contain zero and have deficit one;
the other 20 have deficit two. Their mean is \(11/7\). This rules
out exact common-tree rounding based only on averaged divisor
inequalities, even with the stated local arithmetic conditions and
private witnesses.

### Compatible grouping still cannot repair these whole classes

Allow several output labels to share a containing divisor coset, with
at most one replacement phase at each numerical modulus. The output
\(0\bmod q_e\) forces slot \(q_e\) with phase zero: its only
nonunit divisor is \(q_e\). Neither mixed output in that packet can
use this slot, since its \(q_e\)-phase is one. If both \(i,j\)
survive, their outputs at \(rq_e\) have distinct inverse root digits
\(\theta_1^{-1}(i),\theta_1^{-1}(j)\). They cannot share an
\(rq_e\)-coset, so at least one must use slot \(r\).

If zero belongs to \(S\), the pure output forces slot \(r\) to
have phase \(\theta_1^{-1}(0)\), incompatible with every mixed
output. Otherwise a chosen \(r\)-phase can absorb only labels
belonging to one target digit \(a\in S\). The complete graph on
\(S\), with \(|S|=r\ge3\), has an edge not incident with \(a\);
neither output of that edge can use slot \(r\). Thus grouping does
not remove the obstruction. This conclusion concerns repairs placing
each **whole** output class inside one replacement class, not arbitrary
covers of their union.

The CRT point with \(r\)-word \(1^A\), \(s\)-word \(1^B\), and
every cofactor coordinate equal to 3 avoids all original classes. The
construction is explicitly a **noncover**. For general \(r\), the
tree obstruction above is proved at the fixed safe coordinate
\(u=1^A\); it does not assert failure for every other safe coordinate.
It does not disprove a theorem using whole coverage or EB1 minimality.

### At the ternary prime every safe coordinate fails

Specialize the same construction to \(r=3\) and any prime \(s>6\).
Every safe \(u\bmod3^A\) has first digit 1 or 2, since the original
pure 3-class has phase zero. If its first digit is 1, all mixed-class
activity is exactly (DM9), independently of the higher safe digits.
Thus every common tree has deficit one or two as in (DM13), and the
whole-class grouping obstruction also applies.

If its first digit is 2, both original classes \(q_e\) and \(3q_e\)
survive, with output modulus \(q_e\) and phases 0 and 2. Their only
nonunit divisor slot is \(q_e\), so they leave one unmatched label
per packet under every tree. The \(3sq_e\)-class is inactive. A
surviving \(sq_e\)-class contributes at most one label at \(3q_e\),
which can be assigned its own modulus. The pure \(s\)-class and
the \(3s\)-class contribute \(z_0\) and \(z_1\) outputs at 3.
The higher pure powers contribute at most one output at each
\(3^b\), \(b\ge2\). Writing \(m=\binom{s-1}{2}\), this gives
the exact deficit
\[
 \boxed{\Delta(u,\theta)=m+z_0z_1
 \quad\text{when }u\equiv2\pmod3.} \tag{DM14a}
\]
For the lower bound, use the downward-closed set of all \(q_e\),
and include slot 3 when both first-digit outputs occur. It contains
\(2m\) labels in \(m\) slots, with two additional labels in one
slot in the latter case. For the matching attaining the bound, retain
one label at each \(q_e\), every surviving \(3q_e\)-label at its
own slot, at most one output at 3, and all higher pure-power outputs
at their own slots. No higher power is a divisor available to a
\(q_e\)- or 3-demand.

Grouping complete classes cannot help this branch either: the two
distinct \(q_e\)-phases cannot share their only containing nonunit
coset. Consequently this ternary noncover defeats every joint choice
of a safe coordinate and a common tree, even for the grouped repair
class above, at arbitrary finite heights. The averaged Hall feasibility
in (DM10)--(DM14) is still asserted only under the tree law with a
fixed safe coordinate of first digit 1. Averaging uniformly over **all** safe
coordinates introduces the overloaded prime slots and does not satisfy
those feasibility inequalities. Whole coverage and EB1 minimality
remain excluded from this counterexample.

## 8. Original-phase compatibility supplies a precise repair interface

For surviving original labels \(i,j\) in one common source of report
388 and a divisor slot \(h=r^tm>1\) common to their output moduli,
with \(\gcd(m,rs)=1\),
\[
 \boxed{c_i\equiv c_j\pmod{r^tm}
 \quad\Longleftrightarrow\quad
 \alpha_i\equiv\alpha_j\pmod{s^tm}.} \tag{DM15}
\]
The old \(m\)-coordinate is unchanged. Compatibility of the same tree
gives \(\theta_t(c_i\bmod r^t)=\alpha_i\bmod s^t\), and likewise
for \(j\). Injectivity proves the equivalence at this coordinate;
CRT combines the two. Thus compatibility is determined by the original
phases, even though the source determines which labels survive.

Here is a sufficient alternating-path repair. Let \(M\) be a partial
divisor matching of all outputs, leaving precisely \(U\) unmatched.
For each \(u\in U\), suppose there is a simple label path
\[
 i_0=u,i_1,\ldots,i_t,\qquad t\ge1,\qquad
 M(i_j)=h_j\mid n_{i_{j-1}}\quad(1\le j\le t),
 \tag{DM16}
\]
whose labels \(i_1,\ldots,i_t\) are matched, and whose terminal
phases satisfy \(c_{i_{t-1}}\equiv c_{i_t}\pmod{h_t}\). Require
vertex-disjoint paths for different unmatched labels. For \(j<t\),
replace slot \(h_j\)'s phase by \(c_{i_{j-1}}\bmod h_j\), and
keep the terminal slot at \(c_{i_t}\bmod h_t\). Every earlier
incoming class is wholly contained in its assigned slot. The terminal
slot contains both terminal classes by the assumed compatibility.
Off-path matched labels retain their containing replacements. Distinct
paths use distinct slots, yielding \(|I|-|U|\) classes with distinct
numerical moduli covering **every complete output class**. Equation
(DM15) checks terminal compatibility in the original coordinates.

This conditional exchange does not force paths to exist. The standard
Hall consequence for an inclusion-minimal deficient label set gives
deficit exactly one: deletion of any label leaves a Hall-feasible proper
subset. If outside labels reserve slots, apply this consequence to the
residual graph with those slots removed, not to an artificially freed
divisor palette.

A sufficient unrestricted target is to find, for every hypothetical EB1
whole cover, support primes \(r<s\), one safe \(u\), and one common
finite-height tree whose complete output family has either a full divisor
matching or disjoint compatible absorption paths for all unmatched labels.
No such existence result is established here. The support and heights
remain arbitrary and finite. Section 7 prevents deriving it from local
divisor closure, comparable disjointness, private points and averaged
Hall inequalities alone.

This does not improve the fixed-old-law averaged convex bound in
[report 849](../800-849/849-actual-unions-admit-sharp-common-tree-moment-transport.md#the-averaged-transport-budget-is-dominated-by-the-original-block).
It changes the possible descent certificate to actual numerical inventory
and whole-class liability. The missing arithmetic assertion must use
whole coverage and source ancestry to force a compatible repair of a
terminal deficient block, accounting for outside reservations. These
matching arguments and the all-height construction are ordinary
mathematical deductions, not new Lean verification or a resolution of
Erdős #7.
