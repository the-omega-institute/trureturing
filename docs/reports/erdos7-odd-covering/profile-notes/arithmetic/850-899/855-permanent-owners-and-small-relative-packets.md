[Index](../../../marked_head_profile.md) · [Paid packets](853-paid-packet-absorption-and-residual-moment.md) · [Long paid donors](854-long-paid-donors-and-cluster-moment.md)

# Permanent owners and small relative packets

A sequential rescue closure must retain each cofactor's
permanent output plan. A closure on bare cofactor names can
combine incompatible seed choices and report an unpaid
exchange. The actual congruence counterexample below has two
legal seed plans, each rescuing a different target, while
their union would require two phases of the same $27s$ label.
The obstruction persists when all paid $81s$ outputs are
included.

Arithmetic further restricts a rescue packet. For a target
cofactor $m$, the number of distinct $27s$ donors with a
given relative modulus $d>1$ is at most

$$
\tau\!\left(\prod_{p\mid m,\ p\nmid d}p^{v_p(m)}\right).
\tag{RO1}
$$

For at most six donor outputs, the published Lettl--Sun
bound for an essential class gives an exact alternative:
a compatible divisor donor, or five actual relative-modulus-5
classes carrying all five phases. A bound on distinct donor
digits is a different condition. None of these interfaces
supplies a coherent packet from original whole coverage.

These are conditional ordinary mathematical results, without
a claim of Lean verification of the rescue theorem, a new
D5 declaration, an odd distinct covering realization, or a
resolution of Erdős #7.

## 1. Reused source, payment and mathematical inputs

Use the actual common source, whole continuing inverses,
group payment and numerical collision separation of
[Report 388, Section 74](../350-399/388-source-global-substitution-collision-moment.md#74-grouped-shallow-slots-force-actual-divisor-triples-and-a-common-code-moment).
[Report 853](853-paid-packet-absorption-and-residual-moment.md)
pays one globally compatible packet.
[Report 854](854-long-paid-donors-and-cluster-moment.md)
allows a designated long owner when its group has at most
two nonempty inverses or another long inverse. The seed
catalogue here includes all such admissible plans. Geometry,
actual phases and the full W-coordinate stay fixed throughout
a rescue process.

[Report 850](850-cofactor-dependent-protected-codes.md)
requires protection of complete owner subtrees when the code
varies with a cofactor coordinate.
[Report 852](852-protected-digit-inventory-gap-and-grouped-hulls.md)
separates numerical inventories from whole coverage; its
all-height hull allocation does not make alternative owners
of one $27m$ label simultaneously available.

Lettl--Sun, [*On covers of abelian groups by cosets*,
arXiv:math/0411144v2](https://arxiv.org/abs/math/0411144v2),
Theorem 1.3, equation (1.5), gives

$$
k\ge\mu+\sum_pv_p(n)(p-1)
$$

for an essential class of index n in a $\mu$-cover by k
abelian cosets. Their Remark 1.2 attributes the integer
ordinary-cover case to Znám. The
[repository source note](../../../../../../Library/Arith/lettlsun2008cosets.md)
records this result. The input is the index of an individual
essential class, not an unproved replacement by the index
of the intersection of all the subgroups.

The closure below is the standard finite least-fixed-point
construction. Pinned Mathlib provides `OrderHom.lfp`, its
minimality and induction laws in `Mathlib/Order/FixedPoints.lean`,
and `ClosureOperator` in `Mathlib/Order/Closure.lean`. The
arithmetic uses ordinary valuation identities for quotients,
gcds and lcms. Repackaging these existing tools supplies no
new general closure or factorization theorem; the missing
mathematical interface concerns actual compatible owner choices.

## 2. A state records permanent output plans

For a good cofactor s, a plan records its admissible owner
at $27s$ and the actual assignments at $81s$ and, if needed,
$243s$. Each output retains its own owner's literal cofactor
phase.

For a bad cofactor m, a plan is an ordered choice $(a,b,c)$
of its three owners: omit a, retain b's enclosure at $27m$,
and retain c's enclosure at $81m$. There are six such plans.
Its omission can be rescued only when its whole inverse is
covered by outputs already present. The two surviving outputs
are then permanent; the process cannot later switch that
group's donor owner or omitted inverse.

A state is a partial map from cofactors to plans, together
with their actual output union. Equal activated-cofactor sets
can have different output unions and different enabled rescues.
Their union need not be a legal state: it can give one cofactor
two independently phased outputs with the same numerical label.

One may use only the $27s$ outputs as funding, as in Report
853, or use all already-present outputs with their actual
ternary depths. Fix this convention for the entire process.
The arithmetic packet classification in Sections 5--6 uses
only the former convention. The counterexample in Section 3
also works with all permanent $81s$ outputs available.

### Fixed plans give a closure

Fix one complete plan assignment $\pi$. Let $\mathcal G$
be the good seed groups and $\mathcal B$ the initially bad
groups. For a group set S, let $P_\pi(S)$ be the funding
outputs of its chosen plans, together with any specified
permanent base outputs. Define

$$
F_\pi(S)=\mathcal G\cup S\cup
\{m\in\mathcal B:
 B_{m,a_\pi(m)}\subseteq P_\pi(S)\}.
\tag{RO2}
$$

This map is monotone and inflationary. Starting from
$\mathcal G$, it stabilizes after at most $|\mathcal B|$
strict rounds. Its least fixed point $C_\pi$ is independent
of the order of enabled additions. Every new group is paid
by earlier outputs; a cycle does not pay itself in advance.

A complete legal sequential rescue history exists if and
only if some permanent plan assignment satisfies
$C_\pi=\mathcal G\cup\mathcal B$. A legal history fixes its
plans permanently, and monotonicity reproduces all its
additions in the closure. Conversely, order a complete
closure's additions by their first round. Every omission
is then covered before its outputs are added.

This leaves the plan-selection quantifier intact:

$$
\forall m\in\mathcal B\ \exists\pi:\ m\in C_\pi
\qquad\text{does not imply}\qquad
\exists\pi\ \forall m\in\mathcal B:\ m\in C_\pi.
\tag{RO3}
$$

Only the second assertion pays one complete exchange. EB1
forbids that assertion, not target-specific reachability under
different plans.

## 3. An actual congruence counterexample to forgetting plans

This is a countermodel at the paid-packet arithmetic interface,
not an asserted EB1 whole-cover realization. Take
$W=385=5\cdot7\cdot11$ and work on
$\mathbb Z/81\mathbb Z\times\mathbb Z/W\mathbb Z$;
all classes lift to the common ternary carrier modulo 243.
Write

$$
(\ell;r)_s=[\ell]_{81}\times[r]_s.
$$

The ternary residues $2,29,56$ lie above safe word 2 modulo
nine and share parent 2 modulo 27. A good seed group at
cofactor 5 has two inverses $(2;0)_5,(29;1)_5$. Its two
admissible plans have full output unions

$$
\begin{aligned}
P_0&=([2]_{27}\times[0]_5)
       \cup([29]_{81}\times[1]_5),\\
P_1&=([2]_{81}\times[0]_5)
       \cup([2]_{27}\times[1]_5).
\end{aligned}
\tag{RO4}
$$

There are two bad groups:

$$
\begin{array}{c|c}
m&\text{three full inverse cylinders}\\\hline
35&(56;0)_{35},\ (56;5)_{35},\ (56;10)_{35}\\
55&(56;1)_{55},\ (56;6)_{55},\ (56;11)_{55}.
\end{array}
\tag{RO5}
$$

Within each bad group the three cofactor phases are distinct,
as in the C1 interface. A distinct fourth q-free phase is
15 modulo 35 or 16 modulo 55. The two seed leaves and the
bad groups' common leaf are distinct siblings, so one common
code can contain them.

Under $P_0$, every inverse of group 35 is covered. Every
inverse of group 55 is disjoint from $P_0$: the broad seed
output has the wrong modulo-five phase, while the phase-one
$81\cdot5$ output is on leaf 29 rather than 56. After any
of group 35's six plans, all its added outputs still have
phase zero modulo five, and cannot help group 55.

Under $P_1$, group 55 is covered and group 35 is disjoint
from the packet. Every output from any plan of group 55
has phase one modulo five, so group 35 remains untouched.
The two maximal activated sets are therefore $\{5,35\}$
and $\{5,55\}$. Their union is not reachable.

The fictional packet $P_0\cup P_1$ covers every inverse of
both groups, but contains two phases at the same numerical
$27\cdot5$ label. It is not one legally paid state. On the
period $81\cdot385=31185$, a displayed inverse at cofactor
35 has 11 points and one at cofactor 55 has 7 points.
These cardinalities follow directly from the residue classes;
the modulo-five and ternary-leaf arguments apply to the
whole classes, with no enumeration premise.

This proves failure of union closure of reachable cofactor
sets even when both permanent seed outputs are retained.
Additional whole-cover hypotheses could still imply an
extraction theorem unavailable at this interface.

## 4. The quantifiers in a stopping certificate

For fixed $\pi$, put $T=\mathcal B\setminus C_\pi$.
RO2 gives a missing point only in the inverse designated for
omission by $\pi$ at each $m\in T$. If a run is saturated
over **all** omission choices against its one final actual
packet P, the stronger statement is

$$
\forall m\in T\ \forall a\in\{0,1,2\},\qquad
B_{m,a}\setminus P\ne\varnothing.
\tag{RO6}
$$

Testing the other plans of an unactivated group does not
change any already-permanent plan. A fixed-plan stopping
claim cannot be promoted to RO6 without those tests.

For $27s$ funding outputs, restrict to the paid donors at
a target's same ternary parent. For target cofactor m and
phase r, put $g_j=\gcd(m,s_j)$. Ignore donors for which
$g_j\nmid r_j-r$, with the difference taken in the integers.
The exact remaining relative classes are

$$
[t_j]_{d_j},\qquad d_j=\frac{s_j}{g_j},\qquad
 t_j\equiv\frac{r_j-r}{g_j}
       \left(\frac m{g_j}\right)^{-1}\pmod{d_j}.
\tag{RO7}
$$

These follow by substituting $w=r+mt$ in the target coset.
Their moduli divide $W/m$, and the stopped inverse has a
witness

$$
\exists t\in\mathbb Z/(W/m)\mathbb Z\quad
\forall j,\qquad t\not\equiv t_j\pmod{d_j}.
\tag{RO8}
$$

Every exclusion uses the same permanent packet. Different
inverses can require different witnesses; the three distinct
C1 cofactor phases do not define a common point.

For fixed plans, form hyperedges $H\to m$ from donor group
subfamilies whose actual outputs cover the designated inverse.
Every incoming edge to an unactivated group meets the
unactivated set. This is a closed cut for that plan assignment.
A cycle in a graph of possible suppliers or intersections
supplies no such payment or noncoverage certificate.

An optimistic relaxation dominates every legal sequential
strategy only if it both exposes every candidate output phase
of each activated group and allows **all three** omission
choices of each unactivated group. Its activation rule is
existential over those omissions against the enlarged packet.
Induction then puts every legal history inside the optimistic
closure, so a remaining trap blocks all legal sequential
histories. Fixing omissions in the relaxation only blocks
that restricted set of histories. Success of the full
relaxation still proves no simultaneous payment, as RO4--RO5
show.

### Sequential closure is not every possible simultaneous exchange

An explicitly checked final family can cover a group without
an externally funded first rescue. For example the bad group
at cofactor 5 with inverses

$$
(2;0)_5,\quad(29;0)_5,\quad(56;1)_5
$$

is covered by $[2]_{27}\times[0]_5$ and
$[56]_{81}\times[1]_5$. With no external seed, RO2 does not
start, but these two outputs are a direct local replacement.
This is the existing common-union-hull mechanism of Report
388 SC130, not a rule accepting circular promises.

The example is not C1: the first two owners can use different
q-digits, so equality of their cofactor phases does not violate
SC483. In a C1 group, both other owners' own enclosures
are disjoint from the omitted inverse in the cofactor
coordinate. This particular internal repair therefore does
not remove the hard C1 case. Explicitly verified internal
repairs may instead be included as additional seed plans.

## 5. Exact fibres of the relative-modulus map

Fix $m>0$ and define

$$
\phi_m(s)=\frac{s}{\gcd(s,m)}.
$$

For $d>0$, split the target into

$$
m_{\parallel d}=\prod_{p\mid d}p^{v_p(m)},\qquad
m_{\perp d}=\prod_{p\mid m,\ p\nmid d}p^{v_p(m)},\qquad
m=m_{\parallel d}m_{\perp d}.
$$

The exact fibre is

$$
\phi_m(s)=d
\quad\Longleftrightarrow\quad
s=d\,m_{\parallel d}\,a
\quad\text{for some }a\mid m_{\perp d}.
\tag{RO9}
$$

At a prime dividing d, the valuation identity is
$\max(v_p(s)-v_p(m),0)=v_p(d)>0$, so
$v_p(s)=v_p(m)+v_p(d)$. At a prime not dividing d, it
allows exactly $0\le v_p(s)\le v_p(m)$. These choices
are precisely RO9, and the converse is the same valuation
identity. If $m\mid W$ and $d\mid W/m$, every displayed
s divides W; otherwise the actual carrier can only remove
choices.

There is at most one $27s$ output per distinct cofactor.
The distinct divisors a in RO9 therefore prove RO1, before
phase or parent incompatibilities remove any donors. For
$d=1$ the fibre consists of divisors of m, with $s=1$
omitted from the permitted nonunit donor groups.

An equivalent collision criterion uses

$$
D(s,t)=\prod_{p:\,v_p(s)\ne v_p(t)}
              p^{\max(v_p(s),v_p(t))}.
$$

Then

$$
\phi_m(s)=\phi_m(t)\quad\Longleftrightarrow\quad D(s,t)\mid m.
\tag{RO10}
$$

Equal valuations impose no condition. For unequal valuations
$a<b$, their truncated excesses above $v_p(m)$ agree exactly
when $b\le v_p(m)$. In contrast,
$\operatorname{lcm}(s,t)/\gcd(s,t)\mid m$ is insufficient:
$s=p^2,t=p^3,m=p$ satisfy it but have relative moduli p
and $p^2$.

For a prime-power target $m=p^h$, RO9 has two forms:

- If $p\mid d$, the only possible donor cofactor is $p^hd$.
- If $p\nmid d$, the fibre is the chain $d,pd,\ldots,p^hd$.

Without a compatible divisor donor, Report 853's EB1 collision
consequence therefore requires two paid cofactors on the same
p-chain, with exponents at most h, a common relative modulus
coprime to p, and different actual reduced phases. They must
also lie at the target's ternary parent. A numerical chain
alone gives no whole-coset cover.

## 6. Exact rigidity for at most six outputs

Use a paid packet with at most one $27s$ output per nonunit
cofactor. Suppose it covers a whole short inverse and no
compatible divisor donor covers that inverse. An inclusion-minimal
subcover of its actual relative classes has the following
necessary properties:

- The literal RO7 phases cover all of $\mathbb Z/(W/m)\mathbb Z$.
- Every relative modulus is a nonunit divisor of $W/m$,
  coprime to $3q$, hence at least five.
- Its uniform mass satisfies $\sum_j1/d_j\ge1$. If $p_*$
  is the least prime factor of $W/m$, its size k is at
  least $p_*\ge5$.
- Multiplicity at each relative modulus obeys RO1.
- Some repeated relative modulus has different phases;
  otherwise merging identical restrictions gives a distinct
  odd nonunit integer cover with fewer than the original
  K classes, contrary to EB1.

If $W/m=1$, the non-divisor case is absent and no $p_*$
is needed. All these conditions concern one paid owner
selection, not independently optimized targets.

Now suppose the original packet has at most six outputs.
Its minimal relative subcover has $k\le6$ and every member
is essential. Directly apply Lettl--Sun Theorem 1.3(1.5),
with ordinary covering multiplicity one, to each essential
index d:

$$
\sum_pv_p(d)(p-1)\le k-1\le5.
$$

All its prime factors are at least five. The only nonunit
possibility is $d=5$: index 7 contributes six, index 25
contributes eight, and a product of two allowed distinct
primes contributes still more. Hence the minimal subcover
consists of the five distinct phases modulo five. A sixth
output is dispensable for this target.

Conversely, those five literal relative phases cover the
whole quotient. Including the compatible modulus-one case,
the exact six-output criterion is

$$
\boxed{\text{a compatible divisor donor exists}
\quad\text{or}\quad
\text{five actual }d_j=5\text{ restrictions carry all five phases}.}
\tag{RO11}
$$

All restrictions here are at the target's ternary parent and
pass the compatibility test in RO7. The second case forces
five different actual donor cofactors of the form

$$
s_j=5^{v_5(m)+1}a_j,\qquad
 a_j\mid m/5^{v_5(m)},\qquad a_j\ne a_l\quad(j\ne l).
\tag{RO12}
$$

Thus $\tau(m/5^{v_5(m)})\ge5$. A target $m=5^h$
has no non-divisor rescue with at most six outputs. A target
$m=p^h$, $p\ne5$, needs $h\ge4$, five actual donors
on that p-chain, and all five prescribed relative phases.
These statements do not exclude larger packets.

### A bounded-rescue stopping certificate

Fix the actual permanent packet. For target parent $\lambda$,
cofactor m and phase r, let $\Phi_{m,r,\lambda}$ be the set
of reduced modulo-five phases of already-paid donors at that
parent satisfying RO7 and $s/\gcd(s,m)=5$.
Some subpacket of at most six outputs covers the inverse
if and only if a compatible paid divisor donor exists or

$$
\Phi_{m,r,\lambda}=\mathbb Z/5\mathbb Z.
\tag{RO13}
$$

If all phases occur, choose one paid output per phase. These
are five distinct outputs because one output has only one
relative phase. The entire paid packet may exceed six outputs:
RO13 characterizes the existence of a small covering subpacket,
not coverage by its unrestricted full union.

A bounded-rescue run saturated over all three omission choices
at every remaining group therefore has, for each possible
omitted inverse,

$$
\text{no compatible paid divisor donor},\qquad
\exists\eta\in\mathbb Z/5\mathbb Z:
             \eta\notin\Phi_{m,r,\lambda}.
\tag{RO14}
$$

For a fixed-plan bounded closure this holds only for the
designated omission unless the other two are also tested.
The packet is shared and permanent; missing phases may differ
between inverses. RO1 blocks the five-phase rule whenever
$\tau(m_{\perp5})<5$.

For fixed permanent plans, the bounded process consequently
has single-donor and exact five-phase incoming hyperedges.
It needs no independent rescue rule of arity two, three,
four or six. Actual phases and exclusive plan choices remain
part of these hyperedges.

### Outputs are not digit leaves

A common-parent geometry can hold one prescribed short target
at word z and up to six distinct nonterminal long donor digits
outside the selected six-set. Put the short target in one
of its parent's depth-four children and reserve the other
two children, which have six depth-five leaves, for the long
digits. Seven depth-four slots above z remain available,
including the target slot, so all six prescribed short leaves
still fit. The actual terminals can be placed together at a
compatible word $v\ne z$ as in Report 854: at most five
short requests lie there and five slots remain.

This is one simultaneous completion for all donors and targets.
Every designated long owner must still pass its actual old
ternary test at z and its good-group designation rule. The
permanent plans must coexist. Subject to those conditions,
a five-phase packet from RO11 rescues the complete target
inverse, and the same paid outputs can rescue other targets
passing their actual whole-coset test.

Several cofactors can use the same long q-digit. Thus at most
six distinct donor digits does not imply at most six outputs.
For a concrete arithmetic example, take

$$
m=5^6,\quad W=7m,\quad s_j=7\cdot5^j,\quad
r_j\equiv mj\pmod{s_j}\quad(0\le j\le6).
\tag{RO15}
$$

For target phase zero, $\gcd(m,s_j)=5^j$ and RO7 gives
exactly $t\equiv j\pmod7$. These seven restrictions cover
the whole relative quotient; every six-output subpacket
misses a phase. The seven distinct donor cofactors can share
one ternary parent and one long q-digit. Each has one paid
output. This is an arithmetic interface example, not a
whole EB1 covering realization. It demonstrates why a bound
on digit leaves cannot invoke RO11 for an unrestricted number
of cofactor outputs.

### Essential-cover bounds require a whole relative cover

Nagy--Pach--Tomon, [*Additive bases, coset covers, and
non-vanishing linear maps*, arXiv:2111.13658v1](https://arxiv.org/abs/2111.13658v1),
Theorem 1.2, bounds the subgroup-intersection index of an
irredundant k-member abelian coset cover by
$\exp(O(k\log\log k))$. For an actual irredundant relative
cover from RO7, that index is $\operatorname{lcm}(d_1,\ldots,d_k)$.
The theorem applies after whole-quotient coverage is established.

A stopped process instead supplies RO8. Coverage by unpaid
originals may concern a punctured residual subset, which
need not be a subgroup or coset and may require the target's
own inverse. Even a singleton residual in $\mathbb Z/n\mathbb Z$
is covered by one singleton coset for arbitrarily large n;
a whole-group essential-cover bound does not apply to that
masked problem.

The theorem does not choose one owner per group, find a
seed, supply a small subcover before coverage is known, or
turn pairwise intersections into coverage. Its asymptotic
constant gives no explicit numerical contradiction here.

## 7. The remaining extraction interface

An exact finite search can retain permanent plans, build
RO7's literal restrictions, enforce RO1's multiplicities,
and use RO11--RO14 for rescues by at most six outputs.
Larger packets need their own whole-inverse containment test.
An actual rescue sequence is then checked against its same
source and permanent outputs. A code moment may count the
rescued groups under that one coherent selection.

Whole coverage has not supplied the required compatible
divisor donor or actual relative cover, nor owner choices
that coexist across enough target groups. Bare cofactor
reachability, unions of target-specific policies, graph
cycles, and essential-cover bounds on residual masks do
not close this gap. The five-supplier lower bound cannot
be summed over targets without a separate disjointness or
charge bound, because the same outputs can be reused.

Generic finite closure and the valuation identities are
reused mathematics. The unresolved candidate is a coherent
actual-coset extraction theorem from whole coverage, or a
bound contradicting the required relative-multiplicity and
phase profiles. RO1--RO15 assert neither such an extraction
nor a new Lean admission basis or completion of the
height-two branch.
