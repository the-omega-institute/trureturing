[Index](../../../marked_head_profile.md) · [Balanced source](858-paid-residual-hulls-and-balanced-sibling-extraction.md) · [Owner cores](857-owner-conflict-cores-and-actual-donor-extraction.md) · [Literal collision graph](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#172-literal-prime-root-collisions-have-one-fixed-exceptional-pair-across-all-sources)

# Exceptional top targets and actual Hall obstructions

The existing literal prime-root collision theorem gives a stronger
restriction on the balanced source: one effective output can singly
absorb at most two bad top inverses. Across the six selected parents,
at most twelve exceptional targets meet every such two-target pair.
Outside those exceptions, simultaneous single-output top absorption
is exactly a Hall matching problem.

This does not equate Hall matching with arbitrary cooperative coverage
by a union of outputs, assisted residual coverage, or absorption of a
different inverse in the same bad group. It gives an exact restricted
consumer of the actual cover's phase constraints. Existence of a
compatible exception plan and the required Hall expansion remain open.

## 1. One geometry and one output per good group

Keep Report858's hypothetical globally EB1-minimal whole cover with
$q=113$, $H_3=2$, period $9q^GW$, and its fixed balanced initial code.
The six selected short leaves occupy distinct modulo-27 parents.
All literal phases, the complete $W$ coordinate and the initial source
remain fixed. For an initial good group $s$, use the nonempty effective
owner domain $\Omega_s$ from Report858 section 4. Its selected broad
output is

$$
E_{s,a}=[\ell_{s,a}]_{27}\times[r_{s,a}]_s.
$$

For a bad cofactor $m$, write $B_m=B_{m,2}$ for the **whole** top
inverse of the actual original $9qm$. Define

$$
J^{\rm top}_{ms}=\{a\in\Omega_s:B_m\subseteq E_{s,a}\}.
\tag{ET1}
$$

A successful assignment in this report means

$$
\exists\theta\in\prod_s\Omega_s\quad
\forall m\in\mathscr B\quad\exists s,\quad
\theta_s\in J^{\rm top}_{ms}.
\tag{ET2}
$$

It is sufficient for the existing paid packet to contradict EB1.
An output can serve multiple targets if its same permanent owner
works for all of them. Mere containment of $B_m$ in a union does not
imply a witness in ET1.

## 2. An actual output has at most two top targets

Fix an effective output $E_{s,a}$ with a top hit. Whole containment
implies $s\mid m$ and its actual phase modulo $s$ agrees with that
top target. The good and bad cofactors differ, so $s<m$.
Choose any prime $p\mid s$.

Its modulo-27 parent contains one selected short leaf. Thus every
hit top original $9qm$ has the same old modulo-nine word, the same
actual first q-digit, and the same phase modulo $p$. All such originals
are proper descendants of the original parent $9qp$. That parent
exists by divisor closure, and $\tau(qp)=4\ge3$.
Report385 DR8 consequently gives

$$
\#\{m\in\mathscr B:a\in J^{\rm top}_{ms}\}\le2.
\tag{ET3}
$$

Properness follows already from $p\mid s\mid m$ and $s<m$;
prime-power exclusion is not needed for this particular implication.
The parent phase used here is the descendants' actual shared phase;
it need not be the original parent's own phase.

This cap does not transfer to Report858's assisted relation:
$s\mid\Gamma(B_m\setminus H)$ need not imply $s\mid m$.
Without the latter divisibility, $9qp$ need not be a parent of these
top originals.

## 3. At most twelve exceptional targets

For one selected short leaf, use the literal prime-root collision graph
on its bad top originals: join two when their cofactors share a prime
and their literal phases at that prime agree. Any pair jointly contained
in a nonunit broad output is an edge, by choosing a prime dividing that
output's cofactor. This includes the broad enclosure of a blocked long
owner, even though it is not an admissible selected output. The graph
is an induced subgraph of Report385 section 172's graph on the actual
full-ternary-height originals with the fixed old word and first q-root.

That existing theorem states that the literal collision graph has no
two vertex-disjoint edges, across all cofactor sources and q-heights.
Its proof replaces four colliding originals by four globally fresh
classes of smaller total modulus; it does not identify different
private points or require compatible old parent phases. The hit graph
inherits this restriction.

A graph of matching number at most one is a star or a triangle, with
isolated vertices allowed. A star center, or two triangle vertices,
meets every edge. Select such a set for each of the six selected
leaves, before choosing any owners. Their union $\mathcal E$ satisfies

$$
|\mathcal E|\le12,\qquad
\forall s,a\quad
\#\{m\in\mathscr B\setminus\mathcal E:
                 a\in J^{\rm top}_{ms}\}\le1.
\tag{ET4}
$$

In particular, the abstract four-target crossing square is forbidden
here. If one donor's options hit two disjoint row pairs and another's
options hit the column pairs, connectivity forces all four tops onto
one selected leaf. The row pairs then give two disjoint literal
prime-root edges, contradicting the existing collision theorem.
This exclusion uses the actual EB1 phase constraint, not just the
abstract owner incidence graph.

## 4. Exact Hall matching outside the exceptions

Put $\mathcal O=\mathscr B\setminus\mathcal E$. Join an ordinary
target $m$ to a good group $s$ when $J^{\rm top}_{ms}\ne\varnothing$.
For $T\subseteq\mathcal O$, let $N(T)$ be this set of neighboring
good groups. Then

$$
\begin{split}
&\exists\theta\quad\forall m\in\mathcal O\quad
                  \exists s,\ \theta_s\in J^{\rm top}_{ms}\\
&\hspace{12mm}\iff
\forall T\subseteq\mathcal O,\quad |N(T)|\ge|T|.
\end{split}
\tag{ET5}
$$

For necessity choose one actual witnessing group for each target from
a successful common assignment. ET4 makes these witnesses distinct,
since a group's one chosen output cannot singly contain two ordinary
targets. For sufficiency apply Hall, select a hitting owner for each
matched target's distinct group, and fill the remaining nonempty owner
domains arbitrarily. No owner is selected twice.

This reuses Hall's marriage theorem; it is not a new matching theorem.
It still requires expansion of the **actual** incidence graph.

There is also an exact reconstruction of ET2. Choose a set
$I\subseteq\mathscr G$ with $|I|\le|\mathcal E|$ and a single
partial permanent owner assignment $\eta_s\in\Omega_s$ for $s\in I$.
Require its chosen outputs individually to witness every exceptional
target. Let

$$
\mathcal O_\eta
=\{m\in\mathcal O:\forall s\in I,\ \eta_s\notin J^{\rm top}_{ms}\}.
\tag{ET6}
$$

Then ET2 holds if and only if some such partial assignment has a
matching from $\mathcal O_\eta$ to the unused groups
$\mathscr G\setminus I$. Necessity follows by choosing one witnessing
group per exception from an actual successful assignment, deduplicating
them, and keeping their same owners. Every still-unhit ordinary target
has an unused witness, and ET4 makes these witnesses distinct.
Sufficiency keeps $\eta$ and extends it with the matching as in ET5.

When $\mathcal E=\varnothing$, take $I=\varnothing$; when
$\mathcal O_\eta=\varnothing$, the matching condition is vacuous.
There is no polynomial-time or fixed-parameter complexity claim here.
Under EB1, every available exception plan of this form must leave a
nonempty Hall-deficient ordinary set. Existence of an exception plan
is itself an obligation.

## 5. Deficient sets must pay an actual residual load

Use the full original-q-tail loads $N_m^{q,*},\Lambda_m^q$ and actual
shallow counts $k_{ms}$ from Report858 SF12 and SF21--SF22. Set
$L_m=N_m^{q,*}+\Lambda_m^q$. For any ordinary target set $T$, let
$\mathcal B_T$ be the groups with a blocked unique long owner that
contributes a matching proper-divisor trace to some target of $T$.

By ET4, each effective admissible owner contributes to at most one
target of $T$. The same holds for a blocked long owner: the proof of
ET3--ET4 uses its actual cofactor and broad coset, not admissibility.
Writing $e_s=|\Omega_s|$ for groups with effective long options and
$e_s=0$ for all other groups,

$$
6|T|\le\sum_{m\in T}L_m+
             \sum_{s\in N(T)}e_s+|\mathcal B_T|.
\tag{ET7}
$$

Only groups actually contributing have been included; groups with no
effective admissible long option are handled by the blocked term or
contribute zero. Since $e_s\le3$, a Hall-deficient $T$ therefore obeys

$$
\sum_{m\in T}L_m+|\mathcal B_T|
\ge6|T|-\sum_{s\in N(T)}e_s
\ge6|T|-3|N(T)|\ge3|T|+3.
\tag{ET8}
$$

Different targets may minimize $N_m^q(w)$ at different actual
$w\in Z_m$. This causes no joint-source substitution: each original
cover inequality holds for every such $w$, while the trace reuse bound
is a uniform phase statement independent of the minimizing points.

After fixing an exception plan on $I$, take $T\subseteq\mathcal O_\eta$
with $|N(T)\setminus I|<|T|$. This Hall deficit for unused groups
must still charge the raw traces of groups in $I$. Their
**unchosen** owners may contribute to SF12 even though their outputs
are unavailable for a new matching. The chosen owner misses every
target of $T$ by ET6. All effective owners in its identical
parent-and-phase bucket also miss $T$. If that bucket has size
$c_s(\eta_s)$, the extra raw charge is at most
$\sum_{s\in I,e_s>0}(e_s-c_s(\eta_s))\le2|I|$.
Zero-effective groups contribute no admissible raw charge; their blocked
long owner remains in $\mathcal B_T$. Consequently

$$
\sum_{m\in T}L_m+|\mathcal B_T|+2|I|\ge3|T|+3.
\tag{ET9}
$$

Dropping this committed-group cost would mix raw coverage with the
restricted choice interface.

## 6. Weighted capacities do not replace the exception plan

The exception-plan quantifier in ET6 cannot be removed using only
capacities of target subsets, even when each parent has a double-hit
graph consisting of one edge. Consider this abstract incidence system,
with targets $a_0,a_1$ at one parent and $b_0,b_1$ at another:

| Group | First owner hits | Second owner hits |
| --- | --- | --- |
| $s_0$ | $\{a_0\}$ | $\{a_1\}$ |
| $s_1$ | $\{a_0,a_1\}$ | $\{b_0,b_1\}$ |
| $s_2$ | $\{b_0\}$ | $\{b_1\}$ |

Each owner hits at most two targets, the options of each group are
disjoint, and each two-target output lies within one parent. Thus the
double-hit graph has matching number one at each parent. In particular,
this is different from the forbidden crossing square in section 3,
whose two disjoint collision edges lie at the same parent.

No common owner assignment covers all four targets. If $s_1$ chooses
its first output, the two $b$-targets must both be covered by $s_2$,
which can cover only one. Its second output leaves the same obstruction
at the two $a$-targets. This argument exhausts the middle group's
two choices.

Nevertheless every nonnegative real weighted capacity test succeeds. For
real weights $w_m\ge0$, write $w(A)=\sum_{m\in A}w_m$ and let $H_{s,i}$
be the table's hit sets. Every target belongs to exactly two of its
six options, so

$$
\sum_{s=0}^2\max_{i\in\{0,1\}}w(H_{s,i})
\ge\frac12\sum_{s=0}^2\sum_{i=0}^1w(H_{s,i})
=\sum_m w_m.
\tag{ET10}
$$

Taking $w=\mathbf1_T$ proves every target-subset capacity inequality.
Equivalently, choose each option with probability one half: every
target has expected coverage multiplicity one. That fractional
statement does not supply a single assignment covering all targets.

The choice $\mathcal E=\{a_0,b_0\}$ meets both double edges. The
ordinary targets $a_1,b_1$ have a Hall matching before any exception
plan is fixed. But every plan covering $\mathcal E$ leaves a Hall
deficit among its still-unhit ordinary targets and unused groups, by
the exact equivalence in ET6 and the preceding impossibility. Thus
Hall for the original ordinary graph and weighted capacities for all
targets together still miss the required compatibility.

This reuses the distinction between fractional coverage and integral
group choices. It supplies an obstruction to an abstract inference,
not an arithmetic covering system: no literal CRT realization, complete
original cover, divisor-closed source or EB1-minimality is asserted.
Those additional hypotheses could exclude this incidence pattern;
that requires an actual arithmetic argument. The example supplies no
upper bound for the actual nondivisor loads in ET8--ET9.

## 7. What this reduction leaves to prove

The actual problem is now sharper for the single-output top route:
find one compatible plan for at most twelve exceptions and establish
Hall expansion in the remaining actual graph. A deficient set forces
the nondivisor, deep-divisor, blocked-owner and committed-group charges
in ET8--ET9; no upper bound reversing those inequalities is supplied.

Within Report858 section 8's support-through-113 envelope, the total
original-q tail at heights $j\ge5$ costs at most
$\varepsilon=9368025/(28\cdot113^4)<0.002052$ per target, uniformly
on its actual $Z_m$. Define the remaining load

$$
L_m^{<5}=\Lambda_m^{q,\,2\le j<5}
       +\min_{w\in Z_m}N_m^{q,\,1\le j<5}(w).
$$

Both divisor and nondivisor high tails are included in the same
$\varepsilon$. Applying the original covering inequality at each
point before minimizing, the same counting argument as ET7--ET9 gives

$$
\sum_{m\in T}L_m^{<5}+|\mathcal B_T|+2|I|
\ge(3-\varepsilon)|T|+3
\tag{ET11}
$$

for an unused-group Hall-deficient $T\subseteq\mathcal O_\eta$.
Before any exception plan, omit the $2|I|$ term. Thus a contradiction
can be sought entirely in the actual first four q-layers, with the
certified tail debit shown explicitly. Those low-layer upper bounds
and the compatible exception plan are still missing.

Cooperative output packets and the paid residual hulls of Report858
can succeed beyond this route. Their larger hit relations cannot simply
inherit the two-target cap or the twelve-exception theorem.

The arithmetic restrictions are ordinary independently reviewed
consumers of Report385 DR8 and GLC1--GLC3, with Report858's fixed
geometry and payment. The exact Hall equivalence and deficient-set
arithmetic compile as transient Lean applications using only standard
axioms. They assume the single-output uniqueness premise on ordinary
targets; the arithmetic twelve-exception theorem is not formalized by
those checks. The four-target example is also checked transiently:
no common assignment, disjoint same-group options, the half-mixture
identity and ET10 for every real weight vector, and the Hall deficit
after every exception-covering partial plan. These checks likewise
use only standard axioms. ET11's scalar consequence of the truncated
covering and raw-capacity inequalities also compiles separately; its
arithmetic source premises retain Report858's verification boundary.
No retained wrapper declaration is introduced.
No new frozen declaration or unrestricted resolution is claimed.
