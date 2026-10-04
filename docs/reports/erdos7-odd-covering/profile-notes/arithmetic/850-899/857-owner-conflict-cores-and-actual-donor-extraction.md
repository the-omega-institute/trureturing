[Index](../../../marked_head_profile.md) · [Private fibres](851-private-fibre-shallow-supplier-cost.md) · [Paid packets](853-paid-packet-absorption-and-residual-moment.md) · [Permanent plans](855-permanent-owners-and-small-relative-packets.md) · [Owner laws](856-coherent-owner-laws-and-bounded-relative-certificates.md)

# Owner conflict cores and actual donor extraction

The remaining extraction problem is to obtain enough actual compatible
donors in one fixed geometry to contradict Report856's owner obstruction.
Numerical divisibility, a large divisor inventory and pointwise private-fibre
supply do not provide those donors. Literal phase agreement, a compatible
ternary parent and permanent-owner admissibility must hold together.

There are two useful restrictions on this problem. First, inverses already
covered by retained originals and raw good inverses can be removed before
forming the obstruction. Second, a minimal remaining obstruction has no
autarky: no partial owner assignment satisfies every target it touches.
This gives local probability inequalities and strict weighted incidence
expansion. The weights depend on intersections of actual owner hit sets;
the domain-size weights from digit-disequality SAT cannot be used blindly.

On the arithmetic side, one projected private region gives a sufficient
donor test: the combined mass of deep suppliers, nondivisor shallow
suppliers and inadmissible shallow owners must be below one. The strict
bound is not established here. These results neither resolve the
height-two branch nor unrestricted Erdős #7.

## 1. One source, actual inverses and permanent owners

Assume the hypothetical globally EB1-minimal distinct odd whole cover of
[Report853](853-paid-packet-absorption-and-residual-moment.md#1-one-actual-family-and-one-common-code),
with $q=113$, $H_3=2$, common period $Q=9q^GW$ and $(W,3q)=1$.
Fix one lawful six-code,
its initial leaves, every deeper dictionary and all literal phases.
The common carrier is

$$
\mathcal X=\mathbb Z/3^{3G+2}\mathbb Z\times\mathbb Z/W\mathbb Z.
$$

The source preserves the old modulo-nine and full $W$ coordinates.
Each nonempty shallow inverse, meaning an original of q-height one,
is the whole cylinder

$$
B_{m,i}=[\ell_{m,i}]_{3^{d_{m,i}}}\times[r_{m,i}]_m,
\qquad i\in\{0,1,2\},\quad d_{m,i}\in\{4,5\}.
\tag{CD1}
$$

The original is $3^iqm$, with $m>1$ and $(m,3q)=1$; its
$m$-phase is unchanged. There is no private-region mask in CD1.
A bad group has all three inverses nonempty and of depth four.
Every other group is good; active good groups have a nonempty inverse.
Write $\mathscr B$ and $\mathscr G$ for these fixed sets.

For $s\in\mathscr G$, let $A_s$ be Report856's admissible owners
of the $27s$ output. Each domain is nonempty and has size at most
three. With three nonempty inverses, an admissible designation leaves
a long inverse for $243s$; the unique long owner with two short
companions is not admissible. Fix a legal completion of each designation
to the other group outputs. All owner choices use the same source.

Set

$$
E_{s,a}=[\ell_{s,a}]_{27}\times[r_{s,a}]_s,\qquad
J_{ms}=\{a\in A_s:\exists i,\ B_{m,i}\subseteq E_{s,a}\}.
\tag{CD2}
$$

One owner is chosen once per donor, shared by all its targets.
An edge requires containment of one whole inverse, including actual
phase agreement and the same modulo-27 parent. Separate partial hits
do not create an edge. The clause for target $m$ is
$C_m(\theta)\iff\exists s,\theta_s\in J_{ms}$.
Report853's simultaneous payment implies that these clauses cannot all
hold: such an assignment would improve the same original EB1 family.

## 2. A fixed covered base before owner selection

Let $R_{\rm ret}$ be the union of retained q-free originals on
$\mathcal X$, and define

$$
H=R_{\rm ret}\ \cup\!
\bigcup_{\substack{s\in\mathscr G\\B_{s,j}\ne\varnothing}}B_{s,j}.
\tag{CD3}
$$

This is a set of covered points, not a collection of new output labels.
Every full legal good-group allocation contains each raw inverse in its
assigned enclosure, so its union with the retained originals contains
$H$, independently of the permanent designations. The full allocation
may use $27s,81s,243s$. The designated $27s$ packet alone need not
contain $H$. Raw shallow inverses here include both depths four and five;
raw inverses of originals with q-height at least two are not in CD3.

Let $\mathscr B_{\rm auto}$ consist of bad groups with some whole
$B_{m,i}\subseteq H$, and put
$\mathscr B_{\rm res}=\mathscr B\setminus\mathscr B_{\rm auto}$.
Fix an omission for every automatic group. Its other two short inverses
can receive $27m$ and $81m$ under the existing payment rule.
If an owner assignment singly hits every residual target, these hits and
the fixed automatic omissions absorb all bad groups simultaneously.
Thus Report856's obstruction and probability inequality restrict to

$$
\sum_{m\in\mathscr B_{\rm res}}
   \prod_{s\in\mathscr G}(1-\mu_s(J_{ms}))\ge1
\tag{CD4}
$$

for every product of owner laws. Donors remain the original active
good groups. Using outputs of automatic groups as additional donors
requires fixing their omission and output plans, as in Report855's RO2.
No lower bound on $|\mathscr B_{\rm auto}|$ is supplied here.

There is a precise individual-containment restriction. Suppose a raw
good inverse $B_{s,j}$ contains a bad short inverse $B_{m,i}$.
Prefix disjointness forces the same depth-four initial leaf: a different
leaf, including any long initial leaf, cannot contain it. Hence the
actual first q-digit and old word $z$ agree. Full $W$-coset containment
gives $s\mid m$ and $r_{s,j}\equiv r_{m,i}\pmod s$.
The groups differ, so $s$ is a proper divisor. If $j\le i$, the
nonempty inverses also give both literal ternary phases from $z$,
and the original class of modulus $3^iqm$ lies inside the distinct
original class of modulus $3^jqs$. Irredundancy forbids this. Therefore

$$
j>i.
\tag{CD5}
$$

The same necessary rule holds for a single retained q-free class
of modulus $3^js$ containing $B_{m,i}$: containment gives $s\mid m$
and compatible phases, and $j\le i$ would imply original-class
containment. Sharing only a modulo-27 parent is insufficient for raw
containment; it can suffice after a paid enclosure is broadened.

There is a stronger union statement for the top inverse:

$$
B_{m,2}\not\subseteq H\qquad(m\in\mathscr B).
\tag{CD6}
$$

Choose an actual private point $x$ of the original $9qm$. Its first
q-digit is $c_2(m)$, its old word is $z_m$ and its $W$-coordinate
is some $w$. The bad top inverse is nonempty, so its selected leaf
has old word $f(c_2(m))=z_m$. Choose an output $y$ on that leaf
with $W$-coordinate $w$. Then $y\in B_{m,2}$, and its common
source has the same first q-digit, old word and $W$-coordinate as $x$.
Every membership test in CD3 depends only on those coordinates.
Membership of $y$ in $H$ would therefore put $x$ in a different
actual original, contradicting privacy. Higher q-digits do not enter
these tests, so no surjectivity onto higher source digits is needed.

For $i<2$, the selected old word cuts out only a slice of the original
$3^iqm$ class; irredundancy need not prevent that slice's coverage.
For $i=2$ the slice is the entire original $9qm$, which explains CD6.
Broadened paid enclosures and deep transformed outputs are outside this
exclusion. Nor is $H$ asserted to be the maximal set covered by every
possible full good allocation.

## 3. Minimal cores and local owner obstructions

Choose an inclusion-minimal unsatisfiable target family
$F\subseteq\mathscr B_{\rm res}$. Recompute its donor support:

$$
S_F=\{s:\exists m\in F,\ J_{ms}\ne\varnothing\},\quad
N(T)=\{s:\exists m\in T,\ J_{ms}\ne\varnothing\},
$$
$$
N_F(U)=\{m\in F:\exists s\in U,\ J_{ms}\ne\varnothing\}.
\tag{CD7}
$$

A partial assignment $\eta$ on $U\subseteq S_F$ is an autarky
if it satisfies every target in $N_F(U)$ using donors in $U$.
Deleting all these touched targets preserves satisfiability: remaining
targets have no incident donor in $U$, so a solution of the remainder
extends with the same $\eta$. Satisfying only a selected part of the
touched family does not justify deletion. This preserves the fixed
geometry and owner meanings, but need not preserve a uniform measure.

There is no autarky on a nonempty $U$. Otherwise minimality supplies
a solution of the proper untouched target family, which combines with
the autarky to satisfy $F$. Equivalently,

$$
\forall\varnothing\ne U\subseteq S_F\ \forall\eta\in\prod_{s\in U}A_s,
\quad\exists m\in N_F(U)\ \forall s\in U,\ \eta_s\notin J_{ms}.
\tag{CD8}
$$

In particular, each active donor's nonempty incident hit sets have empty
total intersection. No clause in $F$ has $J_{ms}=A_s$: such a clause
is a tautology. Hence no singleton owner domain is active in the core,
and every active donor touches at least two targets. If the core is one
empty clause, $S_F$ is empty and donor restrictions are vacuous.

Under arbitrary independent laws $\nu_s$ on donors of $U$, the
miss events in CD8 cover the owner product. The existing union bound
and coordinate product formula give

$$
\sum_{m\in N_F(U)}\prod_{s\in U}(1-\nu_s(J_{ms}))\ge1.
\tag{CD9}
$$

Only donor coordinates are independent; target miss events need not be.
For uniform laws, if $D_{m,U}=|\{s\in U:J_{ms}\ne\varnothing\}|$,
then $\sum_{m\in N_F(U)}(2/3)^{D_{m,U}}\ge1$.
This restricts every nonempty partial donor set of the same core.
It does not supply a lower bound on its actual incidence.

## 4. Matching capacities must follow actual intersections

For $s\in S_F$, let $r_s$ be the smallest number of distinct
incident target labels whose hit sets have empty intersection, and put
$\kappa_s=r_s-1$. CD8 makes $r_s$ finite. Any at most $\kappa_s$
incident requests share a hitting owner. This is the largest uniform
local capacity with that guarantee, although some larger compatible
families can still be served. Since every hit set is nonempty, and
one excluding set per owner suffices to empty the intersection,

$$
1\le\kappa_s\le |A_s|-1.
\tag{CD10}
$$

Keep these capacities fixed from $F$, and define
$w(U)=\sum_{s\in U}\kappa_s$ and
$\delta(T)=|T|-w(N(T))$. Then

$$
\delta(T)<\delta(F)\quad(T\subsetneq F),\qquad
|F|\ge1+\sum_{s\in S_F}\kappa_s,
\tag{CD11}
$$
$$
|N_F(U)|\ge1+\sum_{s\in U}\kappa_s
\quad(\varnothing\ne U\subseteq S_F).
\tag{CD12}
$$

For the proof, choose $T\subseteq F$ maximizing $\delta$.
For $R\subseteq F\setminus T$, comparison with $T\cup R$ gives

$$
|R|\le w(N(R)\setminus N(T)).
$$

Replace each donor outside $N(T)$ by $\kappa_s$ distinct slots.
This is Hall's condition for matching every target outside $T$ to
an incident slot. At a donor, the assigned at most $\kappa_s$ requests
share one owner; choose it. The resulting assignments satisfy all
targets outside $T$ using donors that touch no target in $T$.
If $T$ were proper, its solution supplied by minimality would combine
with these assignments to satisfy $F$. Thus every maximizer is $F$.
Comparison with $\delta(\varnothing)=0$ proves CD11.

For CD12, put $T=F\setminus N_F(U)$. Then
$U\subseteq S_F\setminus N(T)$, and CD11 gives
$|N_F(U)|>w(S_F\setminus N(T))\ge w(U)$.
Conversely, CD12 implies the strict part of CD11 by setting
$U=S_F\setminus N(T)$; if this is empty, the deficiency difference
is simply $|F\setminus T|>0$. These are equivalent graph restrictions
at the fixed capacities. Taking all capacities equal to one gives
$|F|>|S_F|$ and strict expansion $|N_F(U)|>|U|$.

For domains of size at most three, $\kappa_s=2$ exactly when the
domain has size three and every nonempty incident hit set has size two.
All three different pairs must occur, since their total intersection is
empty. Otherwise $\kappa_s=1$: a singleton hit set has an incompatible
partner, and on a two-element domain every proper nonempty set is a
singleton. Thus actual hit-set data can sharpen the unweighted bound.

Blind domain weights are false. For $x,y\in\{0,1,2\}$, the three
clauses $(x=i)\lor(y=i)$, $i=0,1,2$, are minimally unsatisfiable:
two coordinates select at most two values, while any two clauses are
satisfiable. All owners are useful and pairwise undominated. There are
three targets and two donors, both with $\kappa=1$; the unsupported
domain-weight bound would require $3\ge1+2+2$.

Minimal unsatisfiability also does not mean Hall-minimality. On one
three-value variable, $x\ne0,x\ne1,x\ne2$ form a minimal core,
but any two clauses are satisfiable and already Hall deficient.
A deficient subset need not itself be unabsorbable: one common owner
can hit several targets. Matching is a sufficient allocation mechanism,
not a physical limit on how many inverses an output can contain.

## 5. A donor test on one projected private region

Let $m$ be any bad group. Use its actual top original $T=9qm$,
with first q-digit $c=c_2(m)$, old word $z$, cofactor phase $r$
and depth-four inverse $B$. Let $p$ be
that inverse's modulo-27 parent. Every original has the unique form
$n=3^a q^e s$, where $0\le a\le2$ and $(s,3q)=1$.

Let $X$ be the projection modulo $9W$ of the complete private region
of $T$. It is nonempty, every point has word $z$ and residue $r$
modulo $m$, and every point avoids all original q-free classes.
Projection may forget which q-tail was private; these three properties
survive because their tests factor through $9W$. Choose one probability
law $\nu$ supported on $X$. Uniform measure on the entire target
cofactor coset is not automatically such a law.

Choose a nonterminal digit
$d\notin\{c_0(m),c_1(m),c_2(m),\alpha,\beta,\gamma\}$ whose
initial leaf lies under $p$. The leaf may be short or long, but its
old word is $z$. Give the original q-cell $d\pmod q$ a uniform
q-tail, independently of $\nu$. This measures original points; it
does not change their phases or replace the fixed code. For an original
with first q-digit $d$ and $e\ge1$, set

$$
v_n=\nu\{x:x\equiv\rho_n\pmod{3^as}\}.
\tag{CD13}
$$

Its cell mass is exactly $q^{1-e}v_n$. Q-free originals have mass
zero by private-region avoidance, and other first q-digits have mass
zero. Every q-height remains present in this calculation.

For a shallow original with $s\mid m$, $v_n$ is zero or one,
since all points of $X$ have the same old word and residue modulo $m$.
When $v_n=1$, its literal phase agrees with $r$ modulo $s$ and
its continuing inverse is nonempty on the leaf for $d$. If its group
is good and its owner admissible, the shared parent and $s\mid m$
give $B\subseteq E_{s,a}$, hence an owner in $J_{ms}$ by PP11.
No unit-cofactor shallow original has digit $d$: their digits are
$\alpha,\beta,\gamma$. The exclusion of all three $c_i(m)$ also
removes every shallow original with $s=m$ from this cell.
Such donors therefore have $1<s<m$. Badness puts every $c_i(m)$
in the selected short-digit set $R$, so a long digit $d\notin R$
automatically avoids these three digits. A $C_1$ target, whose three
digits coincide, is a special case rather than a needed hypothesis.

Partition the remaining contributors to this same cell into

$$
\begin{aligned}
\mathrm{Deep}&:\ e\ge2,\quad\text{any }s;\\
\mathrm{Cross}&:\ e=1,\quad s\nmid m;\\
\mathrm{Blocked}&:\ e=1,\quad1<s<m,\ s\mid m,\quad
\text{group or owner inadmissible}.
\end{aligned}
$$

Blocked means not a good-group admissible designation in this fixed
code. Define

$$
\mathcal E_d(\nu)=\sum_{\mathrm{Deep}}q^{1-e}v_n
                 +\sum_{\mathrm{Cross}}v_n
                 +\sum_{\mathrm{Blocked}}v_n.
\tag{CD14}
$$

All original labels remain distinct in the sums, even when their
restrictions coincide. The sufficient extraction criterion is

$$
\mathcal E_d(\nu)<1\quad\Longrightarrow\quad
\exists s,\ J_{ms}\ne\varnothing.
\tag{CD15}
$$

If there were no donor, every shallow contributor outside Cross and
Blocked would have $v_n=0$ by the preceding containment test. Whole
coverage would then cover this entire measured q-cell using Deep,
Cross and Blocked, and the union bound would give $\mathcal E_d\ge1$.
More precisely, positive mass outside the union of those escape classes
already suffices. CD15 uses the stronger convenient sum condition;
overlap can prevent its necessity. It uses whole coverage on one actual
source, not counts taken at unrelated private points.

## 6. Fixed-parent limits and the minimal-bad exception

Suppose CD15 is established for $r$ distinct compatible digits in
this same geometry. A shallow cofactor group has at most three owners
and hence at most three actual first q-digits, so

$$
D_m\ge\lceil r/3\rceil.
\tag{CD16}
$$

Different projected private-region laws can certify individual digits:
the resulting literal hit sets still belong to one fixed geometry.
Changing the geometry between certificates would invalidate this count.
No useful value of $r$ is established here.

There are at most six other initial digit leaves under $p$. The target
occupies one of its three depth-four children. Each remaining child has
at most three depth-five initial leaves. Choosing a depth-five extension
of each other leaf injects them into these six slots by prefix
disjointness. A terminal or another short leaf only decreases the count.
The bound is attained geometrically by six long leaves, as in
[Report855's distinction between outputs and digit leaves](855-permanent-owners-and-small-relative-packets.md#outputs-are-not-digit-leaves).
Thus this particular distinct-digit argument has $r\le6$ and can
certify at most the lower bound two through CD16. It does not imply
$D_m\le2$: many donors can use one digit. Other target inverses,
parents or compatible owner families are outside this counting limit.

There is one useful way to remove Blocked. Require that $m$ be
divisibility-minimal among **all original bad cofactors** in the fixed
geometry. Choose $d$ at another selected short leaf under $p$,
retaining the exclusions of all three $c_i(m)$ and the unit digits.
Any contributing shallow proper-divisor owner has a nonempty short
inverse. Its group is active and cannot be bad by minimality; every
short owner of a good group is admissible. Therefore Blocked contributes
zero, and CD15 sharpens to

$$
\sum_{\mathrm{Deep}}q^{1-e}v_n+\sum_{\mathrm{Cross}}v_n<1
\quad\Longrightarrow\quad\text{an actual proper-divisor donor}.
\tag{CD17}
$$

Minimality only among residual targets, core targets or $C_1$ groups
is insufficient: a proper divisor outside that smaller family could
still be bad. A minimal original bad cofactor exists, but an eligible
short sibling need not exist. Both other short children can carry the
target's own $c_0(m),c_1(m)$, or there may be no other short leaf.
The private-word construction uses the top original; it does not
assert the corresponding private slice for a lower original.

Under one parent there are at most two other short leaves. Consequently
this short-digit version has $r\le2$ and CD16 certifies at most the
lower bound one. It neither proves that a usable sibling exists nor
bounds the actual number of donors sharing one digit.

## 7. What still obstructs extraction

For each fixed target and digit, CD14 is linear in $\nu$. Let
$d_d(x)$ be the sum of $q^{1-e}$ over Deep originals whose non-q
phase contains $x$, and let $c_d(x),b_d(x)$ count the Cross and
Blocked shallow originals containing $x$. These counts keep labels
distinct. Then $d_d(x)\ge0$, the two counts are nonnegative integers,
and $\mathcal E_d(\nu)=\mathbb E_\nu[d_d+c_d+b_d]$. Consequently

$$
\exists\nu\text{ on }X:\mathcal E_d(\nu)<1
\quad\Longleftrightarrow\quad
\exists x\in X:\ c_d(x)=b_d(x)=0,\quad d_d(x)<1.
\tag{CD18}
$$

Indeed, an average below one has a point below one. At such a point
either positive integer shallow count would already contribute at least
one. Conversely, the indicated point mass gives a successful law.
Equivalently, minimizing CD14 over all laws on the finite nonempty
$X$ is exactly minimizing $d_d+c_d+b_d$ over its points. Mixing can
reduce individual summands, but cannot repair a shallow escape at every
projected private point. The missing certificate is a point with no
active shallow escape and a deep contribution below one; the more precise
escape-union test of Section 5 can still succeed without CD18.

Report851 bounds deep inventory from below when shallow suppliers are
missing; CD15 needs an upper bound on the relevant escape contribution.
Those directions cannot be interchanged. Good-group membership alone
also does not remove a blocked unique long owner.

Original irredundancy excludes simultaneous phase agreement for
comparable numerical moduli. On a fixed non-q coordinate and one
first q-digit, active shallow non-q moduli $3^as$ are therefore
incomparable. This does not produce a phase-preserving downward map:
a numerical divisor has its own actual phase and can miss the fibre.
Changing the target q-digit removes the root agreement needed for
the original comparable-class exclusion. Neither large $\tau(m)$
nor maximality of a bad cofactor forces suppliers to divide it.

The existing noncover in
[Report852](852-protected-digit-inventory-gap-and-grouped-hulls.md)
makes this boundary explicit. Its ten palette primes are at least 61.
For nonempty palette sets $S$, let $m_S$ be their product; the
q-bearing original $3^aqm_S$ has tag

$$
t(a,1,|S|)=4+a+6(|S|-1)
\tag{CD19}
$$

at each prime in $S$. If a nonunit $m_T$ properly divides $m_S$, then
$\varnothing\ne T\subsetneq S$, and for any owners $a,b\in\{0,1,2\}$ the
tag difference is at least four and has absolute value below 61.
Thus the actual phases disagree modulo every palette prime in $T$.
These are all nonunit q-bearing cofactor groups; auxiliary originals
are q-free. No proper-divisor hit is possible, and a good donor cannot
have the same cofactor as a bad target. Hence $J_{ms}=\varnothing$
for every good/bad pair under every lawful completed fixed geometry.
The fixture has divisor closure, private points and eligible-cell
occupancy, but is not a whole cover and fails additional EB1 tests.
It diagnoses the weaker hypotheses, not the genuine whole-cover claim.

## 8. Reuse and verification boundary

The autarky and matching method is standard. The
[Kullmann source note](../../../../../../Library/Combinatorics/kullmann2011clausal.md)
records *Constraint satisfaction problems in clausal form*,
arXiv:1103.3693v1. Section 1.3.1 defines literals as $v\ne e$;
Section 1.4.1 defines autarkies; Lemma 1.9.4 gives unique maximum
deficiency; Corollary 1.9.9 gives the corresponding weighted Tarsi
bound; Lemma 1.11.1 characterizes matching surplus. Its domain weights
rely on disequality literals. CD10 instead supplies the capacity for
arbitrary actual hit sets. Report343 and Report385 already use these
methods for digit-disequality cores, and Report383 uses Hall for a
different arithmetic incidence relation. Those arithmetic hypotheses
do not transfer merely because the matching method is shared.

Pinned Mathlib supplies
`Finset.all_card_le_biUnion_card_iff_existsInjective'` in
`Mathlib/Combinatorics/Hall/Finite.lean`. An exact transient application
checks that a finite owner obstruction with nonempty dependent domains
has a nonempty Hall-deficient target subset. A separate transient check
verifies the assignment-patching implication from minimal obstruction
to CD8. Both have axiom closure
`[propext, Classical.choice, Quot.sound]`.
The finite rational-law averaging interface in CD18 was also checked,
assuming a nonnegative deep load and natural-number shallow counts;
its axiom closure is `[propext, Classical.choice, Quot.sound]`.
The three-clause countermodel to blind domain weights, exact numerical
tag separation in CD19 and $r\le6\Rightarrow(r+2)/3\le2$ were
compiled with axiom closure `[propext, Quot.sound]`.

These checks do not verify the arithmetic extraction map, private-point
lift, prefix-slot argument or full weighted-capacity proof. Those are
the ordinary arguments supplied above, using the existing common-source,
payment and finite probability interfaces. No new Lean declaration is
retained. The unresolved step is an actual same-geometry bound excluding
the escape union, or another compatibility certificate strong enough
to contradict the residual owner obstruction.
