[Index](../../../marked_head_profile.md) · [Owner cores](857-owner-conflict-cores-and-actual-donor-extraction.md) · [Owner laws](856-coherent-owner-laws-and-bounded-relative-certificates.md) · [Private hulls](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md)

# Paid residual hulls and balanced sibling extraction

A fixed covered base permits a stronger donor test: the selected output
need only cover the part of an inverse outside that base. The exact
single-output test uses the congruence hull of this actual residual,
which can have more prime factors than the original target modulus.
Thus the earlier proper-divisor restriction does not apply to these
assisted hits.

There is also a useful common geometry. After excluding prime-power
bad cofactors, one can choose six short leaves with distinct modulo-27
parents. Each then has six long sibling leaves. In this geometry short
owners contribute nothing outside the fixed covered base. Whole coverage
on the siblings yields an actual supplier inequality and a sufficient
condition for donors that work under every choice from fixed owner
domains. The required uniform bound on nondivisor suppliers is still
missing. Neither the height-two branch nor unrestricted Erdős #7 is
resolved.

## 1. Fixed base and exact short-region restriction

Use Report857's hypothetical globally EB1-minimal whole cover,
$q=113$, $H_3=2$, $Q=9q^GW$, $(W,3q)=1$, and one fixed common
source with all literal phases and deeper dictionaries. The carrier is
$\mathcal X=\mathbb Z/3^{3G+2}\mathbb Z\times\mathbb Z/W\mathbb Z$.
The original good and bad shallow groups are $\mathscr G,\mathscr B$.
For an initial good group $s$, $A_s$ is its nonempty admissible domain
of owners of $27s$. Every choice has a fixed legal completion to the
other outputs. All choices below are made once per group.

Retain exactly the base from Report857 CD3:

$$
H=R_{\rm ret}\cup\bigcup_{s\in\mathscr G,j}B_{s,j}.
\tag{SF1}
$$

The union includes all nonempty raw shallow good inverses, at depths
four and five. It does not include deep inverses or newly rescued bad
groups. Every full initial good allocation, together with retained
q-free outputs, contains $H$.

Let $S$ be the union of the selected depth-four leaves, crossed with
the whole $W$ coordinate. Let $F_\theta$ be the union of **all** outputs
of the initial good groups for an owner assignment $\theta$, and let
$P_\theta$ consist of all their $27s$ outputs. Then

$$
(R_{\rm ret}\cup F_\theta)\cap S
   =(H\cup P_\theta)\cap S.
\tag{SF2}
$$

Indeed, a depth-four owner receiving $81s$ has exactly its raw inverse.
A depth-five owner receiving $81s$ or $243s$ misses every selected
short leaf: its depth-four ancestor cannot meet such a leaf without
violating prefix-freeness. Every remaining output is in $P_\theta$.
Conversely the full allocation contains every raw good inverse and all
of $P_\theta$. Adding the same retained set proves SF2.

This equality is not asserted outside $S$, for a partial designated
packet, for deep outputs, or for outputs of newly rescued bad groups.
It uses one cofactor-independent global prefix code.

## 2. The legitimate residual mask and its exact hull

Remove the automatic targets having some $B_{m,i}\subseteq H$.
For every remaining target, all three sets

$$
R_{m,i}=B_{m,i}\setminus H
\tag{SF3}
$$

are nonempty. Define the assisted hit set

$$
\widehat J_{ms}
=\{a\in A_s:\exists i,\ R_{m,i}\subseteq E_{s,a}\},
\qquad
E_{s,a}=[\ell_{s,a}]_{27}\times[r_{s,a}]_s.
\tag{SF4}
$$

If one owner assignment hits every remaining target, each omitted
whole inverse is contained in $H\cup P_\theta$. The same full initial
good allocation already pays for $H$. The automatic omissions and these
assisted omissions therefore satisfy the original simultaneous payment
rule. The contradiction with EB1 gives

$$
\forall\theta\ \exists m\in\mathscr B_{\rm res}\ \forall s\in\mathscr G,
\quad\theta_s\notin\widehat J_{ms}.
\tag{SF5}
$$

Consequently Report856's product-law inequality and Report857's local
minimal-core statements apply with $\widehat J$ in place of $J$.
In particular $J_{ms}\subseteq\widehat J_{ms}$. Several outputs may
still cover one residual jointly without any single-output hit; SF4
does not characterize all feasible packets.

This is a paid complement, as in Report385 PH1 and Report855 RO2.
Arbitrarily replacing a whole inverse by selected private points would
not justify it: that would leave their complement unpaid.

On a fixed selected short leaf $\ell$, there is a fixed set
$H_\ell\subseteq\mathbb Z/W\mathbb Z$ with
$H\cap(\ell\times\mathbb Z/W\mathbb Z)=\ell\times H_\ell$.
Retained q-free tests depend only on its old modulo-nine word and $W$;
the raw good inverses meeting it are precisely the short inverses on
that same leaf. Thus

$$
R_{m,i}=\ell_{m,i}\times K_{m,i},
\qquad K_{m,i}=[r_{m,i}]_m\setminus H_{\ell_{m,i}}.
\tag{SF6}
$$

For a nonempty $K=K_{m,i}$ choose one actual residue $w_0\in K$ and put

$$
\Gamma(K)=\gcd\bigl(W,\{w-w_0:w\in K\}\bigr).
\tag{SF7}
$$

Use representatives for one period. Changing representatives or the
base point preserves this gcd. Report385 PH3--PH4's divisibility test,
applied to this nonempty periodic set, gives

$$
m\mid\Gamma(K)\mid W,\qquad
K\subseteq[r]_s
\iff s\mid\Gamma(K)\ \text{and}\ r\equiv w_0\pmod s
\quad(s\mid W).
\tag{SF8}
$$

Together with matching modulo-27 parents, SF8 exactly tests membership
in SF4. It does not create a source, a phase or an admissible owner.
The gcd-hull argument is reused, not a new standalone theorem.
The old bound counting proper divisors of $m$ cannot bound assisted
donors: $s\mid\Gamma(K)$ need not imply $s\mid m$.

Nor can Report856's small **whole-coset** cover classification be
applied to a punctured $K$ without including $H_\ell$ in the liability.

## 3. A balanced prime-power-free code

In Report856's $110\times5$ array of final cells, any set of at least
224 surviving cells contains six cells in distinct rows, with at most
two in each column. To see this, duplicate each column and consider a
matching. If its maximum size were at most five, König's theorem gives
a vertex cover of size at most five. A lone copy of a column can be
discarded from that cover: the uncovered twin forces all its neighboring
rows to belong to the cover already. Hence the cover consists of $r$
rows and both copies of $t$ columns, with $r+2t\le5$. It covers at most

$$
110t+(5-t)r
\le110t+(5-t)(5-2t)\le223,
\qquad t\in\{0,1,2\}.
\tag{SF9}
$$

The three last bounds are 25, 122 and 223. Two full columns together
with the other three cells of one row attain 223 and permit no six-cell
selection. This sharpness example is an array, not an original cover.

The accepted height envelope leaves at most 284 nonunit prime-power
cofactors. Deleting their final cells leaves at least $550-284=266$.
We can therefore fix a balanced six-code avoiding all such bad groups;
up to 42 additional specified cofactors may also be excluded. All bad
cofactors then have at least two distinct prime factors. Excluding all
$\tau(m)\le5$ cofactors instead leaves only the lower bound 91, which
does not establish balancing.

Each safe old word has three modulo-27 parents. Reserve distinct
parents, above different old words, for the actual $q$ and $3q$
terminals. Choose the $3q$ word in its actual modulo-three phase.
At most two selected cells request any old word, so the six selected
short leaves can occupy different unreserved parents. Each of their
parents has six long sibling leaves. There are 105 long leaves in
total, of which 36 lie in these six sibling regions. If the actual
$9q$ digit $\gamma$ is not terminal, place it among the other 69 leaves.

Complete all remaining assignments and deeper dictionaries once by
Report388 SC469. Every nonempty continuing inverse at q-height $j\ge2$
has one ternary prefix of depth $3j+2$. No target-specific completion
is used.

## 4. Short choices are ineffective on the unpaid region

In this balanced completion, the parent of a short owner contains only
its own selected short leaf. Hence for every initial good short owner,

$$
E_{s,a}\cap S=B_{s,a}\subseteq H.
\tag{SF10}
$$

A long owner whose parent contains no selected short leaf also misses
$S$. Thus both types contribute nothing to $S\setminus H$.
For each initial good group, retain only its admissible long owners
under selected parents, if this set is nonempty. If it is empty, keep
any nonempty subset of its original admissible domain. Call these fixed
domains $\Omega_s$.

Every full assignment can be replaced by one in $\prod_s\Omega_s$
without decreasing the union of its $27s$ outputs on $S\setminus H$:
retain an effective chosen owner, and replace an ineffective one
arbitrarily in $\Omega_s$. Full good allocations still cover $H$.
This preserves both single-output and cooperative residual coverage.
It concerns absorption by **initial good outputs**; it makes no claim
about additional plans using rescued bad groups or deep outputs.

In particular, the unique long owner of a three-inverse group with two
short companions remains inadmissible. Domain restriction never changes
the original payment rule. SF10 fails when different selected short
leaves share a parent, so this reduction uses the common geometry of
section 3.

## 5. Whole coverage on six sibling leaves

For a bad $m$, let $C_m$ be the six long siblings of its top inverse
$B_{m,2}$, with old word $z_m$ and cofactor phase $r_m=r_{m,2}$.
Set

$$
Z_m=[r_m]_m\setminus
\bigcup_{\substack{3^as\ \mathrm{an\ actual\ q\!\text{-}free\ original}\\
\rho_{3^as}\equiv z_m\ (3^a)}}[\rho_{3^as}]_s.
\tag{SF11}
$$

A private point of the actual $9qm$ gives a member of $Z_m$.
For every $w\in Z_m$, all source points in $C_m\times\{w\}$ avoid
q-free originals. Only its old word and $W$ coordinate are needed;
the private point need not be in the source image.

Normalize ternary mass so that one depth-five cylinder has mass one.
For an actual original $n=3^aq^js$, let $\theta_m(n)$ be the mass of
its literal inverse on $C_m$ before imposing its cofactor congruence.
It is either zero or one if $j=1$, and either zero or $27^{1-j}$ if
$j\ge2$. This is a ternary source measure, distinct from Report857's
uniform original-q-tail measure with weights $113^{1-j}$.

For $1<s\mid m$, $s<m$, put

$$
k_{ms}=\sum_{a=0}^2\theta_m(3^aqs)
       \mathbf1_{\rho_{3^aqs}\equiv r_m\ (s)},
\quad 0\le k_{ms}\le3,
\tag{SF12}
$$

where absent originals contribute zero. Separate the rest into

$$
\begin{aligned}
\Lambda_m&=\sum_{\substack{n=3^aq^js\ \mathrm{actual}\\j\ge2,\ s\mid m}}
  \theta_m(n)\mathbf1_{\rho_n\equiv r_m\ (s)},\\
N_m(w)&=\sum_{\substack{n=3^aq^js\ \mathrm{actual}\\j\ge1,\ s\nmid m}}
  \theta_m(n)\mathbf1_{w\equiv\rho_n\ (s)},
\qquad N_m^*=\min_{w\in Z_m}N_m(w).
\end{aligned}
\tag{SF13}
$$

Integrating whole coverage over $C_m\times\{w\}$ gives

$$
6\le N_m^*+\Lambda_m+\sum_{1<s\mid m,\ s<m}k_{ms},
\qquad
\Lambda_m\le\frac{3\tau(m)}{26}(1-27^{1-G})
\le\frac{3\tau(m)}{26}.
\tag{SF14}
$$

No supplier is omitted. Q-free terms vanish by SF11. Shallow unit
cofactors are terminal or were placed away from these siblings. Shallow
cofactor-$m$ inverses are selected short leaves because $m$ is bad.
All other shallow divisor terms occur in SF12. All deep divisor terms,
including unit and $m$, occur in $\Lambda_m$; all nondivisor terms,
including deep ones, occur in $N_m$. The bound for $\Lambda_m$ sums at
most $3\tau(m)$ distinct originals per height against $27^{1-j}$.
Overlaps between traces are allowed in this covering-multiplicity bound.

## 6. Fixed capacities and simultaneous absorption

Let $J^{(2)}_{ms}$ consist of the admissible owners whose broad output
contains the whole top inverse. They must have $s\mid m$ and matching
phase and parent. In the chosen geometry they are long owners in
$C_m$: a short owner there would be on the target's own leaf, so the
corresponding original $3^aqs\mid9qm$ would intersect that target,
contrary to irredundancy.

For an initial good group having an effective admissible long owner,
let $e_s$ count all its admissible long owners under the six selected
parents, and put $\kappa_s=e_s-1$. For a three-inverse group whose
unique long owner is inadmissible, put $\kappa_s=1$ if that long owner
is under a selected parent, and zero otherwise. Set all other capacities
to zero, including inactive and bad groups. These escape allowances
are fixed for the whole source, independently of the target; they are
not Report857's intersection-based matching capacities.

Define

$$
\mathcal R_m=\{s:1<s\mid m,\ s<m,\ s\in\mathscr G,
                       \Omega_s\subseteq J^{(2)}_{ms}\}.
\tag{SF15}
$$

For every proper-divisor group,
$k_{ms}\le\kappa_s+\mathbf1_{s\in\mathcal R_m}$.
If it has effective admissible long owners, every counted hit belongs
to their fixed domain; without an all-option hit at most $e_s-1$ count.
If its unique long owner is blocked, at most one counts and is charged
to $\kappa_s$. All other groups contribute zero. Thus

$$
|\mathcal R_m|\ge
\max\left\{0,\left\lceil
6-N_m^*-\Lambda_m-\sum_{1<s\mid m,\ s<m}\kappa_s
\right\rceil\right\}.
\tag{SF16}
$$

In particular, if

$$
N_m^*+\Lambda_m+\sum_{1<s\mid m,\ s<m}\kappa_s<6
\quad\text{for every bad }m,
\tag{SF17}
$$

then every assignment from the same $\prod_s\Omega_s$ absorbs every
bad top inverse. Witness donors may differ with $m$, but none changes
its chosen owner. The existing payment gives an EB1 contradiction.
The weaker capacities using all long owners are also valid: $L_s-1$
for admissible-long domains, one for a blocked unique long owner, and
zero otherwise. The effective-parent capacities above are no larger.

For a semiprime $m=pr$, $p\ne r$, the deep term is at most $6/13$
and the two proper-divisor capacities total at most four. Hence
$N_m^*<20/13$ suffices for an all-option donor. This is a conditional
threshold, not an established bound on $N_m^*$.

Every hypothetical cover must therefore leave at least one exceptional
bad target failing SF17 for each such common completion. Only those
exceptional targets need enter the failure inequality for an owner law
supported on $\Omega_s$: all other targets have failure probability
zero. Assisted residual hits from SF4 can further reduce this failure
probability, but their extra incidence has no unconditional lower bound
here.

### Actual parent and phase buckets sharpen the existence criterion

For $e_s>0$, partition the effective owner domain by its literal pair
$(\text{modulo-27 parent},\text{phase modulo }s)$. Let $c_s(b)$ be the
sizes of its nonempty buckets, and set

$$
\beta_s=\max\bigl(\{c_s(b):c_s(b)<e_s\}\cup\{0\}\bigr).
\tag{SF18}
$$

For an effective domain the count $k_{ms}$ is exactly the size of the
bucket matching the top target's parent and phase, or zero if there
is no such bucket. This bucket is the entire domain exactly when
$s\in\mathcal R_m$. Thus

$$
k_{ms}\le\beta_s+(e_s-\beta_s)\mathbf1_{s\in\mathcal R_m}.
\tag{SF19}
$$

In the blocked unique-long case use $\beta_s=\kappa_s$ and coefficient
zero; in all other zero-effective cases both terms are zero. With
these conventions, the whole-cover bound becomes

$$
6-N_m^*-\Lambda_m-\sum_{1<s\mid m,\ s<m}\beta_s
\le\sum_{s\in\mathcal R_m}(e_s-\beta_s)
\le3|\mathcal R_m|.
\tag{SF20}
$$

Consequently a strictly positive left side forces an all-option donor.
Here $\beta_s\le\kappa_s$, so the **existence threshold** is at least
as permissive as SF17. The cardinality bound obtained by division by
three need not improve SF16.

Only a group with a single nonempty bucket can belong to $\mathcal R_m$;
then $\beta_s=0$ and all its permitted broad outputs are identical.
Three owners in three different buckets instead have $\beta_s=1$.
Comparable-original disjointness implies that two owners with the same
parent and phase use different long leaves. It does not bound a bucket
by two: three distinct first q-digits are allowed. Their equal broad
outputs can be identified for owner selection, but the three actual
raw traces must retain their multiplicity in SF12.

## 7. The same shallow test on full original q-tails

One can also test the actual original cover directly. Let $\mathcal D_m$ be the
six actual first q-digits assigned to $C_m$. For each $w\in Z_m$, fix
the old word $z_m$ and $W$ coordinate $w$, allow the first q-digit in
$\mathcal D_m$, and use the full uniform original q-tail. Give each first-digit
cell mass one. This has total mass six and uses one original CRT model;
the points need not lie in the chosen source image.

The literal ternary and first-digit tests give the coefficient

$$
\theta_m^{q}(3^aq^js)
=\mathbf1_{\rho_{3^aq^js}\bmod q\in\mathcal D_m}
 \mathbf1_{\rho_{3^aq^js}\equiv z_m\ (3^a)}\,113^{1-j}.
\tag{SF21}
$$

Define $\Lambda_m^q,N_m^q(w),N_m^{q,*}$ by SF13 with these
coefficients. All shallow counts $k_{ms}$ are unchanged. All q-free,
shallow-unit and shallow-target exclusions still hold. Therefore

$$
6\le N_m^{q,*}+\Lambda_m^q+\sum_{1<s\mid m,\ s<m}k_{ms},
\qquad
\Lambda_m^q\le\frac{3\tau(m)}{112}(1-113^{1-G})
\le\frac{3\tau(m)}{112}.
\tag{SF22}
$$

This is Report857's original-q-tail counting applied to six fixed
digits. It changes neither the initial geometry nor the actual owners.
SF16--SF20 consequently hold with the q-superscripted loads too.
For a semiprime, $\Lambda_m^q\le3/28$, so
$N_m^{q,*}<53/28$ suffices for an all-option donor under the coarse
allowance sum of four.

The divisor-load cap is smaller than its ternary counterpart, but
SF22 does not dominate the whole ternary criterion pointwise. A deep
original whose later digits were excluded by the continuing dictionaries
has zero source-inverse mass and can have positive full-q-tail mass.
Both the divisor and nondivisor loads must be calculated in the same
measure. No separate optimized source or owner choice is combined
across targets in this argument.

## 8. Remaining estimate and verification scope

The unresolved step is to control the actual nondivisor load on the
nonempty q-free-uncovered sets $Z_m$, together with the capacities,
for enough targets in one common source. A private point proves
$Z_m\ne\varnothing$; it gives no upper bound for $N_m^*$.
Any probability law supported on $Z_m$ bounds the minimum by its
expected load, but it still needs quantitative congruence-query bounds.
An unconditioned uniform or distortion law cannot be used if it charges
points outside $Z_m$. Report385's survivor-support analysis already
identifies this missing conditional reserve.

König/Hall supplies SF9; existing gcd and congruence results supply SF8;
the paid-complement and owner-obstruction arguments reuse the cited
reports. Exact transient Lean applications verify the nonempty residual
gcd-hull containment test, the paid-complement set identity, the original
three-owner admissibility/allowance table, its sum and strict nonemptiness
implications, and the simultaneous-choice implication. These checks use
only standard axioms and retain no new wrapper declarations.

The balanced-source restriction and supplier partition are
ordinary mathematical deductions with independent source/geometry and
owner-capacity checks. They are not a full Lean proof of the original
covering-system implications. The refined bucket inequality is also
checked over the complete finite model of at most three owners and
four bucket labels, including an empty matching bucket. Its weighted
sum, positive-excess implication and the new q-tail numerical constants
compile separately. Arithmetic source existence is not inferred from
these abstract capacity checks.

No new frozen mathematical declaration, atom coverage or resolution of
the unrestricted problem is claimed by this report.
