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
domains. Within the support-through-113 envelope, a small-divisor
partition gives a uniform bound for all high-q suppliers. The required
bound on the remaining low-height nondivisor incidences is still missing.
Neither the height-two branch nor unrestricted Erdős #7 is resolved.

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

## 8. A uniform tail bound from small divisor witnesses

In the existing support-through-113 envelope, $W$ has at most 27
distinct prime factors. This additional premise is used throughout
this section; selecting $q=113$ alone would not imply it. No bound
on the exponents of those primes is needed here.

Two existing retained-pure repair capacities control all original
labels in one phase. For $r\mid W$ and $h=113r$, they are

$$
\begin{array}{c|c|c}
\tau(r)&\tau(h)&
\#\{n\text{ actual}:h\mid n,\ \rho_n\equiv c\pmod h\}\\ \hline
6&12&\le20\\
8&16&\le14.
\end{array}
\tag{SF23}
$$

These reuse Report385's
[retained-pure repair forest](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#15-retained-pure-powers-reduce-the-fresh-repair-forest),
whose layer counts also appear in its
[third-row table](../350-399/385-private-congruence-hulls-and-crossed-modulus-closure.md#24-separating-the-exact-cofactor3-controls-a-vacant-third-row).
The retained original 3- and 9-classes leave fifteen cells modulo 27.
With twelve cofactor divisors, repair twelve cells and then nine children
of the remaining three cells, using layers of sizes $(12,9)$. With
sixteen divisors, repair all fifteen cells at the first layer.
Every new modulus has ternary height greater than two and is fresh.
The repairs cover the entire phase $c\bmod h$ together with the retained
pure guards, including all integer lifts.

The respective repair counts are 21 and 15. Their modulus sums are
less than $324h$ and $81h$, since $\sigma(h)/h<3$ for these divisor
counts. Removing respectively 21 or 15 distinct odd multiples of $h$
costs at least $21^2h$ or $15^2h$. Both equal-count replacements strictly
decrease the modulus sum, giving SF23. The count includes every
ternary height and every q-height together, not a new allowance at
each height.

### Partition all cofactors before charging labels

Report856 already counts at most
$4\cdot27+\binom{27}{2}=459$ nonunit cofactors with at most five
divisors: they are $p,p^2,p^3,p^4$ or $pt$, with distinct primes
$p,t\mid W$. Every remaining cofactor contains a divisor from

$$
\mathcal R_6=\{p^5\}\cup\{p^2t:p\ne t\},\qquad
\mathcal R_8=\{ptu:p,t,u\text{ distinct}\},
\tag{SF24}
$$

retaining only divisors of $W$. Three distinct prime factors supply
a squarefree triple; exactly two require an exponent at least two;
one requires an exponent at least five. Assign one witness to each
rich cofactor by a fixed ordering. There are at most 729 witnesses
in $\mathcal R_6$ and 2925 in $\mathcal R_8$.

Fix a cofactor point $w$ and one of the six sibling q-digits. Every
contributing label assigned to $r$ lies in the single phase of $113r$
determined by this digit and $w\bmod r$. SF23 bounds the total number
of rich contributing labels by

$$
6(20\cdot729+14\cdot2925)=333180.
\tag{SF25}
$$

No factor three or geometric sum is added: all original heights are
already included in the phase capacities. A witness need not be a
donor, a nondivisor of $m$, or a divisor of a residual hull.
For the small-cofactor part, each triple $(a,j,s)$ specifies at most
one actual numerical label $3^a113^js$. There are three choices of $a$.
No factor six is needed: an original has only one first q-digit.

### Two measures, each with its own uniform error

Let $N^{(\lambda)}_{m,\ge J}(w)$ be the nondivisor load restricted
to $j\ge J$, where $\lambda=113$ means the original-tail coefficients
SF21 and $\lambda=27$ the fixed-dictionary coefficients SF13.
Use each measure separately. For $J\ge2$, every rich contributing
label has weight at most $\lambda^{1-J}$; sum the small-cofactor
inventory geometrically over the actual heights. Then

$$
N^{(\lambda)}_{m,\ge J}(w)
\le\left(333180+\frac{1377\lambda}{\lambda-1}\right)
       \lambda^{1-J}.
\tag{SF26}
$$

The unit cofactor is absent because $1\mid m$. The same partition
also bounds the **total** q-bearing load at these heights, including
divisor and unit cofactors. The rich part needs no change; the unit
adds at most three labels per height. Writing the total tail as
$T^{(\lambda)}_{m,\ge J}(w)$ gives

$$
T^{(\lambda)}_{m,\ge J}(w)
\le\varepsilon_{\lambda,J}:=
\left(333180+\frac{1380\lambda}{\lambda-1}\right)
       \lambda^{1-J}.
\tag{SF27}
$$

In particular the exact total-load errors satisfy

$$
\varepsilon_{113,5}
=\frac{9368025}{28\cdot113^4}<0.002052,
\qquad
\varepsilon_{27,6}
=\frac{4349970}{13\cdot27^5}<0.023320.
\tag{SF28}
$$

These bounds hold at every $w$, for every target and fixed lawful
common completion in the stated support envelope. They contain
neither $\tau(W)$ nor $\tau(m)$. The two proofs use their own
coefficients and assert no ordering of the two actual measures.

Uniformity preserves the error on any nonempty actual subset. If
$F(w)$ is either complete load and $F_{<J}(w)$ its literal truncation,
then for nonempty $A\subseteq\mathbb Z/W\mathbb Z$,

$$
\min_A F_{<J}\le\min_A F
\le\min_A F_{<J}+\varepsilon_{\lambda,J}.
\tag{SF29}
$$

Use a minimizer of the truncated load for the upper bound. This applies
on $Z_m$ and any nonempty paid residual cofactor set, without a new law
or conditional reserve. Restriction can still raise either minimum.

On $Z_m$, whole coverage therefore forces the total original-tail
load from $j\le4$ to be at least
$6-\varepsilon_{113,5}>5.997948$ at every point. The unbounded q-height
tail has a uniform small cost. The remaining low-height incidence,
its actual support and permanent owner choices are still needed;
a small tail does not make that low-height load small.

## 9. Uniform long-digit permutations do not give the coarse small-load test

This section uses an additional restriction on the common completion.
After fixing the two terminal digits and six selected short digits,
there are 105 digits assigned to long leaves. Fix one digit $\delta$
at a long position outside all 36 sibling positions, then uniformly
permute the remaining 104 digits over the remaining long positions.
If the actual $9q$ digit $\gamma$ is nonterminal, take $\delta=\gamma$.
If it is terminal, choose another long digit for $\delta$; the earlier
condition on $\gamma$ alone would not exclude this additional digit.
There are 69 outside long positions, so this restriction is possible.

Write $V$ for the resulting fixed 104-digit pool. Each selected parent's
six-digit set $\mathcal D_m$ is marginally a uniform six-subset of $V$.
The parents share one permutation; their digit sets are not independent.
The uniform tail bounds in section 8 need none of this extra contract.

For a semiprime bad target $m=pr$, with distinct primes $p,r$, let
$A_m\subseteq V$ consist of the first q-digits of actual shallow
originals $3^aqs$ with $1<s<m$, $s\mid m$, whose ternary test agrees
with $z_m$ and whose cofactor phase agrees with $r_m\bmod s$.
This eligible set is fixed before the long-digit permutation. There
are at most six such labels, three for each of $p$ and $r$, so
$|A_m|\le6$; several labels may have the same digit.

Let $h_m(d)$ be the original-tail mass of all deep divisor originals
at first digit $d$, with their literal ternary and cofactor phases
compatible with $z_m,r_m$. Include the unit and $m$ cofactors. The
numerical-distinctness count used in SF22 gives
$\sum_{d\in V}h_m(d)\le3/28$: at each $j\ge2$ there are at most
twelve compatible divisor originals, each contributing $113^{1-j}$
to one first-digit cell.
For $d\in\mathcal D_m\setminus A_m$, a point with $w\in Z_m$ has
no q-free, shallow unit, shallow own-$m$, or shallow proper-divisor
supplier in that first-digit cell. Coverage of its full original tail
therefore requires nondivisor union mass at least $(1-h_m(d))_+$.
Summing the six disjoint cells bounds the load sum, and does so before
minimizing over $w$:

$$
N_m^{q,*}(\mathcal D_m)
\ge\sum_{d\in\mathcal D_m\setminus A_m}(1-h_m(d))_+
\ge6-|\mathcal D_m\cap A_m|-\sum_{d\in\mathcal D_m}h_m(d).
\tag{SF30}
$$

In particular,

$$
N_m^{q,*}<53/28
\quad\Longrightarrow\quad |\mathcal D_m\cap A_m|\ge5.
\tag{SF31}
$$

The ternary trace criterion $N_m^*<20/13$ also requires five eligible
digits, using its deep divisor cap $6/13$ in place of $3/28$.
Five distinct eligible digits force one prime group to supply all
three of its shallow labels, as long inverses in the same parent and
same literal cofactor phase. Thus the coarse test demands that strong
coherent incidence; it is not necessary for every possible paid packet.

The marginal inclusion probability of every $d\in V$ is $6/104$.
Taking expectations in SF30, still permitting a different minimizing
cofactor point for each completion, gives

$$
\mathbb E[N_m^{q,*}]
\ge6-\frac6{104}\left(6+\frac3{28}\right)
=\frac{8223}{1456}>5.6476.
\tag{SF32}
$$

Enlarging $A_m$ to six digits if needed, the same necessary condition
gives the exact hypergeometric bound

$$
\Pr(N_m^{q,*}<53/28)
\le\frac{\binom65\binom{98}1+\binom66}{\binom{104}6}
=\frac{589}{1517381580}<3.882\cdot10^{-7}.
\tag{SF33}
$$

This excludes a low-expectation justification under this uniform
permutation law. It does not assert zero success probability, exclude
optimized common permutations, or limit the more permissive bucket,
masked or cooperative packet criteria.

## 10. Supported cofactor query laws have a necessary cost

For any probability law $\mu$ supported on the actual nonempty $Z_m$,
including the unit modulus in the sum, put

$$
\mathcal Q(\mu)=\sum_{s\mid W}\max_{\rho\bmod s}\mu([\rho]_s).
$$

Fix $z_m$, draw $w$ from this same $\mu$, and independently draw the
complete original q-coordinate uniformly. Every q-free original has
probability zero. Whole coverage and distinct numerical labels imply

$$
1\le\frac{3(1-113^{-G})}{112}\,\mathcal Q(\mu),
\qquad
\mathcal Q(\mu)\ge\frac{112}{3(1-113^{-G})}>\frac{112}{3}.
\tag{SF34}
$$

Indeed, an original $3^a113^js$ costs at most
$113^{-j}\mu([\rho_n]_s)$; sum over at most three ternary heights
and the finite positive heights $1\le j\le G$. For semiprime $m$,
the four divisors of $m$ each contribute exactly one to the query
norm because $\mu$ is supported on $[r_m]_m$. Thus its nondivisor
part exceeds $100/3$.

This is a necessary cost for phase maxima over all q-digits. It is
neither a lower bound on the actual six-digit nondivisor load nor a
construction of a supported law. A diffuse proposed query envelope
must pay this cost as well as establish its support. The pointwise
tail bound in section 8 constructs no cofactor law and remains valid.

## 11. Remaining estimate and verification scope

The unresolved step is to control the actual nondivisor load on the
nonempty q-free-uncovered sets $Z_m$, together with the capacities,
for enough targets in one common source. A private point proves
$Z_m\ne\varnothing$; it gives no upper bound for $N_m^*$.
Section 8 controls the entire tail above a fixed q-height, including
its nondivisor portion, with explicit truncation error. Any probability
law supported on $Z_m$ bounds the minimum by its
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

For section 8, transient Lean checks cover finite witness-fibre charging,
the geometric-sum estimate, the exact inventory and error constants,
and transport of a uniform pointwise error to minima on the same
nonempty set. The actual phase capacities reuse Report385; their
connection to the whole-cover source and the complete divisor-witness
classification are ordinary independently reviewed deductions here,
not a full kernel replay of SF23--SF29.

For sections 9--10, transient Lean checks verify the expected-minimum
implication from the stated pointwise and marginal premises, both
five-digit thresholds, the query-cost consequence and the displayed
exact constants. The actual-cover translation and the corrected
uniform permutation's marginal identities remain explicit ordinary
mathematical premises of those checks. No independent-parent law or
new support reserve is inferred.

No new frozen mathematical declaration, atom coverage or resolution of
the unrestricted problem is claimed by this report.
