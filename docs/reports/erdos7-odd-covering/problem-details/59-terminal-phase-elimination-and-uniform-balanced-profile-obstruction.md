# 59. Terminal phase elimination and a uniform balanced-profile obstruction

## A. A globally simultaneous worst phase assignment on terminal coordinates

Fix finite named core coordinates, and terminal coordinates indexed by q,
each with an alphabet of size q. Every forbidden original label is either
core-only or has requirements on the core and on exactly one terminal
coordinate. Its terminal requirement fixes a single value. Write J_0 for
the core-only labels and J_q for the bucket using q, and suppose |J_q|<=q.
Keep all core requirements fixed. The variable phase data theta assign to
each label in J_q one of the q terminal values, once globally.

Admissible policies first read the entire core, in any permitted
nonanticipative order, and then read every terminal coordinate once.
A terminal row, conditional on the complete transcript and its selection,
is any probability vector satisfying the same deterministic atom cap
r_q>=1/q, with r_q<=1. The permitted core policies admit at least one full core law. Core row
constraints and permitted core schedules do not depend on theta. There are no shared budgets or other constraints
on pasting these rows.

For a completed core tuple x avoiding every J_0 label, let A_q(x) be the
original J_q labels whose core requirements match x, and let

    d_q(theta,x)=|{theta_j : j in A_q(x)}|,
    s_q(theta,x)=min(1, r_q (q-d_q(theta,x))).

If core-only avoidance already fails, final survival is zero. Otherwise
maximum terminal survival, for this completed actual x, is exactly

    s(theta,x)=product_q s_q(theta,x).

Indeed the complement of the d forbidden values has capacity (q-d)r_q.
One can put min(1,(q-d)r_q) of the normalized row there: if it is below
one, put the remainder on forbidden values; the latter capacity suffices
because q r_q>=1. For several terminal coordinates, backward induction
bounds every policy by the product. Earlier successful terminal outcomes
change no other terminal forbidden set. A failed coordinate makes final
survival zero. The product is attained by optimal rows in any fixed
terminal order. This is the [disjoint-component argument](58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md#5-reusable-reduction-when-remaining-constraints-disconnect)
conditional on one complete core tuple, and permits arbitrary later
interleaving among the terminal coordinates.

Choose theta* injective on each entire bucket J_q. This is possible by
|J_q|<=q, and it simultaneously gives

    d_q(theta*,x)=|A_q(x)|>=d_q(theta,x)

for every complete x and every theta. Hence s(theta*,x)<=s(theta,x)
pointwise, including the core-only avoidance indicator.

Let M_C be the common feasible set of actual core laws produced by the
permitted core policies. The best final survival for phase theta is

    W(theta)=sup_(nu in M_C) E_nu[s(theta,X)].

Full finite history and nonempty compact row polytopes give attainment when needed;
pointwise dominance alone proves the comparison for the displayed suprema.
It follows that W(theta*)<=W(theta) for every theta. With minimum bad mass
V(theta)=1-W(theta),

    sup_theta inf_(core-first policy pi) Pr_(theta,pi)(some original label)
      = V(theta*).

This equality does not interchange a supremum and a minimum or choose
phases after observing a branch. One single theta* is pointwise worst for
all possible core outcomes before any policy is optimized.

### Arithmetic realization and the 154-modulus interface

For an original numerical modulus m=q c with gcd(q,c)=1, fixing its core
requirements is fixing a residue b modulo c. Assigning theta_j modulo q
has a unique CRT solution modulo the unchanged original m. Choose that
solution once for each original label. Different labels may be assigned
independently; every one remains fixed across all histories. This preserves
numerical distinctness, all exponents, and every core requirement.

For the [154 original odd 73-smooth moduli between 3 and 500](04c-full-history-capped-laws-and-exact-global-optimization.md#7-a-complete-survivor-count-obstruction-defeats-every-fixed-order), take core primes
3,5,7,11,13,17,19 and terminal primes23 through73. Since23^2>500 and
23*29>500, each modulus contains at most one terminal prime, to exponent
one. Terminal bucket sizes in increasing prime order are

    11,9,8,7,6,6,5,5,4,4,4,4,3,

all at most the corresponding prime. Thus76 terminal labels have the
simultaneously worst terminal phase assignment described above;78 labels
are core-only. The reduction removes only those76 terminal phase choices
from a worst-case core-first search. Their76 actual core requirements
remain parameters and must not be merged with core-only labels or each
other. In particular different original moduli may have the same cofactor
with different fixed residues, which all remain visible.

Under the [balanced profile](57-balanced-depth-profile-and-degree-seven-frontier.md),
terminal coordinates have height one
and only the atom caps, so this row model applies directly. Once the core
has been sampled, every terminal coordinate is still sampled from its
actual normalized row and retained in the complete joint tuple for any
subsequent numerical-tail query. This value reduction does not change the
full-history tail comparison or authorize conditioning multiple times.

The numerical-core-order probes on the original154 and four-change154
inputs give identical exact values with and without this terminal
elimination. Injective terminal rephasing also leaves both values equal
to their original values. These two diagnostics do not establish a
uniform bound over core phases; that task remains open.

The reduction concerns core-first policies. Allowing terminal coordinates
to be read before or between core coordinates enlarges the policy class;
no claim that theta* is worst for that enlarged class follows here. A
core-first bound that closes the required budget would still supply a
legal policy for the full class. A failing core-first bound would not rule
out another schedule, a changed profile or a sharper joint continuation.


### Exact retained inputs and diagnostics

The original input is the complete literal 154-label factory used in
[Chapter 57](57-balanced-depth-profile-and-degree-seven-frontier.md).
The [four-change input](../frontier/source-budgets/adaptive_phase_head_input.json)
is the globally fixed family of
[Chapter 58](58-adaptive-initial-block-recovery-and-all-schedule-budget-obstruction.md).
Both use the same supplied balanced profile. For each input, the numerical
core-order value, the numerical full-order value, and both values after
one global injective rephasing agree exactly:

| Input | Exact minimum bad mass for these fixed numerical orders |
|---|---|
| Original | 39891291142993164384829733829906791483779 / 130822105133669014006347656250000000000000 |
| Four-change | 37673471916353973016316172346954510845661703 / 104396039896667873177065429687500000000000000 |

The original and rephased inputs retain all 154 numerical moduli, and the
certificate includes every rephased residue. For each terminal label,
the verifier checks its original cofactor residue separately; equal
cofactors never identify or merge original labels.

The [producer](../frontier/source-budgets/terminal_phase_reduction.py)
uses the existing laminar Bellman solver for the full twenty coordinates
and for the seven-coordinate problem with the exact terminal product.
Its [complete certificate](../certificates/source_norms/source-budgets/terminal_phase_reduction.json)
retains both inputs, every injected original congruence and the exact values.
The [independent verifier](../frontier/source-budgets/verify_terminal_phase_reduction.py)
uses actual coordinate leaves and integer atom capacities, after checking
that those terminal capacities imply every proper ancestor cap of the
supplied profile. Its
[independent certificate](../certificates/source_norms/source-budgets/terminal_phase_reduction_verification.json)
compares the complete full-coordinate and collapsed objectives.
Both programs support `--write` and `--check` under `python3 -B -I -S -O`.

This is an ordinary mathematical reduction with exact diagnostic
computations. It is not a new Lean declaration or a uniform numerical
bound over the remaining core phases. Unrestricted Erdős #7 remains open.


## B. A seven-phase obstruction to the uniform balanced-profile budget

Keep the original154 odd73-smooth moduli between3 and500, their twenty
named coordinate heights, and the balanced profiles. Change exactly seven
of the original fixed residues:

| Modulus | Original residue | New residue |
|---|---:|---:|
|25|21|13|
|39|22|14|
|45|43|26|
|55|11|28|
|63|7|32|
|189|28|29|
|225|79|11|

The other147 residues are unchanged. Every phase is fixed globally before
sampling. No original modulus, exponent or coordinate is replaced. The
complete clean input is [the retained seven-phase input](../frontier/source-budgets/uniform_phase_capacity_input.json), SHA-256
`ea227d216660f496ecb3a2c89dbc145605f0ad83c94e5996a7ee76d746ea712b`.

For every admissible adaptive read-once law satisfying these deterministic
full-history cylinder caps, its probability epsilon of hitting the union
of the154 original classes obeys

    epsilon >=
      390156972441444866010545862645457 /
      1086338369123261718750000000000000
      = 0.3591486626366003... .                         (1)

This exceeds the exact head threshold of the existing fixed sufficient
budget. Hence this particular balanced-profile budget cannot provide a
uniform arbitrary-phase theorem, even if every transcript-dependent
permutation of all twenty coordinates is allowed.

The statement is an obstruction to the fixed sufficient budget, not to
noncoverage or arbitrary alternative proofs. Indeed the integer34 avoids
every one of these154 original classes.

The obstruction also survives removing the possibility of redundant
head classes. For each of the154 original classes an explicit private
integer is retained in [the retained private witnesses](../frontier/source-budgets/uniform_phase_private_witnesses_input.json); it belongs to that class
and no other one. Checking these finite witnesses against all154 labels
establishes irredundancy of the actual union. The numerical palette is
closed under nontrivial divisors and has initial odd-prime support by its defining rule.
These facts do not assert whole coverage or the stronger exchange
properties of a lexicographically extremal hypothetical cover.


### 1. Global caps do not depend on the sampling order

Write X_p=Z/p^(H_p)Z and r_p=r_(p,H_p). At each selected coordinate p,
conditional on the complete transcript and on that selection, each atom
has mass at most r_p. The selection is nonanticipative and every
coordinate is read once. Any randomizer is included in the transcript.

For any subset A of coordinates and any fixed actual values x_p,

    mu(X_p=x_p for p in A) <= product_(p in A) r_p.     (2)

Induct on the remaining unread coordinates. Selecting a coordinate not
in A leaves the same target event after averaging its outcomes. Selecting
p in A leaves only its one specified value, contributing at most r_p;
apply induction to the remaining target coordinates. Averaging selected
coordinates preserves the bound. This proves (2) for every allowed order.

Consequently any cover of the actual survivor set by actual partial
cylinders gives an upper bound on survivor mass by summing their product
cap prices. Cylinders may leave coordinates unrestricted. Their construction
order is unrelated to the order in which the law mu sampled coordinates.

### 2. Product covers of the terminal coordinates

Use core primes3,5,7,11,13,17,19 and terminal primes23 through73. Every
original modulus is at most500. Since23^2>500 and23*29>500, no label
contains a squared terminal prime or two different terminal primes.

Fix a complete core tuple x. If it already satisfies a core-only class,
there is no surviving completion. Otherwise every still-live original
label forbids one value at exactly one terminal prime. For each terminal
q, let T_q(x) be this actual forbidden-value set, and d_q=|T_q(x)|. The
remaining survivor set is exactly the product of the terminal safe sets.
Repeated forbidden values count once; original labels are still retained
when testing whether they are live.

The safe set at q can be covered either by leaving q unrestricted, at
price1, or by its q-d_q individual allowed values, at price(q-d_q)r_q.
Choose the cheaper cover independently for each q and take the Cartesian
products of their cylinders. The resulting partial cylinders cover all
terminal survivors. Their total price is

    u(x)=product_q min(1, r_q(q-d_q)).                  (3)

Multiplying by the price of the fixed complete core tuple and applying
(2) bounds its surviving completions. This is a product of certificate
prices, not a claim that mu has independent coordinates or satisfies
conditional caps when reordered core first. No such reordered conditional
law is used.

### 3. Optimize the certificate tree on core prefixes

Let J be the original labels still matching a given numerical core prefix,
and i the next core coordinate. A live label whose requirements are all
already fixed means the whole cylinder is forbidden; its survivor cost
is zero. If J is empty, the whole prefix cylinder covers all its survivors
at normalized cost one. At a complete core prefix use (3). Otherwise put

    U(i,J)=min(1,
       r_(p_i,H_i) sum_(z in X_(p_i)) U(i+1,Phi_(p_i,z)(J))).       (4)

Here Phi retains exactly the globally fixed original classes matching z.
The option1 covers by the whole current prefix cylinder. The other option
splits into actual child cylinders and uses their recursive covers. Induction
therefore proves that the root cost covers every actual survivor and

    mu(survivors) <= U(0,all154 labels).                (5)

When computing (4), grouping different actual z with equal original-label
masks uses their exact multiplicity. It does not move a label's residue or
merge original numerical modulus identities.

For the seven-phase input, exact arithmetic gives

    U(0,all labels) =
      696181396681816852739454137354543 /
      1086338369123261718750000000000000.

Taking the complement yields (1). The recurrence visits35558 states.
An independent calculation evaluates3191384 actual local core leaves and
5232 terminal states, without importing the candidate partition/grouping
implementation, and obtains the same exact fraction.

For comparison, requiring the certificate to keep branching in numerical
order through every terminal coordinate, with only whole-prefix stopping,
gives the weaker bad-mass lower bound

    109368246551933266477704238303 /
    306240236010156250000000000000
      = 0.3571321913045617... .                         (6)

Thus allowing unrestricted terminal coordinates inside a partial cylinder
is material to crossing the following threshold; (6) alone does not do so.
Neither certificate is claimed optimal among all fractional cylinder covers.

### 4. The exact sufficient budget is excluded

Retain precisely the existing constants

    Cbar=130197276585546949/250000000000000000,
    Jbar=617212231457700477699/62500000000000000,
    T=326059/4.

The sufficient score is epsilon+Cbar+(Jbar-1)/(T-1). Its required strict
head bound is

    epsilon < eta =
      29187881279576281900621/81513750000000000000000
      = 0.3580731015267520... .

Using (1), every admissible adaptive head law instead has

    epsilon+Cbar+(Jbar-1)/(T-1) >=
      189113081175577219987900984117892393347 /
      188909897037058719843750000000000000000
      = 1.0010755611098483... > 1.                     (7)

The exact excess is

    203184138518500144150984117892393347 /
    188909897037058719843750000000000000000 > 0.

This excludes a phase-uniform guarantee using these caps and these same
Cbar/Jbar/T allowances, regardless of how one adaptively chooses the
sampling order. It does not exclude changing the profiles, using a
sharper actual joint allowance, a different stopping criterion, or a
proof not based on this sufficient score. Cbar and Jbar are upper bounds;
(7) is not a lower bound on the true tail losses or complete-layout moment.

### 5. Verification and relation to the terminal-phase reduction

The complete input contains the154 literal moduli and globally fixed
residues, heights and all profile levels. The candidate producer checks
these against the original numerical palette and the same balanced-profile
tail budget. Its writer and exact replay both exit zero under
`python3 -B -I -S -O`. The independent actual-leaf calculation gives
(1), (6), (7), and directly verifies34 against every original class.
These are ordinary mathematical deductions and exact computations; no
new Lean statement or literature-priority claim is made.

The terminal-phase reduction is a different assertion: within strategies
that finish the core before sampling leaves, globally injective leaf
phases give the largest minimum head loss, simultaneously for every core
tuple. That assertion removes76 terminal phase choices from a restricted
outer search but retains all their core requirements. Formula(3) instead
builds a global-cylinder cover of one fixed input's surviving set, so its
bound applies to all adaptive sampling schedules. Conflating these two
orders would lose precisely the all-schedule strength of (7).

The unrestricted Erdős7 question remains open. The new obstruction rules
out this proposed phase-uniform fixed-profile gateway; it supplies no
covering counterexample and does not invalidate previously proved
fixed-phase or other restricted noncoverage theorems.


The [partial-cylinder producer](../frontier/source-budgets/uniform_phase_capacity.py)
retains both the numerical-prefix bound and the stronger partial-cylinder
bound in its [exact certificate](../certificates/source_norms/source-budgets/uniform_phase_capacity.json).
The [independent actual-leaf verifier](../frontier/source-budgets/verify_uniform_phase_capacity.py)
retains every state and leaf inventory, the strict threshold comparison,
and the integer 34 checks in its
[independent certificate](../certificates/source_norms/source-budgets/uniform_phase_capacity_verification.json).
Both programs expose `--write` and `--check` under `python3 -B -I -S -O`.
The exact continuation constants come from the
[independently verified balanced tail budget](../certificates/source_norms/source-budgets/balanced_profile_tail_verification.json).
