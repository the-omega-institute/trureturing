# Clean-root query phases admit exact incidence states, but small-prefix tails remain too large

On the specified pure-comb sources, one completely clean root in every
observed colour lets all higher query digits be moved to fixed nested
paths without decreasing any increasing convex load cost. Each numerical
label retains its own globally fixed colour selectors. The resulting
exact incidence representation has 14,580 states for the shallow
384-label box, although its full selector optimization remains enormous.
Several smaller h16 prefixes are excluded by a necessary complete-tail
cost. An actual added mixed original shows why arbitrary survivor
restriction needs an additional premise.

These are ordinary mathematical deductions and exact finite controls,
not Lean verification or a positive Erdős #7 certificate. The mechanisms
reused are [Report781](../750-799/781-an-actual-mass-preserving-redistribution-lowers-the-complete-fourth-query-bound.md)'s simultaneous attainable clean-path replacement,
[Report790](../750-799/790-shared-pair-deficits-admit-twenty-nine-at-a-depth-two-profile.md) PC9's conditional weighted-indicator rearrangement,
[Report818](818-coherent-prefix-moments-preserve-the-complete-height-remainder.md)'s globally shared numerical-label phases and complete moment
remainder, and [Report695](../650-699/695-shared-query-labels-tighten-the-fixed-head-envelope.md)'s finite shared-factor replacement.

## 1. The actual family already determines every local prefix law

Use exactly [Report826](826-one-finite-pure-family-obstructs-every-kernel-in-the-h16-comparison.md)'s 53-original family: its 25 listed anchors/mixed
originals, together with the four disjoint pure cylinders at each
q in Q=(5,7,11,13,17,19,23). At 5 these are

    2 mod5; 3+5^(j-1) mod5^j, j=2,3,4.

At the other six primes they are

    1 modq; 2+q^(j-1) modq^j, j=2,3,4.

Write

    S_q=(q-2+q^-4)/(q-1),
    delta_q=1/S_q,                    normalized survivor density,
    a_q=delta_q/q,                    mass of one clean first root.

The observed colours at 5 are {0},{1},{2,3,4}; at the other primes they
are {0},{1,...,q-1}. Their probabilities are

    pi_5=(a_5,a_5,1-2a_5),  pi_q=(a_q,1-a_q) otherwise.

For any requested finite depth e, the exact local prefix law is already
reconstructible from these four original cylinders:

    xi_(q,e)(b) = delta_q [q^-e
      - sum_(j,t in pure_list_q)
          1_(b=t mod q^min(e,j)) q^-max(e,j)].             (CR1)

Here pure_list_q records each cylinder by its depth j and residue t.
The four removed cylinders are disjoint, which is why subtraction in CR1
is exact. At e>4 a cylinder either has a surviving depth-four ancestor and
mass delta_q q^-e, or has mass zero. Thus no additional source data are
missing for the raw retained law once w and u are specified.

For exactly the 53 originals there is an additional useful simplification:
on the pure survivor source their remaining survivor U_53 is categorical.
The only mixed originals using deeper nonternary digits are redundant:
25 mod75 is contained in 10 mod15, 49 mod147 is contained in 7 mod21,
and 175 mod225 is contained in 10 mod15. Every other mixed original
tests only the five ternary leaves and the specified singleton first
colours (including the separate root1 colour at 5). Therefore arbitrary
first-colour u can be restricted to U_53 by multiplying its table by one
categorical zero/one mask. For a K8-admissible u that mask already acts
as the identity, so nu_u restricted to U_53 equals nu_u.

The same does not hold for an arbitrary extension of these originals.
Additional originals can create new joint prefix correlations. Their
survivor profile Gamma_E is not determined by CR1 and the colour table.
In particular, do not replace the inherited complete-head lower bound by
M=nu_u(whole) while retaining the claim about arbitrary later originals.
Report826 explicitly keeps fees for numerical labels absent from its
finite fixture.

## 2. One completely clean root in every colour is enough

Every colour of this particular actual family contains a whole first
root with no pure deletion at any suffix depth. Choose roots

    q=5: 0,1,4 for its three colours;
    q>5: 0,3 for its two colours.

The same choices work at every finite comb depth and for the infinite
comb considered below. Fix one infinite path inside each chosen root;
all further digits can be zero.

Here is the precise reuse of Report781/790. Fix a finite numerical-label
set, one independent phase at every label, a nonnegative retained table
u_l(s) depending only on the ternary leaf and first colours, and either
the hinge phi_h(t)=(t-h)_+ or t^4. Fix a prime q, all other source
coordinates, and one current colour c. In this conditional integral:

* u is constant in x_q, hence only supplies a nonnegative weight;
* labels with q-exponent zero give a fixed baseline;
* labels whose first q-digit lies in another colour vanish;
* each remaining numerical label has a nonnegative coefficient from its
  other-coordinate tests, and a depth-e cylinder with conditional mass
  at most delta_q q^-e/pi_q(c).

Report790 PC9 bounds their weighted hinge by the nested events with these
marginal caps. These events are simultaneously actual: move every
relevant depth-e prefix to the fixed clean path in c. Its conditional
mass is exactly delta_q q^-e/pi_q(c), at every depth. The same replacement
maximizes every increasing convex load cost; for a finite load this also
follows by expressing its convex cost as an affine term plus nonnegative
hinges. This is Report781's attainability step applied separately inside
each observed colour, not a new generic rearrangement mechanism.

Crucially the chosen replacement depends only on q, c and the numerical
label's depth. It does not depend on the other source coordinates or on
which occurrence of that label is being integrated. Therefore the
conditional inequalities integrate to one globally valid new phase
table. Repeating at the seven coordinates retains one phase per label.

The ternary coordinate works similarly. A depth-one label keeps its
choice of root 1 or 2. A depth-at-least-two label keeps its choice of one
of the five leaves (4,7,2,5,8) mod9, and all higher prefixes selecting
that leaf can be aligned along one Haar path above it. Tests on a dead
root/leaf can be replaced by a live one because their old contribution
was identically zero. Root choices for one numerical label and leaf
choices for another remain independent.

It follows that the exact supremum on this raw source is attained among
the reduced phase tables for every finite label set. For arbitrary finite
heights, and then the complete supremum, the same restriction preserves
the value. For hinges this follows by the finite replacements and the
complete summable first-moment inventory: each label cylinder has its
verified product cap, whose sum over exponents is geometric at every
prime. The finite-prefix hinge plus complete first-moment tail mechanism
is the same one used in [Report05](../../001-064/05-the-actual-rectangle-gives-two-further-square-savings.md) HG6. For
fourth powers use Report818's complete fourth-moment bound, which bounds
the nonnegative finite moments uniformly and supplies the finite limit
under monotone exhaustion. First-moment integrability alone would not
justify that fourth-moment assertion. Neither argument optimizes each
source cell independently.

This is not a common CRT centre. Each numerical label retains its own
colour choice at each prime and its own ternary root/leaf choice. Only
the digits within a chosen colour/leaf have been made common. At depth
one a selected test still has mass a_q, not the whole colour mass pi_q(c).
In particular this does not reproduce the colour-cell relaxation in828.

The claim is uniform over all nonnegative first-colour tables u on this
fixed source. It also applies to U_53 by the categorical mask just proved.
It does not establish the same equality after conditioning on an
arbitrary U: the new density can depend on higher digits inside a colour.
Raw-source domination still supplies a valid upper bound there.

## 3. The C point has a specified clean-root realization

Extend the same pure comb to every j>=2. The disjoint removed pure
cylinders have total Haar mass 1/(q-1), so the surviving probability law
has

    S_(q,infinity)=(q-2)/(q-1),
    delta_(q,infinity)=(q-1)/(q-2)=C_q,
    a_(q,infinity)=C_q/q=c_q.                            (CR2)

Its colour probabilities are exactly [Report827](827-retained-factorial-hinges-preserve-complete-heights-but-need-not-improve-the-gate.md)/[Report830](830-selective-conditioning-preserves-complete-heights-but-the-fixed-candidate-chooses-the-root-stop.md)'s point C, including
(4/15,4/15,7/15) at 5. The clean roots listed above remain entirely
untouched. Hence the preceding exact phase reduction applies to this
particular p-adic probability realization of C as well. The retained
table from827 can be used on it without guessing missing higher digits.
The inherited M,L,K4 and tail remain the same colour/cap expressions;
this assertion is a connection of definitions, not a recomputation of
their saved values or of the actual query hinge.

An infinite original family is not an admissible finite covering family
for Erdős #7. This realization is a specified capped-source diagnostic
and the limit of the given finite pure-comb laws. It supplies no claim
that every actual pure source with the same colour probabilities has
the same optimized query value. In particular a completely clean first
root in every colour is an extra geometric hypothesis, not a consequence
of the vector pi alone.

For example, pure labels 5,25,125,625,3125 with respective phases
0,1,2,3,4 damage every first root and have no clean first root at all.
This example only shows the hypothesis can fail; it is not a claim that
this family has the same pi as the source under study.

## 4. One further deep original can invalidate restriction transport

Keep the actual depth-four pure laws from826 and put ternary weight one
at leaf2 mod9. Let u be the indicator of colour{0} at5 and the nonzero
colour at every other prime. This categorical slice avoids all53
originals: the mixed classes with
only first nonternary digits either select another ternary leaf/root or
require a zero root at one of those other primes; the three deeper mixed
classes were already contained in shallower originals.

Add the new, numerically distinct odd original125mod375. On this retained
slice it deletes exactly the5-adic cylinder0mod125. Consider the query
275mod375. It has ternary projection2mod3 and5-adic projection25mod125.
The proposed same-colour move keeps the ternary projection and colour{0}
but moves its5-adic prefix to0mod125, so its new phase is125mod375.

Before this extra deletion both query cylinders are clean and have equal
mass. After restricting to its actual survivor, their masses differ on
one unchanged measure. The depth-four pure5 law has469 surviving residues
mod625. Its retained root0 has125 of them; the new original removes five.
The original query still hits five survivors and the moved query hits
none. Suppressing the same positive factor from the other prime colours,

    restricted mass =120/469,
    old query mass =5/469,
    moved query mass =0.

After division by that one restricted mass, the query means are

    1/24  and  0.

Thus even the linear convex payoff decreases. A unit query may be added,
and any other already canonical labels may be retained, without removing
this first-moment decrease: their indicators are unchanged. The example
uses one actual enlarged original family and one common normalized
survivor law. It does not replace that law by a separate distribution
for each query. Raw-source domination still gives a valid upper bound,
but automatic exact same-colour rearrangement after arbitrary further
original deletion is false.

## 5. Exact integration has a much smaller finite state space

After the replacement, for a query cutoff E_q>=1, record the colour c
and r, the largest matching clean-path depth, truncated at E_q. The
unconditional local masses are

    rho_q(c,0)=pi_q(c)-a_q,
    rho_q(c,r)=a_q(q-1)q^-r,         1<=r<E_q,
    rho_q(c,E_q)=a_q q^(1-E_q).                         (CR3)

They sum to pi_q(c). The r=0 mass vanishes for singleton colours.
For a positive q-exponent e, the test at numerical label n matches
exactly when its globally chosen colour equals c and e<=r. Exponent
zero has no condition.

At ternary cutoff J>=2 retain leaf l and truncated Haar suffix depth
r_3 in {0,...,J-2}. At J=2 there is one suffix state of mass one. For
J>2 its masses are (2/3)3^-r for r<J-2 and 3^-(J-2) at r=J-2.
The label's ternary test uses its root selector if its exponent is one,
and its leaf selector plus r_3>=j-2 if its exponent j is at least two.

For a fixed global selector table, its integral is the finite sum of
the load cost against

    u_l(c_5,...,c_23) rho_3(r_3) product_q rho_q(c_q,r_q).

Every numerical label uses the same selectors in every summand. No
maximization is performed inside that sum. This representation preserves
all mutual query intersections needed by a hinge or fourth power.

The number of ambient positive local-incidence states, before zero
entries of u are removed, is

    5(J-1)(3E_5+1) product_(q>5)(2E_q+1).                (CR4)

For J=2 and every E_q=1 there are 384 numerical labels but only
5*4*3^6=14,580 such integration states. The factor 4 at 5 is the two
singleton-hit states plus hit/miss in the large colour. The factor 3
at each other prime is its singleton-hit plus large-colour hit/miss.
The five ternary leaves need no suffix split at J=2.

Optimization is still enormous. Among these 384 labels, 192 choose a
5-colour and 192 choose a colour at each other prime; 128 choose a
ternary root and 128 a ternary leaf. The reduced table count is

    3^192 * 2^1280 * 5^128 = approximately 10^566.3938.   (CR5)

This is a reduction in source integration and phase description, not an
exhaustive-search result or an upper certificate for the global maximum.

## 6. A small prefix cannot make its complete first-moment tail cheap

At h16, a prefix with at most 16 numerical labels, including the unit,
has identically zero prefix hinge. This does not make the full hinge
small: every omitted label remains in the first-moment remainder.

There is a necessary lower bound for any such remainder on the specified
finite-comb or infinite-comb realization. Let M=nu_u(whole)>0, and let O
be a set of nonternary primes entirely omitted from the prefix. At each
q in O one first root is deleted by its pure original. For

    m=product_(q in D) q^e_q,  empty!=D subset O, e_q>=1,

the projection of nu_u has at most

    N_m=product_(q in D)(q-1)q^(e_q-1)

nonzero cells. These cells carry total mass M, even when nu_u has
arbitrary cross-coordinate correlations. Therefore its largest m-cell
has mass at least M/N_m. Additional pure deletions can only lower the
number of occupied cells and do not weaken this bound.

Every valid cylinder cap c_m must be at least that largest mass. Summing over
all numerical labels supported only on O gives the necessary remainder
cost

    R >= M [product_(q in O)(1+q/(q-1)^2)-1].            (CR6)

Here sum_(e>=1)1/[(q-1)q^(e-1)]=q/(q-1)^2. Different numerical labels
may choose different maximizing phases: this is expressly allowed.
For a first moment their contributions add, so these separate maximizing
choices form one legal complete phase table. No common CRT centre is
assumed. Equivalently, CR6 already follows merely by summing necessary
individual cap inequalities. It does not assert simultaneous attainment
of independently optimized products in a nonlinear moment.

Use only827's saved scalars, without evaluating its table/source again:

    M=0.4784474119263616...,
    L=0.012657886704707326...,
    tail=0.0456822505623063....

The h16 gate leaves less than

    12 L-tail=0.10621238989418161...                      (CR7)

for a coherent hinge plus the first-moment remainder. Exact rational
substitution in CR6 gives:

| Prefix period | Labels | Omitted primes O | Necessary R lower bound |
| --- | ---: | --- | ---: |
| 45 | 6 | 7,11,13,17,19,23 | 0.33944220119376367... |
| 315 | 12 | 11,13,17,19,23 | 0.20629738045327817... |
| 945 | 16 | 11,13,17,19,23 | 0.20629738045327817... |
| 3465 | 24 | 13,17,19,23 | 0.13843978841565618... |
| 45045 | 48 | 17,19,23 | 0.0873599565402025... |

Thus the first four prefixes cannot rescue this saved h16 gate by the
prefix-plus-first-moment-tail route, even if their prefix hinge upper
bound were zero. The last line is merely not excluded by CR6; the other
omitted labels, positive prefix hinge and actual upper certification
remain unpaid. Nothing here excludes other thresholds, different L or
tail estimates, a different retained table, or a remainder interface
that retains more joint information.

The [prefix-cost consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/clean_root_prefix_costs.py)
reads the existing M,L,tail values from the SHA256-bound
[Report827 result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/retained_factorial_hinge.json).
It derives CR5--CR7 and compares the complete exact
[prefix-cost result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/clean_root_prefix_costs.json).
It runs no source reconstruction, query enumeration or optimizer.

## 7. Existing local moment credits are reusable; a hinge needs more data

The small-block alternative already exists for polynomial moments.
Report818 replaces the complete four-tuple contribution inside a finite
prefix by its coherent maximum, and retains every other ordered tuple,
including mixed tuples with some labels outside the prefix. Report695
replaces just the factors supported on labels {3,5,15} in a squared-load
expansion. Other factors containing any of these labels are still paid.
The same literal-factor accounting applies to a chosen finite label
cluster in the quartic inventory: remove only its explicitly budgeted
ordered tuples, replace that entire block by one same-source joint
maximum, and preserve all other terms. This is existing factor reuse,
not a new general theorem. Overlapping clusters need factor budgets.

The hinge has no corresponding fixed nonnegative fourth-tuple expansion.
For a selected cluster load A and omitted load B>=0 its exact relation is

    (A+B-h)_+ = (B-h)_+ + (A-(h-B)_+)_+.                 (CR8)

Thus an unconditional improvement for A at threshold h cannot simply be
subtracted from a bound for A+B. The useful threshold depends on the
same realized B, and A can be correlated with B. If B>=h the cluster
contribution is just its first moment, so a convex-order gain at an
interior threshold can disappear entirely. A valid local hinge credit
must retain the relevant joint/conditional load information or supply a
uniform inequality for every compatible inherited load. This is the
same inherited-load/global-label state discipline used by [Report416](../400-449/416-exact-independent-layout-tree-separation-and-actual-laws.md) and [Report440](../400-449/440-joint-test-profiles-as-composable-boundaries.md).

[Report588](../550-599/588-query-prefix-incidence-strengthens-actual-source-debits.md) is a genuine hinge-credit precedent, but it is not a ready-made
credit for this source. It extracts query-prefix incidence against
actual PA row completion/cap slack on one actual prefix law, before
performing the remaining backward comparisons. It proves no uniform
positive debit, and its PA source, threshold and row hypotheses differ.
Report05 HG6 and its later joint-cost refinements also keep full actual
geometry/conditional costs; they do not license subtraction of an
independent standalone small-prefix hinge from828/830.

For the fixed827/C/table,830's already established best gate remains
negative even with the entire quartic tail debit formally set to zero.
Consequently a quartic-only local credit cannot rescue that unchanged
L/hinge curve. No new evaluation is used for this observation. A next
effective change must also lower the actual phase-coherent hinge or
improve the common-source head/denominator estimate.

## 8. Minimal implementable contract and the actual missing obligation

Input: one specified pure family (or the specified infinite-comb law),
its delta_q, pi_q and clean-root witnesses, the same w/u and literal
selected-null constraints, a finite labelled exponent box, and the
inherited complete remainder coefficients. For a survivor-restricted
improvement supply the actual joint Gamma_E and do not assume CR3 after
extra deletions.

Finite object: a selector variable for each positive prime exponent of
each numerical label, plus the ternary root/leaf selector. Integrate
that one assignment using CR3--CR4. A maximizing layout is a lower
witness for the optimum; an upper certificate must cover every allowed
selector table, for example by valid conditional branch bounds with
the unresolved label identities and inherited loads retained.

Output: a certified upper coherent-prefix cost on the same measure,
plus its complete inherited remainder, and the unchanged mass/tail
scalars. The normalized continuation uses that same mass and the
inherited tail allowance; the prefix hinge plus its complete first-moment
remainder occupies the hinge term of the sufficient numerator. A
computation returning only a good layout, independent cell
maxima, separately maximized tuple gains, or a partial search does not
meet the output contract.

The source-data gap for826 and the specified C realization is closed by
CR1--CR4. The open computational/mathematical gap is an upper certificate
that preserves independent globally fixed label selectors, has a
remainder smaller than the relevant gate allowance, and supplies a
strict improvement large enough to cross the same gate. CR6 rules out
several superficially small h16 prefixes before spending optimization
work. CR5 shows why eliminating redundant higher digits alone has not
solved the remaining selector optimization.

## 9. Small actual-source integration controls

The [phase-compression consumer](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/clean_root_phase_compression.py)
checks the integration and relocation on one two-axis finite control.
It uses the five leaves
mod9, pure originals 2 mod5 and 8 mod25, and one fixed dominated rational
first-colour table. The same actual measure is retained throughout.
There are 95 source points before table zeros, compared with 35 ambient
compressed states at J=2,E_5=2.

Twelve prescribed complete literal phase tables on divisors of225 include
dead, damaged and clean root choices and independent numerical-label
phases. For each, the checker moves only its 5-adic phases inside their
original colours, retains its ternary phases and literal label identity,
and compares the entire compressed load histogram to direct CRT
integration. It also checks hinge nondecrease at every integer threshold
from0 through9 and fourth-moment nondecrease. These exact checks
provide finite implementation controls; the conditional argument in
section2 carries the all-layout claim. This is not an evaluation of the
827 retained table, an optimized prefix, or a research-source gate.

The same consumer also reconstructs the actual depth-four pure5 law and
the additional125mod375 restriction counterexample in section4, including the
one unchanged normalized law and the exact1/24-to-zero query decrease.
Its [saved result](../../../frontier/cover-geometry/refined-capped-source/pure-source-realizability/clean_root_phase_compression.json)
contains all621 explicit checks and the two actual-source controls.

Both consumers use sibling input/result defaults and verify saved results
on ordinary execution. Use --source to locate the bound827 input for the
cost consumer, --result to select another result file, or --write-result
to regenerate that result. Checks remain active with Python optimization.
From the repository root:

```sh
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/pure-source-realizability/clean_root_prefix_costs.py
python3 -I -S -B docs/reports/erdos7-odd-covering/frontier/cover-geometry/refined-capped-source/pure-source-realizability/clean_root_phase_compression.py
```

Portable copies reproduce the same exact results. All16 tested
dependency-hash and saved-result mutation classes are rejected. These
checks cover the consumers'
finite data and dependency bindings; the ordinary proofs bear their
stated arbitrary-layout and complete-height quantifiers.
