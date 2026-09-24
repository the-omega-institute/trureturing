# 64. An attained adaptive core policy and continuous stop-loss optima

The [literal seven-phase input](../frontier/source-budgets/uniform_phase_capacity_input.json)
from [Chapter 59](59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md)
keeps its 154 odd numerical moduli, all exponents, all twenty coordinates,
and the seven globally fixed phase changes are unchanged. Allow arbitrary
history-dependent ordering of the first seven core coordinates 3 through19;
read the thirteen terminal coordinates23 through73 afterwards. Conditional
rows at each complete decision transcript obey the fixed balanced caps.
This is a specified policy class, not every interleaving of twenty primes.

## Sufficient boundary and exact recursion

For remaining core names U and still-matching original label IDs A, all
future head constraints and conditional row polytopes are determined by
(U,A). Complete sampled coordinate values remain in the actual transcript;
(U,A) is a cache key for this head objective, not a replacement for the
actual values needed by later tail queries.

If A already contains a core-only label with no remaining requirement,
its union has occurred and the conditional bad probability is1. All such
histories are one absorbing boundary value for a given denominator. Empty
A has value0. At U empty, no surviving class contains two terminal primes.
For each terminal q let d_q(A) count the DISTINCT literal residues moduloq
of active classes. The maximum simultaneous survival over the terminal
coordinates is

    product_q min(1, r_q (q-d_q(A))).

For a terminal row, at most q-d_q leaves avoid every incident class and
each has cap r_q. A normalized row attains the displayed one-coordinate
maximum by filling these leaves first, then any forbidden leaves. Backward
induction factors the optimal survival because constraints split across
terminal coordinates. Full-history randomization cannot improve that
product. The bad value is1 minus this product.

At any earlier state, choose one p in U and a normalized row nu on its
actual p^H leaves. The next boundary keeps exactly the original labels
matching that actual leaf. The value is the minimum of

    sum_x nu(x) V(U\{p}, A matching x)

over all legal next p and all feasible rows. The input verifies
r_(p,e)=p^(H-e)r_(p,H) for every e>=1, so the leaf cap implies every proper
ancestor cap. Thus sorting actual leaf continuation values and filling
mass up to each leaf's cap solves the row exactly. Equal-cost leaves may
be grouped by equal resulting active masks, retaining their multiplicities.

Write r_(p,H)=c_p/d_p in lowest terms and
D(U)=product_(terminal q)d_q times product_(p in U)d_p. Every recursive
value has an integer numerator over D(U). A row groups n actual leaves
with total integer capacity n*c_p, fills exactly d_p units, and multiplies
child numerators. This proves the integer recurrence has no rounding.

Finite induction proves optimality and attainment. Each chosen row can
be split over its actual leaves in numerical order, each with capacity
c_p/d_p; chosen child policies then paste into one normalized law. A
randomized choice of next prime is an average of its attainable values,
so cannot lower their minimum. A satisfied label stays satisfied, which
justifies returning the absorbing constant before caching.

## Exact result

The exact attained minimum in the declared core-first class is

    epsilon=2630194140308535545098092362189944702313369/6959735993111191545137695312500000000000000
          =0.37791579205187165... .

The numerical fixed-order minimum was0.3808807951029895... . Their difference
is61906915363647989758908839083017479731043/20879207979333574635413085937500000000000000
>0. The optimal first core is3. Subsequent
choices and capped rows are determined by the retained Bellman recurrence;
the root action values and complete-state hash are retained in the result.
This comparison does not prove that adaptation beats every fixed seven-prime
order, or characterize unrestricted twenty-prime adaptive optimality.

## The retained actual policy

The [complete policy](../certificates/source_norms/source-budgets/adaptive_core7_policy.json)
contains every positive boundary row and edge, with original live-label
masks and integer mass units. An absorbing history is completed by legal
rows, for example uniform rows; a null history also admits a feasible
uniform completion. Such completions retain the actual values and do not
change the head union event already decided.

The [policy verifier](../frontier/source-budgets/verify_adaptive_core7_policy.py)
reads this policy and the independently computed optimum, without reading
candidate Bellman values or rerunning an optimization. It enumerates each
actual next-coordinate leaf and recomputes its original-label mask. It
checks each group multiplicity, splits the assigned mass in increasing
actual-leaf order, assigns zero to omitted groups, and checks total mass
one and every absolute residue cylinder at every depth.

At each terminal mask it constructs all thirteen actual rows by filling
allowed residues before forbidden residues. It derives survival from
these assigned masses, then evaluates the positive policy graph upwards.
Each positive child must be a retained row, a retained terminal mask, or
an absorbing covered state. Reachability verifies that the file contains
all and only the positive states reachable from the root.

There are 6511 core rows, 1,886,217 actual core leaves, 1,423,235 positive
actual core-leaf edges, 2542 terminal masks, 33,046 terminal coordinate
rows, 1,614,170 terminal atoms, and 3,644,013 absolute depth-cylinder
checks. All 18,796 positive group edges and 1291 absorbing edges are
verified. The actual reconstructed bad mass equals the independent
optimum. A strictly better feasible continuation at any positive state
would improve the root by substitution, contradicting that independent
optimum; this establishes optimality along the retained positive policy
without trusting internal table numerators.

## Same actual law and complete-tail comparison

[Chapter 55](55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md)'s
remaining-set induction applies to all fixed labeled cylinder
events and all nonnegative increasing convex functions. Its hypotheses are
conditional caps at the actual full transcript after choosing the next
coordinate. The solver satisfies them at every sampled row and never peeks
at an unread value. Global label phases do not change along branches.
In particular each original full cylinder has mass at most the product of
its coordinate caps, even though the final actual law need not be independent
or satisfy the caps in every fixed numerical order.

Select full finite heights for the entire eventual family at the outset.
Append independent uniform extra digits when a coarse head coordinate is
read; prior extra digits reveal no additional coarse information. This
preserves epsilon and lifts caps to r_(p,H)p^(H-e) at larger depths.
Keep the complete actual head tuple and use the normalized numerical
q>73 tail kernels. These preserve its full joint marginal. The existing
auxiliary C_B, K_tau, threshold T_lower and E7 bounds therefore remain
valid for this changed actual head policy, with the same deterministic
profiles. No tail sweep is rerun or replaced by an independence assumption.

For the single common event S avoiding all charged original classes,
mu(S)>=1-epsilon-E7-C_B. For every complete divisor layout b, with its own
arbitrary fixed residue at each divisor,

    E[(L_b^2-tau)_+]<=K_tau,
    E[L_b^2|S]<=tau+K_tau/mu(S).

The event S and law are the same for all b, without requiring a common CRT
center for those layout residues. Hence the sufficient score is

    epsilon+E7+C_B+K_tau/(T_lower-tau)<1.

Only epsilon changes from the audited
[Chapter 63 curve](63-squared-load-stoploss-continuation.md). Exact substitution
produces the following bounds (the saved fractions decide the inequalities):

|B|tau|baseline score|score with E7|
|---:|---:|---:|---:|
|16384|2304|1.0158806119810460|1.0548900567929622|
|32768|9216|0.9767493741221471|1.0157588189340634|
|65536|16384|0.9514887262031105|0.9904981710150268|

At B65536 the D7-extension margin is greater than0.0095018. The permitted
extension remains any finite collection of additional distinct73-smooth
moduli outside D7={all e_p<=5, sum e_p<=7}, together with arbitrary finite
original classes whose largest prime is>73. All residues of added classes
are arbitrary and globally fixed. The original head may be replaced by
any subset, but arbitrary head phase replacement or additional D7-inside
smooth labels are not certified here. BBMST Theorem6.1 then supplies
unrestricted numerical-tail continuation as in
[Chapter 62](62-expanded-stopping-cutoffs-for-the-seven-phase-head.md)
and Chapter 63: global k includes 2 and unused primes, and continuation
starts at the next prime with standard uniform-base delta=1/2 kernels.

These are ordinary proofs and exact computations, not new Lean assertions.
Unrestricted Erdos#7 and phase-uniform head-law existence remain open.
Independent survival maximization gives the same exact optimum and all
seven forced-first-coordinate values. A separate actual-leaf policy audit
reconstructs all6511 positive boundary rows and2542 terminal masks, checks
3644013 absolute cylinder bounds, and recomputes the same root bad mass
from the normalized policy DAG. It does not import the candidate optimizer.
All verification commands exit zero under optimized Python.

The retained actual policy contains18796 positive group edges. Equal-mask
groups are expanded over their literal actual leaves, never over relabeled
phases. The resulting law retains the full transcript even when histories
share a cached continuation. The full554073-state value table is reproducible
from the exact recurrence; its digest is retained while the complete positive
policy itself is retained as data.




## Uniform transfer over complete layouts

The exact hypotheses and strengthened remaining-set induction in Chapter 55 apply. The
selected next core coordinate depends only on the observed transcript. At that full
transcript its chosen row satisfies all fixed cylinder caps; selecting a coordinate
reveals no unread value. The induction is uniform over every admissible continuation
subtree and every nonnegative vector of original-label weights. It bounds each actual
continuation first, then introduces independent auxiliary coordinates and applies the
one-coordinate comparison. It never conditions an actual unread coordinate on arbitrary
future observations or on auxiliary outcomes. Consequently no assertion of caps in every
fixed numerical order is needed.

For a fixed cylinder on any subset of named coordinates, apply that comparison to its one
fixed label and phi(t)=t, with cap one on unused coordinates. Its mass under the same
actual adaptive law is at most the product of the relevant caps. Equivalently, the product
of already-read cylinder indicators and unread caps is a supermartingale: reading an
irrelevant coordinate averages an unchanged remaining bound; reading a relevant coordinate
uses exactly that node's cylinder cap. This argument concerns one fixed event at a time
and never conditions on its future success. Summing these bounds over distinct smooth
exponent vectors outside D7 gives the same E7 union allowance.

For an enlarged finite family, choose complete prime-power heights resolving every
original label and every later cofactor. At each selected head coordinate append
independent uniform extra digits, while the adaptive choice uses the coarse transcript.
Previous extra digits reveal no additional coarse information. Every selected coarse row
retains its caps, and deeper cylinder caps become r_(p,H_p)p^(H_p-e). The original head
event and attained epsilon are unchanged. Thus the same fixed-cylinder comparison holds at
the full heights, including all higher-digit auxiliary tails.

Generate the complete head, then process tail primes q>73 in the original increasing
numerical order with the existing normalized delta=2/5 kernels. Each cofactor has already
been exposed. These kernels preserve the entire previous law, and the Chapter 55
comparison supplies the same aggregate C_B and full-layout convex bounds under the one
resulting law. For every divisor in a complete layout its residue is fixed separately,
with no common CRT-center requirement. With phi(u)=(u^2-tau)_+ on u>=0 and its increasing
convex extension to the real line, the same independent product supplies K_upper(tau).
Full moments retain all high-product mass. Finally use one common avoiding event S and one
conditioning, exactly as in Chapter 63; no independently optimized conditional laws are
combined.


## Continuous optimum of the same upper envelopes

Fix T>0, a real J, and nonnegative coefficients w_d for every positive
integer d with d^2<T. For 0<=tau<T define

    K(tau)=J-tau+sum_d (tau-d^2)_+ w_d,
    R(tau)=K(tau)/(T-tau).

Only the finitely many listed d can affect this interval. This statement
does not require the upper weights w_d to sum to one. Consequently it
applies directly to the upward-rounded atom bounds of Chapter63 without
silently normalizing them into a different distribution.

Between consecutive squared integers K is affine. Its one-sided slopes
at tau are

    K'_-(tau)=-1+sum_(d^2<tau) w_d,
    K'_+(tau)=-1+sum_(d^2<=tau) w_d.

The sign of each one-sided derivative of R is the sign of

    g_±(tau)=K(tau)+(T-tau)K'_±(tau)
            =J-T+sum_(d^2<tau or d^2<=tau)(T-d^2)w_d.

Inside each interval g is constant. Crossing d^2<T increases g by the
nonnegative quantity (T-d^2)w_d. If an interior threshold tau0 satisfies
g_-(tau0)<=0<=g_+(tau0), R is nonincreasing before tau0 and nondecreasing
afterwards. Continuity at each breakpoint proves global minimality over
every real 0<=tau<T. If both inequalities are strict, all earlier interval
slopes are negative and all later ones positive, so this minimum is unique.

For the existing envelopes take w_d=W_d/10^18 and J=J_upper. The selected
thresholds 2304,9216,16384 have strictly negative left and strictly positive
right derivative numerators. All arithmetic comparisons use exact rational
numbers retained in the
[continuous sign
certificate](../certificates/source_norms/source-budgets/continuous_stoploss_optimum.json).
The endpoint K(T) is also strictly positive
at each cutoff, so the ratio tends to positive infinity as tau approaches T.

| B | tau | left derivative numerator | right derivative numerator |
|---:|---:|---:|---:|
|16384|2304|-2343.37753269...|508.70075771...|
|32768|9216|-16.20617016...|3595.65028213...|
|65536|16384|-6062.81390617...|2507.78439788...|

Thus Chapter63's selected square thresholds are in fact the unique minima
of those same directed bounds over the full continuous interval. Chapter63
only asserted the weaker finite-grid conclusion; its computations and
inequalities remain unchanged. Replacing epsilon by a different attained
head loss adds a constant independent of tau, as does the D7 allowance,
so these minimizers also apply to the adaptive core7 continuation.

This optimality concerns the specified auxiliary upper envelope at each
fixed cutoff. It does not establish an optimum for the actual layout law,
other profiles, different cutoffs, or sharper joint comparison bounds.
It does rule out improving this envelope merely by selecting a fractional
threshold between the already scanned square breakpoints.


### Direct finite-difference form and independent signs

Only finitely many terms occur. K and R are continuous on their domain. Between
consecutive square breakpoints K(tau)=a+b tau. On that interval

    R'(tau)=(K(tau)+(T-tau)K'(tau))/(T-tau)^2
           =(a+bT)/(T-tau)^2.

Thus the derivative numerator g=a+bT is constant on each interval. This does not assert
that the derivative itself is constant or globally increasing. Equivalently, for u<v in
one such interval,

    R(v)-R(u)=g(v-u)/((T-v)(T-u)),

which proves the same sign conclusion without differentiation. At tau=d^2<T, K is
continuous and its slope increases by w_d; hence

    g_+(d^2)-g_-(d^2)=(T-d^2)w_d>=0.

The successive interval numerators are nondecreasing. If an interior square threshold
tau_star satisfies g_-(tau_star)<=0<=g_+(tau_star), every interval before it is
nonincreasing and every interval after it is nondecreasing, so it is a global minimum. If
both inequalities are strict, R strictly decreases on every interval before it and
strictly increases on every interval after it; continuity across the finitely many
breakpoints proves that the minimum is unique. One-sided zero signs may instead give a
flat interval. No claim that R itself is convex is required.

The exact direct formulas used by the independent calculation are

    g_-(t^2)=J-T+sum_(1<=d<t)(T-d^2)w_d,
    g_+(t^2)=J-T+sum_(1<=d<=t)(T-d^2)w_d.

Both are also checked against K(t^2)+(T-t^2)K'_±(t^2). The continuous value at the excluded endpoint is

    K(T)=J-T+sum_(d^2<=T)(T-d^2)w_d.

Its positivity implies R(tau) tends to positive infinity as tau approaches T from below.
This endpoint calculation confirms the boundary behavior; strict left/right signs already
prove the global minimum. The lemma uses only nonnegative w_d, not the unsupported
assertion that their upper bounds sum to one.

The [independent continuous verifier](../frontier/source-budgets/verify_continuous_stoploss_optimum.py)
sums each derivative numerator directly. It reads the earlier independent
tail and square-threshold certificates, not the current continuous
candidate result. All 21 corresponding exact fractions agree: threshold,
envelope value, both slopes, both derivative numerators, and endpoint
value at each cutoff. The positive jumps are also retained. All required
product states are at most 643, within the complete table through 26214;
no tail sweep or normalization of the upper mass coefficients is used.

## Exact programs and retained results

The [candidate](../frontier/source-budgets/adaptive_core7.py) minimizes bad
mass, uses ascending core-action order, and evaluates every remaining
action. The [independent survival program](../frontier/source-budgets/verify_adaptive_core7.py)
maximizes survival in descending action order and stops comparing actions
when survival one is attained. Both compute 554,073 nonconstant states
and 5232 terminal states. The candidate evaluates 1,123,561 core actions;
the independent calculation evaluates 1,119,147. Both check the unchanged
balanced profiles. All seven forced-first-coordinate values agree by
complementation, as do the root and all three continued-score pairs.

The [candidate certificate](../certificates/source_norms/source-budgets/adaptive_core7.json)
retains exact root and action values, all state counts, continued scores,
and the digest of the complete reproducible value table. The
[independent optimum certificate](../certificates/source_norms/source-budgets/adaptive_core7_verification.json)
and [actual-policy certificate](../certificates/source_norms/source-budgets/adaptive_core7_policy_verification.json)
retain every verification count and exact reconstructed root. The full
positive policy is stored as data; its numerator at each row is checked
by the actual-policy reconstruction.

The [continuous candidate](../frontier/source-budgets/continuous_stoploss_optimum.py)
and its independent verifier retain the full exact signs and endpoint
values in their respective certificates, including the
[independent continuous
result](../certificates/source_norms/source-budgets/continuous_stoploss_optimum_verification.json).
Every program supports `--write` and `--check` under
`python3 -B -I -S -O`, with source hashes over complete logical artifacts
and all required assertions active under optimization. The finite DP
resource guard fails without an optimum certificate if its bound is hit.
The supplied solution completes within that guard; elapsed time is not
part of exact reproducibility equality.
