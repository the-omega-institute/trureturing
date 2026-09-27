# 65. A ceiling for independent survivor marginals at the fixed cutoff

For the exact actual law attained in [Chapter 64](64-adaptive-core-policy-and-continuous-stoploss-optima.md),
the original154 selected moduli, B=16384, and the unchanged directed
second-moment test at tau=1, independently maximizing each selected
survivor-cylinder mass cannot supply enough credit. The complete query
calculation certifies credit13.066360948503299..., and seven independent
exact maxima strengthen it to14.080193148545026.... Even the best possible
credit within this independent-marginal method satisfies

    Delta_ind <= 31.39987604685079...
              < 31.479384957677265... = required threshold.

A rational certificate, with directions retained, is

    Delta_ind <= 31399876046851/1000000000000
               < 31479384957677/1000000000000
               <= required threshold.

The certified separation is39754455413/500000000000, greater than0.0795.
This conclusion concerns this actual law, E154, cutoff, fixed directed
constants and tau1 method. The joint layout deficit is not bounded above
by this independent-marginal ceiling. Another law, selected set, continuation
bound or survivor stop-loss comparison is outside the conclusion.

The input keeps all154 numerical moduli and phases, all twenty balanced
profiles, full original heights and the complete event H avoiding every
original head class. The law splits each retained positive group mass
across its actual leaves in increasing order up to the leaf cap, then
fills allowed terminal residues first. The earlier complete policy and
all earlier moment/product tables are reused as canonical dependencies.

## Complete-cylinder prices and the selected deficit

Let h=mu(H), epsilon=1-h and E154 be the original154 nonunit moduli.
For every relevant head divisor m put

    q_m=product_p r_(p,v_p(m)),
    M_m=max_(a mod m) mu(H intersect [a mod m]),
    c_m=3*1_(m in E154)
          +2*#{unordered distinct d,e in E154 : lcm(d,e)=m},
    Delta_ind=sum_m c_m(q_m-M_m).

There are4660 distinct m and sum_m c_m=24024. Each residue is fixed before
sampling. A pair of layout cylinders intersects in either no points or
one cylinder modulo their lcm, so M_lcm bounds its H-submeasure even when
the independently chosen layout residues are incompatible. The common
product-cylinder prices give M_m<=q_m.

Expanding a complete head load L_c, including its unit divisor, gives

    integral_H L_c^2
      =h+3 sum_(d>1) mu(H intersect A_(d,c_d))
          +2 sum_(1<d<e) mu(H intersect A_(d,c_d) intersect A_(e,c_e)).

The complete auxiliary moment has the corresponding expansion with h
replaced by1 and every cylinder submeasure replaced by its price. Every
price-minus-submeasure difference is nonnegative. Keeping just E154's
unary and pair terms therefore proves, for every complete head layout,

    integral_H L_c^2 <= J_head-epsilon-Delta_ind.

Any proved lower bound for Delta_ind is a usable uniform credit. The
residues attaining different M_m need not arise from a single head
layout. Accordingly Delta_ind can be smaller than the infimum of the
actual selected-layout deficit. An upper bound for Delta_ind supplies no
upper bound for that stronger joint quantity.

## A full-history query upper bound on each marginal

The actual law is fixed to the retained Chapter64 policy: each positive
group mass is split over its matching literal leaves in increasing order,
and each terminal row fills allowed residues before forbidden residues.
The event H means avoidance of all 154 original classes after every head
coordinate. No residue, original-label identity, or conditional row is
changed by the following query calculation.

At a retained boundary s=(U,A), a label in A has matched every coordinate
already observed. Its remaining condition depends only on the unread
coordinates. Consequently the future avoidance event H_s and the
specified future policy depend only on s. Already observed actual values
are still present in the underlying law; the boundary is only sufficient
for this future calculation. A previously satisfied original label gives
H_s empty. Otherwise the retained row and terminal numerators give its
exact survival probability h_s.

Let m divide the product of the remaining complete coordinate alphabets.
For a globally fixed collection a of its prime-power residues, write
F_s(a)=Pr_s(H_s and the future tuple equals a modulo m).
Define B_s(m) recursively as follows. B_s(1)=h_s. Bad absorbing states
give zero for every query. If the policy at s reads p, its actual leaf
weights are nu_s(x), with child s_x. If p does not divide m, set

    B_s(m)=sum_x nu_s(x) B_(s_x)(m).

If p^e is the p-part of m and m'=m/p^e, set

    B_s(m)=max_(b mod p^e)
             sum_(x=b mod p^e) nu_s(x) B_(s_x)(m').

The same child boundary can arise from different literal x. Every x and
its actual assigned mass is included before grouping by b. Thus original
phases and p-adic residues are retained, including higher digits.

For every fixed a, induction on the number of unread coordinates proves
F_s(a)<=B_s(m). At a nonqueried coordinate, expand by the actual next
leaf and apply the child bound separately. At a queried coordinate the
fixed p-component of a specifies one bin b; each child has the same fixed
remaining residue a', and its value is bounded by B_(s_x)(m'). Maximizing
over b only enlarges the bound. Each child bound may itself be attained
by a different remaining residue, so this procedure relaxes the common
globally fixed residue requirement. It neither asserts simultaneous
attainment nor combines different actual probability laws. The policy's
next coordinate can vary by s: the argument applies at its actual node
and does not require a fixed read order.

At a terminal mask the specified policy uses a fixed row for each of
the thirteen remaining coordinates. H_s is the intersection of their
allowed-residue events. For an unqueried terminal coordinate let A_q be
its assigned allowed mass in denominator units. For a queried terminal
coordinate its largest allowed point mass is min(c_q,A_q), since the
actual row fills allowed residues in increasing order up to c_q each.
Multiplying these factors and dividing by the fixed product denominator
is the exact maximum conditional on that terminal boundary. The earlier
relaxation still permits the terminal maximizing residues to vary across
different boundaries; hence it remains an upper bound at the root.

All arithmetic can use the original state denominator D(U). Every core
edge mass is an integer divided by d_p, and D(U)=d_p D(U\{p}). At a node,
weighted sums and residue-bin maxima are therefore integer numerator
operations. Terminal numerators use the unchanged product of terminal
denominators. No probability rounding or floating-point comparison is
involved.

For every completed query m, the returned B_root(m) bounds
M_m=max_(a mod m) mu(H intersect {x=a mod m}). Two independent generic
bounds are h/m<=M_m (partition H into m residue classes) and M_m<=q_m
(the fixed-cylinder cap theorem). The relaxed query also stays at most
h and q_m: at each node its successful branch is a subevent of H_s,
and at each queried coordinate its bin mass is at most the prescribed
absolute depth cap. This latter induction may allow future residue
choices to depend on earlier values and still uses the same deterministic
cap at each actual node. The program actively verifies the root bounds.


The [complete query program](../frontier/source-budgets/survivor_cylinder_queries.py)
retains all4660 results in its
[certificate](../certificates/source_norms/source-budgets/survivor_cylinder_queries.json).
It reconstructs6511 core rows,2542 terminal masks,1,886,217 actual core
leaves,1,423,235 positive actual leaves and18,796 positive group edges.
The query recursion uses1,749,338 nontrivial cached states,5,102,063 calls
and29,172,312 residue-bin terms. All4660 queries complete; remaining
potential is zero. There are4492 positive-credit and168 zero-credit
queries. Every exact modulus, coefficient, price, upper bound and credit
is retained, with total

    Delta >= 4721409227962983715156146407022642708305664836319697
              /361340793092341676034117718505859375000000000000000
          =13.066360948503299... .

This scalar recursion permits the maximizing residue to change across
histories. It does not claim exact marginal maxima or simultaneous
attainment. The head policy itself is fixed.

## Independent fixed-residue controls

Let U_i be the denominator of the balanced leaf cap and A_i its numerator.
At a positive policy state v=(u,L), the next axis i is fixed by the retained
row. A branch group has its recorded integer allocation b_g in U_i units.
The actual policy splits b_g over that group's original leaves in increasing
order, each taking at most A_i. The audit reconstructs the original masks
and this allocation for every row whose chosen axis is constrained by one
of the eight queries. For other axes, only the total b_g is used, exactly
as required when the query imposes no restriction on that coordinate.

For fixed m,a, write `q_i=gcd(m,p_i^H_i)`. Let

    w_(v,g)(m,a) = sum of actual integer leaf allocations in group g
                   with x == a mod q_i.

No residue is reselected at a descendant history. The same a is used at
every state, and the digits and original labels are unchanged.

Put `D_u=(product of terminal U_i)*(product of remaining core U_i)`.
Deleting axis i gives the exact identity `D_u=U_i D_(u\{i})`.
At a terminal mask, the audit builds each of the thirteen actual terminal
rows, filling allowed named residues before forbidden named residues.
The product of their assigned allowed integer masses is N_(0,L).
All queried primes are core primes, so there is no terminal congruence
restriction. This gives terminal survival probability N_(0,L)/D_0.

An absorbing covered child contributes zero to the head survival event.
Every other positive child is a retained row or terminal mask. Inductively,

    N_v(m,a) = sum_(positive groups g) w_(v,g)(m,a) N_child(m,a),
    probability_v(survive H and meet all remaining query conditions)
          = N_v(m,a)/D_u.

This follows by multiplying the actual row probability w/U_i by the
child probability N_child/D_child. Remaining-coordinate bitmasks strictly
decrease, so the stored topological order supports exact integer recursion.
The boundary state suffices because the actual retained policy chooses its
row from that state; fixed query conditions on earlier coordinates have
already been enforced by the ancestral weights.

At the root the result is exactly `mu(H intersect [a mod m])`. CRT gives a
partition over `a=0,...,m-1`; the audit independently verifies that these
masses sum to the same exact h=mu(H) for every m, and that their maximum is
at least h/m. It then compares that maximum to the independently produced
history-relaxed upper bound. All comparisons use rational numbers.

## Exact-query comparisons

The decimals below abbreviate the complete fractions in the [literal-query
certificate](../certificates/source_norms/source-budgets/survivor_cylinder_literals.json).

| m | Maximum actual survivor-cylinder mass | Maximizing a | Relaxed upper |
|---:|---:|---:|---:|
|1|0.6220842079481284|0|0.6220842079481284|
|3|0.33340018989507425|1|0.33340018989507425|
|5|0.20428287359784109|1|0.27403474608081124|
|7|0.13432601555098259|5|0.16653177254117527|
|9|0.22022230191239883|7|0.22022230191239883|
|15|0.10503839448796097|11|0.14408621245721567|
|21|0.07545912266225215|5|0.09493425464977773|
|35|0.05225139768740214|6|0.07239059346642614|

The maximum is bounded by the relaxed value in all eight cases. Equality
holds for1,3,9. The strict gaps for the other five quantify lost common
fixed-residue information for these inputs; they establish no universal
size or sign beyond the actual comparisons.

The computation reconstructs33,046 terminal coordinate rows and1,614,170
terminal atoms. It reconstructs975 queried core rows with306,857 actual
leaves, and performs625,056 integer state-row updates for96 fixed residues.
The unchanged group allocations suffice for the unconstrained core axes.


The [independent literal program](../frontier/source-budgets/verify_survivor_cylinder_literals.py)
uses the actual positive policy and complete terminal survival. Its96
masses sum to the same h separately for every modulus. It reads the
relaxed result only for exact comparisons, and imports none of the
relaxed query implementation. These eight moduli are a production
control, not an independent recomputation of all4660 query values.

Replacing the seven nonunit entries adds exactly

    76178185733932679688573372874767911941
    /75138850128056049070312500000000000000
    =1.0138322000417272...,

so the mixed bound becomes

    Delta >= 175439591696159138580227501246383867904127727841843
              /12460027348011781932210955810546875000000000000000
          =14.080193148545026... .

The other4653 entries retain their rigorously relaxed upper bounds.

## A ceiling from the actual possible residue support

For every queried m define the literal residue set

    Z_m={a mod m : a != a_d mod d for every original d dividing m},
    z_m=|Z_m|.

Every point of H projects into Z_m. Since h>0, z_m>0, and partitioning
H over these possible residues gives M_m>=h/z_m. Hence

    Delta_ind <= sum_m c_m(q_m-h/z_m).

The [support and combination program](../frontier/source-budgets/survivor_cylinder_ceiling.py)
counts all4660 z_m by exact finite bitsets. Its
[certificate](../certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json)
retains every support count and h/z_m, the unstrengthened ceiling
32.72671445059612..., and the seven exact replacements.
For the seven known nonunit maxima use M_m itself in place of h/z_m.
This yields the strengthened ceiling31.39987604685079.... This is an
upper bound on what further exact independent-marginal queries could
achieve; it does not assume their separate optima are jointly attainable.

The [independent ceiling verifier](../frontier/source-budgets/verify_survivor_cylinder_ceiling.py)
marks forbidden arithmetic-progression slices in byte arrays, without
using the bitset geometric-series formula. It reproduces every z_m over
255,198,568 literal byte cells, independently reconstructs all coefficients
and prices, verifies the full recorded credit sum, substitutes the seven
exact maxima, and rederives the required threshold. Its
[certificate](../certificates/source_norms/source-budgets/survivor_cylinder_ceiling_verification.json)
retains the directed rational separation and count-table digest
`ca68f5671df109521aea47708c4727409951d2690ac42ae85d22256b4212162e`.
This verifies all support counts and credit arithmetic; the other4653
policy-query upper bounds rely on the ordinary induction above.

## Transport of the same head submeasure to the tail

This is the existing ordered-pair and Cauchy--Schwarz transport of
[Chapter 08](08-arbitrary-head-transfer-by-the-joint-load-invariant.md),
using the full-history caps of
[Chapter 55](55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md).
It introduces no common-center assumption or new general theorem.

Let Q_head and Q_tail be coprime complete finite prime-power moduli, with divisor sets A
and B. Sample all complete head coordinates X first, by any admissible law mu, and then
all tail coordinates Y using normalized kernels. Let nu be this one actual joint law; its
head marginal is mu. Each full-history tail row has deterministic cylinder caps r_(p,e),
with r_(p,0)=1. These caps are conditional on the complete head and the actual preceding
tail transcript; marginal caps alone are insufficient.

H is an event measurable with respect to the complete head, and h=mu(H). For every head
layout c=(c_a mod a)_(a in A), including a=1, define

    L_c(x)=sum_(a in A) 1_(x=c_a mod a).

Assume the same finite constant M_H satisfies

    integral_H L_c(x)^2 dmu(x) <= M_H

for every such independently chosen head layout. There is no normalization by h here, and
c is globally fixed before x is sampled. In particular M_H>=h because each layout contains
a=1.

For tail divisors b,e let

    q_(b,e)=product_(tail primes p) r_(p,max(v_p(b),v_p(e))),
    J_tail=sum_(b,e in B) q_(b,e).

This is the exact second moment of the independent nested tail-divisor count D_tail. It is
at least one. Larger certified bounds, including finite-prime infinite-height envelopes,
may replace J_tail.

For every complete layout on divisors ab of Q_head Q_tail, choosing one residue independently for each pair (a,b),

    integral_H L_full^2 dnu <= J_tail M_H.                 (1)

Here H in the integral denotes its lift H times the tail space. The full layout may have
mutually incompatible residues, and different a in a fixed tail layer b may have different
tail residues.

## Independent ordered-pair proof

For each full divisor ab, use CRT to split its fixed residue into a head condition A_(a,b)
and a tail condition B_(a,b). For every fixed b the head conditions as a ranges over A
constitute one legitimate complete head layout; denote its load by L_b(x).

Fix a complete head value x of positive probability. For any two full divisors
(a,b),(a',e), their tail conditions intersect either in the empty set or in one fixed
cylinder modulo lcm(b,e). The deterministic full-history row caps imply

    Pr(B_(a,b) intersect B_(a',e) | X=x) <= q_(b,e).

For the existing fixed numerical tail order, iterated conditional expectation proves this
product bound directly. A legal adaptive read-once tail would also permit the strengthened
remaining-set cylinder argument, but this extension is unnecessary for the current
numerical-tail application. This step does not claim caps conditional on arbitrary future
events. The head value was sampled completely before any tail coordinate.

Expanding L_full^2 into ordered pairs and applying that bound yields

    E[L_full^2 | X=x]
       <= sum_(b,e in B) q_(b,e) L_b(x)L_e(x).

Because H is head-measurable, integrate this conditional inequality over H. Cauchy–Schwarz
for the finite positive submeasure 1_H mu gives, for every pair of head layouts,

    integral_H L_b L_e dmu
       <= sqrt(integral_H L_b^2 dmu * integral_H L_e^2 dmu)
       <= M_H.

The common uniform quantifier over all head layouts is exactly what permits this step;
independently attainable maximizers need not coincide. Summing q_(b,e) proves (1). This
proof never assumes independence of the actual head or tail coordinates.

## Conditioning on the common final survivor event

Let S be any event contained in the lifted H, with

    s=nu(S)>=lambda=h-C-E>0.

The actual event S may depend on every processed coordinate; only the earlier H must be
head-measurable. Since every complete layout load includes the unit divisor, L_full>=1,
and hence

    integral_S (L_full^2-1) dnu
       <= integral_H (L_full^2-1) dnu
       = integral_H L_full^2 dnu-h
       <= J_tail M_H-h.                                  (2)

The last upper bound is nonnegative because M_H>=h and J_tail>=1. Consequently the same
single conditioning for every layout gives

    E[L_full^2 | S]
       <= 1+(J_tail M_H-h)/s
       <= 1+(J_tail M_H-h)/(h-C-E).                       (3)

Taking the supremum over the complete fixed layouts preserves the bound. If the right side
is below the valid continuation threshold T, the existing BBMST interface applies. The
allowance C must bound the relevant actual processed-tail loss under this same normalized
law, and E must have its separately proved scope. This lemma does not improve those loss
bounds.


All complete enlarged head heights must be included in M_H, including
head-prime cofactors of later moduli. Independent uniform extra head
digits preserve H and the selected original marginals. The complete
geometric J_head envelope bounds the remaining higher-digit terms, so
M_H=J_head-epsilon-Delta remains valid at every required finite height.
For the finite set of tail primes, increasing height enlarges the
nonnegative auxiliary divisor count, and its established finite second
moment permits the infinite geometric envelope. No high-product mass or
higher geometric digits are dropped.

The head-only measurability of H is essential. The final S may depend on
all processed coordinates and is used only through S subset H and its
same-law mass lower bound. The complete head is sampled before the tail;
no cap conditional on an arbitrary future event is asserted.

## Directed positive-product criterion at B16384

Let J_bar,T_lower,C_upper,E_upper be the unchanged directed constants from
[Chapter 62](62-expanded-stopping-cutoffs-for-the-seven-phase-head.md)
and [Chapter 63](63-squared-load-stoploss-continuation.md).
The exact full-height head auxiliary moment J_head is retained in the
Chapter62 budget. Independence of the auxiliary products gives
J_full=J_head J_tail, so

    U=J_bar/J_head >= J_tail,
    U=49.110681079535965... .

For a valid nonnegative head bound M_H=J_head-epsilon-Delta, use the
upper factor only in the positive product U M_H. With h=1-epsilon,
s=h-C_upper-E_upper>0 and T=T_lower>1, the sufficient tau1 score is

    epsilon+C_upper+E_upper
      +[U(J_head-epsilon-Delta)-h]/(T-1) < 1.

Solving this strict inequality gives

    Delta > J_head-epsilon-[(T-1)(h-C_upper-E_upper)+h]/U.

Taking E_upper=0 gives31.479384957677265... . The named D7-complement
allowance gives96.64506446379198... . An upper bound on J_tail is never
used as an independently subtracted saving. The positive residual moment
is established before any algebraic rearrangement.

At the mixed certified credit14.080193148545026..., these scores are
1.010415495054979... baseline and1.0494249398668953... with D7 allowance.
Even substituting the favorable independent-max ceiling into the
baseline score gives1.0000475955824055...>1. The directed rational
separation at the start therefore excludes success of this fixed
independent-max tau1 test, even if all remaining M_m were known exactly.

This is a method boundary, not a covering-system impossibility result.
It neither bounds the stronger joint selected-layout gap nor permits
subtracting this second-moment saving from Chapter63's nonlinear
stop-loss envelope at tau>1. It supplies no phase-uniform statement,
new head optimum, new tail bound, or unrestricted Erdős7 conclusion.

## Reproducible retained computations

Four programs support `--write` and `--check` under `python3 -B -I -S -O`.
Their assertions remain active under optimization; relative source hashes
bind complete logical certificates. The query guard permits120 seconds
and2,000,000 nontrivial query states. The actual-residue verifier and
independent support verifier have60-second guards; candidate support
counting has a30-second guard. Canonical publication requires complete
results and fails if a required guard is reached. Runtime is not part of
exact certificate equality.

The programs reuse the existing input, policy and complete moment tables.
They evaluate the fixed law and selected method only; they perform no
head-policy optimization or production-tail sweep. The complete4660
query table, all4660 support counts and all96 actual residue masses are
retained. Ordinary proofs supply the unrestricted finite-height
quantifiers; the finite computations establish the stated fixed-input
values and method boundary.
