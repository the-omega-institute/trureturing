# 66. Shared-phase triangles and the common-center obstruction

For the unchanged actual survivor law of
[Chapter 64](64-adaptive-core-policy-and-continuous-stoploss-optima.md),
jointly optimizing six unary and nine pair terms adds the exact credit

    kappa = 377209134649567678978054910438243767513
            /1769574368957841735351562500000000000000
          = 0.2131637648389528... .

The certified credit from
[Chapter 65](65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md)
therefore increases from14.080193148545026... to14.29335691338398....
The baseline B=16384, tau=1 score becomes1.0102878910741198...>1, so
this improvement does not meet the sufficient criterion. Enlarging
only this triangle block to all seven core primes, while keeping the
other bounds fixed, can supply certified credit at most18.790728637141143...,
still below the required31.479384957677265....

The actual six-variable maximizer happens to share a CRT center.
That is a property of these particular data. An explicit measure on
Z/15 has unrestricted squared-load maximum63 and common-center
maximum60; a strictly positive variant has maxima109 and108. Hence a
common-center restriction is not valid for arbitrary finite measures.
These examples do not claim realization by the actual Chapter64 law
or by an admissible capped survivor law.

## One selected objective under the same survivor submeasure

Let nu(A)=mu(H intersect A), h=nu(whole space), and write

    f_m(a)=nu([a mod m]),     M_m=max_(a mod m) f_m(a).

The law, all154 original numerical moduli and phases, all twenty
balanced profiles, event H, head heights and directed tail constants
are those already retained in Chapters64 and65. Every layout residue
below is fixed independently before sampling a point from this law.

Select the moduli V={3,5,7,15,21,35}. Include one coefficient3 unary
term for each element of V and the coefficient2 pair terms

    {3,5}, {3,15}, {5,15},
    {3,7}, {3,21}, {7,21},
    {5,7}, {5,35}, {7,35}.

Call this set of nine distinct unordered pairs E. For a layout c define

    F(c)=3 sum_(m in V) f_m(c_m)
           +2 sum_({d,e} in E) nu([c_d mod d] intersect [c_e mod e]).

This objective contains selected nonconstant terms of the square-load
expansion. It does not contain the constant h. Each pure-prime unary
appears once, although its modulus belongs to two triangles. Composite
unaries appear once in their own triangle. The six other unordered
pairs among V, and all terms involving other original moduli, remain
in the previously bounded remainder.

For a prime pair (p,q) in {(3,5),(3,7),(5,7)}, fix a_p and a_q and
let r be their CRT residue modulo pq. The pure-pure intersection has
mass f_(pq)(r). For a composite residue b, a pure/composite intersection
is empty if its pure congruence fails; otherwise it is the whole
composite cylinder. Therefore define

    K_pq(a_p,a_q)
      =2 f_(pq)(CRT(a_p,a_q))
         +max_(b mod pq) [3+2*[b mod p=a_p]+2*[b mod q=a_q]] f_(pq)(b).

After fixing the same a3,a5,a7 throughout, the three composite
variables occur in separate selected terms. Their maximizing choices
can be made simultaneously. Consequently the exact unrestricted
selected maximum is

    J_triangle=max_(a3,a5,a7)
      [3*(f3(a3)+f5(a5)+f7(a7))
        +K_(3,5)(a3,a5)+K_(3,7)(a3,a7)+K_(5,7)(a5,a7)].

There are105 pure assignments and71
conditional pure-pair assignments across the three edges. Every
six-residue assignment extends to a full layout by arbitrary choices
of the remaining divisor residues. No common-center condition is
imposed on the composites.

The independent marginal upper sum for exactly these terms is

    U_triangle=3*(M3+M5+M7)+9*(M15+M21+M35).

Each composite coefficient9 is its unary coefficient3 plus three
pair coefficients2. Hence kappa=U_triangle-J_triangle is nonnegative.
This is finite variable elimination with shared variables; the
quantitative result here is its exact application to the fixed law.

## Exact value and insertion in the full-layout bound

The complete actual residue tables are canonical dependencies from
Chapter65. Each composite table projects to both prime tables, and
all six tables sum to h. Conditional maximization and independent
literal CRT enumeration agree on all105 fixed-pure maxima and all
attaining composite tuples. The latter enumerates all1,157,625
six-residue layouts.

| Quantity | Exact value or decimal abbreviation |
|---|---|
| Selected maximum J_triangle | 36607682588876532484279200989519873150173 / 9392356266007006133789062500000000000000 |
| Independent upper U_triangle | 250963651973107546072557700841998585455323 / 61050315729045539869628906250000000000000 |
| Additional credit kappa | 0.2131637648389528... |
| Unique maximizing layout (c3,c5,c7,c15,c21,c35) | (1,1,6,1,13,6) |
| Selected maximum, decimal | 3.897603705831278... |
| Independent upper, decimal | 4.110767470670231... |

The maximizing tuple is induced by76 modulo105. The independent
verifier also checks the common-center restriction and obtains the
same maximum for this particular input. This equality is an output,
not a premise of the optimization.

The unique maximum of f3 occurs at residue1, whereas the unique
maximum of f15 occurs at residue11, whose residue modulo3 is2.
Those two unary maxima cannot be used while their pair simultaneously
attains M15. The shared-variable optimization measures the total
compatibility loss across the three triangles.

For every full layout, partition the square-load terms into F and
the remainder. Chapter65's mixed certificate already uses the exact
M_m for all six selected moduli. Replace just U_triangle by J_triangle;
keep every remainder bound. Thus, with epsilon=1-h,

    Delta_joint >= Delta_mixed_lower+kappa,
    integral_H L_c^2
        <= J_head-epsilon-(Delta_mixed_lower+kappa).

Each selected unary and pair term is replaced once. Their gaps are
not counted again among the remainder. Independent higher head digits
preserve these original cylinder marginals, so the complete-height
and head-measurability arguments of Chapter65 apply without change.

The new certified lower credit is exactly

    5164772923034071641348857983148846300541460489307197
    /361340793092341676034117718505859375000000000000000.

Let U=J_bar/J_head be the same directed upper tail factor, and let
T,C,E be the unchanged directed quantities at B16384. The retained
residual head bound is nonnegative and at least h, so the upper factor
is applied only in the positive product

    U*[J_head-epsilon-(Delta_mixed_lower+kappa)].

The sufficient score and its strict credit threshold remain

    epsilon+C+E+[U*(J_head-epsilon-Delta)-h]/(T-1) < 1,
    Delta > J_head-epsilon-[(T-1)*(h-C-E)+h]/U.

The baseline E=0 score is1.0102878910741198...; the named D7-complement
allowance gives1.049297335886036... . Both exceed1. The baseline
achieved-credit shortfall is17.186028044293288.... The kappa above
must be added to the proved lower credit14.080193148545026..., not to
the independent-method upper ceiling31.39987604685079.... Chapter65's
ceiling for Delta_ind remains valid; this additional joint relation
lies outside that independent-marginal method.

## Capacity of the complete seven-prime triangle block

Keep the same nu and put P={3,5,7,11,13,17,19}. Take

    V7=P union {pq:p<q in P},
    E7={{p,q},{p,pq},{q,pq}:p<q in P}.

There are28 distinct unary labels and63 distinct unordered pairs.
All labels belong to the original E154. Use coefficient3 for each
unary and coefficient2 for each pair. Every other Chapter65 mixed
upper term is kept fixed.

Write B_m for the previously certified marginal upper bound: use
the retained exact small-modulus maximum where available and the
retained query upper bound elsewhere. The selected block's old upper
contribution is

    U7=3 sum_(p in P) B_p+9 sum_(p<q in P) B_(pq).

Let J7 be the exact maximum of this whole block over one fixed
residue c_d for each d in V7. To lower-bound J7, choose these layout
residues independently and uniformly. This averaging occurs only on
the auxiliary space of layouts; it does not change nu. For each
fixed point x and distinct numerical labels d,e,

    Pr_c(x in [c_d mod d])=1/d,
    Pr_c(x in [c_d mod d] intersect [c_e mod e])=1/(de).

The second equality follows from independence of the chosen layout
residues, even when gcd(d,e)>1. It does not assert independence of
the cylinders under nu. Integrating this finite sum proves

    J7 >= A7
       =h*[3 sum_(d in V7) 1/d+2 sum_({d,e} in E7) 1/(de)].

Exact optimization of this block therefore decreases its old upper
bound by at most U7-A7. Keeping the same remainder bounds, the
resulting certified credit can be no larger than

    Delta_mixed_lower+U7-A7.

| Quantity | Decimal abbreviation of retained rational |
|---|---:|
| U7 | 7.781581692934564... |
| A7 | 3.071046204338448... |
| Additional-credit capacity U7-A7 | 4.710535488596116... |
| Upper bound on credit from this replacement | 18.790728637141143... |
| Required baseline credit | 31.479384957677265... |
| Remaining gap, lower bound | 12.688656320536124... |

The exact fractions certify the strict comparison. Thus enlarging
only this triangle block cannot make the stated B16384 tau1 test
pass while every other bound remains fixed. The three smaller
triangles are already contained in this block; kappa must not be
added again. This is a bound on credit obtainable from this fixed
replacement, not an upper bound on the actual full joint deficit.
It does not constrain changes using unselected cross-composite
pairs, higher powers, labels with three or more prime factors,
different laws, cutoffs or stronger stop-loss criteria.

## A common CRT center can lose the maximum

For x in Z/15 give weight2 to x=3,6,9,12, weight1 to x=5, weight3
to x=10, and weight0 elsewhere. Its total mass is W=12. For
independently selected a modulo3, b modulo5 and t modulo15 set

    Q(a,b,t)=sum_x w(x)*(1+[x mod3=a]+[x mod5=b]+[x=t])^2.

The constant1 is the class modulo1. Unlike F above, Q includes the
constant mass W. There are225 unrestricted layouts and15 common
centers (a,b,t)=(t mod3,t mod5,t).

Index the CRT array by r=x mod3 and c=x mod5. It is

    r=0: 0 2 2 2 2
    r=1: 3 0 0 0 0
    r=2: 1 0 0 0 0.

Let R_r and C_c be row and column sums, and write t=(u,v) in these
coordinates. Expansion gives

    Q(r,c,t)=W+3R_r+3C_c+2w_(r,c)
                 +w_(u,v)*(3+2*[u=r]+2*[v=c]).

For a common center this is W+3R_r+3C_c+9w_(r,c). The row sums
are8,3,1 and the column sums are4,2,2,2,2. The exhaustive case table is

| Selected row | Selected column | Max over t | Common-center value |
|---|---|---:|---:|
|0|0|63|48|
|0|1,2,3,4|60|60|
|1|0|60|60|
|1|1,2,3,4|42|27|
|2|0|44|36|
|2|1,2,3,4|31|21|

Therefore max Q=63, uniquely at (a,b,t)=(0,0,10), while the
common-center maximum is60 at t=3,6,9,10,12. At the unrestricted
maximizer, the four weight2 points contribute32, x=10 contributes27,
and x=5 contributes4. Normalizing to a probability measure gives
maxima21/4 and5, separated by1/4. Removing the constant mass gives
selected unary/pair maxima51 and48 and preserves the gap3.

For a strictly positive example add1 at all15 residues. Under the
uniform unit measure the displayed expansion is

    44+2*[u=r]+2*[v=c].

This equals48 at common centers,46 when exactly one relation holds,
and44 when neither holds. Each shifted common-center value is at
most60+48=108. Every shifted noncenter value is at most63+46=109,
and (0,0,10) attains109. The new total mass is27. Its probability
normalization has maxima109/27 and4, separated by1/27.

These are counterexamples to a universal common-center reduction
for finite measures, including strictly positive probability laws.
No minimality of support or total mass is asserted. They do not
show that the actual64 law or any admissible capped survivor law
has this obstruction. A common-center reduction for a narrower
class requires an additional hypothesis and proof.

## Retained computations and scope

The programs support `--write` and `--check` under
`python3 -B -I -S -O`; all required assertions remain active under
optimization. Relative hashes bind complete logical certificates.

| Program | Exact retained output |
|---|---|
| [shared_phase_triangles.py](../frontier/source-budgets/shared_phase_triangles.py) | [Triangle certificate](../certificates/source_norms/source-budgets/shared_phase_triangles.json): all71 conditional edge records, all105 fixed-pure records and every maximizing tuple |
| [verify_shared_phase_triangles.py](../frontier/source-budgets/verify_shared_phase_triangles.py) | [Independent certificate](../certificates/source_norms/source-budgets/shared_phase_triangles_verification.json): all105 conditional maxima, 1,157,625 layouts enumerated via literal CRT intersections and both directed scores |
| [prime_pair_block_capacity.py](../frontier/source-budgets/prime_pair_block_capacity.py) | [Capacity certificate](../certificates/source_norms/source-budgets/prime_pair_block_capacity.json): all28 unary bounds, all63 edges, exact averaging and threshold comparison |
| [common_center_counterexample.py](../frontier/source-budgets/common_center_counterexample.py) | [Counterexample certificate](../certificates/source_norms/source-budgets/common_center_counterexample.json): all450 layout scores and30 center scores for the two measures |

The generic triangle optimizer takes complete consistent marginal
tables and distinct coprime pairs. The independent verifier uses
literal intersection tables and a60-second guard, requiring complete
enumeration. The generic squared-load enumerator accepts arbitrary
nonnegative integer weights and class moduli; the two examples use
the retained [input](../frontier/source-budgets/common_center_counterexample_input.json).
Every counterexample score is also checked against the independent
row-column expansion.

No actual head-policy optimization, new tail sweep or new Lean
declaration is involved. The actual-law computation establishes a
fixed-input joint correction and a boundary for enlarging one block.
The ordinary proofs establish the optimization identity, its valid
insertion in the same-law inequality and the universal-reduction
counterexamples. The full joint optimization, changes of method and
the unrestricted odd-covering problem remain unresolved.
