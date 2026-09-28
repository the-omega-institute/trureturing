# Four fixed shallow families survive arbitrary nonternary heights

Each of four specified191-original phase patterns admits every finite
distinct-odd-modulus extension supported on3,5,7,11,13,17,19,23,29 with
whole-family v3<=2. Added phases and all nonternary heights are
arbitrary. Quantitative positive Haar-density lower bounds appear below.
The base191 phases remain fixed hypotheses; this does not settle the
universal arbitrary-phase question or unrestricted Erdős#7.

The two literal heads are those of the
[all-source direct scalar obstruction](715-actual-heads-obstruct-every-law-in-the-direct-scalar-continuation.md).
The source uses the [sixteen simultaneous conditional responses](716-one-actual-head-supplies-sixteen-joint-continuation-responses.md).
Its shallow cylinder bounds pay all later higher-power originals and
control the complete query sum on this same source. This preserves the
relationship between each high-precision query and its first residue.

## Literal heads

Both have pure originals0mod3,1mod9,0mod5,0mod7, so the retained leaves
are(4,7,2,5,8), and the pure live5/7 digit laws are uniform on four and
six nonzero roots. The seven mixed originals are:

| modulus | opposite-root residue | same-root residue |
| --- | ---: | ---: |
|15|11|1|
|45|2|22|
|21|1|1|
|63|58|16|
|35|3|3|
|105|74|74|
|315|187|47|

Their actual legal head sets contain75 and85 cells, respectively, out
of120 pure-live cells. The separate minimax certificate gives exact
minimum complete scalar query costs47663/23808 and18015/8704, each
strictly greater than8038/4235, the direct six-prime continuation target.
Those optimality claims are reused from that separate primal/dual
certificate, not re-proved by the joint checker.

## Four actual191-original families

Add pure0modq forq=11,13,17,19. For every nonempty subsetD of these four
primes and every cofactorc=3^h5^a7^b withh=0,1,2 anda,b=0,1, include
one original of modulusc product_(q inD)q, exceptc=1 with|D|=1, whose
pure original is already listed. This supplies176 further mixed
originals, hence191 distinct odd originals in total.

In the ALIGNED layout, the head phase of eachc>1 equals the phase of
the already listed head original of numerical modulusc; every outside
coordinate has root1. Thus that head predicate is actually null on the
legal head mask. Only thec=1 outside mixed groups remain active. This
is a declared phase relationship in one family, not an independent
choice at each surviving cell.

In the SPREAD layout, one deterministic formula in the checker assigns
all head and outside phases once from the support mask and the cofactor
index. It varies outside roots and head phases between full numerical
originals. Each complete phase is reconstructed by CRT and checked
against its components. The JSON retains every one of the191(a,m)
pairs and a digest of the full list; no source/query optimization or
per-cell phase choice is used.

At each actual head cell, the unary outside survivor sets are computed
from those originals. Each larger support group's actual first-root
union is deduplicated after unary exclusion, giving its exact
unnormalizedkappa_D. The conditional polynomial responses then come
from this same data. Usef=1 on the actual legal head mask; no LP is
needed for these four instances.

## A general common-source prefix-tail lemma

PutQ={5,7,11,13,17,19}. Leteta be ONE finite nonnegative measure on the
core CRT coordinates3,Q, constant in every deeper nonternary digit
conditional on the joint first digits. Equivalently, its density
relative to Haar is a function only ofx mod9 andx modq forq inQ.
LetS=eta(1). Forj in{0,1,2} andD subsetQ, put

    d(j,D)=3^j product_(q inD)q,
    c_(j,D)=max_(a modd(j,D))eta(x=a modd(j,D)),
    L_D=product_(q inD)q/(q-1).

Take simultaneous upper boundsC_(j,D)>=c_(j,D) from this SAMEeta;
setC_(0,empty)=S. All these quantities retain the original numerical
labels and one common source. No different measure is chosen to
optimize different queries.

For every actual cylinder with exponentse_q>=1 and fixedj<=2, uniform
conditional deeper digits give the EXACT identity

    eta(x=a mod3^j product_D q^e_q)
       =eta(x=a mod d(j,D)) product_D q^(1-e_q).       (PT1)

Thus summing all exponent vectors, including arbitrarily high ones,
givesL_D C_(j,D) as a complete query upper. Removing only the all-one
exponent vector gives(L_D-1)C_(j,D) as the complete deep-query upper.
Define

    A(eta,C)=sum_(j,D)(L_D-1)C_(j,D),
    K(eta,C)=sum_((j,D)!=(0,empty))L_D C_(j,D).        (PT2)

The threeD=empty terms inA are zero. The unit has massS and is excluded
fromK; the two pure ternary query types3 and9 remain inK.

Supposeeta is supported on avoidance of an actual family containing
all191 distinct labelsd(j,D)>1, with their actual fixed original phases.
Every added distinct core-only original must have at least onee_q>=2.
By the union bound andPT1--PT2, restrictingeta by ANY finite collection
of such added originals gives ONE source nu with

    alpha=nu(1)>=S-A,
    complete_nonunit_query_sum(nu)<=K.               (PT3)

The new phases and heights are arbitrary. This includes pure high
powers. Althoughnu need no longer be constant on deeper digits, PT1
was only applied to its dominating pre-deletion sourceeta. Therefore
no invalid conditional uniformity is used after the restriction.

The existing actual pure-conditioned23/29 continuation now supplies
unnormalized surviving mass at least

    (1+sout-Qout)(S-A)-Qout K
       =(49/567)Delta,
    Delta=(566/49)(S-A)-K,                           (PT4)

whereQout=49/567 andsout=48/567. A strict positiveDelta is sufficient;
it also impliesS>A. All actual23/29-bearing originals have their own
fixed phases and distinct numerical labels. Their pure powers are
handled by the two actual outside pure laws, whose joint Haar density
cap isCout=616/567.

Ifeta has Haar density<=D0, the surviving Haar density is at least

    49Delta/(616D0).                                (PT5)

This is a conditional theorem for arbitrary actual finite phase data,
not a proof that every possible base191 phase pattern admits a positive
Delta. The missing universal assertion is stated below.

## How the current joint construction supplies one such source

Fix either literal head and either ALIGNED or SPREAD layout. Forq inQ
use the BASE lawlambda_q which is Haar conditioned only onx_q!=0modq.
All original191 phases are exactly those in the existing fixture JSON.
Use the same five ternary leaves and weightsw, the same actual head
maskf=U, the same actual outside unary lawsxi_(q,u), and the same full
outside avoidance measuregamma_u. On each positive row take only ONE
thinning

    zeta_u=[Z(u)/gamma_u(1)]gamma_u,
    eta=sum_u w_l rho5(r5)rho7(r7)f(u) zeta_u.

All masks and the factorZ(u)/gamma_u(1) depend only on first digits;
therefore thiseta satisfiesPT1. The sixteen simultaneous marginal
bounds from the four-coordinate construction are

    (zeta_u)_T <= H_T(u) product_(q inT)lambda_q.

For a core shallow queryD, writeE=D intersect{5,7} and
T=D intersect{11,13,17,19}. For each permitted ternary selector at
heightj and each SINGLE selected first residue on the queried head
axesE, sum

    w_l rho5(r5)rho7(r7)f(u)H_T(u)

across all head cells consistent with those selections. Maximize that
sum over one global selector/residue tuple, and multiply by
product_(q inT)1/(q-1). This isC_(j,D). The outside factor is its actual
base first-cylinder cap. Whole head axes are summed, queried head axes
are fixed. No independent phase is picked at each head cell. There are
3*64=192 such screens including the unit. Each screen bounds an actual
eta cylinder by the SAMEH_T marginal-measure inequalities; it does not
construct a new source for that query.

Becauseeta<=w product_Qlambda_q, its base Haar density cap is

    D0=(9/4)product_Qq/(q-1)=323323/73728.

The all-height fees inPT2 use the exact conditional deeper-digit ratio
fromPT1, not the looser generic pure-survivor cylinder caps. The newA
replaces the previoustau or tau_all; none of these tail budgets is
added twice.

## Four exact all-height certificates

The fixed source masses are unchanged. All fractions below come from
the simultaneous192-screen table of that source.

| Actual fixed base | S | A | K |
| --- | --- | --- | --- |
|opposite-root aligned|203435/331776|2266410021539/8255648563200|17084757899939/8255648563200|
|opposite-root spread|1257859/3317760|1596857727659/8255648563200|11853933398699/8255648563200|
|same-root aligned|316825/497664|774442051373/2751882854400|6020944502573/2751882854400|
|same-root spread|3871057/9953280|1610953474561/8255648563200|11979745589761/8255648563200|

The strict gates and positive Haar density lower bounds are:

| Actual fixed base | Delta | Haar lower bound | Decimal lower bound |
| --- | --- | --- | ---: |
|opposite-root aligned|1013898227189/550376570880|1013898227189/30342315294720|0.03341532171625|
|opposite-root spread|19126047980189/26968451973120|19126047980189/1486773449441280|0.01286413070355|
|same-root aligned|17214913507787/8989483991040|17214913507787/495591149813760|0.03473611971129|
|same-root spread|21234065782231/26968451973120|21234065782231/1486773449441280|0.01428197805806|

Consequently, for EACH of these four fixed base phase patterns, EVERY
finite distinct-odd-modulus extension with support contained in
{3,5,7,11,13,17,19,23,29} and whole-familyv3<=2 leaves at least the
listed Haar density. Added original phases and all nonternary heights
are unrestricted. The base191 original phases remain hypotheses.

The opposite/same heads are exactly the two literal heads from the
separate direct scalar minimax obstruction. The joint route and its
higher-height extension therefore succeed on those same head data;
this comparison does not identify different outside phase patterns.

The exact scalar K0 is the sum of all nonunit first-digit caps, so
K=K0+A. This identity checks that neither deep labels nor the unit were
duplicated. The general theorem is an ordinary proof, supported by
exact finite computation, not new Lean verification.

## The remaining universal criterion is now entirely at first digits

For ANY supported prefix-constant sourceeta, the gate can equivalently
be written

    (566/49)eta(1) > sum_((j,D)!=(0,empty))
       [1+(615/49)(L_D-1)] C_(j,D).                 (PT6)

Thus unknown nonternary heights have been removed from the optimization
variables while preserving a rigorous all-height sufficient condition.
For fixed actual shallow phases, one may optimize a single nonnegative
mass on the finite CRT first-digit cells, with the cap constraints
sum_(cell in actual query fiber)mass(cell)<=C_(j,D), and zero mass on
every actual base forbidden cylinder. PT6 is a homogeneous finite LP;
normalizing total mass to1 makes the objective a weighted sum of fiber
maxima. Such an optimization must use one common mass table.

No proof is supplied that PT6 is feasible for every actual191 phase
pattern. A negative LP optimum for one pattern would refute this
sufficient method there, not prove that the original family covers.
The fixed-weightH_T construction is a tractable source family for this
criterion, not a completeness claim for all possible measures.

## Comparison with a coarser product-tail certificate

The same fixed base laws give the source-independent tail estimate

    tau_all=(7/4)[product_Q(1+q/(q-1)^2)-product_Q(1+1/(q-1))]
           =34396590319/101921587200.

The product difference enumerates precisely exponent vectors with some
nonternary exponent>=2, including pure high powers. With the generic
query screens from Report716 it gives positive gates1.0975980101 and
1.2493872025 on the two aligned layouts, but negative gates-0.9671842761
and-0.8695444120 on the spread layouts. Both are valid sufficient tests;
the source-specific prefix costs above prove all four extensions.
Failure of the coarser test is not a covering counterexample.

The original Report716 head-deep budget17978/98175 also yields positive
finite-source gates for all four fixtures, but it is not interchangeable
with an all-coordinate high-power budget. The retained fixture results
show that comparison explicitly. PT2 replaces either tail estimate; it
is not added to one of them.

## Exact verification

The [actual-family checker](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_fixtures.py)
reconstructs every original phase and the conditional mass/query response.
Its [literal results](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_fixtures.json)
retain all191 classes for each case. The [full-height checker](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_heights.py)
reconstructs those responses before accepting their retained data,
checks the complete label inventory and coarse tail sum, reconstructs
the192 same-source shallow screens and computes PT2--PT5. Its
[result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_heights.json)
records all four positive refined gates and the two negative coarse gates.

An independent integer-residue reconstruction agrees on all191 originals
and each S/K value in the generic fixture response; it evaluates the432
query modes literally rather than grouping proportional rows. Independent
rational arithmetic also checks the complete height fees and Haar-density
conversion. These are ordinary proofs plus exact computation, not new
Lean verification. The four layouts are explicitly specified tests,
not the result of a phase scan.

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_fixtures.py
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_joint_heights.py
```
