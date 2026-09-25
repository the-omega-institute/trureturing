# Nested actual incidences force unbounded fixed-law credit

For every finite K>=1 there is an actual irredundant family of40+K
distinct odd numerical moduli whose complete normalized-Haar survivor law
has all-height query norm below4. Select c=0 in Report609's free-energy
family and, at every occupied label, choose the least numerical maximizing
query phase. Every actual-incidence linear fractional-schedule certificate
specified below then exceeds119K/120. At K=12 it exceeds119/10>566/49;
as K grows its loss is unbounded although that same selected law continues
to have query norm below4.

The new scope is the actual-incidence credit condition left open in
[Report609](609-linear-schedule-credit-fails-on-an-actual-irredundant-core.md),
for this fixed selected law and canonical phase choice. The obstruction
does NOT cover optimizing another c or choosing other maximizing-phase
ties. It is not a lower bound on the optimal query norm or a resolution
of unrestricted Erdős #7. These are ordinary proofs and exact arithmetic
checks, not new Lean verification.

## The retained base and the new actual high-power originals

Use Report609's forty literal original classes, reproduced in its
[input](../../frontier/cover-geometry/linear_schedule_credit_obstruction_input.json),
on

    P={3,5,7,11,13,17,19}, L0=product P=4849845.

Let U0 be their COMPLETE survivor, H product Haar, and rho0=H(.|U0).
Direct marking of all L0 residues and recounting the forty exact cylinder
maxima gives

    |U0 mod L0|=741126,
    h0=H(U0)=247042/1616615,
    R_P(rho0)<=B0=1506044247059/409813032960<4.   (NI1)

The all-height bound retains the full Euler remainder as in Report609;
it is not the sum of just those forty queried labels. The least two
nonnegative survivors are29 and32. The retained private witness of each
base original lies in its own class and none of the other39.

For1<=k<=K add the ACTUAL original

    d_k=L0*3^k,
    a_k=32+L0*3^(k-1),
    C_k=[a_k]_(d_k).                           (NI2)

All d_k are distinct nonunit odd numerical labels, larger than every
base modulus. Their3-exponents are k+1 and their other prime exponents
are one. The phases in NI2 are fixed once; no modulus is repeated with
another phase.

Every new original lies within the old survivor cylinder[32]_(L0).
Writing x=32+L0*t there, the new conditions are

    t=3^(k-1) mod3^k.

They are pairwise disjoint. If k<ell, a_ell is32 mod d_k, whereas a_k
is32+L0*3^(k-1) mod d_k. Thus a_k is a private witness for its own
new original and lies in no other new class or old class. Old private
witnesses lie outside U0, so none belongs to a new original. The full
40+K family is irredundant for EVERY finite K, and no survivor-equivalent
subfamily can discard a label.

Let U_K be its complete survivor, h_K=H(U_K), and rho_K=H(.|U_K).
Disjointness gives exactly

    h_K=h0-(1-3^(-K))/(2L0),
    h_infinity:=h0-1/(2L0)=1482251/9699690,
    3/20<h_infinity<h_K<h0<A/(566/49),
    A=product_(p in P)p/(p-1)-1=212731/110592.    (NI3)

The symbol h_infinity is a scalar lower bound for these finite-family
masses; no infinite original family is required by the theorem.
For K=12 the complete period and survivor count are

    L12=2577406476645,
    |U12 mod L12|=393864476846,
    h12=23168498638/151612145685.               (NI4)

These follow from
741126*3^12-(3^12-1)/2, not from enumerating the trillion-point period.

## The same selected law has all-height query norm below4

For every numerical P-smooth query label e and every phase,
U_K subset U0 implies

    rho_K([a]_e)<=(h0/h_K)rho0([a]_e).

Taking each maximum and then summing all nonunit numerical query labels
preserves this inequality. Hence for every finite K,

    R_P(rho_K)<(h0/h_infinity)B0
      =1506044247059/409812756480<4.            (NI5)

This comparison includes every height, with no query truncation. At K=12
the more precise bound is

    R_P(rho12)<=29643468914862297/8066344485806080<4.

Now use the same finite-simplex free-energy definition as Report609,
with reference probability rho_K. At c=0 its objective is only relative
entropy D(nu||rho_K); its unique minimizer is

    mu_0=rho_K, F(0)=0, Z_0=h_K.               (NI6)

Thus the small law in NI5 is exactly the selected law used by the method
obstruction, not a separate favorable replacement law.

## Canonical maximizing phases create a real nested incidence

The ENTIRE cylinder[29]_(L0) survives every original in the enlarged
family. Each new forbidden original is in[32]_(L0), and the base originals
miss[29]_(L0). Therefore at every new occupied label d_k,

    J_(d_k)=[29]_(d_k),
    q_(d_k)(rho_K)=1/(d_k*h_K).                 (NI7)

This is a maximum: no cylinder has Haar mass exceeding1/d_k. It is
also the least numerical maximizing phase. Every phase a<29 is already
killed by the base family, and d_k is a multiple of L0, so those query
cylinders have rho_K mass zero. Phase29 has positive maximum mass.

Choose the least maximizing phase at every other occupied label as well;
its particular value will not enter the argument. The K cylinders in
NI7 are nested, and all occur simultaneously on the ACTUAL survivor
cylinder

    [29]_(L0*3^K),
    rho_K([29]_(L0*3^K))=1/(L0*3^K*h_K)>0.     (NI8)

No abstract incidence pattern is substituted for this positive-mass set.
Other occupied maximizing cylinders may also occur there, which does not
weaken the argument below because all credits are nonnegative.

## Actual-incidence linear credit still charges every member of the chain

Let M_K be the full40+K inventory and I(x) the occupied labels whose fixed
maximizing J_d contain x. For each schedule pi_j, a random subset T of
M_K replaces exactly those originals by their fixed J_d. Require only

    sum_(d in I(x))w_d^j<=Pr_(pi_j)(T intersects I(x))
       for every actual x in U_K,
    w_d^j>=0.                                 (NI9)

Unlike Report609's all-subset rule, NI9 is imposed solely on realized
incidences. Choose finitely many nonnegative schedule coefficients lambda_j
that fractionally pay every occupied label:

    sum_j lambda_j*w_d^j>=1 for every d in M_K. (NI10)

On the real cylinder NI8, nonnegativity and NI9 imply, for EACH schedule,

    sum_(k=1..K)w_(d_k)^j
      <=sum_(d in I(x))w_d^j
      <=Pr_(pi_j)(T intersects I(x))<=1.

Summing NI10 over the new labels therefore gives

    K<=sum_j lambda_j.                         (NI11)

No leakage optimizer, descendant routing or schedule correlation can
alter this implication of the stated actual-incidence contract.

Use the existing universal legal-family constant

    alpha7=7235955529/6075000000000<1/800.

For this fixed c=0 law, consider the Report609 numerical certificate

    C=U_0+sum_j lambda_j[1-(alpha7-Lambda_j)/h_K],
    U_0>=0, Lambda_j>=0.                       (NI12)

The same selected law, phases and Z_0=h_K are used throughout. Allowing
zero unpaid-query cost and zero exterior leakage only improves this
certificate and is granted in the lower bound. NI3 implies

    alpha7/h_K<1/120.

Consequently NI11--NI12 give

    C>(119/120)sum_j lambda_j>=119K/120.        (NI13)

Clipping an individual bracket above at1 would not evade this lower
bound, since both its unclipped value and1 exceed119/120. At K=12,

    C>119/10>566/49,
    119/10-566/49=171/490.                      (NI14)

Every finite K gives a legal actual family. Letting these finite values
of K increase proves unbounded distortion of THIS fixed-law, fixed-phase
linear interface. It does not show that every permitted c, every phase
tie choice or every supported probability suffers that distortion.

## The same incidence chain has a uniformly small frequency cost

For N_new(x)=sum_(k=1..K)1_(J_(d_k))(x), nesting and NI7 give

    Pr_(rho_K)(N_new>=j)=1/(L0*3^j*h_K), 1<=j<=K.

Thus its actual occupied query sum is

    E_(rho_K)N_new=(1-3^(-K))/(2L0*h_K).

At K=12 this is

    132860/196932238423<10^-6.                  (NI15)

The exponential-tail identity also gives exactly

    E_(rho_K)exp(N_new)-1
      =[(e-1)/(3L0*h_K)]sum_(j=0..K-1)(e/3)^j.

Using e<11/4<3 and(e-1)/(3-e)<7, followed by log(1+t)<t, yields

    log E_(rho_K)exp(N_new)
      <7/(L0*h_K)<14/1482251<10^-5             (NI16)

uniformly in K. The full exponential comparison is certified by
exp(1)<49/18<11/4, bounding the complete factorial tail.

NI13 and NI16 concern the same actual law and same fixed maximizing
phases. The linear contract sees a realized K-fold overlap without
weighting how rarely it occurs; the frequency bound retains that mass.
This does not prove a favorable frequency bound for arbitrary branching
incidences or arbitrary original families.

## The same maximizing probabilities admit different joint incidences

Keep exactly the same family and rho_K, but at the new labels choose

    J'_(d_k)=[29+L0*3^(k-1)]_(d_k).             (NI17)

Each lies inside the unchanged complete survivor cylinder[29]_(L0),
so it has the SAME maximum query probability1/(d_k*h_K) as NI7.
The cylinders in NI17 are pairwise disjoint: for k<ell, their phases
are incongruent modulo gcd(d_k,d_ell)=d_k, exactly as in the disjoint
original construction with32 replaced by29.

Thus this is a pair of phase choices with the same selected law and
the same numerical query maxima, but different joint incidences. The
new block alone can now be paid by one schedule that replaces all new
labels, with credit1 on each new label and zero on the old labels.
At every actual point at most one new label is incident, so NI9 holds
with equality for that block. Taking lambda=1 pays all K new labels.
This removes the CHAIN'S forced total weight K; it does not establish
success of the complete numerical certificate.

For this family, all occupied phases can also be chosen jointly so the
maximum actual incidence is independent of K. Let c_(d,a) be the exact
base-survivor count at an old label d. Its new unnormalized cylinder
mass, in base-cell units, is

    L0*H(U_K intersect[a]_d)
       =c_(d,a)-t_K*1_(a=32 mod d),
    t_K=(1-3^(-K))/2, 0<t_K<1/2.               (NI18)

All c_(d,a) are integers. The perturbation cannot change the ordering
of unequal counts; it only breaks a maximum tie against32 mod d.
For EVERY K>=1 choose the least base maximum different from32 mod d
if one exists, and otherwise choose32 mod d. These are exactly the
old labels' least maximizing phases under rho_K, independent of K.
The producer retains all forty such choices and their count evidence.

Their actual old incidence load has maximum14 on U0, attained at
x=1190264, and takes value1 on the whole base cylinder[29]_(L0).
The maximizing witness is outside both[29]_(L0) and[32]_(L0), so it
survives every extension and meets no new query cylinder. Consequently
for the full40+K occupied inventory the two phase choices have exact
maximum incidences

    nested new phases: max(14,K+1),
    disjoint new phases: 14.                   (NI19)

For the disjoint choice, take one replace-all schedule on the FULL
inventory, w_d=1/14 for every label and lambda=14. At a nonempty actual
incidence the response is1 and the total credit is at most1; at an
empty incidence both are zero. It fractionally pays every label.
Conversely, the real14-fold incidence at1190264 and NI10 force the total
schedule weight to be at least14. The optimal total INSIDE fractional
schedule weight for this chosen phase system is therefore exactly14,
uniformly in K. The same argument gives max(14,K+1) for the nested choice.

This inside optimization omits exterior leakage and unpaid query cost.
Even the chosen disjoint phase system retains the base14-fold obstruction
and gives C>14*(119/120)>566/49 for certificates NI12. Other old-label
phase choices or another c remain outside this exclusion. The example
identifies phase selection as genuine joint data: unchanged individual
maxima do not determine the incidence constraints that a linear credit
certificate must satisfy.

There is also a fixed choice of the OLD maximizing ties with a smaller
constant. The retained
[phase input](../../frontier/cover-geometry/nested_actual_incidence_tie_choices.json)
chooses one phase at every old label. NI18 and the exact integer counts
verify that all forty choices maximize under rho_K for every K>=1.
Its old incidence histogram on all741126 base survivors is

    load:  0      1       2       3       4      5     6     7    8   9
    count:62326 150925  212886  178681   87051  34577 11441 2831  390  18.

The maximum is9, attained outside the base29 and32 cells, while the
load on the entire base29 cell is2. With the disjoint new queries NI17,
the full occupied incidence maximum is therefore EXACTLY9 for every K.
A replace-all schedule with w_d=1/9 and lambda=9 is feasible and covers
every occupied label. The actual9-fold witness gives the matching lower
bound on total inside schedule weight, so that optimum is exactly9 for
THIS fixed maximizing phase system.

The phase input is a finite certified witness, not a claim of globally
optimal phase selection. A prior floating-cost search supplied the base
candidate; exact verification identifies that its19-coordinate phase13
would cease to maximize after the extension. The retained input uses
phase12 at19 instead, and its validity and histogram are checked solely
with integers. No search or floating objective is a proof input.
Exterior leakage, unpaid query cost and the selected c remain additional
requirements. In particular, the inside total9 does not certify that the
complete bound NI12 crosses566/49.

## Relation to prior results and the reusable nonlinear interface

Report530's35-label squarefree example already has a fixed query phase
choice with a large exponential moment and a small all-height query law.
It excludes a universal opposite raw-moment bound. The construction here
adds an arbitrarily long chain of DISTINCT HIGH-POWER original labels,
proves its least maximizing phases for the selected c=0 law, and makes the
actual-incidence LINEAR certificate diverge while the chain's frequency
cost stays uniformly small. Report609's stronger quantifier over all c
applies to its all-subset rule; it is not transferred to NI13.

A frequency-sensitive residual can use the existing Gibbs/entropy
variational interface rather than NI9--NI10. If one fixed common law mu,
reference rho, unpaid load W and schedule responses B_j satisfy
E_mu B_j<=beta_j, then the standard entropy inequality gives

    E_mu W-D(mu||rho)
      <=sum_j lambda_j beta_j
          +log E_rho exp(W-sum_j lambda_j B_j),
    lambda_j>=0.                              (NI20)

For a selected free-energy law, add its already-paid free-energy term
to both sides to bound the complete query norm. NI20 follows directly
by applying E_mu f-D(mu||rho)<=log E_rho exp(f) to
f=W-sum_j lambda_j B_j. This is the classical Gibbs variational formula
used in Report530's entropy-density construction, not a new entropy
theorem or a new formalization target. The underlying log-sum-exp
variational identity is also standard convex duality.

To use NI20 for the general query target, the responses and their exterior
costs must be certified for the SAME actual source, selected law, phases
and schedule data. The residual must then have a sufficiently small
uniform frequency bound. Neither such a uniform residual bound nor a
joint choice of c and maximizing phases is proved here. The chain example
only shows why actual incidence alone, without its frequency or a changed
source/phase choice, does not automatically repair the linear method.

## Reproducible arithmetic

The [producer](../../frontier/cover-geometry/nested_actual_incidence_obstruction.py)
and [data](../../frontier/cover-geometry/nested_actual_incidence_obstruction.json)
check3058 named conditions. The input is the literal forty-class family;
the producer independently marks the full4849845-point base period and
recounts the40 residue partitions by iterating its survivors. It retains
all52 originals for K=12 and checks every private-witness/class pair,
all added-cylinder disjointness, both maximizing-query choices and their
gcd incompatibilities, the unchanged full29 cylinder, old-phase incidence
counts, the fixed40-phase witness with uniform full-incidence bound9,
exact period/count formulas, all-height norm bounds and complete geometric
tails.

The new trillion-point period is not enumerated. The disjoint-cylinder
proof supplies NI3 for every finite K; the finite replay checks K=12
and the exact rational uniform bounds. No floating optimizer or new Lean
proof is involved.

    python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/nested_actual_incidence_obstruction.py
