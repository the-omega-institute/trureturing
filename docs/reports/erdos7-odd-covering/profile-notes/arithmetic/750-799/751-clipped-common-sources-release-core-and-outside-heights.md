# Clipped actual fibres give a uniform all-core-height singleton-outside bridge

Let P={11,13,17,19,23}. Every finite original family considered below has
distinct odd numerical moduli greater than1 and globally fixed arbitrary
residues. Every modulus divides the common finite carrier

    Q=3^H3 5^H5 7^H7 product_(p in P)p^E_p.

All core heights are nonnegative finite integers. An outside exponent E_p
is arbitrary nonnegative finite on the declared full-height axes and at
most1 on the others. No primes outside this carrier are admitted.
Call an original core-shallow when its3/5/7 exponents are at
most(2,1,1). Assume every core-shallow outside-bearing original contains
exactly ONE outside prime. At every allowed exponent of that outside
prime, all eleven nonunit old315 cofactors are allowed, with arbitrary
phases. There is no bound on the number of deleted roots or on conditional
fibre survival at an individual old point.

Every original which is NOT core-shallow is unrestricted within the
stated carrier, and may contain several outside primes at their allowed
heights. The3/5/7 heights are arbitrary finite throughout. Under this
structural assumption the following three uniform lower bounds hold:

| Outside axes allowed arbitrary finite heights | Other outside exponents | Actual Haar survivor lower bound |
|---|---|---|
|none|11,13,17,19,23 at most1|229886/596362975>1/2600|
|19,23|11,13,17 at most1|129274/1028859975>1/8000|
|17,23|11,13,19 at most1|45629/724786920>1/16000|

The same bounds hold for ANY five ordered outside primes p1<...<p5,
all greater than7. The displayed primes11,13,17,19,23 are the reference
lower bounds by position; the full-height flags refer respectively to
no positions, positions4 and5, or positions3 and5. The explicit comparison
is given below. All heights may be zero; absent coordinates can be harmlessly padded.
This is ordinary mathematics and exact rational certification, not Lean
or unrestricted Erdős #7. In particular, core-shallow originals involving
two outside primes remain outside the theorem.

## Simultaneous observations on one actual old315 source

Use [Report725](../700-749/725-one-common-shallow-carrier-admits-an-arbitrary-height-last-prime.md)'s supported pruning and common cylinder-preserving
normalization. One actual uniform old315 subset mu0 belongs to one of
six canonical shapes, with N>=Nmin. [Report744](../700-749/744-core-height-convex-transport-and-the-joint-fibre-boundary.md) supplies simultaneous
saturated partial-query bounds beta_S, and [Report741](../700-749/741-an-actual-full-height23-source-supports-six-fresh-primes.md) supplies simultaneous
complete-query hinges H_a on the SAME unchanged mu0:

    E_mu0 F_S<=beta_S,
    E_mu0(L-a)_+<=H_a.

Here L includes its unit term. No different sources or attained extrema
are identified. Put

    lambda0=sum_(nonempty S subset{3,5,7})
                   beta_S product_(p in S)1/(p-1).

The numerical data needed by the fixed construction are:

|shape|Nmin|lambda0|H4|H6|
|---|---:|---:|---:|---:|
|root1 same/other|77|476821/920304|16/39|10/77|
|root1 other/same|78|78233/153504|32/79|5/39|
|root1 other/other|78|78233/153504|32/79|5/39|
|root2 same/other|75|477419/889200|2/5|2/15|
|root2 other/same|74|474271/877344|2/5|5/37|
|root2 other/other|74|474271/877344|2/5|5/37|

The fixed checker recomputes each lambda0 from all seven individual beta_S
values rather than treating these summed entries as separate observations.

## Actual pure laws, complete exponent tails, and clipping levels

For each outside axis p choose one actual pure-avoiding probability nu_p.
Its construction and constants depend only on whether that axis is shallow
or allowed arbitrary heights. Let epsilon_p=0 or1 respectively.

For a shallow axis, exclude its actual pure root if present; otherwise
exclude one fixed auxiliary root. The uniform live-root law has density
D_p=p/(p-1) relative to Haar and single-root cap c_(p,1)=1/(p-1).
Its total positive-depth cap is z_p=1/(p-1).

For an arbitrary-height axis, take the uniform law on the ACTUAL pure-power
survivor set at its finite height. There is at most one pure original at
each exponent. Its ambient mass is at least

    1-sum_(e>=1)p^-e=(p-2)/(p-1)>0.

Thus its Haar density is bounded by D_p=(p-1)/(p-2), and every depth-e cylinder has
mass at most c_(p,e)=D_p p^-e. Summing the whole geometric majorant gives
z_p=1/(p-2). Missing pure classes only improve these bounds. There is no
assumption that actual pure cylinders are nested or mutually disjoint.

These cases are summarized by

    z_p=1/(p-1-epsilon_p),
    D_p=(p-epsilon_p)/(p-1-epsilon_p).

Choose thresholds a_p>=1 with p-a_p-epsilon_p>0 and set

    s_p=1-(a_p-1)z_p>0,
    b_p=p-a_p-epsilon_p,
    z_p/s_p=1/b_p,
    D_p/s_p=(p-epsilon_p)/b_p.                         (C1)

The three results above use the SAME fixed threshold vector

    (a11,a13,a17,a19,a23)=(4,6,6,6,6).

No optimizer or assertion that these thresholds are optimal is needed.

## Actual conditional survival determines one finite measure

For an old315 point x and each outside p, let A_p(x) be the actual set of
p-coordinate values avoiding every core-shallow nonpure original p^e*d
whose old condition contains x. Let t_p(x)=nu_p(A_p(x)); it may be zero.
Let q_(p,e)(x) count the corresponding active old conditions at depth e.
There is at most one at each numerical d|315,d>1. Consequently1+q_(p,e)
is a partial complete old315 query, dominated by a complete query after
filling missing labels. Therefore on the same mu0,

    E(q_(p,e)-(a_p-1))_+<=H_(a_p).                     (C2)

A union bound, used only within the ACTUAL conditional outside law, gives

    1-t_p(x)<=sum_e c_(p,e) q_(p,e)(x).

For a full-height axis, add zero q at unused depths and use the entire
summable cap sequence. Jensen, or the elementary subadditivity of the
positive part after this common weighted threshold, gives

    (sum_e c_(p,e)q_(p,e)-(a_p-1)z_p)_+
       <=sum_e c_(p,e)(q_(p,e)-(a_p-1))_+.

Define f_p(x)=min(1,t_p(x)/s_p). Combining with(C2),

    E_mu0(1-f_p)<=H_(a_p) z_p/s_p=H_(a_p)/b_p.         (C3)

Now define ONE actual, UNNORMALIZED finite measure on the shallow-core
carrier and all its outside coordinates:

    nu(dx,dy)=mu0(dx) product_p
       [1_(y_p in A_p(x)) f_p(x)/t_p(x) nu_p(dy_p)],    (C4)

where the whole p-factor is zero if t_p(x)=0. This law is supported on
the actual core-shallow survivors. Conditional factorization is valid
because no such original uses multiple outside primes. It makes no claim
of unconditional independence after averaging x.

Its mass is Z=E_mu0 product_p f_p. Since0<=f_p<=1,

    Z>=1-sum_p E(1-f_p)
      >=1-sum_p H_(a_p)/b_p=:Z0.                     (C5)

Moreover f_p/t_p<=1/s_p wherever t_p>0. The source accounts for zero
fibres by assigning them zero mass; it does not force a fixed old marginal
through a dead fibre. Its Haar density is bounded by

    nu<=D0 Haar,
    D0=(315/Nmin) product_p (p-epsilon_p)/b_p.          (C6)

## Marked queries and every higher-core original share that source

For an old cylinder C and an outside numerical cofactor with support J
and positive depths(e_p), integrate(C4) over its query cylinder. The
queried p-factors have mass at most c_(p,e_p)/s_p. Unqueried factors have
mass f_p<=1. Hence

    nu(C times queried outside cylinder)
       <=mu0(C) product_(p in J)c_(p,e_p)/s_p.          (C7)

For a fixed saturated core support S, sum all its old slots and then all
outside cofactor choices. The same old partial-query bound beta_S gives

    complete marked unnormalized mean
       <=beta_S product_p(1+z_p/s_p)
        =beta_S product_p(1+1/b_p).                  (C8)

The outside exponent sums include all depths on every full axis. This is
one measure and uniform query bounds, not independently realized maxima.

Uniformly extend nu in all additional core digits. Classify every actual
higher-core original by its nonempty excess support S and positive excess
depths. At a fixed excess vector, different numerical originals project
to different saturated slots; outside powers remain part of those labels.
Using(C8) and the complete core geometric sums, their TOTAL actual deletion
mass is at most

    lambda0 product_p(1+1/b_p).                       (C9)

Thus actual remaining nu-mass is at least

    M=1-sum_p H_(a_p)/b_p
          -lambda0 product_p(1+1/b_p).               (C10)

When M>0, the actual Haar survivor density is at least M/D0. The use of
an unnormalized source keeps the same Z on both sides; no unproved
survival-normalization identity is required.

## Transport to every larger ordered outside prime set

Assign thresholds(4,6,6,6,6) by the ordered positions and retain the same
full-height flags epsilon_i. Every ordered five-prime set above7 satisfies
p_i>=(11,13,17,19,23)_i. For each fixed a_i and epsilon_i,

    rho_i(p)=1/(p-a_i-epsilon_i),
    density_i(p)=(p-epsilon_i)/(p-a_i-epsilon_i)
                 =1+a_i/(p-a_i-epsilon_i)

are positive and decrease as p increases. All coefficients in the total
cost sum_i H_(a_i)rho_i+lambda0 product_i(1+rho_i) are nonnegative, so
that cost cannot increase. The raw Haar bound D0 also cannot increase.
Consequently M/D0 for every canonical shape is at least its reference
value. This proves the same uniform density bounds for every such ordered
prime set; it is not a heuristic based only on larger prime sizes.

## Exact paired certification for all three scopes

For each of the six shapes and each declared full-axis set, the fixed
consumer computes every term of(C1)--(C10). The maximum total cost1-M
and minimum paired density are:

| Full outside axes | max(1-M) | min(M/D0) |
|---|---:|---:|
|none|69655678/70690165|229886/596362975|
|19,23|12926803/12991440|129274/1028859975|
|17,23|199093841/199595760|45629/724786920|

All three maxima are strictly below1. Every row's M and D0 come from the
same canonical source. The controlling shapes are the last two, but all
eighteen paired calculations are retained and checked.

The [fixed-threshold consumer](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_clipped_core_bridge.py)
authenticates both inherited data files, checks that the literal beta_S
and H4/H6 values refer to the same canonical sources and cardinality
contracts, then recomputes every paired budget using exact rational
arithmetic. The [retained result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_clipped_core_bridge.json)
is compared with a complete replay; stale results are rejected. No numerical threshold
search, sampled family, or LP optimality is a premise. It does not claim
to re-run the complete query-layout proofs of the inherited interfaces.

Pruning and missing axes use one common cylinder-preserving map and free
coordinate padding. The source and all actual original phases are fixed
once. The unresolved boundary is the permission for core-shallow originals
to join multiple outside axes, or stronger exponent patterns than those
actually certified above; these are not silently admitted by the formula.

For shallow outside axes, this explicitly supplies a feasible weighting in
the [marked source interface](750-marked-boundaries-and-joint-deletion-updates.md):
u(x)=mu0(x) product_p f_p(x)/Z and conditional uniform actual remaining
fibres. Positivity of(C10) guarantees its normalized higher-core debit is
below1. The quantifier is existence on the canonical supported subset
selected for each actual family; arbitrary preselected smaller supports
need not admit that weighting. At higher outside powers, the actual
prefix-cylinder memberships in(C4) replace the single-root interface.
