# 61. Coordinate retention and an excluded profile neighborhood

Keep the [complete seven-phase 154-class input](../frontier/source-budgets/uniform_phase_capacity_input.json)
and the actual surviving set from
[Chapter 59](59-terminal-phase-elimination-and-uniform-balanced-profile-obstruction.md),
twenty original head coordinates, their full heights, the existing
geometric higher-digit extension, the tail comparison schedule delta=2/5,
B=16384 and T=326059/4. This result concerns that auxiliary sufficient
budget. It is not a lower bound on actual tail losses or actual-law moments.

## 1. The independent auxiliary objects

For each named head prime p let the nonnegative integer K_p have survival
tail R_p(e)=Pr(K_p>=e), with R_p(0)=1. Through H_p, these are the supplied
balanced depth caps. Above H_p put

    R_p(e)=R_p(H_p) p^(H_p-e).

All auxiliary coordinates are independent. For each later odd prime
q in [79,16384], its unchanged auxiliary height has tail

    R_q(e)=c_q/q^e, e>=1,
    c_q=5(q-1)/(3(q-2)).

All products here use these named odd-prime coordinates; there is no
coordinate at prime 2. Write D_(<q)=product_(p<q)(1+K_p), and define

    C(R)=sum_q E[(5 D_(<q)-(2q+1))_+]/[3(q-2)],
    J(R)=E[product_(p<=B)(1+K_p)^2],
    Bfun(R)=C(R)+(J(R)-1)/(T-1).

The sum has exactly 1879 primes, from 79 through 16381. Each individual
charge is nonnegative and coordinatewise increasing in all heights.
The same is true of product(1+K_p)^2-1. All expectations are finite because
there are finitely many coordinates with geometric tails.

## 2. General coordinatewise retention comparison

Let R'_p be any new feasible monotone finite depth profiles on the same
head coordinates and heights, with the same geometric extension rule.
Put

    alpha_p=min(1,min_(1<=e<=H_p) R'_p(e)/R_p(e)).

Every balanced denominator is positive. Feasibility makes every new
denominator tail positive as well, so 0<alpha_p<=1. The same ratio at
H_p continues above H_p. Consequently

    R'_p(e)>=alpha_p R_p(e), e>=1.

Independently retain the base K_p with probability alpha_p, and otherwise
replace it by zero. The resulting auxiliary coordinate L_p has tail
alpha_p R_p(e) for each positive depth. The new K'_p stochastically
dominates L_p. Independent inverse-CDF couplings at each coordinate
therefore compare their product laws for every nonnegative increasing
functional F. This argument does not identify the actual head law with
an independent auxiliary law.

The law of L is also the law of independently erased base coordinates.
On the event that all twenty coordinates are retained, F has its complete
base distribution. That event is independent of both the base heights and
the unchanged tail heights. Nonnegativity gives

    E F(K',tail)>=E F(L,tail)
       >=(product_p alpha_p) E F(K,tail).

This proof uses only equality in distribution for the erasure description;
it does not require the erasure randomizers to remain independent after
the monotone coupling with the new heights is constructed. Applying it to
each charge and to product(1+K_p)^2-1 gives

    Bfun(R') >= (product_p alpha_p) Bfun(R).             (1)

These are bounds on exact independent comparison functionals. In
particular the subtraction of 1 in J-1 is essential: the nonnegative
functional being retained is the whole product minus 1.

## 3. Combining the fixed geometric cover and the auxiliary bound

Let S be the actual surviving head set, which contains integer 34. The
fixed positive cylinder polynomial P from
[Chapter 60](60-positive-cylinder-covers-across-head-profiles.md) has 38
positive integer coefficients and degree at most 12. For every actual
nonanticipative read-once head law with the new deterministic full-history
caps, including every adaptive choice of next coordinate,

    mu(S)<=P(R'_H).

Here R'_H includes the full-height cap of every one of the twenty
coordinates. This estimate concerns one fixed covering of the same actual
set S. It makes no claim that the actual law has independent coordinates.

For any verified lower bound B_lower<=Bfun(R), writing epsilon=1-mu(S),
equation (1) gives

    epsilon+Bfun(R')
      >=1-P(R'_H)+(product_p alpha_p) B_lower.          (2)

Thus P(R'_H)<=(product_p alpha_p)B_lower excludes the new profile from a
certificate requiring the score to be strictly less than 1. Equality is
already enough for exclusion. A profile not excluded by this necessary
condition has not thereby been proved feasible or successful.

For the relative box

    (1-h)R_p(e)<=R'_p(e)<=(1+h)R_p(e),
    1<=e<=H_p, h=1/50000,

one has alpha_p>=1-h. The finite depth caps may vary independently within
the box, subject to their feasibility and monotonicity constraints; they
need not all move by the same factor. Nonnegative coefficients and the
degree bound imply

    P(R'_H)<=(1+h)^12 P(R_H)=(1+h)^12 U,
    U=696181396681816852739454137354543
      /1086338369123261718750000000000000.              (3)

Equations (2) and (3) reduce the entire box to one exact inequality.

## 4. Directed lower calculation by output divisors

The [output-divisor program](../frontier/source-budgets/verify_profile_auxiliary_transport.py)
imports neither the [factor-convolution program](../frontier/source-budgets/profile_auxiliary_transport.py)
nor its implementation. It maintains lower integer masses
W(d)/10^15 for product D=d, through d=6553. Each new atom of 1+K is
computed directly as R(f-1)-R(f) and rounded downward. For each target
integer n, the update enumerates the exact divisors f of n:

    W_new(n)=sum_(f|n) floor(W(n/f) A(f)/10^15).

Every summand is a lower bound on its true independent product mass.
Products are positive integers, so masses beyond the retained table
cannot reenter it. This is an independent target-indexed divisor-sum
implementation of the distribution update.

Full first and second moments are retained separately and include every
discarded high product. Their factors are derived by conditioning on the
geometric tail rather than using the candidate's survival-sum formulas.
For head K, condition on K>=H and write K=H+G, with

    E G=1/(p-1), E G^2=(p+1)/(p-1)^2.

The atoms below H are added exactly. For a tail coordinate, K=0 with
probability 1-c/q, and otherwise K=1+G with the corresponding geometric
G. Multiplying each previous lower moment by its exact positive factor
and rounding downward preserves a lower bound.

For a=2q+1, the pointwise identity

    (5D-a)_+=5D-a+sum_(d<=floor(a/5))(a-5d)1_(D=d)

has nonnegative coefficients on the mean and every approximated mass;
only the exact constant -a is negative. Thus lower substitution, downward
division by 3(q-2), and taking the maximum with zero all preserve a lower
bound for that charge. Summing these lower bounds preserves direction.

A prime sieve supplies all 1879 stages. Every stage charge and cumulative charge agrees exactly with the
factor-convolution calculation. The output-divisor calculation evaluates 3,206,294 divisor terms and 5,833,107 charge-table terms,
with 20 head and 1879 tail updates. It verifies

    C(R)>=130197166187131/250000000000000,
    J(R)>=2468848925830800739/250000000000000.

The complete polynomial coefficients reproduce U and
degree 12. Exact rational arithmetic gives

    (1-h)^20 [C_lower+(J_lower-1)/(T-1)]-(1+h)^12 U
      =354752923942358689456571608399832327780199397081606699757554854228773625666715498227877812370186242933620981665176961020591
       /533803013093902361392974853515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
      =0.0006645764734189565... >0.0006645.

The exact inequality therefore shows that every feasible
profile in the stated box and every admissible adaptive head law obeys

    epsilon+C(R')+(J(R')-1)/(T-1)>1.0006645.

Any sound upper allowances for these same exact auxiliary quantities
also fail the strict sufficient test. This does not exclude other
profiles outside the box, different thresholds or tail schedules, a
sharper comparison using actual joint structure, or a different proof
method. It does not settle Erdős #7.


## 5. Factor-convolution calculation and complete moments

The factor-convolution program uses the same scale Q=10^15 and keeps
product indices 1 through floor((2B+1)/5)=6553. For each multiplier f=1+K,
put A(f)=floor(Q Pr(1+K=f)). Its update is

    W_new(df) += floor(W(d) A(f)/Q), for every df<=6553.

Thus it rounds each nonnegative contribution downward before addition.
The output-divisor program groups exactly these terms by their target
integer. It is an independent implementation of the same lower recurrence.
Once a geometric atom rounds to zero, every subsequent atom also rounds
to zero; the programs can omit those zero lower terms. This omission is
confined to the finite low-product mass table. All high-product mass is
still included in the analytic moment factors.

Writing r_e=R_p(e), the head factors used by the factor-convolution program
are obtained from survival sums:

    E(1+K_p) = 1 + sum_(e=1)^H r_e + r_H/(p-1),
    E(1+K_p)^2 = 1 + sum_(e=1)^H (2e+1)r_e
                   + r_H[(2H+1)/(p-1)+2p/(p-1)^2].

For each later q, with c=5(q-1)/(3(q-2)), they are

    E(1+K_q) = 1+c/(q-1),
    E(1+K_q)^2 = 1+c(3q-1)/(q-1)^2.

Multiplying the previous lower integer moment by the exact positive
factor and taking its integer floor preserves the lower direction.
The output-divisor program derives these same factors by conditioning on
the geometric tail, as in Section 4. Neither calculation substitutes a
truncated low-state moment for the full moment.

For delta=2/5, the charge in Section 1 is also exactly

    E[(D_(<q)-1-(q-2)delta)_+] / [(q-2)(1-delta)].

Its equivalent integer expression has denominator 3(q-2), as used in
Section 4. Both calculations use every prime from 79 through 16381 and
retain the full list of 1879 triples

    (prime, lower charge times Q, cumulative lower charge times Q).

The [factor-convolution certificate](../certificates/source_norms/source-budgets/profile_auxiliary_transport.json)
and [output-divisor certificate](../certificates/source_norms/source-budgets/profile_auxiliary_transport_verification.json)
contain every triple, the exact rational C and J lower bounds, and the
exact relative-box gap. Both programs support `--write` and `--check`
under `python3 -B -I -S -O`, with required checks active under optimization.
They bind the actual input, the fixed polynomial, and current program
sources. These are ordinary mathematical deductions and exact arithmetic;
no new Lean declaration or unrestricted Erdős #7 conclusion is asserted.
