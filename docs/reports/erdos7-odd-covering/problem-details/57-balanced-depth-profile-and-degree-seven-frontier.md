# 57. A balanced depth profile and the degree-seven frontier

For any subset of the prescribed 154 head classes in
[Chapter 04c](04c-full-history-capped-laws-and-exact-global-optimization.md),
the following additional classes are allowed simultaneously: arbitrary
finitely many distinct odd 73-smooth moduli divisible by some prime sixth
power **or** having at least eight prime factors counted with multiplicity,
and arbitrary finitely many distinct odd moduli whose largest prime factor
exceeds 73. Their residues are fixed but arbitrary. Under the conditional
comparison and BBMST continuation inputs of
[Chapter 04, (US1)–(US12)](04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md),
the resulting family does not cover the integers. All moduli exceed one;
prime support and finite exponents of the numerical tail, including its
small-prime cofactors, are unrestricted.

This is a quantitative application of the full-height law in
[Chapter 54](54-depth-profile-head-laws-with-unrestricted-original-tails.md)
and the outside-exponent budget in
[Chapter 56](56-exponent-frontiers-and-cylinder-cover-certificates.md).
The prescribed head residues remain literal. A suitable law for arbitrary
73-smooth head phases is not asserted, and the unrestricted distinct odd
covering problem remains open. The proof is ordinary mathematics with exact
rational computation; it introduces no Lean theorem or claim of novelty for
the optimization and comparison methods.

## The profile and the actual head law

Let P be the following 20 odd primes, processed in this numerical order:

    3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73.

Their original coordinate heights are

    5,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1.

Each original label retains its numerical modulus, literal residue and every
prime-power requirement. At every full preceding-coordinate history, the
conditional row for p is a probability measure on `Z/p^(H_p)Z` satisfying

    Pr(X_p=a mod p^e | full preceding coordinates) <= r_(p,e).

These are absolute cylinder masses in that row, not conditional masses
inside the parent p-adic cylinder. Set `r_(p,0)=1`; the complete new profile
is as follows.

| p | H_p | r_1 through r_H |
|---|---:|---|
| 3 | 5 | 729/1100, 243/1100, 81/1100, 27/1100, 9/1100 |
| 5 | 3 | 7/18, 7/90, 7/450 |
| 7 | 3 | 49/229, 7/229, 1/229 |
| 11 | 2 | 1243/9700, 113/9700 |
| 13 | 2 | 481/4700, 37/4700 |
| 17 | 2 | 17/220, 1/220 |
| 19 | 2 | 2147/32100, 113/32100 |
| 23 | 1 | 9/175 |
| 29 | 1 | 53/1350 |
| 31 | 1 | 53/1450 |
| 37 | 1 | 53/1750 |
| 41 | 1 | 53/1950 |
| 43 | 1 | 53/2050 |
| 47 | 1 | 17/750 |
| 53 | 1 | 1/50 |
| 59 | 1 | 17/950 |
| 61 | 1 | 51/2950 |
| 67 | 1 | 51/3250 |
| 71 | 1 | 17/1150 |
| 73 | 1 | 51/3550 |

The [balanced input](../frontier/source-budgets/balanced_profile_head_input.json)
is separate from the retained
[Chapter 54 input](../frontier/source-budgets/depth_profile_head_input.json).
The actual 154 labels come from the same canonical literal factory used by
Chapter 04c. The word balanced describes this supplied choice of caps; no
optimization over all possible profiles is certified.

All displayed caps satisfy `r_(p,e)>=p^(-e)`, so uniform rows are feasible.
For each p-adic row, give each actual leaf its continuation cost. At a leaf
the feasible cost function is one linear segment of length `r_(p,H_p)`.
At an internal node merge its children's nondecreasing marginal-cost
segments and retain the cheapest mass up to that node's own cap. The merge
is the infimal convolution of the child cost functions. At the root take
mass one. Thus every ancestor cap is imposed before the row minimum is
used; equal leaf-cost histograms do not erase the locations of their leaves.

Backward induction on the fixed prime order gives an actual finite joint
law: paste an optimal conditional row at every full history, with arbitrary
feasible rows at null histories. The active original-label set is a
memoization key for this head objective. The sampled full coordinates are
still retained and supplied to later kernels. The terminal payoff is
membership in the union of the original congruences. Exact evaluation gives

    epsilon = 39891291142993164384829733829906791483779
              /130822105133669014006347656250000000000000
            = 0.3049277574476712... .

This is the minimum head-union mass for the displayed profile and fixed
order, attained by the constructed law. It is not a combination of optima
from different laws. The
[head producer](../frontier/source-budgets/balanced_profile_head.py) and
[independent original-leaf verifier](../frontier/source-budgets/verify_balanced_profile_head.py)
retain the exact value in their
[head certificate](../certificates/source_norms/source-budgets/balanced_profile_head.json)
and [independent certificate](../certificates/source_norms/source-budgets/balanced_profile_head_verification.json).
The independent calculation evaluates 3,363,080 actual local leaves over
45,029 states and checks 7,788,582 ancestor-capacity subtractions. It does
not enumerate the entire global CRT period or call the candidate row solver.

## Finite original families and all higher digits

Fix any one finite enlarged family in the stated scope. Choose finite
heights `H'_p>=H_p` large enough to resolve every original requirement in
that family, including requirements in later numerical-tail cofactors.
Extend the coarse head law by

    X_p = x_p+p^(H_p) U_p,
    U_p uniform on {0,...,p^(H'_p-H_p)-1},

where all extra digits are independent of each other and of the entire
coarse law. Conditioning on earlier full coordinates reveals earlier coarse
coordinates and independent digits. It therefore leaves the next coarse
row unchanged. Its cylinder caps are

    R_(p,0)=1,
    R_(p,e)=r_(p,e)                         for 1<=e<=H_p,
    R_(p,e)=r_(p,H_p) p^(H_p-e)             for e>H_p.

Only exponents through `H'_p` are required for this actual finite law. The
original head union depends on the coarse coordinates, so its mass remains
epsilon. Subsequent normalized tail kernels preserve this entire prior law.
No original cofactor digit is removed by the extension.

For comparison introduce independent auxiliary nonnegative integer heights
with tails `Pr(K_p>=e)=R_(p,e)`. The displayed profiles are nonincreasing
and their geometric tails tend to zero, so these are probability laws.
The infinite auxiliary law dominates every finite lifted version. The
tail-sum identities give exactly

    E(1+K_p) = 1+sum_(e=1..H_p) r_(p,e)+r_(p,H_p)/(p-1),

    E[(1+K_p)^2] = 1+sum_(e=1..H_p)(2e+1)r_(p,e)
                  +r_(p,H_p)[(2H_p+1)/(p-1)+2p/(p-1)^2].

The final terms charge every additional geometric digit. Bounds based only
on the finite original heights would not establish the stated scope.
Infinite auxiliary sums are bounds for each finite original realization;
they do not replace it by an infinite original congruence family.

## The numerical-tail budget under this same law

Use the existing numerical-tail schedule with `delta=2/5`. At each prime
`q>73`, its normalized conditional kernel has auxiliary tails

    Pr(K_q>=e)=c_q q^(-e),
    c_q=5(q-1)/(3(q-2)),                    e>=1.

The actual kernel sees the complete actual prefix. Every mixed original
label retains its original cofactor cylinder. Distinct numerical moduli
permit at most one label of each exponent type; for each fixed cofactor
the completion over q exponents uses `sum_(e>=1)(q-1)q^(-e)=1`.
Thus the conditional comparison and original-label completion of Chapter 04
apply without imposing a support or exponent bound on the finite family.

For the independent auxiliaries put

    D_q = product_(odd prime p<q)(1+K_p),
    C_B = sum_(73<q<=B prime)
          E[(D_q-1-(q-2)delta)_+] / ((q-2)(1-delta)),
    J_B = product_(odd prime p<=B) E[(1+K_p)^2].

Actual coordinates need not be independent. The comparison bounds aggregate
expected tail charges by `C_B` and the second moment of each complete layout
load by `J_B`, under the one unconditioned actual law. Every such load L
includes the unit divisor and satisfies `L>=1`.

At `B=16384`, the 1,879 primes after 73 end at 16,381, the 1,900th prime.
Exact directed arithmetic, including the twenty geometric head tails, gives

    C_B <= Cbar = 130197276585546949/250000000000000000,
    J_B <= Jbar = 617212231457700477699/62500000000000000.

The [tail producer](../frontier/source-budgets/balanced_profile_tail_budget.py)
and [independent divisor-convolution verifier](../frontier/source-budgets/verify_balanced_profile_tail_budget.py)
retain the bounds in their
[tail certificate](../certificates/source_norms/source-budgets/balanced_profile_tail_budget.json)
and [independent certificate](../certificates/source_norms/source-budgets/balanced_profile_tail_verification.json).
The independent certificate retains all 1,879 computed stage rows and checks
every triple `(prime, stage charge, cumulative charge)` against the producer.
Its divisor-index convolution differs from the producer's factor-driven update.
Full first and second moments are propagated analytically; the finite
product-state table stores the low values needed in the positive-part
identity. Its largest queried index is 6,552, below the retained limit 6,553.
This truncation does not discard the high product-state contribution.

Specifically, with `a=2q+1`, the exact identity is

    E[(5D_q-a)_+]
      =5E[D_q]-a
       +sum_(d<=floor(a/5))(a-5d) Pr(D_q=d).

Dividing by `3(q-2)` gives the q-stage charge. Every retained probability
coefficient `a-5d` is nonnegative. Thus upward bounds for the full mean and
the retained point probabilities give an upward charge bound. On the
integer scale `10^18`, each product convolution and moment update rounds
upward. A positive geometric atom that falls below one scale unit is bounded
by one unit, never replaced by zero. The negative constant term is exact,
so it does not reverse any rounding direction. The analytic full mean
already includes product states above the stored cutoff.

Keep the conservative stopping threshold used in Chapters 54 and 56:

    T=326059/4=81514.75.

Before extra 73-smooth classes are charged, the exact sufficient score is

    epsilon+Cbar+(Jbar-1)/(T-1)
      =21540413935703453068684589604160825138045123609
       /22749440794324506859647832031250000000000000000
      =0.9468546559209192... < 1.

The gain here comes from the changed head profile and its recomputed costs;
the stopping threshold is unchanged.

## The degree-seven exponent allowance

For an exponent vector `e in N_0^P`, write

    w(e)=product_p R_(p,e_p),
    D_d={e : every e_p<=5 and sum_p e_p<=d}.

Iterated conditional expectation using the full-prefix caps bounds any one
fixed original head residue class of vector e by `w(e)`. There is at most
one such class per vector because the numerical moduli are distinct. Hence
an arbitrary finite extra family with vectors outside `D_d` has union mass
at most

    E_Dd = product_p (sum_(e>=0) R_(p,e)) - sum_(e in D_d) w(e).

All terms are nonnegative and each local sum converges geometrically. This
is completion over the complement of one exponent set; overlapping reasons
for lying outside it are not charged separately. Its use under the actual
law requires no independence of actual coordinates.

To evaluate the inside weight form

    f_p(z)=sum_(e=0)^5 R_(p,e) z^e.

The sum of degrees zero through d of `product_p f_p(z)` is the inside
weight. The total infinite weight is

    product_p [1+sum_(e=1..H_p) r_(p,e)+r_(p,H_p)/(p-1)].

The [frontier producer](../frontier/source-budgets/balanced_profile_exponent_frontier.py)
uses exact rational convolution. The
[independent verifier](../frontier/source-budgets/verify_balanced_profile_exponent_frontier.py)
recovers the coefficients by logarithmic differentiation. If `b_(p,n)`
is the coefficient of `z^n` in `z f'_p/f_p` and `B_n=sum_p b_(p,n)`, then

    c_0=1,    n c_n=sum_(j=1..n) B_j c_(n-j).

Independent bounded-composition inclusion-exclusion gives

    |D_d|=sum_(j=0..floor(d/6)) (-1)^j binom(20,j) binom(d-6j+20,20).

The [frontier certificate](../certificates/source_norms/source-budgets/balanced_profile_exponent_frontier.json)
and [independent certificate](../certificates/source_norms/source-budgets/balanced_profile_exponent_frontier_verification.json)
retain the exact rational values underlying the following displays. The
producer retains all 101 product coefficients, all 101 cardinality
coefficients, and the actual exponent vectors of all 154 original moduli.
The independent logarithmic-derivative check compares the product
coefficients through degree seven, the portion needed for both displayed
regions; it does not claim to verify the remaining 93 coefficients.

| Total degree limit d | Cardinality including zero | Outside weight E_Dd | Sufficient score |
|---|---:|---:|---:|
| 6 | 230,210 | 0.08972534737358748... | 1.0365800032945067... |
| 7 | 887,610 | 0.0390094448119163... | 0.9858641007328355... |

The score is `epsilon+Cbar+E_Dd+(Jbar-1)/(T-1)`. In particular, exact
arithmetic verifies the simpler strict bounds

    epsilon < 61/200,    Cbar < 521/1000,
    Jbar < 9876,         E_D7 < 1/25.

For any chosen finite extra family outside `D_7`, let S be the single common
event avoiding the prescribed head, the extra head classes and all numerical
tail classes through B. The union and tail-charge bounds under the same law
give

    mu(S) >= 1-epsilon-E_D7-Cbar > 67/500.

For each complete layout, nonnegativity of `L^2-1` now gives

    E[L^2 | S]
      =1+E[(L^2-1)1_S]/mu(S)
      <=1+(Jbar-1)/mu(S)
      <1+9875/(67/500)
      =4937567/67
      <326059/4,

    326059/4-4937567/67=2095685/268>0.

The event S is identical for every complete layout, so these inequalities
hold simultaneously as required by the continuation interface. There is
one final conditioning step. No separate optimization or reconditioning is
performed for an added class or an individual layout. The BBMST continuation
then supplies an integer outside the entire finite family. If all its tail
primes are already at most B, positive avoiding mass and CRT suffice.

The complement of `D_7` consists exactly of the head moduli with some
`p^6` divisor **or** with `Omega(n)>=8`, where Omega counts prime factors with
multiplicity. Every original154 modulus has total exponent at most five,
so the permitted extra moduli are disjoint from the prescribed ones. The
full prescribed-head law proves the same conclusion for every subset of its
154 classes: retaining the stronger forbidden event only reduces the
available avoiding set.

## Scope and source relation

The degree-six score exceeds one. This particular sufficient upper
certificate therefore fails for that larger outside allowance; it does not
refute noncoverage there or prove that degree seven is optimal. The count
887,610 is a count of exponent vectors including zero, not of arbitrary
residue assignments or unresolved covering systems. Other 73-smooth head
classes inside `D_7` remain outside this result.

All six programs expose `--write` and `--check`, bind canonical inputs and
producer bytes, and keep required arithmetic checks active under Python
`-O`. The independent head, tail and frontier computations use the same
literal family and profile, with distinct arithmetic routes for each
comparison. Their role is to certify the displayed finite rational bounds.

The ordinary comparison source is
[Schroeder, Section 3](../../../../Library/Arith/schroeder2026noncoverage.md);
the terminal analytic input is
[BBMST, Theorem 6.1](../../../../Library/Arith/balister2018covering.md),
through Chapter 04's transfer. Chapter 54 supplies the full-history
laminar law and uniform-digit bridge, while Chapter 56 supplies the general
outside-exponent accounting. These analytic inputs and ordinary deductions
are not newly formalized here. The fixed-cap obstructions and the distinct
profiles and conclusions of Chapters 54–56 retain their stated meanings.
