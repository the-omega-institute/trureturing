# 56. Exponent frontiers and cylinder-cover certificates

The deterministic cylinder bounds from Chapters 54 and 55 support two forms
of accounting under one actual law. Summing prices of extra forbidden head
classes gives a sufficient extension budget. Covering the actual avoiding
set by positively weighted cylinders gives a necessary upper bound on how
much mass an admissible law can place there.

For the prescribed 154-class head of Chapter 54, a joint exponent cutoff
allows every extra 73-smooth modulus divisible by a prime sixth power or
having at least ten prime factors counted with multiplicity, together with
the already unrestricted numerical tail. Separately, seven literal classes
of period105 show a sharp survival bound `14/15`: full-atom capacity alone
misses a constraint already visible in a single ternary marginal.

These are ordinary mathematical applications of the existing comparison and
continuation. The outside budget is a direct application of Chapter 54's
cutoff formula to a different finite exponent set, and the cylinder cover is
standard linear-programming weak duality. No new Lean theorem, novelty claim
or unrestricted odd-covering result is asserted. The two numerical examples
use different specified families and laws.

## A general, schedule-independent cylinder bound

Fix finite named coordinate spaces `X_p` and a read-once strategy that samples
each original coordinate exactly once. Coordinate selection uses the observed
full transcript. Randomized selection is permitted if the selected row's caps
hold after conditioning on its selection randomizer as well. Previously
sampled values are retained. For each fixed original coordinate event
`A_(p,a)`, suppose every selected row obeys a deterministic bound

    Pr(X_p in A_(p,a) | full selection transcript) <= R_(p,a).

Neither these events nor their caps may be changed in response to a branch.
For an unconstrained coordinate use the whole space and cap 1. The conclusion
below only uses caps for the finitely many coordinate events actually named
by the cylinders in the proposed certificate.

For every fixed product cylinder `C=product_p A_(p,a_p)`, any such actual law
satisfies

    mu(C) <= rho(C),    rho(C)=product_p R_(p,a_p).

One proof is induction on the remaining named-coordinate set. At a transcript
whose previously sampled coordinates match C, select its next coordinate p.
For every sampled value that lies in `A_(p,a_p)`, the induction hypothesis
bounds the probability of completing the remaining requirements by the
product of the remaining deterministic caps; outside that event the
completion probability is zero. Averaging against the actual selected row
therefore gives at most `R_(p,a_p)` times that remaining product. This is the
same full product regardless of the coordinate selected. Conditioning first
on a randomized selection and then averaging proves the randomized case.
No independence of the actual coordinates and no fixed global sampling order
is used. This is also the single-cylinder instance of the ordinary adaptive
conditional comparison.

Let S be any fixed actual event, for example the avoiding set of an original
congruence family. Suppose fixed cylinders `C_1,...,C_m` and nonnegative real
coefficients `alpha_1,...,alpha_m` give the pointwise cover

    1_S(x) <= sum_j alpha_j 1_(C_j)(x)    for every actual x.

Integrating under the same actual law and using the cylinder bounds yields

    mu(S) <= sum_j alpha_j rho(C_j).

This is standard linear-programming weak duality: a nonnegative weighted
cylinder cover is a sufficient upper certificate for surviving mass. It
refines the uniform full-atom count by charging a larger cylinder once when
that is cheaper than charging all its atoms separately. It does not prove
that every law obeying the cylinder bounds is realizable by a read-once
strategy, that an optimal cover has been found, or that the original
congruence family covers. There is no novelty claim for this dual principle.

For p-adic profiles, the cylinders are the original residue requirements
`X_p=a_p mod p^(e_p)` and their prices are
`rho(C)=product_p R_(p,e_p)`, with `R_(p,0)=1`. Thus the certificate retains the
actual residue geometry while being independent of all admissible schedules.

## An outside budget for any finite exponent region

Fix a finite head-prime set P and write each original head modulus uniquely
as `product_p p^(e_p)`. For the actual full-height head law let its cylinder
caps be `R_(p,e)`, with `R_(p,0)=1`. For every fixed residue class of exponent
vector e, the preceding single-cylinder comparison gives

    Pr(that original class) <= w(e),    w(e)=product_p R_(p,e_p).

Let D be any finite subset of `N_0^P`. For an arbitrary finite extra family of
distinct numerical head moduli whose vectors lie outside D, at most one
original class occurs per exponent vector. The union bound, followed by
completion over the complement of D, therefore gives

    Pr(extra forbidden union) <= E_D,
    E_D = sum_(e outside D) w(e)
        = product_p (sum_(e>=0) R_(p,e)) - sum_(e in D) w(e).

All terms are nonnegative, so Tonelli justifies factorization over the
finitely many prime axes. The geometric tails used in Chapter 54 make the
total finite. Downward closure is useful for describing a frontier; the
inequality itself does not require it. Each actual finite enlarged family
is first represented at sufficiently large finite coordinate heights. The
infinite series bounds those finite realizations; it does not claim that one
finite sample resolves all infinitely many potential labels simultaneously.

The extra classes have fixed actual residues and cannot change across a
branch. Their loss, the original head loss epsilon, and the existing tail
charges stay under the same unconditioned actual law. Existing normalized
numerical-tail kernels preserve the entire earlier law. If `Cbar` and `Jbar`
are the already established charge and complete-layout moment upper bounds,
then the common avoiding event at the stopping point has mass at least

    lambda = 1-epsilon-Cbar-E_D.

For `T>1`, the sufficient condition

    epsilon+Cbar+E_D+(Jbar-1)/(T-1) < 1

makes lambda positive and gives, simultaneously for every complete layout,
`E[L^2 | common survive] <= 1+(Jbar-1)/lambda < T`. Here `L>=1` includes the
unit divisor, exactly as in Chapter 54. The published BBMST continuation then
applies. There is one final conditioning event; no intermediate conditioning,
replacement of the law, deletion of high cofactor requirements or change of
the numerical tail schedule is licensed by this accounting.

## The verified joint exponent cutoff

Use precisely Chapter 54's fixed-order literal154 profile, its uniform
extra-digit extension, and its complete 1,879-stage tail budget. Thus P is the
20 odd primes through73, and the infinite cap tails are
`R_(p,e)=r_(p,H_p) p^(H_p-e)` beyond the original height. Take

    D_9 = {e : every e_p<=5 and sum_p e_p<=9}.

Its complement is exactly the set of 73-smooth moduli divisible by some
`p^6` or with `Omega(n)>=10`, where Omega counts prime factors with
multiplicity. This is one complement, so the overlap of these conditions is
charged once. Compared with the rectangular cutoff in Chapter 54, it also
admits vectors within that rectangle whose total degree is at least ten.

Every original154 modulus is independently factored in the retained
certificate. Its maximum total exponent is exactly five, and its per-prime
maxima equal the original full-height vector. Hence all original vectors lie
inside D_9, and the new moduli are disjoint from them. Using the full original
head law also proves the conclusion for every subset of those prescribed
classes. Additional head classes inside D_9 are outside this statement.

For each prime form

    f_p(z)=sum_(e=0)^5 R_(p,e) z^e.

The inside weight is the sum of coefficients of degrees zero through nine in
`product_p f_p(z)`. The [producer](../frontier/source-budgets/head_exponent_downset.py)
uses exact rational convolution and retains all 101 product coefficients and
cardinality coefficients. The total infinite weight is

    product_p (1+sum_(e=1)^H_p r_(p,e)+r_(p,H_p)/(p-1)).

The [independent verifier](../frontier/source-budgets/verify_head_exponent_downset.py)
uses a different identity. If `b_(p,n)` is the coefficient of `z^n` in
`z f'_p/f_p`, put `B_n=sum_p b_(p,n)`. The product coefficients satisfy

    c_0=1,    n c_n=sum_(j=1..n) B_j c_(n-j).

This follows by differentiating the product. The verifier derives each local
logarithmic derivative by coefficient division and reconstructs the product
through degree nine. It calls neither the candidate convolution nor any
head-optimization routine; literals are read from the canonical producer.
Cardinalities are computed independently by bounded-composition
inclusion-exclusion:

    |D_d| = sum_(j=0..floor(d/6)) (-1)^j binom(20,j) binom(d-6j+20,20).

The exact [full result](../certificates/source_norms/source-budgets/head_exponent_downset.json)
and [independent result](../certificates/source_norms/source-budgets/head_exponent_downset_verification.json)
retain the fractions underlying these decimal displays:

| Total degree limit | Cardinality including zero | Outside weight | Sufficient score |
|---|---:|---:|---:|
| 8 | 3,103,485 | 0.02368196140618897... | 1.000406359050823... |
| 9 | 9,979,585 | 0.019033610247202... | 0.9957580078918361... |

In particular, the exact strict bounds are

    E_D9 < 191/10000,
    epsilon < 2/5,  Cbar < 47/100,  Jbar < 9000,
    lambda > 1-2/5-47/100-191/10000 = 1109/10000,
    Gamma < 1+8999/(1109/10000) = 89991109/1109,
    326059/4 - 89991109/1109 = 1634995/4436 > 0.

Consequently any subset of the prescribed154 head classes, any finitely many
additional distinct 73-smooth classes outside D_9 with arbitrary fixed
residues, and any finitely many distinct odd tail classes whose largest prime
exceeds73 form a noncovering family. Prime support and all finite exponents,
including head-prime cofactors of tail moduli, remain unrestricted under the
existing continuation hypotheses.

The degree8 upper score exceeds one. That particular certificate does not
establish the stronger cutoff; it neither refutes noncoverage there nor
proves degree9 optimality. The count of D_9 measures the exponent vectors not
covered by this outside allowance, not all their phase assignments or a
tractable exhaustive search. A diagonal boundary here is only a joint
boundary in the prime-exponent lattice, with no physical spacetime premise.

The two programs expose `--write` and `--check`, use only the Python standard
library and exact rational arithmetic, and keep required checks active under
`-O`. The original head labels and profiles come from their canonical
Chapter04c and Chapter54 sources; the present result does not rerun or replace
the already verified head optimization and continuation.

## The actual 105 geometry and its sharp dual

Fix the seven original congruence classes

    3:0, 5:0, 7:0, 15:1, 21:1, 35:2, 105:52,

with conditional coordinate atom caps `1/2, 1/3, 1/5` at primes `3,5,7`,
respectively. These apply at every full selection transcript as specified
above. The [unique literal input](../frontier/source-budgets/readonce_cylinder_cover_input105.json)
retains all seven numerical moduli, residues and coordinate caps.

Write the original CRT coordinates as `X_3,X_5,X_7`. The three pure classes
exclude zero in each coordinate. The mixed requirements are exactly

    15:1   -> (X_3,X_5)=(1,1),
    21:1   -> (X_3,X_7)=(1,1),
    35:2   -> (X_5,X_7)=(2,2),
    105:52 -> (X_3,X_5,X_7)=(1,2,3).

Consequently the avoiding set S has the following ternary fibers:

- `X_3=0`: no avoiding residue.
- `X_3=1`: `X_5=2` allows `X_7=4,5,6`, and `X_5=3,4` each allow
  `X_7=2,3,4,5,6`. This gives `3+5+5=13` actual residues.
- `X_3=2`: `X_5=2` allows five nonzero values other than 2, and
  `X_5=1,3,4` each allow all six nonzero values. This gives `5+6+6+6=23`.

The thirteen residues in the first nonempty fiber are

    S_1={4,13,19,34,58,67,73,79,82,88,94,97,103} modulo105.

Pointwise on every actual CRT residue,

    1_S <= 1_(X_3=2) + sum_(s in S_1) 1_(X=s modulo105).

Each full atom has price `(1/2)(1/3)(1/5)=1/30`, while the ternary cylinder
`X_3=2` has price `1/2`. The preceding weak dual gives

    mu(S) <= 1/2 + 13/30 = 14/15,
    mu(forbidden union) >= 1/15.

This is a single certificate valid simultaneously for every fixed order,
every adaptive order and every admissible randomized strategy. The code
checks its pointwise cover on all 105 actual integers; it is not a cover of
an abstract histogram or a relabelled family.

## A short attaining policy

Use the fixed order `3,5,7`. Sample `X_3` uniformly on `{1,2}`. If `X_3=1`,
sample `X_5` uniformly on `{2,3,4}` and `X_7` uniformly on `{2,3,4,5,6}`.
If `X_3=2`, instead use `{1,3,4}` for `X_5` and `{1,2,3,4,5}` for `X_7`.
The last-coordinate choices do not depend further on `X_5`.

Every conditional row has the prescribed cap, and the resulting 30 distinct
CRT points each have mass `1/30`. Its only forbidden points are 37 and 52:
37 is in the original class `2 mod35`, and 52 is in the original class
`52 mod105`. Hence its forbidden mass is exactly `2/30=1/15`. It saturates the
dual prices on all thirteen atoms in `S_1` and gives exactly mass `1/2` to the
ternary cylinder `X_3=2`.

This explicit primal law and the preceding dual prove the adaptive optimum
without enumerating strategies. The independent dynamic program additionally
checks that all six fixed orders, not just this attaining order, have the
same optimum.

## Exact full-history computation

For one row with atom cap `1/k` and increasing ordered continuation costs,
its minimum is the average of the k cheapest costs. Uniform mass on those
k actual values attains the bound. To see the lower bound, let t be the kth
cost. Terms with cost below t have negative `cost-t` and mass at most `1/k`;
terms above t contribute nonnegatively. Thus every normalized row has cost
at least

    t + (1/k) sum_(cost<t)(cost-t),

which is precisely that average, including ties. At any full actual history,
randomizing the choice of next coordinate averages the available row minima
and cannot beat their minimum.

The independent program evaluates terminal membership directly from the
original integer CRT value. Its adaptive state is the full partial coordinate
tuple, using an unread marker; it does not import a candidate solver or use
compressed original-label states. It checks all 105 CRT integers and visits
192 full partial-coordinate states. The conditional continuation minima are:

| First prime | Costs for its residues in numerical order | Capped root minimum |
|---|---|---|
| 3 | `1, 2/15, 0` | `1/15` |
| 5 | `1, 1/2, 1/5, 0, 0` | `1/15` |
| 7 | `1, 1/2, 1/6, 1/6, 0, 0, 0` | `1/15` |

For each selected first prime, both fixed orders of the other two coordinates
give this same row. Thus the six fixed-order minima and the adaptive minimum
are all exactly `1/15`. The reconstructed DP law has 30 equal-mass points,
nine reachable transcript rows and 55 checked conditional atom inequalities.
The separate simple attaining policy above is also verified directly.

The [independent full-history program](../frontier/source-budgets/readonce_cylinder_cover.py) uses only exact integers and fractions and exits 0
under `python3 -B -I -S -O`; its canonical interface exposes `--write` and `--check`. Its [complete certificate](../certificates/source_norms/source-budgets/readonce_cylinder_cover.json) retains the
original labels, all actual avoiding residues, all six fixed-order results,
the full optimal law and transcript rows, the simple attaining policy, and
the complete sharp cylinder-cover certificate.

## What this example does and does not separate

The full-atom constraint alone permits the uniform avoiding law, because
there are 36 avoiding residues and `1/36<=1/30`. Its coordinate marginals are

    X_3: (0,13,23)/36,
    X_5: (0,6,8,11,11)/36,
    X_7: (0,4,5,6,7,7,7)/36.

Only the displayed ternary marginal violates its corresponding coordinate
cap: `23/36>1/2`. In particular, adding merely
`mu(X_3=2)<=1/2` to the full-atom relaxation already forces forbidden mass at
least `1/15`, and the legal attaining policy shows that this relaxation's
minimum is exactly `1/15`. Adding all other valid cylinder constraints keeps
that same optimum for this objective.

The verified structural lesson is that total surviving cardinality and one
uniform atom cap omit useful coordinate geometry. A weighted cover using a
larger original cylinder detects that omission. No conclusion here asserts
that cylinder constraints characterize read-once implementability or that a
law meeting all such constraints must admit a schedule. No new Lean theorem
or resolution of the unrestricted odd covering problem is claimed.

## Source relation

The full-transcript comparison and uniform finite-height extension are the
ordinary interfaces established in
[Chapter 54](54-depth-profile-head-laws-with-unrestricted-original-tails.md)
and [Chapter 55](55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md).
Their one-coordinate input is the published conditional comparison in
[Schroeder, Section 3](../../../../Library/Arith/schroeder2026noncoverage.md),
with the existing [fixed-chain Lean comparison](../../../../D5/S3/Arith/Congruence/ConditionalComparison/ThreePrime/Comparison.lean)
and [capped rearrangement](../../../../D5/S3/Arith/Congruence/ConditionalComparison/CappedGainRearrangement.lean)
providing the repository's formal source relation. The numerical-tail consumer
uses the same [Chapter 04 transfer](04-a-complete-star-family-refutes-the-unrestricted-gamma-73-bound.md)
and [BBMST continuation](../../../../Library/Arith/balister2018covering.md).
The ordinary extensions and finite computations in this chapter are not new
Lean declarations.
