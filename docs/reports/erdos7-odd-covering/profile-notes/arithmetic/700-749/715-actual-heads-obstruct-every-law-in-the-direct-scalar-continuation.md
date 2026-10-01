# Actual heads obstruct every law in the direct scalar continuation

Two explicit families of eleven distinct odd original moduli leave
survivors, but no probability law on those survivors meets the direct
scalar query threshold for adjoining all six primes11,13,17,19,23,29.
The exact optimal query values are47663/23808 and18015/8704, both larger
than the required8038/4235. This optimizes over every supported law,
including arbitrary leaf weights and correlated5/7 coordinates. It
is stronger than failure of one proposed source or one upper bound.

This is an obstruction to that scalar sufficient criterion. It is not
a covering counterexample, a failure of joint continuation, or a
resolution of unrestricted Erdős#7. The proof uses ordinary mathematics
and exact rational certificates, not new Lean verification.

## 1. Actual original families

All three cases contain the pure classes0mod3,1mod9,0mod5,0mod7.
The two nontrivial cases add the following globally fixed phases:

| Numerical modulus | Opposite-root family | Same-root family |
|---:|---:|---:|
|15|11|1|
|45|2|22|
|21|1|1|
|63|58|16|
|35|3|3|
|105|74|74|
|315|187|47|

The complete period is315. Direct enumeration gives respectively
120 survivors for the pure-only control,75 for the opposite-root
family, and85 for the same-root family. Each class keeps its own
numerical modulus; every modulus is odd and greater than one.
The five ternary leaves are{4,7}|{2,5,8}mod9.

Letmu be any probability law on the3-,5-,7-adic coordinates supported
on the appropriate complete survivor set. DefineR_2(mu) as the supremum
of the sum of nonunit cylinder probabilities over finite query layouts
with at most one residue for each numerical label3^j5^e7^f, where
j=0,1,2 ande,f are arbitrary nonnegative integers. Equivalently,

    R_2(mu)=sum_(j<=2,e,f>=0; j+e+f>0)
                   max_a mu(x=a mod3^j5^e7^f).       (PM1)

The possibly infinite sum is justified by increasing finite layouts;
each term has finitely many phases. A query cofactor is not an added
original of the same modulus: it can be the head of a distinct later
original involving outside primes. No original label is reused.

## 2. Exact reduction of all query heights to first-cylinder masses

ForE subset{5,7}, putc_E=product_(q inE)q/(q-1). For eachj<=2,
letM_(j,E) be the largest probability of a cylinder of modulus
3^j product_(q inE)q. The first-cylinder functional is

    C(mu)=sum_(j,E except0,empty)c_E M_(j,E).         (PM2)

It has eleven nonunit modes, with fees1,5/4,7/6,35/24 according toE.
For fixed positive exponents(e_q) onE, a first cylinder splits into
product_q q^(e_q-1) deeper cylinders. At least one child therefore has
mass at least its parent's mass divided by that number. Apply this to
a maximizing first cylinder and sum the geometric series over every
positive exponent. This proves

    R_2(mu)>=C(mu)                                  (PM3)

for every supported law, with no independence or density hypothesis.

Conversely, give any probability vectorp on the actual modulo315
survivors independent Haar tails inside each of its315 cylinders.
Every deeper child has exactly the corresponding fraction of its
first-cylinder mass. All inequalities inPM3 are then equalities,
simultaneously for all modes and exponents. Consequently

    inf_(all supported mu)R_2(mu)
       =min_(probability vectors p on actual315 survivors)C(p). (PM4)

This is an exact minimax calculation on the full allowed height range,
not a truncation to first-digit queries. Ternary query height remains
at most two throughout.

## 3. Finite rational certificates

For each first-mode modulusm, the epigraph constraints are

    sum_(x=a modm)p_x <= t_m,
    p_x>=0, sum_x p_x=1.

Minimize sum_m c_m t_m. A lower certificate consists of nonnegative
weightsy_(m,a) satisfying

    sum_a y_(m,a)<=c_m,
    sum_(m,a: x=a modm)y_(m,a)>=z
                 for every actual survivingx.       (PM5)

For every feasiblep, the first inequality bounds its weighted queries
below bysum_(m,a)y_(m,a)mu(C_(m,a)); the second bounds that expression
below byz. ThusPM5 is a universal lower bound. An explicitly retained
probability vector gives an upper bound. The exact certificates make
the two values equal:

| Actual family | Surviving315 cells | Exact minimumR_2 | Decimal |
|---|---:|---:|---:|
|Pure-only control|120|1339/768|1.7434895833|
|Opposite-root|75|47663/23808|2.0019741263|
|Same-root|85|18015/8704|2.0697380515|

The [retained witnesses](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_pair_minimax_witnesses.json)
list every nonzero primal mass and every literal dual modulus/phase
weight. The [standalone verifier](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_pair_minimax.py)
enumerates actual integers0..314, checks original distinctness and
support, verifies normalization, all eleven dual budgets, every
surviving cell's dual coverage and exact equality with the primal
objective. It uses only standard-library rational arithmetic; an
optimizer is not part of validation. Its
[result](../../../frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_pair_minimax.json)
records all three exact minima. An independent integer-residue verifier
agrees with every certificate.

## 4. The precise continuation criterion that fails

ForoutsideB={11,13,17,19,23,29}, letb_q=1/(q-2),

    Q=product_(q inB)(1+b_q)-1,
    s=sum_(q inB)b_q.

After conditioning on actual pure outside exclusions, the generic
union bound chargesR_2 Q for nonunit head cofactors andQ-s for the
unit head with at least two outside coordinates. Its positive-reserve
condition is

    R_2 < (1+s)/Q-1 =8038/4235.                     (PM6)

The opposite-root exact minimum exceedsPM6 by10484101/100826880;
the same-root minimum exceeds it by6330773/36861440. Therefore changing
only the supported head law cannot make this particular direct scalar
criterion work for either actual head. The pure-only control lies
below the threshold, so the obstruction uses actual mixed relations.

[Report714](714-one-actual-five-seven-boundary-controls-every-depth-two-star-profile.md)
gives a uniform actual5x7 boundary construction with query bound below
three. PM4--PM6 explain why improving its weights alone cannot make
the six-outside scalar test universal. A continuation that retains the
head's joint responses to actual outside constraints is a different
interface and is not excluded by these certificates. No claim that
the six-prime extension really covers, or that every sharper scalar
inequality fails, is made.

Run the exact verifier from the repository root:

```sh
python3 -I -S -B -O docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-depth-two-obstruction/fibre_credit_depth_two_pair_minimax.py
```
