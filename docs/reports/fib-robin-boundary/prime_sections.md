# Fixed prime sections of Fibonacci recurrences

`prime_sections.py` reproduces finite source identities and root-permutation
counts used in FIB theory §§196–205. It requires Python 3.9+ and only its
standard library:

```sh
python3 docs/reports/fib-robin-boundary/prime_sections.py --out /tmp/fib-prime-sections.json
```

The required output path is the only file written; rerunning overwrites it.
Optimized Python and overwriting the source itself are rejected. The retained
`prime_sections.json` binds the finite results to the program's SHA-256.

For the seed `(16,29)`, the program checks 42 polynomial identities, 420 actual
integer factorizations and 863 actual prime incidences, each with its separate
factor-to-polynomial bridge. Windows are 4, 8, 16, 24 and 32, every even residue
is used, index quotients range from 0 through 9, and primes are below 500.
Polynomial calculations use exact integer coefficient arrays; they do not test
irreducibility.

It enumerates the root action at windows 4, 8, 16, 24, 32, 64 and 128. At the
mixed window 24, all 96 group elements are checked under the Chinese remainder
map to windows 8 and 3. Exactly 44 elements fix at least one root; each parity
orbit has 24 such elements, with intersection 4. Thus the finite fixed-root
fraction is `11/24`. The two factor events are not independent.

A separate check uses all 25 primitive nonnegative coefficient pairs in
`[0,6]^2`, odd windows 3, 7 and 21, every residue, and five index quotients.
It checks 3,875 actual integers and 3,649 prime incidences below 100. Full affine
root groups at odd squarefree windows 3, 7, 21, 39 and 273 are enumerated and
compared with the exact fraction `phi(k)/k`.

The paper argument identifies these permutation groups with number-field
Galois groups using a nonzero prime-ideal valuation. Fixed-field Chebotarev then
converts root counts to prime densities. Neither step is proved by this
program. The joint Euler-product estimate, fixed-seed asymptotic Robin margin,
and passage over all indices are also outside these finite diagnostics and
have not been newly verified in Lean.

The result in §§196–199 concerns each fixed seed with its own eventual
threshold. Section 200 gives a separate uniform paper estimate for seeds with
a prescribed slow norm growth and a nonzero valuation coprime to the fixed
window. Those multiplicative results do not cover all changing seeds, an added
unit bit, or RH. The affine additions below treat the actual shifted integer.
The golden-unit classification and Fibonacci–Lucas doubling identity
are existing repository results; their use does not certify the remaining
number-field and analytic argument.

The prime 113 example additionally checks every displayed quadratic-algebra
power and all 1,356 candidate roots of the twelve window-24 polynomials.
The paper proof explains why this excludes 113 from all even-index terms;
the program does not enumerate an infinite sequence.

For §200, the window-105 experiment enumerates all 48 unit slopes and 105
translations with the quadratic-character twist. It checks that the twisted
slope map is an involutive group automorphism, gives 5,040 distinct
permutations with a trivial kernel, and finds 2,304 permutations with a fixed
root: exactly `16/35`. The full fixed-point histogram agrees with the Chinese
remainder product over 3, 5 and 7. These are finite group checks; the paper
must still establish the full Kummer degree before identifying a Galois group.

The actual-source checks use seeds `(16,29)`, `(1,4)` and `(1,5)`, indices
0 through 420 and primes at most 2,000 outside `5*k*Q`. They find 1,678
actual prime incidences among 377,637 divisibility checks, including 405
incidences at which the actual trace-polynomial root has zero derivative.
For example, seed `(16,29)`, index 107 and prime 13 give trace root 10,
`D_105(10) = 2` and `D_105'(10) = 0` modulo 13. The quadratic-algebra orbit and
Frobenius relations still hold. Thus the diagnostic includes the repeated-root
cases that a polynomial-discriminant exclusion would discard.

For the changing family `(4+361*t,1)`, the program evaluates the displayed norm
identity at 12 specified parameters and checks the actual source congruences
for `t=0,...,7`, indices 0 through 210 and primes at most 500. It finds 1,959
prime incidences among 152,131 divisibility checks. The all-parameter valuation
statement follows in the paper from `Q_t = 19 (mod 361)`; finite samples do not
prove it. These computations do not verify the discriminant estimate,
exceptional-zero control, effective Chebotarev theorem or asymptotic Robin bound.

## Actual unit-bit-one sources (§§202–205)

For `N = g*(2*A+3*B)+1`, the new character section uses the exact identity
`(g*(4*A+7*B))^2 - D = 5*N*(N-2)`, where `D = 5-4*g^2*Q(A,B)`.
The paper Euler-product estimate retains all ramified primes. It applies only
when this actual discriminant is nonsquare; a large moving discriminant still
requires a separate estimate.

The finite affine checks comprise 340 shifted square identities, 3,060
translation norm and new-coordinate-gcd checks, 426 actual prime quadratic
residue incidences, 1,506 nonnegative bounded translations and 118 exact
Fibonacci-plus-one factorizations. All parameters and finite ranges are in
`unit_bit_one_affine` in the JSON.

At seed `(16,29)` and index 4, the canonical quantity 817 becomes 818 by
changing only its external unit bit. Prime 409 divides 818, but exhaustive
evaluation finds no root of the old window-105 polynomial modulo 409.
The exact golden-unit order 408 and common period 14,280 provide the modular
certificate for the repeated obstruction at `j = 4+14280*t`. Canonical legality
for every such index is justified by the explicit Fibonacci address in §203.
This rejects transfer of the old prime envelope, not Robin's inequality.
The translation examples also distinguish the raw golden norm from the norm
after division by the actual new coordinate gcd.

The fixed-parameter experiment checks 29,328 actual affine quadratic identities,
79 square-discriminant root pairs, 158 norm-one targets, 2,348 actual prime-ideal
places, 2,473 trace/Kummer congruences, 1,314 unit/rank congruences and 156
canonical unit-one prime-support witnesses. Split primes are checked at each
of their two residue-field places; a product-zero test in the whole split
algebra would not justify the root assignment. Exact rational golden
arithmetic handles negative powers without changing the older integer-power
helper. Counts, source ranges and representative roots are retained in
`unit_one_fixed_parameter_sources`.

The resulting paper theorem in §204 fixes both the primitive seed `v` and
multiplier `g` before the index tends to infinity: the Robin ratio of
`g*V_j+1` tends to zero. Its threshold depends on these fixed parameters.
The finite checks do not certify the Kummer degree, Chebotarev estimates,
unit classification or limiting ratio.

For varying multipliers, §205 constructs a different canonical family
`N_r = 1+g_r*F_r`, with prime `r` and `F_r/10 <= g_r <= F_r/5`. A CRT choice
produces a coprime lcm core and a rough cofactor on the same actual integer.
Effective PNT/Mertens input and finite inclusion-exclusion give the paper limit
`exp(gamma)*log(log(N_r))-Z(N_r) -> exp(gamma)*log(2) > 0`, while its Robin
ratio tends to one. This is a constructed family, not a lower bound for every
allowed multiplier.

The six exact CRT samples use the explicit integer settings below. Their
cutoffs are input parameters, not certified approximations to the paper's
asymptotic cutoff formulas.

| Prime index | lcm cutoff | Rough cutoff |
|---|---|---|
| 101 | 2 | 148 |
| 211 | 10 | 320 |
| 401 | 28 | 627 |
| 809 | 78 | 1,301 |
| 1,601 | 180 | 2,638 |
| 3,203 | 418 | 5,398 |

For each sample the program independently greedy-decodes the actual integer,
checks its composition and unit bit, verifies primitive norm one, coprimality,
roughness, the affine identity and raw translated-norm bounds. It also finds an
allowed multiplier realizing each prime below `2*r-1`. Different primes may
use different multipliers; no simultaneous realization is asserted. The JSON
retains the chosen multiplier, lcm core, exact core response and integer hash.
It reports no floating-point Robin margin or certified infinite limit.

These additions are reviewed paper mathematics with reproducible finite
diagnostics. They introduce no new Lean declarations or frozen claims. The
uniform estimate for all changing multipliers and seeds, and RH, remain open.
