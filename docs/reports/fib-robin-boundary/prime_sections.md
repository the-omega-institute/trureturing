# Fixed prime sections of Fibonacci recurrences

`prime_sections.py` reproduces finite source identities and root-permutation
counts used in FIB theory §§196–199. It requires Python 3.9+ and only its
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

The result concerns each fixed seed with its own eventual threshold. It does
not provide a common threshold for changing seeds, cover an added unit bit, or
prove RH. The golden-unit classification and Fibonacci–Lucas doubling identity
are existing repository results; their use does not certify the remaining
number-field and analytic argument.

The prime 113 example additionally checks every displayed quadratic-algebra
power and all 1,356 candidate roots of the twelve window-24 polynomials.
The paper proof explains why this excludes 113 from all even-index terms;
the program does not enumerate an infinite sequence.
