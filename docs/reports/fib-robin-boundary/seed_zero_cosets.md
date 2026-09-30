# Primitive seeds and prime zero classes

FIB §§191–192 record a paper argument extending the Euler-tail estimate to
fixed primitive nonnegative seeds `v = (a,b)`, using the actual response
`V_j = a F_(j+3) + b F_(j+4)`. The zero indices modulo a prime form at most
one residue class modulo its Fibonacci entry point. That class need not
be the zero class.

An elementary weighted rank bound yields a density-one set of indices
with small Euler tail. On each sufficiently large good index, the ensuing
Robin estimate is uniform over all multipliers `1 <= g <= C phi^j`, where
the seed and `C` are fixed. The canonical strip then restricts this same
estimate to all legal unit-zero sources with that seed. The exceptional
set can still be infinite. No assertion covers all varying seeds or all
integers.

[seed_zero_cosets.py](seed_zero_cosets.py) checks the finite modular part,
using Python 3.9+ and the standard library. From the repository root:

```sh
python3 -B docs/reports/fib-robin-boundary/seed_zero_cosets.py \
  --out /tmp/fib-seed-zero-cosets.json
```

The [stored results](seed_zero_cosets.json) contain 45 primitive seeds with
both coordinates in `0..8` and all 95 primes at most 500. Each response is
checked at indices `0..2*z(p)`: 4,275 seed-prime pairs, of which 2,852 have
nonempty zero classes, and 26,235 prescribed interval-count checks. The
output also records the ranges, entry points, prime-level counts and a
digest of every checked row.

Trial primality uses `isqrt`, and interval comparisons use
`count*z <= length+z`; all arithmetic checks are exact integers. Results
are deterministic from any working directory. Disabled assertions and
source overwrites, including hard links, are rejected.

These finite checks do not establish the infinite zero-class theorem,
the prime-tail estimate, the density result or its uniform Robin
consequence. Those remain paper arguments, with the published alternative
tail input documented in the
[Leonetti–Sanna note](../../../Library/Scale/leonetti2017fibonaccigcd.md).
