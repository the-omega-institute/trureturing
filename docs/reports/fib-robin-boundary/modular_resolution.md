# Factorial resolution and the external unit field

FIB §§188–190 record paper arguments for comparing divisor weights at the
same factorial residue with a controlled height. The comparison has sharp
relative error of order `log log m / log m` in heights at most `(m!)^C`, for
fixed `C > 1`. Actual pairs in the zero residue class attain that order and
have unbounded additive weight difference. Relative convergence alone
therefore does not supply the fixed additive margin needed in the earlier
Robin estimates.

The neighborhood argument retains the actual near-boundary source
`C_m = m! F_(j(m!)+6m+3)` from §187. Signed offsets use the valuation relation
for equal or opposite residues. Arbitrary offsets do not preserve canonical
window data. The offset `+1` does: its external unit bit changes, while every
window, End marker, composition coordinate, coordinate gcd and raw norm
remain the same. The two different Robin-ratio limits are a paper deduction
using the uniform comparison, not a conclusion established by finite tests.

The script [modular_resolution.py](modular_resolution.py) checks exact finite
arithmetic and actual canonical sources with Python 3.9+ and the standard
library. Regenerate the checked-in [data](modular_resolution.json) from the
repository root with:

```sh
python3 -B docs/reports/fib-robin-boundary/modular_resolution.py \
  --out /tmp/fib-modular-resolution.json
```

The output is deterministic. The program does not depend on the current
working directory, rejects disabled assertions, and refuses to overwrite
its source, including through a hard link.

The finite checks cover:

- Complete factorization and an independent direct divisor sum for `1..256`.
- 47,500 ordered equal-residue pairs and 46,964 ordered opposite-residue
  pairs for the local Euler-factor sandwich, with `m = 2..7`.
- The factorial truncation product and rational error bounds for `m = 2..120`.
- 21 actual same-zero-residue product witnesses within height `(m!)^8`.
  Their fixed finite cutoffs check exact multiplicativity and height only;
  they do not certify the asymptotic sharp coefficient.
- 48 complete canonical unit-bit flips and 288 signed-offset local-factor
  checks at the corresponding actual centers.

Every equality and inequality check uses integers or rational numbers. The
Mertens input is documented in
[Lichtman's source note](../../../Library/Scale/lichtman2020mertens.md).
The uniform estimates and the sharp asymptotic rate remain paper arguments;
this experiment neither supplies their Lean bridge nor settles Robin or RH.
