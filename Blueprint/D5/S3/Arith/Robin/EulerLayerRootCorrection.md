# Strict Euler inventory root correction

The exact target is retained as an open proposition. For every positive epsilon
there should be one real threshold T>1 such that every real t>=T and every
positive natural U satisfying the strict prime factorization law obey

$$
\left|\frac{\log U-\psi(t)}{\sqrt t}-(\sqrt2-1)\right|<\varepsilon.
$$

The strict law keeps every strictly profitable exponent layer and excludes
equality layers. The proposed proof must uniformly squeeze the active second
layer at the `sqrt 2` scale, show the complete contribution of layers at least
three is `o(sqrt t)`, and use the Costa--Pereira inequalities plus the prime
number theorem to identify `(psi(t)-theta(t))/sqrt t` with `1`. The existing
`strict_inventory_sqrt_discrepancy` is only an `O(sqrt t)` envelope and does not
close this statement.

The source paper result is attributed to the existing theory counterpart in
`ZECKENDORF_EULER_5040.md`, Definition 7.1, Theorem 8.1 and (19)--(24), as
also recorded by `mantovanelli2026primeworkload.md`; it is not a new literature
claim and is not a Lean supplier.

Lean statement: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_root_correction_statement`

The proposition is preserved without a proof or freeze while the arithmetic
threshold and tail suppliers remain open.
