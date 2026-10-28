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

**Theorem 1.1 (The complete actual contribution from layers at least three).**

Lean statement: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_third_layer_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_third_layer_bound` (`✓ scoped`). ∎

*Commentary.* For every real `t>=2` and every positive strict-inventory integer
`U`, the sum of `(v_q(U)-2) log(q)` over its primes with `v_q(U)>=3` is at most
`((3t)^(1/3)+1) log(t log(t)/log(2))`. The proof uses the actual active-power
cutoff, bounds each contributing prime below `(3t)^(1/3)`, and counts the finite
prime support. It keeps every active exponent and uses no equality-layer
replacement.

**Theorem 1.2 (Uniform root-scale vanishing of all layers at least three).**

Lean statement: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_third_layer_vanishing`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_third_layer_vanishing` (`✓ scoped`). ∎

*Commentary.* For every positive epsilon there is one threshold working for all
real `t` beyond it and all positive strict-inventory integers `U`, such that the
third-and-higher layer mass divided by `sqrt(t)` is below epsilon. An explicit
`240*t^(-7/60)` envelope is used. This closes the higher-layer tail needed by
the exact correction but does not identify the second-layer coefficient.

Lean statement: `D5/S3/Arith/Robin/EulerLayerRootCorrection.strict_inventory_root_correction_statement`

The proposition is preserved without a proof or freeze while the arithmetic
threshold and the root-scale `psi-theta` limit remain open. In particular, the
uniform second-layer activation/inactivation squeeze at `sqrt(2)*sqrt(t)`, its
weighted prime-mass limit, and the Costa--Pereira/PNT derivation of
`(psi(t)-theta(t))/sqrt(t)->1` have not been formalized. The existing
`strict_inventory_sqrt_discrepancy` remains only an `O(sqrt(t))` bound.

The faithful Reg source reconstruction is retained without a validated
four-slot registration; the original telescopes and their missing variation,
sensitivity, dependence and source-selection evidence remain an audit
obligation owned by the caller.
