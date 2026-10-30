# Actual global bracketing

## Abstract

Every integer is bracketed at one positive price by the complete original strict and maximal optimizers.

Strict and maximal products keep their distinct tie conventions. Activation finiteness, a usable positive seed and coverage are proved rather than assumed as finiteness, growth or cofinality premises.

**Theorem 1.1 (The entire product at the next activation).**

Lean statement: `D5/S3/Arith/Robin/ActualGlobalBracketing.next_event_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualGlobalBracketing.next_event_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above a positive seed, if strictInteger(q)>1, the least activation value r>q has maximalInteger(r)=strictInteger(q). Every prime factorization entry is identified, including all simultaneous ties. The equality concerns the entire integer, not a prefix or one-prime update.

**Theorem 1.2 (A positive-price bracket for every integer).**

Lean statement: `D5/S3/Arith/Robin/ActualGlobalBracketing.all_integer_bracketing`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualGlobalBracketing.all_integer_bracketing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n>=2 there is a positive real q with strictInteger(q)<=n<=maximalInteger(q). The nth two-adic marginal gives a seed whose maximal product is at least n. Choose the greatest qualifying activation value. If its strict product exceeded n, the next-event identity would give a greater qualifying activation, a contradiction. No optimizer-existence, inventory-growth or coverage premise remains.

**Theorem 1.3 (Retain the original 5040 boundary).**

Lean statement: `D5/S3/Arith/Robin/ActualGlobalBracketing.coverage_above_5040`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ActualGlobalBracketing.coverage_above_5040` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every n>5040 is either at most boundaryCap, the maximal product in the constructed 5041 bracket, or lies in a same-price interval whose strict endpoint already exceeds 5040. Cross-price divisibility places every interval crossing 5040 in that finite region. The Robin interval consumer separately identifies and pays this finite boundary and keeps the analytic endpoint estimates explicit.

## References

- Truth anchor: `D5/S3/Arith/Robin/ActualGlobalBracketing.all_integer_bracketing`
- Truth anchor: `D5/S3/Arith/Robin/ActualGlobalBracketing.coverage_above_5040`
- Truth anchor: `D5/S3/Arith/Robin/ActualGlobalBracketing.next_event_product`
- Dependency: [D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval](../GoldenResource/GoldenResourcePriceInterval.md)
- Dependency: [D5/S3/Arith/Robin/ActualTwoPriceDefect](ActualTwoPriceDefect.md)
