# M1728 Countershot

## Abstract

A concrete alternating phase walk gives a nonzero residue divisible by twenty-four and forty-eight.

**Theorem 1.1 (The concrete walk is minus forty-eight).**

$$\operatorname{alternatingWalk}([1, 1, 23, 1, 1, 71]) = -48 \land (-48) \operatorname{mod} 24 = 0 \land (-48) \operatorname{mod} 48 = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/M1728Countershot.m1728_countershot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed address is evaluated directly by the alternating-list definition. The same nonzero result has remainder zero modulo twenty-four and modulo forty-eight. This numerical certificate does not identify the result with a Jacobi selector without a separate address-to-selector bridge.

**Theorem 1.2 (The countershot has a nonzero witness).**

$$\operatorname{alternatingWalk}([1, 1, 23, 1, 1, 71]) = -48 \land (-48)\neq 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/M1728Countershot.m1728_countershot_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete address evaluates to minus forty-eight, and the residue is explicitly nonzero, so the divisibility facts above are not a zero-walk artifact.

## References

- Truth anchor: `D5/S1/Phase/Interference/M1728Countershot.m1728_countershot`
- Truth anchor: `D5/S1/Phase/Interference/M1728Countershot.m1728_countershot_witness`
- Dependency: [D5/S1/Phase/WalkFormula](../WalkFormula.md)
