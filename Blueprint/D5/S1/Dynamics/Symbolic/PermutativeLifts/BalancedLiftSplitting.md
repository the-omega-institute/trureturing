# Full binary lifts over the balanced base

## Abstract

Full binary lifts over the balanced base.

**Definition 1.1 (splitting).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every k and every bipermutative binary block code of length k+2, the full inverse image of the same fixed balancedSubshift is homeomorphic to BalancedPoint times the literal prefix set Fin(k+1) to Bool. The whole inverse image and every prefix are retained. For a source x with coded image y, the transformed prefix label β(y)^(-1)(sourcePrefix x) is valued in that original prefix set.

**Theorem 1.2 (splitting_conjugacy).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting_conjugacy`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The homeomorphism conjugates the actual lift shift to the balanced base shift and fixes the transformed prefix label β(y)^(-1)(sourcePrefix x), valued in the original prefix set.

**Theorem 1.3 (splitting_fibre_invariant).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting_fibre_invariant`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting_fibre_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every signed integer iterate preserves the transformed prefix label β(y)^(-1)(sourcePrefix x), valued in the original prefix set.

**Theorem 1.4 (splitting_fibre_clopen).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting_fibre_clopen`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting_fibre_clopen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each actual fibre is clopen, by continuity and discreteness of the prefix set.

**Theorem 1.5 (full_lift_not_minimal).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.full_lift_not_minimal`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.full_lift_not_minimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two distinct constant prefixes yield distinct nonempty closed invariant fibres, so the entire inverse image is nonminimal. Exact minimal component count is not asserted here.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.full_lift_not_minimal`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting_conjugacy`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting_fibre_clopen`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting.splitting_fibre_invariant`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedCoboundary](BalancedCoboundary.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal](BalancedMinimal.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativeLift](BipermutativeLift.md)
