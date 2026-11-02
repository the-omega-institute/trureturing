# Minimal actual prefix fibres

## Abstract

Minimal actual prefix fibres of the balanced full lift.

**Theorem 1.1 (Every orbit closure).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.orbit_closure_eq_fibre`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.orbit_closure_eq_fibre` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The orbit closure of every point in the entire inverse image is exactly the clopen minimal fibre selected by the transformed prefix label β(y)^(-1)(sourcePrefix x), valued in the original prefix set.

**Theorem 1.2 (Exact number of distinct orbit closures).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.orbit_closure_family_card`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.orbit_closure_family_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct original prefixes give distinct nonempty fibres. The range of the orbit-closure map is exactly this fibre family, whose cardinal is the binary prefix cardinal 2^(k+1).

**Theorem 1.3 (All integer shifts).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.splitting_integer_conjugacy`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.splitting_integer_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full product splitting intertwines every signed integer shift with the balanced base shift and fixes the transformed prefix label β(y)^(-1)(sourcePrefix x), valued in the original prefix set.

**Definition 1.4 (Actual fibre homeomorphism).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.componentHomeomorph`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.componentHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each value of the transformed prefix label in the original binary prefix set, its nonempty clopen fibre in the full inverse image is homeomorphic to the balanced base. The inverse is the full splitting inverse with that label fixed.

**Theorem 1.5 (Minimal fibres).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.componentMinimal`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.componentMinimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fibre homeomorphism intertwines the inherited integer shift and the already proved minimal balanced action. Its image of every fibre orbit is a dense balanced orbit. Thus each fibre is minimal.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.componentHomeomorph`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.componentMinimal`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.orbit_closure_eq_fibre`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.orbit_closure_family_card`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftComponents.splitting_integer_conjugacy`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedLiftSplitting](BalancedLiftSplitting.md)
