# Minimality and an actual balanced Toeplitz generator

## Abstract

Minimality and an actual balanced Toeplitz generator.

**Theorem 1.1 (A window meets two blocks).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_infix_pair`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_infix_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A length-r window of any actual point lies inside two successive level-n words whenever every level-n word has length at least r. The proof uses the unique marked presentation at the original physical coordinates.

**Theorem 1.2 (The window occurs in every high block).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_infix_block`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_infix_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every occurring length-r window is an infix of each level-(r+3) balanced word. Equal heights make level r+1 long enough, and the previously proved pair-infix theorem places every ordered pair two levels higher.

**Theorem 1.3 (A uniform explicit recurrence bound).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_uniform_recurrence`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_uniform_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any length-r window of any point, each point and each integer starting position u admit an occurrence starting between u and u+2h(r+3). The next actual high-level boundary supplies a block containing the window. This is a uniform bound across the whole compact intersection.

**Theorem 1.4 (One common finite language).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_occurs_everywhere`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_occurs_everywhere` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite consecutive window of one actual point occurs in every other actual point. This follows from the uniform recurrence bound and does not assume minimality.

**Theorem 1.5 (Every finite coordinate pattern is reached).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balanced_finite_pattern`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balanced_finite_pattern` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite set of signed integer coordinates and any two points, an integer shift of the first matches the second on that set. A centered interval containing all specified coordinates reduces the assertion to actual word occurrence.

**Theorem 1.6 (Every integer orbit is dense).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balanced_orbit_dense`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balanced_orbit_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each integer shift orbit is dense in BalancedPoint. Basic product-open sets constrain only finitely many coordinates, so the finite-pattern theorem supplies an orbit point in every nonempty open set.

**Definition 1.7 (The integer shift action).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedShiftAction`

*Formalization.* `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedShiftAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The subtype inherits the actual physical integer shifts as an additive action. The separate balancedShiftMinimal instance records the proved dense-orbit property for this action.

**Theorem 1.8 (The exact ambient orbit closure).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balanced_orbit_closure`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balanced_orbit_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the ambient two-sided binary full shift, the closure of the integer orbit of any BalancedPoint is exactly balancedSubshift.carrier. Closed invariance gives one inclusion and subtype orbit density gives the other.

**Theorem 1.9 (The aligned point is in this space).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.alignedPeriodicPoint_mem`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.alignedPeriodicPoint_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compact aligned-tower point constructed in AlignedTowerLimit belongs to the same actual intersection, since each aligned marked representation is also an ordinary marked representation.

**Theorem 1.10 (An actual nonperiodic Toeplitz point).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.exists_balanced_toeplitz_point`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.exists_balanced_toeplitz_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is an actual point of this compact intersection with a positive period at each signed coordinate, valid for every positive and negative integer multiple, and with no positive global shift period. This combines aligned coordinate periodicity with the independently proved aperiodicity of every BalancedPoint.

**Theorem 1.11 (The point generates the entire subshift).**

Lean statement: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.exists_balanced_toeplitz_generator`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.exists_balanced_toeplitz_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same binary point has periodic coordinates, no positive global period and ambient integer orbit closure exactly equal to balancedSubshift.carrier. This completes actual Toeplitz generation and minimality. Regular periodic-skeleton density, essential periods, unique ergodicity and lift splitting require separate proofs. The public theorem escape registrations are unfinished under https://github.com/the-omega-institute/trureturing/issues/24726; the current scoped report verifies the Lean declarations and standard axiom closure, and does not constitute declared_validated four-slot audit evidence.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.alignedPeriodicPoint_mem`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedShiftAction`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_infix_block`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_infix_pair`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_occurs_everywhere`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balancedWindow_uniform_recurrence`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balanced_finite_pattern`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balanced_orbit_closure`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.balanced_orbit_dense`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.exists_balanced_toeplitz_generator`
- Truth anchor: `D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedMinimal.exists_balanced_toeplitz_point`
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/AlignedTowerLimit](AlignedTowerLimit.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedSubshift](BalancedSubshift.md)
- Dependency: [D5/S1/Dynamics/Symbolic/PermutativeLifts/FactorialMinimal](FactorialMinimal.md)
