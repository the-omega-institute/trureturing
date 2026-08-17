# Golden Periodic Enumeration

## Abstract

Exact quadratic arithmetic freezes the complete golden periodic enumeration through period seven.

Each chart-compatible branch word is composed as an affine map over Q(phi). Its fixed-point equation is solved exactly, and the real branch word of any periodic state is sent back to that finite symbolic list.

**Theorem 1.1 (Sixty periodic points through period seven).**

$$\operatorname{card}\left(\mathit{goldenPeriodicPointCodesSeven}\right) = 60$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenPeriodicEnumeration.golden_periodic_point_code_count_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deduplicating every exact fixed-point code from periods one through seven gives sixty points.

**Theorem 1.2 (Twelve disjoint periodic orbits).**

$$\operatorname{length}\left(\mathit{goldenPeriodicOrbitRepresentativesSeven}\right) = 12 \land \operatorname{card}\left(\mathit{goldenEnumeratedOrbitStatesSeven}\right) = 60$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenPeriodicEnumeration.golden_periodic_code_partition_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sixty codes split without repetition into twelve cycles: one each of lengths one through four, two each of lengths five and six, and four of length seven.

**Theorem 1.3 (The periodic-orbit enumeration is complete).**

$$\forall p \in N, s \in \mathit{GoldenSurvivorState},\; \left(\left(p \ge 1 \land p \le 7\right) \land \operatorname{iterate}\left(\mathit{goldenTransition}, p, s\right) = s\right) \Rightarrow s \in \mathit{decodedRepresentativeOrbitUnion}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenPeriodicEnumeration.golden_periodic_orbit_enumeration_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero period at most seven, any real state fixed by that iterate occurs on one of the twelve decoded cycles. This is the completeness half of the finite certificate.

**Theorem 1.4 (The golden periodic maximin through seven).**

$$\operatorname{IsGreatest}\left(\mathit{goldenPeriodicOrbitMinimaSeven}, \mathit{goldenThreshold}\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/Champions/GoldenPeriodicEnumeration.golden_periodic_orbit_maximin_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every displayed cycle has an attained minimum arm and a selected state whose arm is at most phi inverse squared over two. The period-three cycle has all three arms at least that value and attains equality, so it is the greatest finite-orbit minimum.

## References

- Truth anchor: `D5/S0/Tower/Champions/GoldenPeriodicEnumeration.golden_periodic_code_partition_seven`
- Truth anchor: `D5/S0/Tower/Champions/GoldenPeriodicEnumeration.golden_periodic_orbit_enumeration_complete`
- Truth anchor: `D5/S0/Tower/Champions/GoldenPeriodicEnumeration.golden_periodic_orbit_maximin_seven`
- Truth anchor: `D5/S0/Tower/Champions/GoldenPeriodicEnumeration.golden_periodic_point_code_count_seven`
- Dependency: [D5/S0/Tower/Champions/GoldenSurvivorTubes](GoldenSurvivorTubes.md)
