# Tribonacci Periodic Generator

## Abstract

Five certified branches and exact cubic arithmetic generate every periodic fixed-point equation.

The three normalized gap types have one, two, and two legal outgoing branches. Affine compositions are evaluated exactly in Q(t), using t cubed equal to t squared plus t plus one.

**Theorem 1.1 (Branch targets match the frozen substitution).**

$$\forall g \in \mathit{TribonacciGap},\; \operatorname{mapTargets}\left(\operatorname{tribonacciStepsFrom}\left(g\right)\right) = \operatorname{gapLetterSubstitution}\left(g\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator.tribonacci_steps_from_targets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mapping each legal edge to its target gap gives exactly the frozen three-letter Tribonacci gap substitution.

**Theorem 1.2 (Periodic points return to generated cubic codes).**

$$\forall p \in N, s \in \mathit{TribonacciPeriodicState},\; \left(\operatorname{iterate}\left(\mathit{tribonacciPeriodicTransition}, p, s\right) = s \land \operatorname{fixedPointDenominator}\left(p, s\right) \ne 0\right) \Rightarrow \left(\exists c \in \mathit{TribonacciCubicCode},\; c \in \operatorname{tribonacciFixedPointCodes}\left(p\right) \land s = \operatorname{decodeTribonacciState}\left(c\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator.tribonacci_periodic_point_enumeration_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reading the actual legal branch at every iterate constructs a closed symbolic word. When its exact fixed-point denominator is nonzero, the original real state is the decoding of the generated code.

## References

- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator.tribonacci_periodic_point_enumeration_complete`
- Truth anchor: `D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator.tribonacci_steps_from_targets`
- Dependency: [D5/S0/Tower/DBonacci/OrbitAlgebra](../DBonacci/OrbitAlgebra.md)
