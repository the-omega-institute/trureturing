# BoundedWholeGain

## Abstract

Let q=(6/5)(9x-1)(2+3x)

Let q=(6/5)(9x-1)(2+3x). The literal parent equation gives εℓ=-qk(1-u), while the actual fifth response gives εα=k(1-u)((P₅-24)(1-k)-v(108x-12)). Both equations are derived by exact denominator clearing on the original source.

The unique drift lift is the scalar product of (ℓ,α) with these two right sides divided by ℓ²+α². The denominator is positive on the full compact source. Its continuity on the compact source times any bounded fifth-response interval produces a uniform bound for ε; singular Λ=0 is included because the lift divides by the derived vector norm, not by Λ.

The even samples at clocks 0,2,4 are controlled by ε and x. The cubic fourth-difference relation controls a₁+a₃, and equal odd readings imply a₁=(1-u)(a₁+a₃), a₃=u(a₁+a₃). Thus all four original gain coordinates are bounded without dividing by a limiting zero odd trace. Ordinary coefficient bounds follow through the fixed linear coefficient transform in OriginalWorld.

**Theorem 1.1 (normalized parent equations).**

Lean statement: `D5/S3/Observer/CubicGain/BoundedWholeGain.normalized_parent_equations`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/BoundedWholeGain.normalized_parent_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every strict parent, εℓ equals driftRight and εα equals fifthRight evaluated at its actual fifth response, with both right sides evaluated at the same compact source.

**Theorem 1.2 (driftLift actual).**

Lean statement: `D5/S3/Observer/CubicGain/BoundedWholeGain.driftLift_actual`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/BoundedWholeGain.driftLift_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every strict parent C, driftLift evaluated at its compact source and actual fifth response equals its original drift offset ε=C.2.2.

**Theorem 1.3 (bounded fifth bounds drift).**

Lean statement: `D5/S3/Observer/CubicGain/BoundedWholeGain.bounded_fifth_bounds_drift`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/BoundedWholeGain.bounded_fifth_bounds_drift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real M there is a real D such that |P₅|≤M implies |ε|≤D for every strict parent, including those with Λ=0.

**Theorem 1.4 (boundedGain actual).**

Lean statement: `D5/S3/Observer/CubicGain/BoundedWholeGain.boundedGain_actual`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/BoundedWholeGain.boundedGain_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every strict parent C, boundedGain evaluated at its compact source and drift offset equals the entire sample vector parentGain C.

**Theorem 1.5 (bounded fifth bounds whole gain).**

Lean statement: `D5/S3/Observer/CubicGain/BoundedWholeGain.bounded_fifth_bounds_whole_gain`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/BoundedWholeGain.bounded_fifth_bounds_whole_gain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real M there are bounds D,G such that every strict parent with |P₅|≤M has |ε|≤D and |aᵢ|≤G for every i : Fin 4.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/BoundedWholeGain.boundedGain_actual`
- Truth anchor: `D5/S3/Observer/CubicGain/BoundedWholeGain.bounded_fifth_bounds_drift`
- Truth anchor: `D5/S3/Observer/CubicGain/BoundedWholeGain.bounded_fifth_bounds_whole_gain`
- Truth anchor: `D5/S3/Observer/CubicGain/BoundedWholeGain.driftLift_actual`
- Truth anchor: `D5/S3/Observer/CubicGain/BoundedWholeGain.normalized_parent_equations`
- Dependency: [D5/S3/Observer/CubicGain/SourceCompactification](SourceCompactification.md)
