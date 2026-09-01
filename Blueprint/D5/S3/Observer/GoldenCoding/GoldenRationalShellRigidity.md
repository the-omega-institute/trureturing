# Golden Rational Shell Rigidity

## Abstract

Nonzero rational scales cannot collide under a positive golden shell translation.

**Theorem 1.1 (Rational golden-shell collisions are trivial).**

$$\begin{gathered}\forall q_{1}, q_{2}: \mathbb{Q}, n: \mathbb{N}, q_{2} \neq 0 \land q_{1} = (phi^{2})^{n} \cdot q_{2}\\{}\Rightarrow n = 0 \land q_{1} = q_{2}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenRationalShellRigidity.rational_shell_collision_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two nonzero rational scales differ by a natural power of the orientation-preserving golden unit, then the shell depth is zero and the scales are equal.

The proof reduces positive powers of the golden unit to a nonzero rational coefficient of the irrational golden ratio. It gives exact rigidity without a quantitative near-collision bound.

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenRationalShellRigidity.rational_shell_collision_rigidity`
- Dependency: [D5/S3/Observer/GoldenCoding/PrimeGoldenScaleCoordinate](PrimeGoldenScaleCoordinate.md)
