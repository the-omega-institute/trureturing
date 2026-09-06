# Observed-Break Decomposition

## Abstract

Observed symmetry breaking splits into observer and intrinsic defects.

**Theorem 1.1 (Observed breaking has two exact sources).**

$$\begin{aligned}\forall X: \operatorname{Type}, Y: \operatorname{Type},\\{}[\operatorname{AddGroup}\left(X\right)], [\operatorname{AddGroup}\left(Y\right)],\\{}J_{X}: X \to X, J_{Y}: Y \to Y,\\{}O: \operatorname{AddMonoidHom}\left(X, Y\right), x: X,\\{}(\left(J_{Y}\right)\left(O\left(x\right)\right) - O\left(x\right)) = (\left(J_{Y}\right)\left(O\left(x\right)\right) - O\left(\left(J_{X}\right)\left(x\right)\right)) + O\left((\left(J_{X}\right)\left(x\right) - x)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Naturality/ObservedBreakDecomposition.observed_break_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observer term measures failure of the readout to intertwine the object update with the observed update. The second term reads the object's intrinsic update defect.

The source writes the readout as an ordinary function, but the displayed identity requires preservation of subtraction. Lean records that repair by typing the readout as an AddMonoidHom.

After applying map_sub, additive cancellation gives the exact split. This declaration is the bind-only companion of the explicit nonadditive counterexample below.

**Theorem 1.2 (Additivity cannot be dropped).**

$$\begin{aligned}O(z) = z \cdot z, J_{X}(z) = z+1,\\{}J_{Y}(z) = z,\\{}(\left(J_{Y}\right)\left(O\left(1\right)\right) - O\left(1\right)) \neq (\left(J_{Y}\right)\left(O\left(1\right)\right) - O\left(\left(J_{X}\right)\left(1\right)\right)) + O\left((\left(J_{X}\right)\left(1\right) - 1)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Naturality/ObservedBreakDecomposition.nonadditive_observer_break_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the integers, the quadratic readout O(z)=z z, the successor object update, and the identity observed update violate the decomposition at z=1.

This concrete computation is the module's escape witness: it establishes that the repaired additivity hypothesis is mathematically necessary, rather than a Lean convenience.

## References

- Truth anchor: `D5/S3/Observer/Naturality/ObservedBreakDecomposition.nonadditive_observer_break_counterexample`
- Truth anchor: `D5/S3/Observer/Naturality/ObservedBreakDecomposition.observed_break_decomposition`
