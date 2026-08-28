# Critical Damping Flatness

## Abstract

A finite centered damping defect vanishes exactly when every damping rate is critical.

**Definition 1.1 (Finite centered damping defect).**

Lean statement: `D5/S3/Zeros/Symmetry/CriticalDampingFlatness.criticalDampingDefect`

*Formalization.* `D5/S3/Zeros/Symmetry/CriticalDampingFlatness.criticalDampingDefect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defect is constructed by summing the nonnegative centered hyperbolic-cosine contribution of every member of the finite multiplicity-indexed zero window.

**Theorem 1.2 (Vanishing damping defect characterizes critical rates).**

$$\begin{gathered}\forall Zero: \operatorname{Type}, realPart: Zero \mapsto \mathbb{R}, \tau \in \mathbb{R},\\{}\operatorname{Fintype}(Zero) \land \tau \neq 0 \Rightarrow\\{}(\forall \rho \in Zero, \operatorname{realPart}(\rho) = \frac{1}{2}) \Leftrightarrow \operatorname{criticalDampingDefect}(realPart, \tau) = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/CriticalDampingFlatness.critical_damping_flatness_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite carrier records the zero window with multiplicity, and realPart records its damping rates. The displayed defect is the trace-cosh sum after centering those rates at one half.

Every summand is nonnegative. A zero total therefore makes each summand zero, and Mathlib's strict hyperbolic-cosine criterion together with the nonzero scale forces every centered rate to vanish.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/CriticalDampingFlatness.criticalDampingDefect`
- Truth anchor: `D5/S3/Zeros/Symmetry/CriticalDampingFlatness.critical_damping_flatness_criterion`
