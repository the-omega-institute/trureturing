# Nyman-Beurling Shell Mass Decomposition

## Abstract

Orthogonal shell tails satisfy the exact mass recurrence and detect the terminal defect.

**Theorem 1.1 (Shell recurrence, terminal mass, and RH).**

$$\left(\forall N \in \mathbb{N},\; \left(d_{N}\right)^{2} = \left(d_{N+1}\right)^{2}+\operatorname{shellMass}\left(N\right)\right) \land \left(\left(\forall N \in \mathbb{N},\; \left(d_{N}\right)^{2} = \operatorname{tailShellMass}\left(N\right)+m_{infinity}\right) \land \left(totalShellMass+m_{infinity} = 1 \land \left(\left(RH \Leftrightarrow m_{infinity} = 0\right) \land \left(RH \Leftrightarrow totalShellMass = 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/NymanBeurlingShellMassDecomposition.nyman_beurling_shell_mass_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a unit target have a complete orthogonal Hilbert-sum decomposition into a zero initial component, extracted shells, and a terminal component. Identify the terminal component with the orthogonal Nyman-Beurling defect.

Writing shell n for source coordinate Q_(n+1), the squared tail distance is the sum of all later shell masses and the terminal mass. Consecutive tails differ by exactly one shell, and total mass is one.

The source omitted the definitions and compatibility assumptions connecting the shell projections, distances, terminal projection, and RH. The Lean statement makes those hypotheses explicit and uses the analytic Nyman-Beurling criterion as an assumption.

## References

- Truth anchor: `D5/S3/Observer/NymanBeurlingShellMassDecomposition.nyman_beurling_shell_mass_decomposition`
- Dependency: [D5/S3/Observer/Hilbert/NymanBeurlingTargetQuotientCriterion](Hilbert/NymanBeurlingTargetQuotientCriterion.md)
- Dependency: [D5/S3/Observer/Tomography/VectorShellEnergy](Tomography/VectorShellEnergy.md)
