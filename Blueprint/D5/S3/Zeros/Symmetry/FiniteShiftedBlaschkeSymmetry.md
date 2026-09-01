# Finite Shifted-Blaschke Symmetry

## Abstract

Conjugate reflection preserves positive zero windows and fixes exactly the critical line.

**Theorem 1.1 (Conjugate reflection has the critical line as its fixed locus).**

$$sigma(\rho) := 1 - \overline{\rho},\ \forall \rho\in \mathbb{C},\ sigma(sigma(\rho)) = \rho \land \operatorname{Im}(sigma(\rho)) = \operatorname{Im}(\rho) \land (\Re(sigma(\rho)) - \frac{1}{2}) = -(\Re(\rho) - \frac{1}{2}) \land (sigma(\rho) = \rho \Leftrightarrow \Re(\rho) = \frac{1}{2}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry.critical_line_mirror_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen reflection sigma sends rho to one minus its complex conjugate. It is involutive, preserves the imaginary coordinate, reverses signed displacement from real part one half, and fixes exactly the critical line.

**Theorem 1.2 (Abstract xi zeros remain in the positive ordinate window).**

$$(\forall s,\ \xi(1 - s) = \xi(s)) \land (\forall s,\ \xi(\overline{s}) = \overline{\xi(s)}) \Rightarrow \forall T,\ 0 < T \Rightarrow \forall \rho\in \mathbb{C},\ \operatorname{MirrorSpec}(\rho) \land (\xi(\rho) = 0 \Rightarrow \xi(sigma(\rho)) = 0) \land (0 < \operatorname{Im}(\rho) \land \operatorname{Im}(\rho) \leq T \Rightarrow 0 < \operatorname{Im}(sigma(\rho)) \land \operatorname{Im}(sigma(\rho)) \leq T).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry.finite_shifted_blaschke_reflection_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an abstract complex function xi, the functional equation and conjugation covariance are explicit hypotheses. Their composition proves that sigma transports a zero to a zero; zero stability is not introduced as a third hypothesis.

MirrorSpec denotes the four laws proved immediately above. Since sigma preserves the ordinate, it preserves the exact left-open, right-closed window zero less than Im rho and Im rho at most T. The source's multiplicity count is not formalized: the two supplied function identities prove pointwise zero stability but do not by themselves encode analytic orders of vanishing.

**Theorem 1.3 (One half plus three i is a fixed witness).**

$$\rho := \frac{1}{2} + 3i,\ \operatorname{MirrorSpec}(\rho) \land sigma(\rho) = \rho \land \operatorname{Im}(sigma(\rho)) = 3.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry.critical_line_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The on-line witness verifies all four structural laws, fixedness, and the preserved ordinate explicitly.

**Theorem 1.4 (Three quarters plus three i is an off-line witness).**

$$\rho := \frac{3}{4} + 3i,\ \operatorname{MirrorSpec}(\rho) \land sigma(\rho) = \frac{1}{4} + 3i \land sigma(\rho) \neq \rho \land \operatorname{Im}(sigma(\rho)) = 3.$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry.off_line_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The off-line witness verifies all four structural laws, maps real part three quarters to one quarter, is not fixed, and retains ordinate three.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry.critical_line_mirror_spec`
- Truth anchor: `D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry.critical_line_witness`
- Truth anchor: `D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry.finite_shifted_blaschke_reflection_spec`
- Truth anchor: `D5/S3/Zeros/Symmetry/FiniteShiftedBlaschkeSymmetry.off_line_witness`
- Dependency: [D5/S3/Weil/ReflectionLedger](../../Weil/ReflectionLedger.md)
- Dependency: [D5/S3/Zeros/CompletedZeta](../CompletedZeta.md)
