# Symmetric-Shift Toroidal Hermite-Biehler Defect

## Abstract

Symmetric completed-xi shifts form a sharp pair, and nonzero toroidal carriers recover their Hermite-Biehler amplitude defect.

**Theorem 1.1 (Symmetric xi frame energies recover the Hermite-Biehler defect).**

$$\forall V \in \operatorname{NormedSpace}\left(\mathbb{C}\right), z \in \mathbb{C}, omega \in \mathbb{R}, Tplus \in V, Tminus \in V,\; \left(0 < \operatorname{Im}\left(z\right) \land \left(0 < omega \land \left(Tplus \ne 0 \land Tminus \ne 0\right)\right)\right) \Rightarrow \left(\frac{1}{2} < \operatorname{Re}\left(\operatorname{s}\left(z\right)\right) \land \left(\operatorname{Eminus}\left(omega\right) = \operatorname{sharp}\left(\operatorname{Eplus}\left(omega\right)\right) \land \operatorname{H}\left(omega, z, Tplus, Tminus\right) = \left\lVert \operatorname{Eplus}\left(omega, z\right) \right\rVert^{2} - \left\lVert \operatorname{Eminus}\left(omega, z\right) \right\rVert^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Szego/SymmetricShiftFrameDefect.symmetric_shift_xi_toroidal_frame_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For z in the upper half-plane, s(z)=1/2-iz lies strictly to the right of the critical line. Reflection and real structure identify the negative shift with the sharp conjugate of the positive shift.

Each observed toroidal frame is the corresponding shifted-xi amplitude times its carrier. Mathlib's scalar norm identity then cancels the carrier norm squared on both sides.

Both carriers are explicitly nonzero. This is required because Lean defines division by zero; the module computes a zero-carrier counterexample with defect -1 and target value 0.

## References

- Truth anchor: `D5/S3/Weil/Szego/SymmetricShiftFrameDefect.symmetric_shift_xi_toroidal_frame_defect`
- Dependency: [D5/S3/Zeros/Symmetry/ZetaConjugationCovariance](../../Zeros/Symmetry/ZetaConjugationCovariance.md)
