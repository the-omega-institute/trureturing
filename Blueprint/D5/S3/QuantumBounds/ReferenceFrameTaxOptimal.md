# Optimal Reduced Reference-Frame Tax

## Abstract

The sharp scale-free upper bound completes the sine reference witness as the greatest value of the reduced zero-boundary nearest-neighbour quadratic form and yields the optimal-tax identity, without claiming the physical reduction to that form.

**Theorem 1.1 (The cosine-squared value is a universal scale-free upper bound).**

$$\forall N \in \mathbb{N},\ \forall c:\operatorname{Fin}(N)\to \mathbb{R},\ Q_{N}(c)\leq \operatorname{cos}(\frac{\pi}{N+1})^{2} \sum_{i \in \operatorname{Fin}(N)} c_{i}^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTaxOptimal.nearestNeighborQuadratic_le_cos_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N and every real vector c indexed by Fin N, the nearest-neighbour quadratic value is at most cos(pi/(N+1))^2 times the sum of the squared coordinates. There is no hypothesis on N. The statement is scale-free and therefore stronger than the unit-vector inequality needed for optimality.

The proof is elementary and deliberately avoids operator norms and diagonalisation: mathlib supplies no packaged path-graph or tridiagonal norm result for this form. For each averaged pair it applies weighted Cauchy-Schwarz in the form ((a+b)/2)^2 <= ((u+v)/4)(a^2/u+b^2/v), with positive sine weights.

The frozen sine recurrence (w_(m-1)+w_(m+1))/2 = cos(theta) w_m turns the local prefactor into cos(theta) w_m / 2. The two shifted sums are then re-indexed by bijections between their nonzero summands. Thus unmatched endpoint terms vanish through the zero extension instead of requiring separate endpoint calculations. The recurrence reduces the re-indexed double sum to 2 cos(theta) times the squared norm, and the bound collapses to cos(theta)^2 times that norm.

**Theorem 1.2 (The cosine-squared value is the greatest unit quadratic value).**

$$\forall N \in \mathbb{N},\ 1\leq N \Rightarrow \operatorname{IsGreatest}(\left\{q \in \mathbb{R} \mid \exists c:\operatorname{Fin}(N)\to \mathbb{R},\ (\sum_{i \in \operatorname{Fin}(N)} c_{i}^{2}=1) \land Q_{N}(c)=q\right\},\ \operatorname{cos}(\frac{\pi}{N+1})^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTaxOptimal.reference_frame_tax_isGreatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 <= N, cos(pi/(N+1))^2 belongs to the set of quadratic values attained by unit real vectors and bounds every member of that set from above. The predecessor module proved that the normalized sine reference attains this value but explicitly did not prove that no unit vector exceeds it. Specializing the scale-free upper bound to unit vectors supplies exactly that missing half. This IsGreatest theorem therefore closes the gap named in the previous document.

**Theorem 1.3 (The optimal tax is the sine-squared value).**

$$\forall N \in \mathbb{N},\ 1\leq N \Rightarrow 1-\operatorname{cos}(\frac{\pi}{N+1})^{2}=\sin(\frac{\pi}{N+1})^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrameTaxOptimal.reference_frame_tax_optimal_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 1 <= N, one minus the greatest quadratic value is sin(pi/(N+1))^2. Combined with the IsGreatest theorem, this is the source's stated identity 1 - F_e^opt = sin(pi/(N+1))^2 for the reduced finite real quadratic-form problem.

As in the predecessor, no physical reduction is claimed. This module does not model or prove a passage from an excitation-exchange unitary and a conservation-ladder reference to the finite real quadratic form; its optimality conclusion begins only after that form has been specified.

## References

- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTaxOptimal.nearestNeighborQuadratic_le_cos_sq`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTaxOptimal.reference_frame_tax_isGreatest`
- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrameTaxOptimal.reference_frame_tax_optimal_identity`
- Dependency: [D5/S3/QuantumBounds/ReferenceFrameTax](ReferenceFrameTax.md)
