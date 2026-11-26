# Quark mixing and the generation count

## Abstract

Quark mixing phases and gauge beta coefficients constrain the generation count.

Indices start at zero. For a complex matrix V, the quartet Q(i,j,k,l) is Vᵢⱼ Vₖₗ times the conjugate of Vᵢₗ Vₖⱼ. The invariant J(V) is the imaginary part of Q(0,1,1,2). The symbol e is alternating with e₀₁₂ = 1.

**Theorem 1.1 (Two-sided quartet invariance).**

Lean statement: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.quartet_biRephase_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.quartet_biRephase_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural dimension and every complex square matrix, multiplying entry (i,j) by αᵢ and the conjugate of βⱼ preserves every quartet when each phase has norm one. Each row or column phase appears once with its conjugate.

**Theorem 1.2 (Real representatives in dimension two).**

Lean statement: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.u2_real_rephasable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.u2_real_rephasable` (`✓ std3`). ∎

*Citation.* Makoto Kobayashi and Toshihide Maskawa (1973). *CP-Violation in the Renormalizable Theory of Weak Interaction*. DOI: [10.1143/PTP.49.652](https://doi.org/10.1143/PTP.49.652). URL: <https://doi.org/10.1143/PTP.49.652>.

*Commentary.*

Every two-dimensional unitary matrix admits norm-one row and column phases making the imaginary part of every entry zero. Orthogonality makes the sum of the two column quartet imaginary parts vanish, and the repeated-column term is already real. The phase construction also permits zero entries.

**Theorem 1.3 (Quartets in dimension two).**

Lean statement: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.u2_all_quartets_real`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.u2_all_quartets_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every two-dimensional unitary matrix, all quartets have zero imaginary part. The sum of the imaginary parts over the two column choices vanishes, and the quartet with repeated columns is real.

**Theorem 1.4 (A nonreal quartet requires three generations).**

Lean statement: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.cp_violation_requires_three_generations`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.cp_violation_requires_three_generations` (`✓ std3`). ∎

*Citation.* Makoto Kobayashi and Toshihide Maskawa (1973). *CP-Violation in the Renormalizable Theory of Weak Interaction*. DOI: [10.1143/PTP.49.652](https://doi.org/10.1143/PTP.49.652). URL: <https://doi.org/10.1143/PTP.49.652>.

*Commentary.*

If a finite-dimensional unitary matrix has a quartet with nonzero imaginary part, its dimension is at least three. Dimension zero has no index, dimension one has repeated indices, and dimension two has a real representative.

**Theorem 1.5 (One invariant gives every imaginary quartet).**

$$\operatorname{Im}(Q(i,j,k,l))=J(V)\sum_{m}\sum_{n}e_{ikm}e_{jln}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.jarlskog_universal_all_quartets` (`✓ std3`). ∎

*Citation.* Cecilia Jarlskog (1985). *Commutator of the Quark Mass Matrices in the Standard Electroweak Model and a Measure of Maximal CP Nonconservation*. DOI: [10.1103/PhysRevLett.55.1039](https://doi.org/10.1103/PhysRevLett.55.1039). URL: <https://doi.org/10.1103/PhysRevLett.55.1039>.

*Commentary.*

For every three-dimensional unitary V and all four indices, orthogonality gives zero sums over either of the two varying indices. Alternation then leaves one real value for the chosen orientation.

**Theorem 1.6 (Sharp absolute bound).**

$$|J(V)|\leq\frac{1}{6\sqrt{3}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.jarlskog_abs_le_sharp` (`✓ std3`). ∎

*Citation.* Charles F. Dunkl and Karol Życzkowski (2009). *Volume of the set of unistochastic matrices of order 3 and the mean Jarlskog invariant*. DOI: [10.1063/1.3272543](https://doi.org/10.1063/1.3272543). URL: <https://arxiv.org/abs/0909.0116>.

*Commentary.*

For every three-dimensional unitary V, the products V₀ⱼ times the conjugates of V₁ⱼ form a closed triangle with perimeter at most one. Twice the area is the absolute imaginary quartet. Heron's identity and the arithmetic–geometric mean inequality bound the area.

**Theorem 1.7 (Fourier attainment).**

$$F_{3} \in U(3) \land |J(F_{3})|=\frac{1}{6\sqrt{3}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.fourier3_attains_max_jarlskog` (`✓ std3`). ∎

*Citation.* Charles F. Dunkl and Karol Życzkowski (2009). *Volume of the set of unistochastic matrices of order 3 and the mean Jarlskog invariant*. DOI: [10.1063/1.3272543](https://doi.org/10.1063/1.3272543). URL: <https://arxiv.org/abs/0909.0116>.

*Commentary.*

The entries of F₃ are ω to the power jk divided by √3, where ω = −1/2 + i√3/2. This matrix is unitary and its chosen quartet has positive imaginary part.

**Theorem 1.8 (Vanishing and real representatives).**

Lean statement: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.u3_jarlskog_zero_iff_real_rephasable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.u3_jarlskog_zero_iff_real_rephasable` (`✓ std3`). ∎

*Citation.* Charles F. Dunkl and Karol Życzkowski (2009). *Volume of the set of unistochastic matrices of order 3 and the mean Jarlskog invariant*. DOI: [10.1063/1.3272543](https://doi.org/10.1063/1.3272543). URL: <https://arxiv.org/abs/0909.0116>.

*Commentary.*

A three-dimensional unitary matrix satisfies J(V) = 0 exactly when norm-one row and column phases make every entry real. If some row has three nonzero entries, it fixes the column phases. Otherwise, two rows with two nonzero entries must have the same support, since orthogonal rows cannot have exactly one common nonzero entry.

**Theorem 1.9 (Mass commutator determinant).**

$$det(-i[H_{u},H_{d}])=-2J(V)\Delta(d_{u})\Delta(d_{d})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.jarlskog_commutator_det` (`✓ std3`). ∎

*Citation.* Cecilia Jarlskog (1985). *Commutator of the Quark Mass Matrices in the Standard Electroweak Model and a Measure of Maximal CP Nonconservation*. DOI: [10.1103/PhysRevLett.55.1039](https://doi.org/10.1103/PhysRevLett.55.1039). URL: <https://doi.org/10.1103/PhysRevLett.55.1039>.

*Commentary.*

Let Hᵤ = Uᵤ diag(dᵤ) Uᵤ† and H_d = U_d diag(d_d) U_d†, where both U are three-dimensional unitary matrices and both diagonals are real. Set V = Uᵤ† U_d. For either diagonal d, Δ(d) = (d₁ − d₀)(d₂ − d₀)(d₂ − d₁). The determinant is nonzero exactly when J(V) is nonzero and both spectra have distinct entries.

**Theorem 1.10 (One-loop Standard Model ratio).**

$$\frac{b_{2}-b_{3}}{b_{1}-b_{2}}=\frac{110+5N_{H}}{220-2N_{H}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.sm_unification_ratio_generation_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N_g and N_H be rational and N_H differ from 110. The coefficient triple is (4N_g/3 + N_H/10, −22/3 + 4N_g/3 + N_H/6, −11 + 4N_g/3). The common generation term cancels from both differences.

**Theorem 1.11 (Standard Model and MSSM values).**

Lean statement: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.sm_mssm_unification_ratios`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.sm_mssm_unification_ratios` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rational N_g, the one-doublet Standard Model ratio is 115/218. The MSSM triple (2N_g + 3/5, −5 + 2N_g, −9 + 2N_g) gives 5/7. These rational values are distinct.

**Theorem 1.12 (Three-color two-loop coefficient window).**

Lean statement: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.qcd_confinement_and_cp_generation_window`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.qcd_confinement_and_cp_generation_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural N_g and N_c = 3, the coefficients are b₀ = 11 − 4N_g/3 and b₁ = 102 − 76N_g/3. The inequality b₀ > 0 is equivalent to N_g ≤ 8, and b₁ > 0 is equivalent to N_g ≤ 4. Both strict inequalities together with N_g ≥ 3 hold exactly at N_g = 3 or N_g = 4. In the two-loop beta polynomial, positivity of both coefficients excludes a positive perturbative fixed point. The window constrains the coefficient signs.

## References

- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.cp_violation_requires_three_generations`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.fourier3_attains_max_jarlskog`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.jarlskog_abs_le_sharp`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.jarlskog_commutator_det`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.jarlskog_universal_all_quartets`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.qcd_confinement_and_cp_generation_window`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.quartet_biRephase_invariant`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.sm_mssm_unification_ratios`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.sm_unification_ratio_generation_independent`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.u2_all_quartets_real`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.u2_real_rephasable`
- Truth anchor: `D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.u3_jarlskog_zero_iff_real_rephasable`
