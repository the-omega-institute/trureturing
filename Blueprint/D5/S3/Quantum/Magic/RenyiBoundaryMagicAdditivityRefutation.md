# Boundary Rényi magic additivity

## Abstract

Boundary alpha-z Rényi magic additivity fails for a pair of three-qubit states at alpha = 2 and z = 1.

**Definition 1.1 (Support inclusion).**

$$\forall n \in \mathbb{N},\; \forall rho \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; \forall sigma \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; (\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.SupportLE}\left(rho, sigma\right)) \Leftrightarrow (\forall v \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(n\right) \to \mathbb{C},\; (\operatorname{Matrix.mulVec}\left(sigma, v\right) = (0: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(n\right) \to \mathbb{C})) \Rightarrow (\operatorname{Matrix.mulVec}\left(rho, v\right) = (0: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Bits}\left(n\right) \to \mathbb{C})))$$

*Formalization.* `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.SupportLE` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

Every vector annihilated by sigma is annihilated by rho. For positive matrices this is the support inclusion used in Eq. (2): the support of rho lies in the support of sigma.

**Definition 1.2 (Base-two logarithms).**

$$\forall x \in \mathbb{R},\; \operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.log2}\left(x\right) = \operatorname{Real.logb}\left((\operatorname{Nat.cast}\left((2: \mathbb{N})\right): \mathbb{R}), x\right)$$

*Formalization.* `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.log2` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

The logarithm is Real.logb with base 2. The quantum relative entropies of §2 are measured with base-two logarithms.

**Definition 1.3 (The data-processing region).**

$$\forall alpha \in \mathbb{R},\; \forall z \in \mathbb{R},\; (\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.DPI}\left(alpha, z\right)) \Leftrightarrow ((0 < z) \land (((0 < alpha) \land ((alpha < 1) \land (\operatorname{max}\left(alpha, 1 - alpha\right) \le z))) \lor ((alpha = 1) \lor (((1 < alpha) \land ((alpha \le (\operatorname{Nat.cast}\left((2: \mathbb{N})\right): \mathbb{R})) \land ((\frac{alpha}{(\operatorname{Nat.cast}\left((2: \mathbb{N})\right): \mathbb{R})} \le z) \land (z \le alpha)))) \lor (((\operatorname{Nat.cast}\left((2: \mathbb{N})\right): \mathbb{R}) \le alpha) \land ((alpha - 1 \le z) \land (z \le alpha)))))))$$

*Formalization.* `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.DPI` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

The region D in §2 requires z > 0 and includes the three displayed alpha-z ranges together with the line alpha = 1.

**Definition 1.4 (The spectral-power trace).**

$$\forall n \in \mathbb{N},\; \forall alpha \in \mathbb{R},\; \forall z \in \mathbb{R},\; \forall rho \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; \forall sigma \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; \operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.Qaz}\left(alpha, z, rho, sigma\right) = \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tr}\left((\mathrm{if} (h: \operatorname{Matrix.IsHermitian}\left((\mathrm{if} (h: \operatorname{Matrix.IsHermitian}\left(rho\right)) \mathrm{then} \operatorname{Matrix.IsHermitian.cfc}\left(h, (\lambda (t: \mathbb{R}) \mapsto (\operatorname{Real.rpow}\left(t, \frac{alpha}{(\operatorname{Nat.cast}\left((2: \mathbb{N})\right): \mathbb{R}) \cdot z}\right)))\right) \mathrm{else} (0: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right))) \cdot (\mathrm{if} (h: \operatorname{Matrix.IsHermitian}\left(sigma\right)) \mathrm{then} \operatorname{Matrix.IsHermitian.cfc}\left(h, (\lambda (t: \mathbb{R}) \mapsto (\operatorname{Real.rpow}\left(t, \frac{1 - alpha}{z}\right)))\right) \mathrm{else} (0: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right))) \cdot (\mathrm{if} (h: \operatorname{Matrix.IsHermitian}\left(rho\right)) \mathrm{then} \operatorname{Matrix.IsHermitian.cfc}\left(h, (\lambda (t: \mathbb{R}) \mapsto (\operatorname{Real.rpow}\left(t, \frac{alpha}{(\operatorname{Nat.cast}\left((2: \mathbb{N})\right): \mathbb{R}) \cdot z}\right)))\right) \mathrm{else} (0: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right)))\right)) \mathrm{then} \operatorname{Matrix.IsHermitian.cfc}\left(h, (\lambda (t: \mathbb{R}) \mapsto (\operatorname{Real.rpow}\left(t, z\right)))\right) \mathrm{else} (0: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right)))\right)$$

*Formalization.* `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.Qaz` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

The trace expression in Eq. (2) sandwiches the sigma power between two rho powers and then raises the product to z. Each matrix power uses Matrix.IsHermitian.cfc with the real function t ↦ t^x when the matrix is Hermitian, and is the zero matrix otherwise. Real powers use Real.rpow. The outer trace is its real part. This total definition applies to arbitrary operators; on positive states it gives the spectral expression of §2.

**Definition 1.5 (The alpha-z divergence and its support guards).**

$$\forall n \in \mathbb{N},\; \forall alpha \in \mathbb{R},\; \forall z \in \mathbb{R},\; \forall rho \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; \forall sigma \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; (\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.Daz}\left(alpha, z, rho, sigma\right): \operatorname{EReal}) = \operatorname{ite}\left(alpha = 1, \operatorname{ite}\left(\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.SupportLE}\left(rho, sigma\right), (\operatorname{Real.toEReal}\left(\frac{\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tr}\left(rho \cdot \left((\mathrm{if} (h: \operatorname{Matrix.IsHermitian}\left(rho\right)) \mathrm{then} \operatorname{Matrix.IsHermitian.cfc}\left(h, \operatorname{Real.log}\right) \mathrm{else} (0: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right))) - (\mathrm{if} (h: \operatorname{Matrix.IsHermitian}\left(sigma\right)) \mathrm{then} \operatorname{Matrix.IsHermitian.cfc}\left(h, \operatorname{Real.log}\right) \mathrm{else} (0: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right)))\right)\right)}{\operatorname{Real.log}\left((\operatorname{Nat.cast}\left((2: \mathbb{N})\right): \mathbb{R})\right)}\right): \operatorname{EReal}), (\operatorname{Top.top}: \operatorname{EReal})\right), \operatorname{ite}\left(((alpha < 1) \land (rho \cdot sigma \ne (0: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right)))) \lor (\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.SupportLE}\left(rho, sigma\right)), (\operatorname{Real.toEReal}\left(\frac{\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.log2}\left(\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.Qaz}\left(alpha, z, rho, sigma\right)\right)}{alpha - 1}\right): \operatorname{EReal}), (\operatorname{Top.top}: \operatorname{EReal})\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.Daz` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

Equation (2) assigns a finite expression when alpha < 1 and rho times sigma is nonzero, or when the support inclusion holds; otherwise it assigns ⊤ in EReal, the value +∞. At alpha = 1, the supported branch is the Umegaki expression from Eq. (8), divided by Real.log 2, and failure of support inclusion again gives ⊤. Matrix logarithms use Matrix.IsHermitian.cfc with Real.log on Hermitian matrices and zero otherwise. Real.toEReal embeds each real-valued branch in EReal. These formulas state the total definition, including inputs outside the parameter region or state domain.

**Definition 1.6 (The infimum over stabilizer states).**

$$\forall n \in \mathbb{N},\; \forall alpha \in \mathbb{R},\; \forall z \in \mathbb{R},\; \forall rho \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; (\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.magic}\left(alpha, z, rho\right): \operatorname{EReal}) = \operatorname{sInf}\left(\operatorname{Set.image}\left((\lambda (sigma: \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right)) \mapsto (\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.Daz}\left(alpha, z, rho, sigma\right))), \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.STAB}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.magic` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

Equation (10) takes the infimum of the alpha-z divergence over mixed stabilizer states. Here sInf is taken in EReal over the image of STAB n under the divergence with rho fixed.

**Definition 1.7 (Boundary additivity for two and three qubits).**

$$(\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.claim}) \Leftrightarrow (\forall alpha \in \mathbb{R},\; \forall z \in \mathbb{R},\; (\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.DPI}\left(alpha, z\right)) \Rightarrow ((\left|\frac{1 - alpha}{z}\right| = 1) \Rightarrow (\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; ((n = 2) \lor (n = 3)) \Rightarrow (((m = 2) \lor (m = 3)) \Rightarrow (\forall rho \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(n\right),\; \forall omega \in \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.Op}\left(m\right),\; (\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.IsState}\left(rho\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.IsState}\left(omega\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.magic}\left(alpha, z, \operatorname{D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape.tensor}\left(rho, omega\right)\right) = \operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.magic}\left(alpha, z, rho\right) + \operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.magic}\left(alpha, z, omega\right))))))))$$

*Formalization.* `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.claim` (`✓ std3`).

*Citation.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

Section 5 asks whether all alpha-z magic monotones with |(1 − alpha)/z| = 1 are additive for all two- and three-qubit states. This proposition quantifies over the data-processing region, both permitted subsystem sizes independently, and all density matrices on those subsystems.

**Theorem 1.8 (A three-qubit pair refutes boundary additivity).**

$$\neg \operatorname{D5.S3.Quantum.Magic.RenyiBoundaryMagicAdditivityRefutation.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/rubboli-takagi-tomamichel-2024-magic-additivity-refutation` (refuted) by `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rubboli-takagi-tomamichel-2024-magic-additivity-refutation","declaration_gid":"D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Roberto Rubboli, Ryuji Takagi, Marco Tomamichel (2024). *Mixed-state additivity properties of magic monotones based on quantum relative entropies for single-qubit states and beyond*. DOI: [10.22331/q-2024-10-04-1492](https://doi.org/10.22331/q-2024-10-04-1492). URL: <https://arxiv.org/abs/2307.08258v4>.

*Commentary.*

The universal statement in §5 is false. At alpha = 2 and z = 1, take rho = (11I + 4S)/88 and its entrywise conjugate, with S from D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape. The completed-square inequality and the three-qubit polar bound give each marginal magic value a lower bound of log2(1015/726). A six-qubit stabilizer mixture of the product comparison state and three Bell pairs gives a joint value strictly below twice that bound. Singular comparison states have divergence +∞ by the support guard. The positive definite comparisons use the trace of rho squared times the inverse comparison matrix. These bounds contradict the claimed equality for this pair.

## References

- Truth anchor: `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.DPI`
- Truth anchor: `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.Daz`
- Truth anchor: `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.Qaz`
- Truth anchor: `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.SupportLE`
- Truth anchor: `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.log2`
- Truth anchor: `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.magic`
- Truth anchor: `D5/S3/Quantum/Magic/RenyiBoundaryMagicAdditivityRefutation.result`
- Dependency: [D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow](../Dynamics/ProjectionProbabilityFlow.md)
- Dependency: [D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape](ThreeQubitStabilizerPolarEscape.md)
