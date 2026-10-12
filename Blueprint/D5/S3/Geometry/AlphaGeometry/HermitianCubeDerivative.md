# HermitianCubeDerivative

## Abstract

The positive Hermitian cubic derivative is an invertible real operator.

**Definition 1.1 (herm_inner).**

$$\operatorname{fun} \{ n : \mathbb{N} \} (A B : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) \mapsto \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} (A * B))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.herm_inner` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

The closed defining function of the real trace pairing on Hermitian matrices. The declaration name is herm_inner; the formula displays its defining expression.

**Definition 1.2 (cubeDerivative).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{cubeDerivative} Y = ((\operatorname{selfAdjointPartL} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{toLinearMap} . \operatorname{comp} ((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) (Y . \operatorname{val} ^{2}) + ((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) Y . \operatorname{val}) . \operatorname{comp} ((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{flip} Y . \operatorname{val}) + (\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{flip} (Y . \operatorname{val} ^{2}))) . \operatorname{comp} (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{subtype}$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cubeDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of cubeDerivative.

**Theorem 1.3 (positive_hermitian_cube_derivative_equiv).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , (Y . \operatorname{val} . \operatorname{PosDef}) \to \operatorname{Function} . \operatorname{Bijective} (\operatorname{cubeDerivative} Y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.positive_hermitian_cube_derivative_equiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.4 (cubeDerivativeEquiv).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) (\operatorname{hY} : Y . \operatorname{val} . \operatorname{PosDef}) (\operatorname{hB} : \operatorname{Function} . \operatorname{Bijective} (\operatorname{cubeDerivative} Y)) , \operatorname{cubeDerivativeEquiv} Y \operatorname{hY} = (\operatorname{LinearEquiv} . \operatorname{ofInjectiveEndo} (\operatorname{cubeDerivative} Y) \operatorname{hB} . 1) . \operatorname{toContinuousLinearEquiv}$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cubeDerivativeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full equivalence construction from the cubic derivative. The injectivity proof is displayed as a bound proof argument; proof irrelevance identifies it with the established positive-derivative proof.

**Definition 1.5 (cube).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{cube} Y = \operatorname{selfAdjointPartL} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) (Y . \operatorname{val} ^{3})$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of cube.

**Theorem 1.6 (cube_val).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (\operatorname{cube} Y) . \operatorname{val} = Y . \operatorname{val} ^{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cube_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.7 (cube_contDiff).**

$$\forall (n : \mathbb{N}) , \operatorname{ContDiff} \mathbb{R} (\operatorname{top} : \mathbb{N}_{\infty}) ((\operatorname{fun} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) \mapsto \operatorname{cube} Y))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cube_contDiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.8 (cube_hasFDerivAt).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{HasFDerivAt} \operatorname{cube} (\operatorname{cubeDerivative} Y) . \operatorname{toContinuousLinearMap} Y$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cube_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.9 (F).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , F Y = (Y . \operatorname{val} ^{3}) . \operatorname{trace} . \operatorname{re}$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of F.

**Definition 1.10 (DF).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{DF} Y = (3 : \mathbb{R}) \cdot (((\operatorname{Complex} . \operatorname{reCLM} . \operatorname{comp} (\operatorname{Matrix} . \operatorname{traceLinearMap} (\operatorname{Fin} n) \mathbb{R} \mathbb{C} : (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) \to_{l} [ \mathbb{R} ] \mathbb{C}) . \operatorname{toContinuousLinearMap})) . \operatorname{comp} (((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{toContinuousBilinearMap} (Y . \operatorname{val} ^{2})) . \operatorname{comp} ((\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) . \operatorname{subtypeL}))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.DF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of DF.

**Theorem 1.11 (F_hasFDerivAt).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{HasFDerivAt} F (\operatorname{DF} Y) Y$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.F_hasFDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.12 (F_fderiv).**

$$\forall \{ n : \mathbb{N} \} (Y V : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{fderiv} \mathbb{R} F Y V = 3 * \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} (((Y . \operatorname{val} ^{2})) * (V . \operatorname{val})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.F_fderiv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.13 (alphaEmbed3).**

$$\forall \{ n : \mathbb{N} \} (A : \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) , \operatorname{alphaEmbed3} A = (3 : \mathbb{C}) \cdot \operatorname{CFC} . \operatorname{rpow} A (1 / 3 : \mathbb{R})$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.alphaEmbed3` (`✓ std3`).

*Citation.* Paolo Gibilisco; Tommaso Isola (2005). *On the monotonicity of scalar curvature in classical and quantum information geometry*. DOI: [10.1063/1.1834693](https://doi.org/10.1063/1.1834693). URL: <https://arxiv.org/abs/math-ph/0407007v2>.

*Commentary.*

Definition 4.5 (printed p. 11): “The α-geometry on D¹ₙ is the geometry induced by the pull-back of the map Aₚ(ρ): D¹ₙ → Mₙ defined by” Aₚ(ρ) := pρ^(1/p) for p ∈ R \ {0}, and log(ρ) for p = ∞, where p = 2/(1−α). Here p = 3 and CFC.rpow is the operator functional calculus.

**Definition 1.14 (root).**

$$\forall \{ n : \mathbb{N} \} (A : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) (h : \operatorname{IsSelfAdjoint} (\operatorname{CFC} . \operatorname{rpow} A . \operatorname{val} (1 / 3 : \mathbb{R}))) , \operatorname{root} A = (\langle \operatorname{CFC} . \operatorname{rpow} A . \operatorname{val} (1 / 3 : \mathbb{R}) , h \rangle : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operator cube root in the real Hermitian subspace. The self-adjointness proof field is explicitly bound; proof irrelevance fixes the subtype value.

**Theorem 1.15 (root_posdef).**

$$\forall \{ n : \mathbb{N} \} (A : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (A . \operatorname{val} . \operatorname{PosDef}) \to (\operatorname{root} A) . \operatorname{val} . \operatorname{PosDef}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.root_posdef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.16 (root_contDiffAt_cube).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (Y . \operatorname{val} . \operatorname{PosDef}) \to \operatorname{ContDiffAt} \mathbb{R} (\operatorname{top} : \mathbb{N}_{\infty}) \operatorname{root} (\operatorname{cube} Y)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.root_contDiffAt_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.17 (rhoH).**

$$\forall \{ n : \mathbb{N} \} (x : \operatorname{Fin} (n ^{2} - 1) \to \mathbb{R}) , \operatorname{rhoH} x = \operatorname{selfAdjointPartL} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}) (\operatorname{rho} x)$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.rhoH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of rhoH.

**Theorem 1.18 (rhoH_val).**

$$\forall \{ n : \mathbb{N} \} (x : (\operatorname{Fin} (n ^{2} - 1) \to \mathbb{R})) , (\operatorname{rhoH} x) . \operatorname{val} = \operatorname{rho} x$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.rhoH_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.19 (immersion).**

$$\forall \{ n : \mathbb{N} \} (x : (\operatorname{Fin} (n ^{2} - 1) \to \mathbb{R})) , \operatorname{immersion} x = \operatorname{root} (\operatorname{rhoH} x)$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.immersion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of immersion.

**Theorem 1.20 (immersion_contDiffAt).**

$$\forall \{ n : \mathbb{N} \} (x : (\operatorname{Fin} (n ^{2} - 1) \to \mathbb{R})) , ((\operatorname{rho} x) . \operatorname{PosDef}) \to \operatorname{ContDiffAt} \mathbb{R} (\operatorname{top} : \mathbb{N}_{\infty}) \operatorname{immersion} x$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.immersion_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.21 (immersion_derivative_injective).**

$$\forall \{ n : \mathbb{N} \} (x : (\operatorname{Fin} (n ^{2} - 1) \to \mathbb{R})) , (0 < n) \to ((\operatorname{rho} x) . \operatorname{PosDef}) \to \operatorname{Function} . \operatorname{Injective} (\operatorname{fderiv} \mathbb{R} \operatorname{immersion} x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.immersion_derivative_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.22 (immersion_level_one).**

$$\forall \{ n : \mathbb{N} \} (x : (\operatorname{Fin} (n ^{2} - 1) \to \mathbb{R})) , (0 < n) \to ((\operatorname{rho} x) . \operatorname{PosDef}) \to F (\operatorname{immersion} x) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.immersion_level_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.23 (herm_inner_smul_left).**

$$\forall \{ n : \mathbb{N} \} (c : \mathbb{R}) (A B : (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} (((c \cdot A)) * (B))) = c * \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} ((A) * (B)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.herm_inner_smul_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.24 (herm_inner_smul_right).**

$$\forall \{ n : \mathbb{N} \} (c : \mathbb{R}) (A B : (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} ((A) * ((c \cdot B)))) = c * \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} ((A) * (B)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.herm_inner_smul_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.25 (herm_inner_add_right).**

$$\forall \{ n : \mathbb{N} \} (A B C : (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} ((A) * ((B + C)))) = \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} ((A) * (B))) + \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} ((A) * (C)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.herm_inner_add_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.26 (herm_inner_symm).**

$$\forall \{ n : \mathbb{N} \} (A B : (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} ((A) * (B))) = \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} ((B) * (A)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.herm_inner_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.27 (trace_pow_eq_eigenvalues).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) (k : \mathbb{N}) , (Y . \operatorname{val} ^{k}) . \operatorname{trace} . \operatorname{re} = \sum i , (Y . \operatorname{property} . \operatorname{isHermitian} . \operatorname{eigenvalues} i) ^{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.trace_pow_eq_eigenvalues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.28 (S4).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{S4} Y = (Y . \operatorname{val} ^{4}) . \operatorname{trace} . \operatorname{re}$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.S4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of S4.

**Theorem 1.29 (S4_eq_sum).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{S4} Y = \sum i , Y . \operatorname{property} . \operatorname{isHermitian} . \operatorname{eigenvalues} i ^{4}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.S4_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.30 (S4_pos).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (0 < n) \to (Y . \operatorname{val} . \operatorname{PosDef}) \to 0 < \operatorname{S4} Y$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.S4_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.31 (normal).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{normal} Y = (\operatorname{Real} . \operatorname{sqrt} (\operatorname{S4} Y)) ^{-1} \cdot (\langle Y . \operatorname{val} ^{2} , Y . \operatorname{property} . \operatorname{pow} 2 \rangle : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.normal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of normal.

**Theorem 1.32 (normal_val).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (\operatorname{normal} Y) . \operatorname{val} = (\operatorname{Real} . \operatorname{sqrt} (\operatorname{S4} Y)) ^{-1} \cdot Y . \operatorname{val} ^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.normal_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.33 (normal_unit).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (0 < \operatorname{S4} Y) \to \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} (((\operatorname{normal} Y) . \operatorname{val}) * ((\operatorname{normal} Y) . \operatorname{val}))) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.normal_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.34 (DF_normal).**

$$\forall \{ n : \mathbb{N} \} (Y V : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (0 < \operatorname{S4} Y) \to \operatorname{fderiv} \mathbb{R} F Y V = 3 * \operatorname{Real} . \operatorname{sqrt} (\operatorname{S4} Y) * \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} (((\operatorname{normal} Y) . \operatorname{val}) * (V . \operatorname{val})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.DF_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.35 (jordan).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{jordan} Y = (\operatorname{selfAdjointPartL} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{comp} ((((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{toContinuousBilinearMap} Y . \operatorname{val}) . \operatorname{comp} (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{subtypeL}) + (((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{toContinuousBilinearMap}) . \operatorname{flip} Y . \operatorname{val}) . \operatorname{comp} (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{subtypeL})$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.jordan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of jordan.

**Theorem 1.36 (jordan_val).**

$$\forall \{ n : \mathbb{N} \} (Y V : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (\operatorname{jordan} Y V) . \operatorname{val} = Y . \operatorname{val} * V . \operatorname{val} + V . \operatorname{val} * Y . \operatorname{val}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.jordan_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.37 (square).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{square} Y = (\langle Y . \operatorname{val} ^{2} , Y . \operatorname{property} . \operatorname{pow} 2 \rangle : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.square` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of square.

**Definition 1.38 (DS4).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , \operatorname{DS4} Y = (4 : \mathbb{R}) \cdot (((\operatorname{Complex} . \operatorname{reCLM} . \operatorname{comp} (\operatorname{Matrix} . \operatorname{traceLinearMap} (\operatorname{Fin} n) \mathbb{R} \mathbb{C}) . \operatorname{toContinuousLinearMap})) . \operatorname{comp} (((\operatorname{LinearMap} . \operatorname{mul} \mathbb{R} (A := \operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{toContinuousBilinearMap} (Y . \operatorname{val} ^{3})) . \operatorname{comp} ((\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) . \operatorname{subtypeL}))$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.DS4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of DS4.

**Definition 1.39 (projection).**

$$\forall \{ n : \mathbb{N} \} (Y V : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{projection} Y V = V - \operatorname{RCLike} . \operatorname{re} (\operatorname{Matrix} . \operatorname{trace} (((\operatorname{normal} Y) . \operatorname{val}) * (V . \operatorname{val}))) \cdot \operatorname{normal} Y$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of projection.

**Theorem 1.40 (regular_level_set_shape_operator).**

$$\forall \{ n : \mathbb{N} \} (Y V : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (0 < \operatorname{S4} Y) \to \operatorname{fderiv} \mathbb{R} \operatorname{normal} Y V = (\operatorname{Real} . \operatorname{sqrt} (\operatorname{S4} Y)) ^{-1} \cdot \operatorname{projection} Y (\operatorname{jordan} Y V)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.regular_level_set_shape_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Theorem 1.41 (normal_contDiffAt).**

$$\forall \{ n : \mathbb{N} \} (Y : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C}))) , (0 < \operatorname{S4} Y) \to \operatorname{ContDiffAt} \mathbb{R} (\operatorname{top} : \mathbb{N}_{\infty}) \operatorname{normal} Y$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.normal_contDiffAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

**Definition 1.42 (readoutEquiv).**

$$\forall (n : \mathbb{N}) , \operatorname{let} f : (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) \to_{l} [ \mathbb{R} ] (\operatorname{Fin} n \times \operatorname{Fin} n \to \mathbb{R}) := \operatorname{LinearMap} . \operatorname{pi} (\operatorname{fun} (p : \operatorname{Fin} n \times \operatorname{Fin} n) \mapsto (\operatorname{if} p . 1 \leq p . 2 \operatorname{then} \operatorname{Complex} . \operatorname{reCLM} . \operatorname{toLinearMap} \operatorname{else} \operatorname{Complex} . \operatorname{imCLM} . \operatorname{toLinearMap}) . \operatorname{comp} (((\operatorname{LinearMap} . \operatorname{proj} p . 2) . \operatorname{comp} (\operatorname{LinearMap} . \operatorname{proj} p . 1)) . \operatorname{comp} (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) . \operatorname{subtype})) ; \forall (\operatorname{hB} : \operatorname{Function} . \operatorname{Bijective} f) , \operatorname{readoutEquiv} n = \operatorname{LinearEquiv} . \operatorname{ofBijective} f \operatorname{hB}$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.readoutEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full real-coordinate equivalence construction. Its coordinate map is displayed as the local f, and its bijectivity proof is bound explicitly; proof irrelevance fixes the inverse equivalence.

**Theorem 1.43 (hermitian_jordan_operator_trace_formulas).**

$$\forall \{ n : \mathbb{N} \} (Y : \operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) , \operatorname{LinearMap} . \operatorname{trace} \mathbb{R} (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) (\operatorname{jordan} Y) . \operatorname{toLinearMap} = 2 * (n : \mathbb{R}) * (\sum i , Y . \operatorname{property} . \operatorname{isHermitian} . \operatorname{eigenvalues} i) \land \operatorname{LinearMap} . \operatorname{trace} \mathbb{R} (\operatorname{selfAdjoint} . \operatorname{submodule} \mathbb{R} (\operatorname{Matrix} (\operatorname{Fin} n) (\operatorname{Fin} n) \mathbb{C})) ((\operatorname{jordan} Y) . \operatorname{toLinearMap} ^{2}) = 2 * (n : \mathbb{R}) * (\sum i , Y . \operatorname{property} . \operatorname{isHermitian} . \operatorname{eigenvalues} i ^{2}) + 2 * (\sum i , Y . \operatorname{property} . \operatorname{isHermitian} . \operatorname{eigenvalues} i) ^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.hermitian_jordan_operator_trace_formulas` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real Hermitian Jordan operator has diagonal eigenvalues 2λᵢ and off-diagonal eigenvalues λᵢ + λⱼ. Their real multiplicities determine the first two operator traces.

**Definition 1.44 (rankOneProjection).**

$$\forall (V : \operatorname{Type}) [ \operatorname{AddCommGroup} V ] [ \operatorname{Module} \mathbb{R} V ] (f : V \to_{l} [ \mathbb{R} ] \mathbb{R}) (u : V) , \operatorname{rankOneProjection} f u = 1 - \operatorname{LinearMap} . \operatorname{smulRight} f u$$

*Formalization.* `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.rankOneProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The defining expression of projection.

**Theorem 1.45 (gauss_trace_rank_one_contraction).**

$$\forall \{ V : \operatorname{Type} \} [ \operatorname{AddCommGroup} V ] [ \operatorname{Module} \mathbb{R} V ] [ \operatorname{Module} . \operatorname{Free} \mathbb{R} V ] [ \operatorname{Module} . \operatorname{Finite} \mathbb{R} V ] (f : V \to_{l} [ \mathbb{R} ] \mathbb{R}) (u : V) (K : \operatorname{Module} . \operatorname{End} \mathbb{R} V) (s : \mathbb{R}) , (f u = 1) \to (s \neq 0) \to (\operatorname{LinearMap} . \operatorname{trace} \mathbb{R} V (s ^{-1} \cdot (\operatorname{rankOneProjection} f u * K * \operatorname{rankOneProjection} f u))) ^{2} - \operatorname{LinearMap} . \operatorname{trace} \mathbb{R} V ((s ^{-1} \cdot (\operatorname{rankOneProjection} f u * K * \operatorname{rankOneProjection} f u)) ^{2}) = ((\operatorname{LinearMap} . \operatorname{trace} \mathbb{R} V K) ^{2} - \operatorname{LinearMap} . \operatorname{trace} \mathbb{R} V (K ^{2}) - 2 * \operatorname{LinearMap} . \operatorname{trace} \mathbb{R} V K * f (K u) + 2 * f ((K ^{2}) u)) / s ^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.gauss_trace_rank_one_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stated identity or implication holds for every displayed parameter.

## References

- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.DF`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.DF_normal`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.DS4`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.F`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.F_fderiv`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.F_hasFDerivAt`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.S4`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.S4_eq_sum`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.S4_pos`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.alphaEmbed3`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cube`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cubeDerivative`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cubeDerivativeEquiv`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cube_contDiff`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cube_hasFDerivAt`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.cube_val`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.gauss_trace_rank_one_contraction`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.herm_inner`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.herm_inner_add_right`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.herm_inner_smul_left`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.herm_inner_smul_right`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.herm_inner_symm`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.hermitian_jordan_operator_trace_formulas`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.immersion`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.immersion_contDiffAt`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.immersion_derivative_injective`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.immersion_level_one`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.jordan`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.jordan_val`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.normal`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.normal_contDiffAt`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.normal_unit`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.normal_val`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.positive_hermitian_cube_derivative_equiv`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.projection`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.rankOneProjection`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.readoutEquiv`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.regular_level_set_shape_operator`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.rhoH`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.rhoH_val`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.root`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.root_contDiffAt_cube`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.root_posdef`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.square`
- Truth anchor: `D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative.trace_pow_eq_eigenvalues`
- Dependency: [D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates](HermitianDensityCoordinates.md)
