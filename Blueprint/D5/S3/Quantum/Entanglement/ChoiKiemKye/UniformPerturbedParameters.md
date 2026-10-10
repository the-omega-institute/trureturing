# UniformPerturbedParameters

## Abstract

Public declarations of UniformPerturbedParameters, with complete parameters and the Lean operations.

**Theorem 1.1 (Anchor.largest_root_psd).**

$$\forall (n : \mathbb{N}) , (3 \leq n) \to (\forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (r : \mathbb{R}) , (\operatorname{ConstructionReduction}. \operatorname{LargestRoot} a b r) \to ((\operatorname{ConstructionReduction}. D a b r) . \operatorname{PosSemidef}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters.largest_root_psd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.2 (Anchor.D_shift).**

$$\forall (n : \mathbb{N}) , \forall (a : Fin n \to \mathbb{C}) , \forall (b : Fin n \to \mathbb{C}) , \forall (r : \mathbb{R}) , \forall (R : \mathbb{R}) , \operatorname{ConstructionReduction}. D a b R = \operatorname{ConstructionReduction}. D a b r + \operatorname{val}\left(R - r\right) \cdot 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters.D_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.3 (Anchor.perturbed_kernel_stability).**

$$\forall (m : \mathbb{N}) , (15 \leq m) \to (\exists (r : \mathbb{R}) (r' : \mathbb{R}) (q' : \operatorname{EuclideanSpace} \mathbb{C} (Fin (m + 2))) , \operatorname{ConstructionReduction}. \operatorname{LargestRoot} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorAlpha} (m + 2)) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} (m + 2)) r \land \operatorname{ConstructionReduction}. \operatorname{LargestRoot} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} (m + 2)) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} (m + 2)) r' \land \operatorname{ConstructionReduction}. \operatorname{SimpleRoot} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} (m + 2)) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} (m + 2)) r' \land 5 < r' \land \left\lVert q' \right\rVert = 1 \land (\operatorname{ConstructionReduction}. D (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} (m + 2)) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} (m + 2)) r') . \operatorname{mulVec} q'. \operatorname{ofLp} = 0 \land \left\lVert q' - (\lambda (m : \mathbb{N}) (r : \mathbb{R}) \mapsto \operatorname{NormedSpace}. \operatorname{normalize} (\operatorname{WithLp}. \operatorname{toLp} 2 (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{kernel} m r))) m r \right\rVert \leq 4 \cdot (\operatorname{norm} \circ \operatorname{val}\left(\operatorname{Matrix}. \operatorname{toEuclideanCLM}\right)) (\operatorname{ConstructionReduction}. D (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} (m + 2)) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} (m + 2)) 0 - \operatorname{ConstructionReduction}. D (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{anchorAlpha} (m + 2)) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} (m + 2)) 0) \operatorname{HDiv}.\operatorname{hDiv} (1 \operatorname{HDiv}.\operatorname{hDiv} (9 \cdot \operatorname{val}\left(m + 2\right))) \land \left\lVert q' - (\lambda (m : \mathbb{N}) (r : \mathbb{R}) \mapsto \operatorname{NormedSpace}. \operatorname{normalize} (\operatorname{WithLp}. \operatorname{toLp} 2 (\operatorname{UniformParameterAnchor}. \operatorname{Anchor}. \operatorname{kernel} m r))) m r \right\rVert \leq 4 \cdot (2 \cdot \operatorname{Real}. pi \operatorname{HDiv}.\operatorname{hDiv} (1000000000 \cdot (\operatorname{val}\left(m + 2\right))^{4})) \operatorname{HDiv}.\operatorname{hDiv} (1 \operatorname{HDiv}.\operatorname{hDiv} (9 \cdot \operatorname{val}\left(m + 2\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters.perturbed_kernel_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

**Theorem 1.4 (Anchor.n_ge_17).**

$$\forall (n : \mathbb{N}) , (17 \leq n) \to (\exists (r : \mathbb{R}) (w : Fin n \to \mathbb{C}) , \operatorname{ConstructionReduction}. \operatorname{Admissible} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) \land 5 < r \land \operatorname{ConstructionReduction}. \operatorname{LargestRoot} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) r \land \operatorname{ConstructionReduction}. \operatorname{SimpleRoot} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) r \land w \neq 0 \land (\operatorname{ConstructionReduction}. D (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) r) . \operatorname{mulVec} w = 0 \land \operatorname{ConstructionReduction}. \operatorname{StarCondition} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) w \land \operatorname{ConstructionReduction}. PPT (\operatorname{ConstructionReduction}. rho (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) r) \land \operatorname{ConstructionReduction}. \operatorname{Edge} (\operatorname{ConstructionReduction}. rho (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) r) \land (\operatorname{ConstructionReduction}. rho (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) r) . \operatorname{rank} = n \cdot n - 1 \land (\operatorname{ConstructionReduction}. \operatorname{rhoGamma} (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{alpha} n) (\operatorname{UniformParameterAnchor}. \operatorname{Uniform}. \operatorname{beta} n) r) . \operatorname{rank} = n \cdot n - 2 \cdot n + 3)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters.n_ge_17` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The formula uses the actual Lean names and notation. HDiv.hDiv is displayed in infix position for Lean’s division operator: natural-number floor division, Euclidean integer division, or field division according to the carrier. Natural-number subtraction is truncated. val denotes the displayed Lean coercion.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters.D_shift`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters.largest_root_psd`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters.n_ge_17`
- Truth anchor: `D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformPerturbedParameters.perturbed_kernel_stability`
- Dependency: [D5/S3/Quantum/Entanglement/ChoiKiemKye/UniformParameterAnchor](UniformParameterAnchor.md)
