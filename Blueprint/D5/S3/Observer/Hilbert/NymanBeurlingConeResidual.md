# Nyman-Beurling Cone Residual

## Abstract

The orthogonal residual of the actual Nyman target in its full complex arithmetic span is the real-cone residual, and its negative is a dual witness.

H is exactly NymanBeurlingFiniteGramDistance.Carrier: Lp Complex 2 positiveMeasure, with positiveMeasure equal to volume restricted to (0,infinity). The existing target chi is the Lp class of the indicator of (0,1), with squared norm one. The existing sourceVector a ha, for natural a and ha : 1 <= a, is denoted f_a and represents ofReal(fract(1/(a*x))) almost everywhere. These are the source owner's target_coe_ae, sourceVector_coe_ae and target_norm_sq facts.

S_N is the existing complex span of sourceVector(i+1), i : Fin N. M is BoundedInverseLimitReconstruction.cumulativeSpace shell, exactly the topological closure of the supremum of all complex shells. K is the real ProperCone obtained by restricting M's scalars to the nonnegative reals. Its underlying set, norm and topology stay on the identical Lp carrier. P_M and P_(M orthogonal) are the existing complex starProjection operators; P_K is ConeResidualWitness.coneProjection. Define p=P_M chi, r=P_(M orthogonal) chi and w=-r independently of P_K. The notation dual(K) uses the nonnegative real inner pairing. Polar membership of y is written -y in K dual, following MoreauDecomposition.

**Theorem 1.1 (Nested source shells).**

$$\forall n\in \mathbb{N}, \forall m\in \mathbb{N}, n\le m\Rightarrow S_{n}\subseteq S_{m}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.shell_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite source generator survives in every later complex span.

**Theorem 1.2 (Zero shell).**

$$S_{0} = \{0\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.shell_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The span indexed by Fin 0 is the bottom submodule.

**Theorem 1.3 (Full arithmetic closure).**

$$M = \overline{\{x\in \mathcal{H} \mid \exists N\in \mathbb{N}, x\in S_{N}\}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.cumulative_eq_closure_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Monotonicity identifies the submodule supremum with the union.

**Theorem 1.4 (Positive source indices).**

$$\{x\in \mathcal{H} \mid \exists N\in \mathbb{N}, x\in S_{N}\} = \{x\in \mathcal{H} \mid \exists N\in \mathbb{N}, 0<N \land x\in S_{N}\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.shell_union_eq_positive_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero shell contributes no new vector: it is included in shell one. The displayed positive-N union is the source union.

**Theorem 1.5 (Source completion).**

$$M = \overline{\{x\in \mathcal{H} \mid \exists N\in \mathbb{N}, 0<N \land x\in S_{N}\}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.cumulative_eq_closure_positive_union` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both closure operations use the existing Lp topology.

**Theorem 1.6 (Every shell is retained).**

$$\forall N\in \mathbb{N}, S_{N}\subseteq M$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.shell_le_cumulative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This holds for every natural stage, including zero.

**Theorem 1.7 (Every positive generator is retained).**

$$\forall n\in \mathbb{N}, f_{n+1}\in S_{n+1} \land f_{n+1}\in M$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.sourceVector_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positivity proof for n+1 is derived. No arithmetic generator is omitted.

**Theorem 1.8 (Full complex scalar closure).**

$$\forall c\in \mathbb{C}, \forall s\in \mathcal{H}, s\in M\Rightarrow cs\in M$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.complex_smul_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In particular multiplication by the imaginary unit stays in M; this is not the real span of the displayed generators.

**Theorem 1.9 (Existing residual owner).**

$$\operatorname{residualSpace}(shell) = M^{\perp}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.residualSpace_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The infinite residual uses the same cumulativeSpace owner.

**Theorem 1.10 (Unchanged closed set).**

$$\forall x\in \mathcal{H}, x\in K \iff x\in M$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.mem_cone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restriction of scalars changes neither membership nor the ambient carrier.

**Theorem 1.11 (Scalar pairing identification).**

$$\forall x\in \mathcal{H}, \forall y\in \mathcal{H}, \langle x, y\rangle_{\mathbb{R}} = \operatorname{Re}(\langle x, y\rangle_{\mathbb{C}})$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.real_inner_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This uses the existing L2 real and complex inner products and commutation of the real part with the integral. No global instance is installed.

**Theorem 1.12 (Independent projections agree).**

$$\forall x\in \mathcal{H}, P_{K}x = P_{M}x$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.coneProjection_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chosen cone nearest point satisfies the complex submodule's existing nearest-point characterization, which determines starProjection uniquely.

**Theorem 1.13 (All-vector residual identity).**

$$\forall x\in \mathcal{H}, x-P_{K}x = P_{M^{\perp}}x$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.cone_residual_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity holds on the whole actual Lp carrier, beyond finite shells.

**Theorem 1.14 (Dual is the complex orthogonal complement).**

$$\forall w\in \mathcal{H}, w\in \operatorname{dual}(K) \iff w\in M^{\perp}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.mem_innerDual_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Testing a vector and its negative forces zero real pairing. Testing the imaginary multiple then forces the imaginary pairing to vanish as well. The reverse direction uses complex orthogonality.

**Theorem 1.15 (Polar is the same orthogonal complement).**

$$\forall w\in \mathcal{H}, -w\in \operatorname{dual}(K) \iff w\in M^{\perp}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.mem_polar_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both implications preserve the full complex orthogonal complement.

**Theorem 1.16 (Exact dual and polar signs).**

$$\forall w\in \mathcal{H}, (w\in \operatorname{dual}(K) \iff (\forall s\in K, 0\le \langle s, w\rangle_{\mathbb{R}})) \land (-w\in \operatorname{dual}(K) \iff (\forall s\in K, \langle w, s\rangle_{\mathbb{R}}\le0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.cone_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dual uses inner(s,w) >= 0; the polar uses inner(w,s) <= 0. Real symmetry reconciles the argument order.

**Theorem 1.17 (Actual Nyman residual and witness).**

$$\begin{gathered}\mathrm{chi} = p+r \land p\in M \land r\in M^{\perp}\\\land \langle p, r\rangle_{\mathbb{C}} = 0\\\land r = \mathrm{chi}-P_{K}\mathrm{chi}\\\land w\in \operatorname{dual}(K) \land -r\in \operatorname{dual}(K)\\\land (\forall s\in \mathcal{H}, s\in M\Rightarrow (\langle w, s\rangle_{\mathbb{C}} = 0 \land \langle w, s\rangle_{\mathbb{R}} = 0))\\\land \langle w, \mathrm{chi}\rangle_{\mathbb{R}} = -\Vert r\Vert^{2}\\\land (r = 0 \iff \mathrm{chi}\in M)\\\land (\neg (\mathrm{chi}\in M)\Rightarrow \langle w, \mathrm{chi}\rangle_{\mathbb{R}}<0)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.nyman_beurling_cone_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier, target, infinite complex span and independently defined p, r, w are fixed above. The decomposition uses Moreau; the generic cone residual duality supplies the witness and conditional strict negativity. The negative-square identity itself is unconditional. This is the Nyman closed-subspace row only. It proves no nonmembership, nonzero residual, vanishing residual, density or Riemann-hypothesis statement. The separate analytic Nyman-Beurling equivalence and the other three cone rows remain open.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.complex_smul_mem`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.coneProjection_eq`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.cone_residual_eq`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.cone_signs`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.cumulative_eq_closure_positive_union`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.cumulative_eq_closure_union`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.mem_cone`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.mem_innerDual_iff`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.mem_polar_iff`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.nyman_beurling_cone_residual`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.real_inner_eq`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.residualSpace_eq`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.shell_le_cumulative`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.shell_monotone`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.shell_union_eq_positive_union`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.shell_zero`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingConeResidual.sourceVector_mem`
- Dependency: [D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance](NymanBeurlingFiniteGramDistance.md)
- Dependency: [D5/S3/Observer/Separation/MoreauDecomposition](../Separation/MoreauDecomposition.md)
- Dependency: [D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction](../../Quantum/Completion/BoundedInverseLimitReconstruction.md)
