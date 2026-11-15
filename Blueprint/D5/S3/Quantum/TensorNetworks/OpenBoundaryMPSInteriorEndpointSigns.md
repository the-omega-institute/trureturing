# General regular-sector annular endpoint signs

## Abstract

Full complex-linear operator norm limits of the native inverse dual transfer imply strict negative real residual values on both annular boundary circles for every regular sector and positive definite left target.

**Definition 1.1 (Zero-endpoint matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.Mzero`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.Mzero` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

With v=(-alpha,1), Mzero is exactly diagonalStarInverse applied to vecMulVec(star v,v).

**Definition 1.2 (Infinity-endpoint matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.Minf`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.Minf` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

With u=(beta,-1), Minf is exactly diagonalStarInverse applied to vecMulVec(star u,u).

**Definition 1.3 (The existing inverse as a complex-linear operator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.inverseDualOperator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.inverseDualOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The underlying function is the existing inverseDualTransfer. The Bond norm is the elementwise supremum norm; the continuous-linear endomorphism space carries its genuine operator norm. No matrix multiplication normed-ring assumption is made.

**Definition 1.4 (The zero limiting operator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.zeroLimitOperator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.zeroLimitOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every Bond X, zeroLimitOperator(s)(X)=(X11/d) smul Mzero, with d=normSq(delta). All scalar arithmetic in this displayed operator is complex, with the real d cast to Complex.

**Definition 1.5 (The infinity limiting operator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.infinityLimitOperator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.infinityLimitOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every Bond X, infinityLimitOperator(s)(X)=(X00/d) smul Minf, with the same complex scalar convention.

**Theorem 1.6 (Exact native equality).**

$$\forall s \in Sector,\; \forall z \in Complex,\; \forall X \in Bond,\; inverseDualOperator\left(s, z, X\right) = inverseDualTransfer\left(s, z, X\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.inverse_dual_operator_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

This equality is consumed in the scalar-power/native-iterate bridge. The native inverse, targets, residual and observation are reused unchanged.

**Theorem 1.7 (Operator norm convergence at punctured zero).**

$$\forall s \in Sector,\; (Regular\left(s\right)) \Rightarrow (Tendsto\left((\lambda (z: Complex) \mapsto (smul\left(ofReal\left(norm\left(z\right)^{2}\right), inverseDualOperator\left(s, z\right)\right))), puncturedNhds\left(0\right), nhds\left(zeroLimitOperator\left(s\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.inverse_dual_operator_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every regular complex sector, norm(z)^2 times the bundled native inverse tends to zeroLimitOperator in the norm topology of Bond toL[Complex] Bond as z tends to zero through nonzero complex values.

**Theorem 1.8 (Operator norm convergence at infinity).**

$$\forall s \in Sector,\; (Regular\left(s\right)) \Rightarrow (Tendsto\left(inverseDualOperator\left(s\right), cobounded\left(Complex\right), nhds\left(infinityLimitOperator\left(s\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.inverse_dual_operator_infinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every regular complex sector, the bundled native inverse tends to infinityLimitOperator along the cobounded filter on Complex. This includes every complex direction and is not a radial or pointwise assertion.

**Theorem 1.9 (Fixed native powers at punctured zero).**

$$\forall s \in Sector,\; \forall p \in Nat,\; \forall P \in Bond,\; ((Regular\left(s\right)) \land (1 \le p)) \Rightarrow (Tendsto\left((\lambda (z: Complex) \mapsto (smul\left(ofReal\left(norm\left(z\right)^{2 \cdot p}\right), trialLeft\left(s, p, P, z\right)\right))), puncturedNhds\left(0\right), nhds\left(smul\left(entry\left(P, 1, 1\right) \cdot inv\left(ofReal\left(normSq\left(delta\left(s\right)\right)\right)\right)^{p} \cdot inv\left(ofReal\left(1 + normSq\left(mu\left(s\right)\right)\right)\right)^{p - 1}, Mzero\left(s\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.trial_left_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For each fixed natural p at least one and arbitrary complex Bond P, norm(z)^(2p) times native trialLeft tends to P11 d^(-p) aone^(-(p-1)) smul Mzero, where aone=1+normSq(mu). No positivity is needed for this limit.

**Theorem 1.10 (Fixed native powers at infinity).**

$$\forall s \in Sector,\; \forall p \in Nat,\; \forall P \in Bond,\; ((Regular\left(s\right)) \land (1 \le p)) \Rightarrow (Tendsto\left(trialLeft\left(s, p, P\right), cobounded\left(Complex\right), nhds\left(smul\left(entry\left(P, 0, 0\right) \cdot inv\left(ofReal\left(normSq\left(delta\left(s\right)\right)\right)\right)^{p} \cdot div\left(ofReal\left(normSq\left(beta\left(s\right)\right)\right), ofReal\left(1 + normSq\left(lambda\left(s\right)\right)\right)\right)^{p - 1}, Minf\left(s\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.trial_left_infinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For each fixed natural p at least one and arbitrary Bond P, native trialLeft tends to P00 d^(-p) (normSq(beta)/azero)^(p-1) smul Minf, where azero=1+normSq(lambda). There is no norm-growth assertion at infinity.

**Theorem 1.11 (Simultaneous circle-wide native residual signs).**

$$\forall s \in Sector,\; \forall p \in Nat,\; \forall P \in Bond,\; \forall zo \in Complex,\; ((((Regular\left(s\right)) \land (1 \le p)) \land (PosDef\left(P\right))) \land (zo \neq 0)) \Rightarrow (\exists epsilon \in Real,\; \exists R \in Real,\; (((0 < epsilon) \land (epsilon < norm\left(zo\right))) \land (norm\left(zo\right) < R)) \land (\forall q \in Nat,\; \forall H \in Bond,\; \forall z \in Complex,\; ((norm\left(z\right) = epsilon) \lor (norm\left(z\right) = R)) \Rightarrow (re\left(residual\left(s, p, q, P, H, z\right)\right) < 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.annular_residual_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every regular sector, every p at least one, every positive definite Bond P and every nonzero z0, the proof constructs 0<epsilon<norm(z0)<R. For every natural q, every Bond H and every complex z on either whole boundary circle, the real component of the existing residual is strictly negative. The radii are independent of q and H.

Write U with rows (beta,-1),(0,0) and V with rows (0,0),(-alpha,1). For z nonzero the exact native inverse matrix is delta inverse smul (U+z inverse smul V). Congruence precedes diagonalStarInverse. The infinity extension is d inverse smul T((U+wV) dagger X (U+wV)); its composition with w=z inverse is the native operator. The zero extension is d inverse smul T(norm(z)^2 U dagger X U + conjugate(z) U dagger X V + z V dagger X U + V dagger X V). Exact equality with norm(z)^2 times the native operator holds throughout the punctured domain.

Entry continuity of the extension for every application is promoted by pinned Mathlib continuous_clm_apply using finite-dimensional Bond. This proves continuity into the actual endomorphism operator norm. Fixed powers of these same parameter-dependent operators converge by Tendsto.pow before evaluating at P. Composition is in native order; the exact scalar-power bridge gives the native iterates. The rank-one limiting operators are powered explicitly using Mzero11=1/aone and Minf00=normSq(beta)/azero.

Let c=normSq(1+conjugate(lambda) mu). The exact real determinant formulas are det(Mzero)=normSq(alpha)(1/(azero aone)-1/c) and det(Minf)=normSq(beta)(1/(azero aone)-1/c). The identity c=azero aone-d and Regular give c>0, d>0 and strictly negative determinants. Positive definiteness makes P00 and P11 real and positive; both fixed-power determinant limits are therefore strictly negative. At zero, det(t smul X)=t squared det(X) with t=norm(z)^(2p)>0 removes the scale. At infinity, the unscaled determinant tends to a negative constant. Neighborhood and cobounded-filter bases produce signs uniformly on circles enclosing the arbitrary z0.

This directly supplies the boundary-sign premise of annular_regular_root_actual_ambiguity. Full C9, real transversality, finite chart coverage, polynomial clearance and genericity in actual state and density images remain separate obligations. This unit earns zero solved external open problems. It introduces no dynamics, energy, physical clock, normalization, physical inverse or thermodynamic assertion.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.Minf`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.Mzero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.annular_residual_negative`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.infinityLimitOperator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.inverseDualOperator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.inverse_dual_operator_apply`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.inverse_dual_operator_infinity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.inverse_dual_operator_zero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.trial_left_infinity`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.trial_left_zero`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns.zeroLimitOperator`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization](OpenBoundaryMPSInteriorRootRealization.md)
