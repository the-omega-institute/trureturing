# Traceless cohomology fails diagonal freeness

## Abstract

The traceless cohomology at p = 5 and N = 4 is not free over the exterior algebra of the diagonal creators.

The matrix size is four and the supercharge has degree five. A Lie subalgebra or submodule used as a type denotes its carrier. Subtype.val denotes the underlying vector of a subtype element. All named objects retain their Lean namespaces.

**Definition 1.1 (The traceless one-particle space).**

$$\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.V} = \operatorname{LieAlgebra.SpecialLinear.sl}\left(\operatorname{Fin}\left(4\right), \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.V` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

In v2 §2 the traceless one-particle space consists of trace-zero complex matrices. Here it is Mathlib's LieAlgebra.SpecialLinear.sl (Fin 4) ℂ, the space of trace-zero 4 by 4 complex matrices.

**Definition 1.2 (The traceless exterior algebra).**

$$\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.E} = \operatorname{ExteriorAlgebra}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.V}\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.E` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

The traceless Fock space of v2 §2 is the exterior algebra over ℂ of the traceless one-particle space. Its multiplication is exterior multiplication.

**Definition 1.3 (The traceless matrix-unit vectors).**

$$\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \operatorname{Subtype.val}\left(\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.creatorVec}\left(i, j\right)\right) = \operatorname{Matrix.single}\left(i, j, (1: \mathbb{C})\right) - \operatorname{HSMul.hSMul}\left(\operatorname{ite}\left(i = j, (\frac{1}{4}: \mathbb{C}), (0: \mathbb{C})\right), (1: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.creatorVec` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

For every pair of indices in Fin 4, creatorVec is the element of V whose underlying matrix is Matrix.single i j 1 minus (if i = j then (1 / 4 : ℂ) else 0) times the identity matrix. The subtraction removes the trace of each diagonal matrix unit, as in v2 §2; off-diagonal matrix units are unchanged.

**Definition 1.4 (The matrix of traceless creators).**

$$\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.A}\left(i, j\right) = \operatorname{ExteriorAlgebra.\iota}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.creatorVec}\left(i, j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.A` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

The matrix A has entries in E. Each entry is ExteriorAlgebra.ι ℂ applied to the corresponding traceless matrix-unit vector. This is the traceless creator matrix A of v2 §2.

**Definition 1.5 (The quintic supercharge).**

$$\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.Q} = \operatorname{Matrix.trace}\left(\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.A}^{5}\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.Q` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

Specializing Q_p = Tr(A^p) from v2 §2 to p = 5 gives this element of E. The fifth power is matrix multiplication over the exterior algebra. Q is homogeneous of degree five and Q squared is zero.

**Definition 1.6 (The traceless diagonal subspace).**

$$\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.H} = \operatorname{Submodule.span}\left(\mathbb{C}, \operatorname{Set.range}\left((\lambda (i: \operatorname{Fin}\left(4\right)) \mapsto (\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.creatorVec}\left(i, i\right)))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.H` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

The diagonal action in v1 §5 and v2 §6.3 comes from the span of all four traceless diagonal vectors. Their sum is zero, and the first three are independent, so H has dimension three.

**Definition 1.7 (The exterior algebra of diagonal vectors).**

$$\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.R} = \operatorname{ExteriorAlgebra}\left(\mathbb{C}, \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.H}\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.R` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

The anticommuting, square-zero diagonal creators of v1 §5 and v2 §6.3 generate the exterior algebra of H. This is the algebra over which the traceless cohomology is considered.

**Definition 1.8 (The diagonal inclusion and its action).**

$$\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.actionMap} = \operatorname{ExteriorAlgebra.map}\left(\operatorname{Submodule.subtype}\left(\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.H}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.actionMap` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

ExteriorAlgebra.map extends the inclusion H into V to a complex algebra map from R to E. The Module R E structure is actionMap.toRingHom.toModule: r acts on x by actionMap r times x. This realizes the diagonal exterior multiplication of v1 §5 and v2 §6.3.

**Definition 1.9 (The differential as right multiplication).**

$$\forall x \in \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.E},\; \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.dR}\left(x\right) = x \cdot \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.Q}$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.dR` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

Right multiplication by Q is R-linear because the diagonal action is left multiplication. The source complex in v1 §5 and v2 §6.3 uses left multiplication. Since Q has odd degree, xQ = −CliffordAlgebra.involute (Qx); the grade involution therefore identifies the kernels, and left and right multiplication have the same range. Thus this differential gives the source's cycles and boundaries.

**Definition 1.10 (The cycles of the traceless complex).**

$$\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.Cycles} = \operatorname{LinearMap.ker}\left(\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.dR}\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.Cycles` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

Cycles is the R-submodule of elements x in E satisfying xQ = 0. It is the cycle space of the traceless complex in v1 §5 and v2 §6.3.

**Definition 1.11 (Restricting the differential to cycles).**

$$\forall x \in \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.E},\; \operatorname{Subtype.val}\left(\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.dToCycle}\left(x\right)\right) = \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.dR}\left(x\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.dToCycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LinearMap.codRestrict gives the R-linear map from E to Cycles whose underlying value at x is dR x. The codomain condition holds because (xQ)Q = x(Q squared) = 0. Its range is the boundary submodule inside Cycles.

**Definition 1.12 (The traceless cohomology module).**

$$\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.B0} = \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.Cycles}/(\operatorname{LinearMap.range}\left(\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.dToCycle}\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.B0` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

The quotient of Cycles by the range of dToCycle is the traceless cohomology B_0 of v1 §5 and v2 §6.3. Its AddCommGroup B0 and Module R B0 structures are the inherited quotient structures. The R-action is the induced diagonal exterior multiplication.

**Definition 1.13 (Freeness over the diagonal exterior algebra).**

$$(\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.claim}) \Leftrightarrow (\operatorname{Module.Free}\left(\operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.R}, \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.B0}\right))$$

*Formalization.* `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.claim` (`✓ std3`).

*Citation.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

At (p,N) = (5,4), this is the freeness conjectured in v1 §5 and proposed as a sufficient explanation in v2 §6.3. Module.Free R B0 asks for freeness as an R-module without imposing a grading. A graded decomposition B_0 as the exterior algebra of H tensored with a graded complex vector space would imply this proposition.

**Theorem 1.14 (A degree-four obstruction to freeness).**

$$\neg \operatorname{D5.S3.Quantum.Fermionic.TierzTracelessFreenessRefutation.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/tierz-2026-traceless-bps-freeness-refutation` (refuted) by `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tierz-2026-traceless-bps-freeness-refutation","declaration_gid":"D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Miguel Tierz (2026). *BPS spectra of Tr[Ψ^p] matrix models for odd p*. URL: <https://arxiv.org/abs/2604.27164v2>.

*Commentary.*

Write the fifteen independent entries of A in the order a = A(0,0), b = A(1,1), c = A(2,2), d = A(0,1), e = A(0,2), f = A(0,3), g = A(1,0), h = A(1,2), i = A(1,3), j = A(2,0), k = A(2,1), l = A(2,3), m = A(3,0), n = A(3,1), o = A(3,2). Then A(3,3) = −a−b−c. Let ℓ be the exterior image of creatorVec 0 0 + creatorVec 1 1, so ℓ = a+b. Take the cubic y = −bej + cej + dhj − egk + bhk + chk − bfm − cfm + dim − elm − fgn + bin − cin − hln + fjo + iko, with each product in the displayed order, and put z = ℓy. Exterior multiplication gives Qz = 0 and ℓz = 0.

If B0 were free over R, multiplication by the nonzero diagonal vector ℓ would have kernel equal to image: contraction with a linear functional taking value one on that vector gives this exactness on the exterior algebra of H, and a basis gives it on every free R-module. Apply exactness to the degree-four class of z and lift a preimage to Cycles. Projection to exterior degree three yields a cycle x with ℓx = z, because boundaries have zero degree-four component. Exactness of multiplication by ℓ on E then gives x = y + ℓt for some t.

Let π be the exterior algebra map induced by the coordinate projection that kills c, f, h, j, l, n, o and fixes a, b, d, e, g, i, k, m. The products satisfy π(Qℓ) = 0 and π(Qy) = −20·abdegikm. The latter is nonzero because abdegikm is a basis monomial. Hence π(Qx) = π(Qy) + π(Qℓ)π(t) is nonzero, contradicting that x is a cycle. This disproves freeness even without a grading, and therefore also the graded freeness proposed in v1 §5 and v2 §6.3. The separate Hilbert-series divisibility question is not settled by this result.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.A`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.B0`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.Cycles`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.E`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.H`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.Q`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.R`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.V`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.actionMap`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.creatorVec`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.dR`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.dToCycle`
- Truth anchor: `D5/S3/Quantum/Fermionic/TierzTracelessFreenessRefutation.result`
