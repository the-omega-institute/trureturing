# Native Relative Ghost Pairing

## Abstract

The native kernel of b(0) is isotropic for BPZ, while the genuine c(0)-insertion form has zero left and right radicals. Its integer selection is two; its conjugate-left restriction to actual ghost degree one is Hermitian.

The only carrier is GhostFock = (Finset Nat) →₀ Complex, with arbitrary finite coefficient support over the infinite exterior mode set. Relative is literally LinearMap.ker(b(0)). The bilinear map relativeForm(x,y) is BPZ(x,c(0)y), using the native ordered-word variable-phase BPZ and the actual primitive CAR. The insertion c(0) is not an endomorphism of Relative: for x in Relative, b(0)c(0)x=x. In vertex current indices b(0)=currentMode(b,1) and c(0)=currentMode(c,-2). No matter tensor state or original full-state B0 is identified with these ghost operators.

**Theorem 1.1 (Why the insertion is necessary).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostRelativeForm.relative_isotropic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostRelativeForm.relative_isotropic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every first and second in the actual Relative submodule, BPZ(first,second)=0. CAR gives first=b(0)c(0)first. The native b-transpose law then pairs Pi(c(0)first) with b(0)second=0. Pi remains the native mixed-state parity operator throughout; no scalar parity is assigned to a superposition. Restricting BPZ without insertion therefore gives the zero form, not the desired nondegenerate relative form.

**Theorem 1.2 (Both actual relative radicals vanish).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeForm_radicals`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeForm_radicals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

LinearMap.ker(relativeForm)=bottom and LinearMap.ker(relativeForm.flip)=bottom. Unrestricted BPZ nondegeneracy is first proved from BPZ_basis, eps_nonzero and chi_involutive, not assumed as a form field. Every ambient state z splits as b(0)c(0)z+c(0)b(0)z. The first summand is relative by b(0)^2=0, and isotropy and the insertion tests annihilate the two summands for a left radical vector. For the right radical, the same decomposition and the native c-transpose law, together with c(0)^2=0, show c(0)x=0; CAR reconstructs x=0. Both arguments apply to mixed integer degrees without a positivity or symmetry premise.

**Theorem 1.3 (Selection at total ghost degree two).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeForm_degree_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeForm_degree_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all leftGrade,rightGrade in Int and first,second in Relative, native HomogeneousDegree(leftGrade,first) and HomogeneousDegree(rightGrade,second), together with leftGrade+rightGrade not equal to 2, imply relativeForm(first,second)=0. The number operator J is diagonal with the actual degree of each occupation set. Its existing J_c_commutator gives c(0) a degree increase of one. The native BPZ selection leftGrade+(rightGrade+1)=3 then gives the stated criterion. Conformal energy is not used or substituted for ghost number.

**Theorem 1.4 (Nondegeneracy inside the true degree-one intersection).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeOneForm_radicals`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeOneForm_radicals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RelativeDegreeOne is the literal intersection of Relative with Finsupp.supported Complex Complex {S | degree(S)=1}; membership is the same actual support condition as HomogeneousDegree(1,x). Both kernels of the restricted relativeOneForm and its flip are bottom. The native annihilate_coeff law characterizes Relative by vanishing coefficients on all occupation sets containing site 3. The actual degree-one coefficient projection therefore stays in Relative. Linear induction over arbitrary finite-support coefficients reduces preservation of a test value to a basis occupation. Occupations containing site 3 are killed by c(0); other occupations are relative, and the degree-two selection law kills every degree other than one. Projecting any relative test state to degree one preserves that test value. This supplies genuine homogeneous tests, rather than assuming restricted nondegeneracy. The conjugate-left Hermitian law then turns a right radical vector into a left radical vector after actual coefficient conjugation, whose injectivity forces the original vector to vanish.

**Theorem 1.5 (Conjugate-left Hermitian degree-one form).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeHermitianForm_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeHermitianForm_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every first,second in RelativeDegreeOne, relativeHermitianForm(first,second)=star(relativeHermitianForm(second,first)). The form is a starRingEnd(Complex)-semilinear map in its left argument and an ordinary Complex-linear map in its right argument, with value Hghost(first,c(0)second)=BPZ(conjCoeffs(first),c(0)second). Native create_coeff and annihilate_coeff, with their real signs, prove conjugation commutes with the actual b(0) and c(0) before it is restricted. Conjugation preserves actual integer degree. The degree-one parity proof yields Pi(conjCoeffs(second))=-conjCoeffs(second); this cancels the native negative c-transpose phase. The previously proved unrestricted Hghost_hermitian supplies the conjugation step, so no duplicate conjugation or symmetry theorem is needed.

Classical context: Belavin, Polyakov and Zamolodchikov, Infinite conformal symmetry in two-dimensional quantum field theory (1984); Kato and Ogawa, Covariant quantization of string based on BRS invariance (1983); Frenkel, Garland and Zuckerman, Semi-infinite cohomology and string theory (1986). These references provide provenance for BPZ and relative ghost conventions, not substitute proofs or a novelty claim. The present results are standard ghost algebra derived on the specified native carrier.

There is no cutoff, quotient, assumed nondegenerate form, no-ghost or positive-signature premise. Full mixed-degree relativeForm is not asserted symmetric or positive. No total-Q adjoint, Q-boundary descent, quotient well-definedness, matter-coordinate phase, transverse isometry, unitarity, physical realization, Monster construction, full string theory or AdS/CFT completion follows. Original-Q quotient descent and the full original mathematical objective remain open; ghost stress and matter stress laws are not used here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeForm_degree_selection`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeForm_radicals`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeHermitianForm_hermitian`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostRelativeForm.relativeOneForm_radicals`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostRelativeForm.relative_isotropic`
- Dependency: [D5/S3/VertexAlgebra/BcGhostBpZForm](BcGhostBpZForm.md)
