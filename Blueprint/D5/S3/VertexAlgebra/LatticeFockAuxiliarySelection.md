# Hermitian Auxiliary Selection on the Actual Oscillator

## Abstract

The actual substituted Fock form pairs only opposite auxiliary degrees.

D is the existing integral even symmetric LatticeData of arbitrary natural rank. Oscillator(D) is the full complex multivariate polynomial ring on Fin(rank(D)) x N. Every occupation and every polynomial support is finite; neither support has a fixed cutoff. The pairing is exactly LatticeOscillatorFockForm.fockForm and the substitution is exactly OriginalQQuartetSource.coordinateSub, whose matrix rows are generator directions. No alternate pairing, inverse matrix, positive signature, positive energy, or HPL isometry is introduced.

**Theorem 1.1 (Real longitudinal rows imply Hermitian contraction balance).**

Lean statement: `D5/S3/VertexAlgebra/LatticeFockAuxiliarySelection.frame_hermitian_aux_balance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeFockAuxiliarySelection.frame_hermitian_aux_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct xAxis and yAxis, assume only that their frame rows are fixed by complex conjugation and that gramPair(frame(y),frame(row)) is delta(row,x), while gramPair(frame(x),frame(row)) is delta(row,y). The proven balance is (w(first)+w(second))*gramPair(star(frame(first)),frame(second))=0, with the existing axisAuxDegree w. Transverse rows may be complex. Conjugation of the integral Gram contraction and symmetry supply the column equations; the bilinear frameGram_aux_balance is not substituted for this Hermitian equation. This consumed helper is bind-only, not independent new mathematical content.

**Theorem 1.2 (Actual contracted creator and coordinate derivative).**

Lean statement: `D5/S3/VertexAlgebra/LatticeFockAuxiliarySelection.substituted_creator_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeFockAuxiliarySelection.substituted_creator_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any complex frame, any generator (axis,n), and arbitrary f,g, the form of coordinateSub(X(axis,n)*f) against coordinateSub(g) equals (n+1) times the form of coordinateSub(f) against coordinateSub(coordinateDerivative(frame,star(frame(axis)),n,g)). This derivative is the existing finite sum of gramPair(star(frame(axis)),frame(row)) times pderiv(row,n). The original creation adjoint and original_derivative_coordinate_chain_rule are applied directly. Coefficients in the creator slot are conjugated. This bind-only organization helper is actually consumed by the unrestricted polynomial induction, not retained as an exact-check wrapper.

**Theorem 1.3 (Arbitrary integer homogeneous degrees and full finite supports).**

Lean statement: `D5/S3/VertexAlgebra/LatticeFockAuxiliarySelection.fockForm_auxiliary_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeFockAuxiliarySelection.fockForm_auxiliary_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the real longitudinal rows and exact dual equations above, for every pair of integers r,s and arbitrary polynomials f,g homogeneous for the actual auxiliaryWeight, r+s!=0 implies fockForm(D,coordinateSub(frame,f),coordinateSub(frame,g))=0. There is no nonnegativity restriction on r or s, no bound on occupation, and no Gram nondegeneracy or frame invertibility assumption. Rank zero is not excluded from the carrier; an instance of this longitudinal theorem still requires its explicitly quantified distinct axes.

The proof uses the existing auxDiagonal, not a duplicate auxiliary operator. Its derivative commutator and the derived Hermitian balance show that the contracted derivative has the compensating auxiliary degree. Induction through constants, sums, and multiplication by a generator establishes F(Ef,g)+F(f,Eg)=0 for all polynomials. The constant coefficient of coordinateSub(p) equals that of p, and the constant coefficient of Ep vanishes. Weighted homogeneity makes Ef=r*f and Eg=s*g. Both integers are real in the conjugate-linear slot, so (r+s)*F(f,g)=0. This all-polynomial induction is the substantive escape witness; neither finitely many states nor a presumed Wick formula establishes it.

The supplied released59040 source-design counterexample is uncompiled, not a kernel theorem. It distinguishes bilinear null duality from Hermitian balance: in rank 26 with G=diag(2,2,-2,2,...,2), use beta=e0+e2, x=(e0+i*e1)/2, y=beta, z=e1-i*e0-i*e2 and the remaining coordinate rows. The proposed bilinear null block has gramPair(x,y)=1 while gramPair(star(x),x)=1, incompatible with the claimed self-selection of the weight-one creator without a real null plane. No counterexample theorem or toy sign table is retained here, and this document claims no kernel verification for that design.

This increment proves matter auxiliary selection only. Actual two-slot tensor filtration orthogonality, original-Q HPL lift norms, Lorentzian transverse positivity, all-charge and zero-charge chart coverage, and literal original quotient descent remain separate obligations. The full moonshine, VOA, CFT, anomaly, fusion, string theory and AdS/CFT objective remains open. The source derives a native structural rule; it does not claim new general physical mathematics.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeFockAuxiliarySelection.fockForm_auxiliary_selection`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeFockAuxiliarySelection.frame_hermitian_aux_balance`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeFockAuxiliarySelection.substituted_creator_adjoint`
