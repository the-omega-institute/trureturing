# Finite Current Correction

## Abstract

Actual current insertion with every original-source finite correction triangle.

Let D be arbitrary LatticeData, hu:IsUnit D.G.det, index:Index(D), b:Carrier(D), gamma,k integers and x:ActualTensor(D,hu). The ordinary source carrier and actual tensor carrier are distinct. Put m=sourceWeight(D,index)=index.2+1>0 and N=vectorFrequencyBound(D,b)+1. Choose any natural L with N<=L. There is no positivity, eigenstate, homogeneity, single-charge, locality, module-law or Jacobi assumption.

**Theorem 1.1 (Every original-source cutoff gives the same actual insertion coefficient).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCurrentCorrection.correctedField_negative_current_insertion_finite_triangle`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCurrentCorrection.correctedField_negative_current_insertion_finite_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The coefficient of correctedField(D,hu,neutralMode(D,index.1,-m,b)) at -2*k-gamma-3, applied to x, equals the sum for 0<=j<m of halfBinomial(j) times currentResidue(D,hu,index.1,correctedField(D,hu,b),gamma,-m+j,k-j,x), plus the sum for 0<=s<L of halfBinomial(m+s) times the sum for 0<=n<L of: choose(1/2,n-s) times the coefficient of correctedField(D,hu,neutralMode(D,index.1,n,b)) at -2*(k-m-n)-gamma-3, applied to x, when s<=n; zero when s>n. Every natural-to-integer cast is explicit in the Lean statement. The branch s<=n is essential; truncated natural subtraction alone does not express the triangle.

For n>=N, neutralMode_vanish kills the positive source mode on the original b. Linearity of correctedField and its coefficient then gives zero at the actual x. This extends the whole-field insertion correction from range(N) to range(L), without measuring a transformed source or the target input. Finite sum exchange restricts s to range(n+1), since n<L. The consumed halfBinomial_positive_convolution yields m halfBinomial(m) halfBinomial(n)/(m+n); its positive-m premise is discharged from sourceWeight=index.2+1. The terminal n=0 and s=0 contributions are retained.

Evaluate the whole-field correctedField_negative_current_insertion on coefficient -2*k-gamma-3 and the arbitrary actual tensor x. The public shiftField_coefficient_public transports the shift m+n to -2*(k-m-n)-gamma-3. The complete accepted singleton_negative_current_residue supplies the entire negative convolution, including j=0 and both ordered residues with all signed gamma,k. Only finite sums are exchanged here; no unproved infinite Fubini or uniform endomorphism support is used.

This repository-derived consequence uses the existing lattice twisted-field constructions, with background in Bakalov and Kac, Twisted Modules over Lattice Vertex Algebras, math/0402315. It does not identify the positive source triangle with actual positive-current residues. That identification, the full actual residue source-product law, twisted Jacobi, and the Moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT programme remain further obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockFiniteCurrentCorrection.correctedField_negative_current_insertion_finite_triangle`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue](LatticeHalfFockNegativeCurrentResidue.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](LatticeHalfFockOriginalTranslation.md)
