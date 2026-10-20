# Negative Current Residues

## Abstract

Complete ordered negative-current residue convolution on arbitrary actual native fields.

Let D be LatticeData, hu:IsUnit D.G.det, F any NativeField(D,hu), i a current colour and gamma an integer. All operators act on the original ActualTensor(D,hu). Write A(q)=tensorCurrent(D,ActualGround(D,hu),i,q) and B(t)=F.coeff(-2*t-gamma-2). Define R(r,t,x) as the finsum over natural l of (-1)^l choose(r,l) A(r-l)(B(t+l)x), minus (-1)^r times the finsum of (-1)^l choose(r,l) B(r+t-l)(A(l)x). The outer signed power uses the integer exponent r. Both orderings are retained at every actual input x.

**Theorem 1.1 (The first ordered residue has finite support at each input).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.current_residue_left_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.current_residue_left_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For arbitrary integer r,t,gamma and actual x, the first natural-index summand has finite support. The coefficient exponent -2*(t+l)-gamma-2 eventually falls below the Hahn order of F(x). Its vanishing occurs before the current acts. No uniform finite support in the endomorphism space is asserted.

**Theorem 1.2 (The reverse ordered residue has finite support at each input).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.current_residue_right_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.current_residue_right_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The actual tensor-current truncation at x kills A(l)x for sufficiently large natural l. Applying the seed coefficient afterwards preserves zero. This proves the second ordered support independently of the first and without an assumed residue or module law.

For r=-h-1, the first ordering reindexes by q=-h-1-l. The missing negative modes -h-1<q<0 have choose(-q-1,h)=0. The reverse ordering reindexes by q=l, and the signed outer residue power combines with choose(-q-1,h) exactly. Both branches have B(t-h-1-q), acting after the current for q>=0 and before the current for q<0. The resulting common integer-mode kernel has finite support: the seed order bounds the negative branch and actual current truncation bounds the nonnegative branch.

**Theorem 1.3 (The actual singleton coefficient equals the complete finite negative convolution).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.singleton_negative_current_residue`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.singleton_negative_current_residue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every D,hu,index,F,gamma,k,x, put m=sourceWeight(D,index)=index.2+1. Then (singletonLinear(D,hu,index)F).coeff(-2*k-gamma-3)x is the sum for 0<=j<m of halfBinomial(j) times R(-m+j,k-j,x), with i=index.1. All these residues reindex to the same actual kernel B(k-m-q). Finite Vandermonde gives sum_j choose(-1/2,j) choose(-q-1,m-1-j)=choose(-q-3/2,m-1), exactly jetScalar(index.2,q). The public wordField_coefficient and flatTerm_finite identify this with the original singleton normal coefficient. The exponent is exactly -2*(k-m-q)-gamma-2, including m=1.

This is a repository-derived coefficient calculation in the classical twisted-lattice setting, with background in Bakalov and Kac, Twisted Modules over Lattice Vertex Algebras, math/0402315. It supplies the negative outer part of the current iterate. The complete all-cutoff iterate, positive correction, arbitrary-state twisted Jacobi identity, and the Moonshine, VOA, CFT, anomaly, fusion, string and AdS/CFT programme require further results.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.current_residue_left_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.current_residue_right_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockNegativeCurrentResidue.singleton_negative_current_residue`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFiniteCorrection](LatticeHalfFockFiniteCorrection.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockFockNormalField](LatticeHalfFockFockNormalField.md)
