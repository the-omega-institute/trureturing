# Original Source Pairing: Reflection, Energy and Currents

## Abstract

Reflection, exact energy support and signed integer-current transposes for the original complex bilinear source form.

D is an arbitrary LatticeGeneratingFieldLocality.LatticeData, with natural rank, symmetric integral Gram matrix G and even diagonal. Rank zero, degenerate matrices and indefinite matrices are included. Oscillator(D) is exactly MvPolynomial (Fin D.rank x Nat) Complex, and Carrier(D) is exactly Charge(D) ->_0 Oscillator(D), with Charge(D)=Fin D.rank -> Int. B denotes OriginalSourcePairing.sourcePairing D, the complex bilinear opposite-charge sum of integerWick. No determinant-unit or positive-definiteness premise occurs in the three laws below.

The reflection is the existing LatticeInvolution.theta D: it sends single(a,p) to single(-a,sigma(p)), where sigma negates every oscillator variable and fixes complex coefficients. The creation and lowering transposes of integerWick and the actual anticommutation of sigma with Gram-weighted differentiation prove invariance on arbitrary oscillator polynomials. Finite-support induction lifts it to every pair of Carrier states.

The current is the existing LatticeFiniteNegativeGeneration.neutralMode D i m. For m<0 it multiplies by X(i,-m-1); for m>0 it is m times the actual Gram-weighted partial derivative at mode m-1. For m=0 it multiplies the charge-a sector by bilinear D (unitCharge D i) a. Opposite charges give opposite zero-mode scalars. The integerWick bridges therefore give the transpose for every signed integer mode, including zero.

The grades are the full existing LatticePositiveEnergy.grade D h, defined by exact coefficient support at E(a,d)=bilinear D a a/2 + sum_x (x.2+1)*d(x), with E valued in Int. Same-mode Gram substitution preserves this oscillator weight. The factorial form pairs equal monomial exponents, while B pairs opposite charges, whose quadratic energies agree. Distinct basis energies are orthogonal; linear-span induction extends the conclusion to the entire grades, including infinite-dimensional or negative grades.

substitution_monomial_weight is available at this original owner for direct reuse by OriginalSourceCoevaluation. Its unchanged proof applies to every same-mode complex matrix family and every monomial coefficient: the substituted monomial has integer weighted degree Finsupp.weight (fun x => x.2+1) alpha. The concrete inverse Gram substitution consumes this result to prove support before forming its finite fixed-grade representative.

**Theorem 1.1 (Reflection isometry).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws.sourcePairing_theta`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws.sourcePairing_theta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and u,v:Carrier(D), B(theta(D)(u),theta(D)(v))=B(u,v). The reflection is the literal existing linear equivalence on Carrier(D).

**Theorem 1.2 (All signed integer-current transposes).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws.sourcePairing_neutralMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws.sourcePairing_neutralMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, i:Fin D.rank, m:Int and u,v:Carrier(D), B(neutralMode(D,i,m)(u),v)=-B(u,neutralMode(D,i,-m)(v)). The minus sign is bilinear and carries no complex conjugation.

**Theorem 1.3 (Orthogonality of full energy grades).**

Lean statement: `D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws.sourcePairing_grade`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws.sourcePairing_grade` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, h,k:Int with h!=k and all u,v:Carrier(D), u in grade(D,h) and v in grade(D,k) imply B(u,v)=0. No finite-basis selection, finite-dimensionality or Gram inverse is assumed.

These are algebraic consequences of the same-ring Wick construction and existing coefficient and current APIs, without a novelty claim. Mathlib finite-support, weighted-homogeneous and linear-span machinery retains its Apache-2.0 license and original authorship. The charged-primary transpose, complete wordField BPZ, fixed-grade perfection, mixed Jacobi, crossing, fusion, anomaly, string theory and AdS/CFT require further results.

## References

- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws.sourcePairing_grade`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws.sourcePairing_neutralMode`
- Truth anchor: `D5/S3/VertexAlgebra/SourceBPZ/SourcePairingLaws.sourcePairing_theta`
- Dependency: [D5/S3/VertexAlgebra/LatticeEnergyGrading](../LatticeEnergyGrading.md)
- Dependency: [D5/S3/VertexAlgebra/SourceBPZ/OriginalSourcePairing](OriginalSourcePairing.md)
