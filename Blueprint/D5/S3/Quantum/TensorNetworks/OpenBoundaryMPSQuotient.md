# An inverse on actual raw prefix observations

## Abstract

A rational boundary Gram and thirteen observable quotient coordinates

The original normalized Cramer reconstruction and its canonical core are the C8 mathematics attributed to Haobo Ma and Wenlin Zhang. This unit reuses their original minorPoly, basisNumerator, leftNumerator and matrixNumerator, together with the existing complex four-entry transfer matrix. It does not introduce a second Cramer formula, a Hermitian-coordinate transfer matrix or a new selector determinant.

**Definition 1.1 (Five canonical core coordinates).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.coreCoordinates`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.coreCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Read l0, A0(0,0), A0(0,1), A1(0,0), A1(0,1) from the original reconstruction. The normalized rows l Ai=e_i and l1=1 force precisely the existing five-coordinate core shape. Original canonical_core_rigidity proves self-recovery of these coordinates.

**Definition 1.2 (The original normalized-row contraction).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryLeft`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryLeft` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The (k,w) entry is l(w0)l(w1) if w2=k and zero otherwise. On the actual coherent chart this is a left inverse of prefixMap A l 3. The proof consumes the original boundary_contraction, after identifying the canonical shape; no extra invertibility hypothesis is imposed.

**Definition 1.3 (Cleared contraction).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.leftNumeratorMap`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.leftNumeratorMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Replace l by the evaluated original leftNumerator b. Writing d=eval t minorPoly, the normalized contraction is d inverse squared times this matrix L0.

**Definition 1.4 (The existing four-complex-entry transfer numerator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.transferNumerator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.transferNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Let N_i be the original matrixNumerator evaluation. M is transferMatrix N, exactly the evaluation of numeratorTransfer in independent t and conjugate-t variables. The canonical transfer matrix is h(d)/h(v) times M, where v=eval t basisNumerator.det and h(z)=z conjugate(z).

**Definition 1.5 (Algebraic squared modulus).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.modulus`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.modulus` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The complex scalar z conjugate(z), equal on actual complex values to the real norm square embedded into the complex numbers.

**Definition 1.6 (Exact cleared boundary numerator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.gramNumerator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.gramNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For Q=Q3, t is its fixed all-zero column and B=L0 Q L0 dagger. The numerator is h(v)^m times unvec(adj(M)^m vec(B)). The exponent m is the actual complement length. The transfer inverse need not preserve positivity on arbitrary input matrices.

**Definition 1.7 (Exact scalar denominator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.gramDenominator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.gramDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The denominator is h(d)^(m+2) det(M)^m. The extra square comes from the two normalized-row boundary contractions. There is no determinant of a new selector, and det(M) is not det(A0+A1).

**Definition 1.8 (Rational observable boundary Gram).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryGram`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryGram` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Divide the displayed numerator by the displayed denominator. This is defined on arbitrary observed matrices; the theorem identifies it with the actual full-length canonical boundary Gram only on actual free-boundary MPS in the fixed recovery chart.

**Theorem 1.9 (The full-length actual boundary Gram).**

$$\forall (m: \mathbb{N}), (\forall (psi: \operatorname{Word}\left(3 + m\right) \to \mathbb{C}), (((psi \in \operatorname{openBoundaryMPS}\left(3 + m\right)) \land (\operatorname{MvPolynomial.eval}\left(\operatorname{realCoordinates}\left(\operatorname{fixedTensor}\left(\operatorname{rawPrefix}\left(3, m, psi\right)\right)\right), \operatorname{recoveryPolynomial}\left(\right)\right) \ne 0)) \to (\exists (q: \operatorname{Fin}\left(2\right) \to \mathbb{C}), ((psi = \operatorname{mpsState}\left(3 + m, \operatorname{canonicalCore}\left(\operatorname{fixedTensor}\left(\operatorname{rawPrefix}\left(3, m, psi\right)\right), 0\right), \operatorname{canonicalCore}\left(\operatorname{fixedTensor}\left(\operatorname{rawPrefix}\left(3, m, psi\right)\right), 1\right), \operatorname{reconstructedLeft}\left(\operatorname{fixedTensor}\left(\operatorname{rawPrefix}\left(3, m, psi\right)\right)\right), q\right)) \land (\operatorname{boundaryGram}\left(m, \operatorname{rawPrefix}\left(3, m, psi\right)\right) = \operatorname{vecMulVec}\left(q, \operatorname{star}\left(q\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.actual_boundary_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The observed coherent vector is produced from the actual density by observed_coherent. The original gauge_lift supplies the full-length canonical boundary q. Apply density_factor, contract on both sides with the original normalized-row left inverse, flatten the four complex entries, and iterate transferMatrix_apply. The adjugate identity and exact scalar cancellation recover q q dagger. The inverse transfer is algebraic; positivity is obtained from this actual rank-one Gram identity, rather than asserted for the inverse on arbitrary matrices.

**Definition 1.10 (Conjugation of paired polynomial variables).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.polynomialConjugate`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.polynomialConjugate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Conjugate every coefficient and swap the original and conjugate variable labels. This is the generic original conjugation operation used by both the observable quotient and native independent-trial interior polynomial recurrences.

**Theorem 1.11 (Exact conjugate-diagonal evaluation).**

$$\forall (K: Type), (\forall (p: \operatorname{PhasePolynomial}\left(K\right)), (\forall (z: \operatorname{Function}\left(K, Complex\right)), (\operatorname{actual}\left(\operatorname{polynomialConjugate}\left(p\right), z\right) = \operatorname{star}\left(\operatorname{actual}\left(p, z\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.polynomialConjugate_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every index type, polynomial and complex variable assignment, actual evaluation of polynomialConjugate is the conjugate of actual evaluation. Coefficient conjugation and the variable swap both contribute; coefficient conjugation alone would not conjugate the paired variables. The original proof is reused unchanged by the native interior polynomial adjoints.

**Definition 1.12 (A literal polynomial numerator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryGramPolynomial`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryGramPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The variables are all entries of Q and independent conjugate entries, not merely points in a parametrized image. Substitute the selected column into the original Cramer polynomials, conjugate by coefficient conjugation and swapping the paired variables, form L0 Q L0 dagger, and apply the original transfer adjugate power. The exact evaluation is gramNumerator for every complex matrix Q.

**Definition 1.13 (A literal polynomial denominator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryDenominatorPolynomial`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryDenominatorPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

In the same paired observed variables, form h(d)^(m+2) det(M)^m. Its evaluation is exactly gramDenominator on every observed matrix.

**Definition 1.14 (The rational phase quotient).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientCoordinates`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The coordinates are five complex canonical core entries, sigma=Re G00 and eta=G10/G00, thirteen real numbers in total. On actual points with G00 nonzero, sigma=normSq(q0)>0 and eta=q1/q0. The lower-left orientation is essential.

**Definition 1.15 (A positive phase representative).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.positiveBoundary`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.positiveBoundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The representative boundary is (sqrt(sigma), sqrt(sigma) eta). This realization uses a square root. It is not called rational and is separate from the rational coordinate inverse and polynomial raw observations.

**Theorem 1.16 (Exact unit-phase reconstruction).**

$$\forall (m: \mathbb{N}), (\forall (psi: \operatorname{Word}\left(3 + m\right) \to \mathbb{C}), ((((psi \in \operatorname{openBoundaryMPS}\left(3 + m\right)) \land (\operatorname{MvPolynomial.eval}\left(\operatorname{realCoordinates}\left(\operatorname{fixedTensor}\left(\operatorname{rawPrefix}\left(3, m, psi\right)\right)\right), \operatorname{recoveryPolynomial}\left(\right)\right) \ne 0)) \land (\operatorname{boundaryGram}\left(m, \operatorname{rawPrefix}\left(3, m, psi\right), 0, 0\right) \ne 0)) \to ((0 < \operatorname{sigma}\left(\operatorname{quotientCoordinates}\left(m, \operatorname{rawPrefix}\left(3, m, psi\right)\right)\right)) \land (\exists (z: \mathbb{C}), ((\operatorname{norm}\left(z\right) = 1) \land (psi = \operatorname{smul}\left(z, \operatorname{mpsState}\left(3 + m, \operatorname{core}\left(\operatorname{quotientCoordinates}\left(m, \operatorname{rawPrefix}\left(3, m, psi\right)\right), 0\right), \operatorname{core}\left(\operatorname{quotientCoordinates}\left(m, \operatorname{rawPrefix}\left(3, m, psi\right)\right), 1\right), \operatorname{left}\left(\operatorname{quotientCoordinates}\left(m, \operatorname{rawPrefix}\left(3, m, psi\right)\right)\right), \operatorname{positiveBoundary}\left(\operatorname{quotientCoordinates}\left(m, \operatorname{rawPrefix}\left(3, m, psi\right)\right)\right)\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.actual_quotient_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

First recover the actual boundary Gram. Nonzero G00 then implies q0 nonzero, sigma strictly positive, and the correctly oriented ratio eta=q1/q0. The constructed positive boundary has exactly the same Gram, and the original boundary_phase theorem gives an exact unit complex phase between the full states. Raw affine scale is retained.

**Definition 1.17 (Polynomial raw observations on the quotient).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientObservation`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientObservation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For any prefix length k and complement length m use boundary (1,eta), the original canonical core and left row, then multiply the entire raw density by the real sigma. No square root occurs in this observation map.

**Theorem 1.18 (Exact thirteen-coordinate observable retraction).**

$$\forall (m: \mathbb{N}), (\forall (p: \operatorname{Quotient}\left(\right)), (((0 < \operatorname{sigma}\left(p\right)) \land (\operatorname{MvPolynomial.eval}\left(\operatorname{realCoordinates}\left(\operatorname{fixedTensor}\left(\operatorname{quotientObservation}\left(3, m, p\right)\right)\right), \operatorname{recoveryPolynomial}\left(\right)\right) \ne 0)) \to (\operatorname{quotientCoordinates}\left(m, \operatorname{quotientObservation}\left(3, m, p\right)\right) = p)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotient_retraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For sigma>0 the observation is the actual raw density of the positive-boundary representative. Original canonical-core rigidity and the actual boundary Gram return the same core, sigma and eta. No coherent sum-tail, invertibility of A0+A1, two-site leading block or genericity condition is added to the original fixed-density recovery condition.

**Definition 1.19 (An explicit refined observed chart).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientLocusPolynomial`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientLocusPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Multiply the existing real observed recovery polynomial by the norm-square polynomial of the boundary numerator at 00. Its nonvanishing is exactly recovery plus a nonzero numerator at 00. It is a literal real polynomial on the arbitrary-entry observed matrix space.

**Theorem 1.20 (A nonzero actual witness at every length).**

$$\forall (m: \mathbb{N}), ((((\operatorname{mpsState}\left(3 + m, \operatorname{originalCore}\left(0\right), \operatorname{originalCore}\left(1\right), \operatorname{vector}\left(1, 0\right), \operatorname{vector}\left(1, 2\right)\right) \in \operatorname{openBoundaryMPS}\left(3 + m\right)) \land (\operatorname{MvPolynomial.eval}\left(\operatorname{realCoordinates}\left(\operatorname{entries}\left(\operatorname{rawPrefix}\left(3, m, \operatorname{mpsState}\left(3 + m, \operatorname{originalCore}\left(0\right), \operatorname{originalCore}\left(1\right), \operatorname{vector}\left(1, 0\right), \operatorname{vector}\left(1, 2\right)\right)\right)\right)\right), \operatorname{quotientLocusPolynomial}\left(m\right)\right) \ne 0)) \land (\operatorname{MvPolynomial.eval}\left(\operatorname{realCoordinates}\left(\operatorname{fixedTensor}\left(\operatorname{rawPrefix}\left(3, m, \operatorname{mpsState}\left(3 + m, \operatorname{originalCore}\left(0\right), \operatorname{originalCore}\left(1\right), \operatorname{vector}\left(1, 0\right), \operatorname{vector}\left(1, 2\right)\right)\right)\right)\right), \operatorname{recoveryPolynomial}\left(\right)\right) \ne 0)) \land (\operatorname{boundaryGram}\left(m, \operatorname{rawPrefix}\left(3, m, \operatorname{mpsState}\left(3 + m, \operatorname{originalCore}\left(0\right), \operatorname{originalCore}\left(1\right), \operatorname{vector}\left(1, 0\right), \operatorname{vector}\left(1, 2\right)\right)\right), 0, 0\right) \ne 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotient_locus_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Use the original matrices [[1,2],[3,4]] and [[5,6],[7,8]], left (1,0), right (1,2), for every N=3+m. The original fixed-density positivity and recovery witness supply the recovery condition. The original full-length witness_gauge identifies the canonical boundary, whose first coordinate is 5 times 2^(2+m), hence nonzero. The exact recovered Gram gives a nonzero 00 numerator without presupposing membership in the refined chart. This is an actual-image witness, with no replacement by a Zariski closure.

**Definition 1.21 (The positive-denominator numerator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.positiveGramPolynomial`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.positiveGramPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Multiply boundaryGramPolynomial by conjugate(det(M))^m. This is still a literal paired-variable polynomial.

**Definition 1.22 (A positive real denominator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.positiveGramDenominator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.positiveGramDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The denominator is normSq(d)^(m+2) normSq(det(M))^m. It is strictly positive on the original observed recovery chart. The exact corresponding numerator is the positiveGramPolynomial evaluation.

**Definition 1.23 (The thirteen real coordinates).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientRealCoordinates`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientRealCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The index is Fin 5 plus Fin 5 plus Fin 3: five real core parts, five imaginary core parts, sigma, real eta, imaginary eta.

**Definition 1.24 (Real polynomial coordinate numerators).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientRealNumerator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientRealNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Each complex quotient p/q is multiplied by conjugate(q). Convert the paired-variable polynomial to Cartesian variables using the existing coordinate equivalence, then take coefficientwise real or imaginary parts. These are additive coefficient maps, not ring homomorphisms.

**Definition 1.25 (Real polynomial coordinate denominators).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientRealDenominator`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientRealDenominator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Use the existing sum-of-squares normPolynomial of q. Every denominator is strictly positive on the refined chart. The construction gives actual ratios of real polynomials, not a smoothness or analyticity substitute.

**Definition 1.26 (Real polynomial raw observation entries).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientObservationPolynomial`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientObservationPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Substitute the canonical core and boundary (1,eta) into the original twelve-complex-parameter amplitude polynomials. Multiply the amplitude/conjugate-amplitude complement sum by sigma, then take coefficientwise real or imaginary parts. The universal evaluation identity holds for every real quotient parameter, every prefix and complement length, and either component; no square root or positivity condition is used in this polynomial identity.

**Theorem 1.27 (Rationality with exact real polynomial expressions).**

$$\forall (m: \mathbb{N}), (\forall (Q: \operatorname{Matrix}\left(\operatorname{Word}\left(3\right), \operatorname{Word}\left(3\right), \mathbb{C}\right)), ((\operatorname{MvPolynomial.eval}\left(\operatorname{realCoordinates}\left(\operatorname{entries}\left(Q\right)\right), \operatorname{quotientLocusPolynomial}\left(m\right)\right) \ne 0) \to ((((((\operatorname{Fintype.card}\left(\operatorname{QuotientRealIndex}\left(\right)\right) = 13) \land (\forall (i: \operatorname{QuotientRealIndex}\left(\right)), ((0 < \operatorname{MvPolynomial.eval}\left(\operatorname{realCoordinates}\left(\operatorname{entries}\left(Q\right)\right), \operatorname{quotientRealDenominator}\left(m, i\right)\right)) \land (\frac{\operatorname{MvPolynomial.eval}\left(\operatorname{realCoordinates}\left(\operatorname{entries}\left(Q\right)\right), \operatorname{quotientRealNumerator}\left(m, i\right)\right)}{\operatorname{MvPolynomial.eval}\left(\operatorname{realCoordinates}\left(\operatorname{entries}\left(Q\right)\right), \operatorname{quotientRealDenominator}\left(m, i\right)\right)} = \operatorname{quotientRealCoordinates}\left(\operatorname{quotientCoordinates}\left(m, Q\right), i\right))))) \land (0 < \operatorname{positiveGramDenominator}\left(m, Q\right))) \land (\forall (i: \operatorname{Fin}\left(2\right)), (\forall (j: \operatorname{Fin}\left(2\right)), (\operatorname{boundaryGram}\left(m, Q, i, j\right) = \frac{\operatorname{PhasePolynomial.actual}\left(\operatorname{positiveGramPolynomial}\left(m, i, j\right), \operatorname{entries}\left(Q\right)\right)}{\operatorname{Complex.ofReal}\left(\operatorname{positiveGramDenominator}\left(m, Q\right)\right)})))) \land (\forall (k: \mathbb{N}), (\forall (a: \mathbb{N}), (\forall (u: \operatorname{Word}\left(k\right)), (\forall (v: \operatorname{Word}\left(k\right)), (\forall (imaginary: \operatorname{Bool}\left(\right)), (\forall (p: \operatorname{Quotient}\left(\right)), (\operatorname{MvPolynomial.eval}\left(\operatorname{quotientRealCoordinates}\left(p\right), \operatorname{quotientObservationPolynomial}\left(k, a, u, v, imaginary\right)\right) = \operatorname{component}\left(imaginary, \operatorname{quotientObservation}\left(k, a, p, u, v\right)\right))))))))) \land (\operatorname{boundaryGram}\left(m, Q, 0, 0\right) \ne 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.rational_quotient_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

There are exactly thirteen real indices. For every index the named real polynomial denominator is positive on the refined observed chart and the ratio of the named real polynomial numerator and denominator is exactly the corresponding quotient coordinate. The theorem also gives the full Gram with its positive real denominator and exact polynomial numerator, the universal polynomial evaluation identity for every raw quotient observation entry, and the nonzero 00 Gram entry required by the actual-state representative theorem. The statement holds on arbitrary observed matrices satisfying this explicit polynomial condition; its interpretation as a rank-one physical boundary Gram additionally uses actual_boundary_gram.

The interior-genericity consumer uses canonical_shape in place, with its original telescope and proof, to align the actual quotient core with canonicalCore before transferring injectivity. Its public helper audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/30422. This is a rational inverse unit for the prefix N=3+m, including every original N at least four. It does not prove generic-point Q2 ambiguity on a dense intrinsic actual-image locus, compose the later maximal-rank and C1 fiber argument, or settle Conjecture 9. No solved-open-problem increment, interior-window theorem, normalized-state statement, dynamics, time group, energy, physical clock, physical recovery operation, stability, sample complexity or thermodynamic cost is asserted.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.actual_boundary_gram`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.actual_quotient_representative`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryDenominatorPolynomial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryGram`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryGramPolynomial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.boundaryLeft`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.coreCoordinates`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.gramDenominator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.gramNumerator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.leftNumeratorMap`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.modulus`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.polynomialConjugate`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.polynomialConjugate_eval`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.positiveBoundary`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.positiveGramDenominator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.positiveGramPolynomial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientCoordinates`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientLocusPolynomial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientObservation`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientObservationPolynomial`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientRealCoordinates`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientRealDenominator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotientRealNumerator`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotient_locus_witness`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.quotient_retraction`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.rational_quotient_inverse`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient.transferNumerator`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityGenericity](OpenBoundaryMPSDensityGenericity.md)
