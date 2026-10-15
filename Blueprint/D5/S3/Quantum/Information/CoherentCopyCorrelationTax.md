# Coherent Premeasurement and Correlation Tax

## Abstract

A coherent premeasurement retains the input entropy and divides system-record mutual information into diagonal entropy and relative entropy of coherence.

**Definition 1.1 (The basis-copying isometry).**

$$\forall (n: \operatorname{Type}), [\operatorname{DecidableEq}\left(n\right)], \forall (p: n \times n), \forall (i: n), \operatorname{copyIsometry}\left(p, i\right) = \operatorname{ite}\left(p.1 = p.2, (1: \operatorname{Matrix}\left(n, n, \mathbb{C}\right))\left(p.1, i\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.copyIsometry` (`✓ std3`).

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The rectangular matrix sends basis vector i to the product basis vector (i,i).

**Theorem 1.2 (Basis copying is an isometry).**

$$\forall (n: \operatorname{Type}), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)], \operatorname{Matrix}.\operatorname{conjTranspose}\left((\operatorname{copyIsometry}: \operatorname{Matrix}\left(n \times n, n, \mathbb{C}\right))\right) \cdot (\operatorname{copyIsometry}: \operatorname{Matrix}\left(n \times n, n, \mathbb{C}\right)) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.copyIsometry_star_mul` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The adjoint of the copying matrix followed by the copying matrix is the identity on the input space.

**Definition 1.3 (Coherent matrix copying).**

$$\forall (n: \operatorname{Type}), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)], \forall (M: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), \operatorname{copyMatrix}\left(M\right) = (\operatorname{copyIsometry}: \operatorname{Matrix}\left(n \times n, n, \mathbb{C}\right)) \cdot M \cdot \operatorname{Matrix}.\operatorname{conjTranspose}\left((\operatorname{copyIsometry}: \operatorname{Matrix}\left(n \times n, n, \mathbb{C}\right))\right)$$

*Formalization.* `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.copyMatrix` (`✓ std3`).

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

Coherent copying conjugates the input matrix by the rectangular copying isometry.

**Theorem 1.4 (Entries of the copied matrix).**

$$\forall (n: \operatorname{Type}), [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)], \forall (M: \operatorname{Matrix}\left(n, n, \mathbb{C}\right)), \forall (p: n \times n), \forall (q: n \times n), \operatorname{copyMatrix}\left(M, p, q\right) = \operatorname{ite}\left(p.1 = p.2, \operatorname{ite}\left(q.1 = q.2, M\left(p.1, q.1\right), 0\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.copyMatrix_entry` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The copied matrix retains an input entry exactly between two correlated product-basis indices and is zero at every other pair.

The copying isometry sends basis vector i to the joint basis vector (i,i). The joint state is V rho V*, including the input's off-diagonal entries. Both marginals are obtained by partial trace.

**Theorem 1.5 (Coherence survives on the correlated subspace).**

$$\forall \rho, i, j, \operatorname{jointEntry}\left(\rho, i, j\right) = \operatorname{inputEntry}\left(\rho, i, j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.coherentCopyState_correlated_entry` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For every input density state and every pair of indices, the joint matrix entry at (i,i),(j,j) equals the input entry at i,j.

**Theorem 1.6 (The system marginal is the pinched input).**

$$\forall \rho, \operatorname{marginalRight}\left(\operatorname{coherentCopyState}\left(\rho\right)\right) = \operatorname{basisPinchingState}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.marginalRight_coherentCopyState` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

Tracing out the record leaves precisely the diagonal of the input.

**Theorem 1.7 (The record marginal has the Born weights).**

$$\forall \rho, \operatorname{marginalLeft}\left(\operatorname{coherentCopyState}\left(\rho\right)\right) = \operatorname{basisPinchingState}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.marginalLeft_coherentCopyState` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

Tracing out the system produces the same diagonal state: its ith diagonal entry is rho(i,i), and its off-diagonal entries vanish.

**Theorem 1.8 (Coherent copying preserves entropy).**

$$\forall \rho, \operatorname{vonNeumannEntropy}\left(\operatorname{coherentCopyState}\left(\rho\right)\right) = \operatorname{vonNeumannEntropy}\left(\rho\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.vonNeumannEntropy_coherentCopyState` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The copying map preserves multiplication, adjoints and trace. Functional calculus transports the logarithm through this map, including zero eigenvalues, so the entropy trace is unchanged.

**Theorem 1.9 (Correlation equals record entropy plus coherence tax).**

$$\forall \rho, \operatorname{quantumMutualInformation}\left(\operatorname{coherentCopyState}\left(\rho\right)\right) = \operatorname{vonNeumannEntropy}\left(\operatorname{basisPinchingState}\left(\rho\right)\right) + \operatorname{quantumRelativeEntropy}\left(\rho, \operatorname{basisPinchingState}\left(\rho\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.coherent_copy_correlation_tax` (`✓ std3`). ∎

*Citation.* T. Baumgratz, M. Cramer, M. B. Plenio (2014). *Quantifying Coherence*. URL: <https://arxiv.org/abs/1311.0275v3>.

*Commentary.*

The two marginal entropies are the diagonal entropy, and the joint entropy is the original entropy. The pinching entropy identity supplies the remaining relative entropy term.

## References

- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.coherentCopyState_correlated_entry`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.coherent_copy_correlation_tax`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.copyIsometry`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.copyIsometry_star_mul`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.copyMatrix`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.copyMatrix_entry`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.marginalLeft_coherentCopyState`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.marginalRight_coherentCopyState`
- Truth anchor: `D5/S3/Quantum/Information/CoherentCopyCorrelationTax.vonNeumannEntropy_coherentCopyState`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
