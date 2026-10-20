# Circulants and paired real cosine modes

## Abstract

Fourier modes factor the characteristic polynomial of a circulant matrix.

**Definition 1.1 (A positive primitive root).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.root`

*Formalization.* `D5/S3/Quantum/Matrix/CirculantCharpoly.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive n, the complex exponential exp(2 pi i/n) is primitive and fixes the positive orientation of the modes.

**Definition 1.2 (Complex mode values).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.fourierValue`

*Formalization.* `D5/S3/Quantum/Matrix/CirculantCharpoly.fourierValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value at mode j is the sum of v(k) times the primitive root to the natural power j k.

**Definition 1.3 (Fourier vectors).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.fourierVector`

*Formalization.* `D5/S3/Quantum/Matrix/CirculantCharpoly.fourierVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vector at mode j has coordinate exp(-2 pi i j k/n). Mathlib defines a circulant entry by v(a-b), so this negative vector exponent corresponds to a positive eigenvalue exponent.

**Definition 1.4 (An invertible Fourier basis).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.fourierBasis`

*Formalization.* `D5/S3/Quantum/Matrix/CirculantCharpoly.fourierBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport the coordinate basis through the invertible discrete Fourier transform, then identify the finite residue indices with Fin n. No primality assumption on n is needed.

**Theorem 1.5 (The Fourier eigenvector equation).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.circulant_mulVec_fourier`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CirculantCharpoly.circulant_mulVec_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplication of a circulant by a Fourier vector gives that vector multiplied by its positive-exponent Fourier value. Reflecting the generating vector in the discrete Fourier diagonalization proves the equation.

**Theorem 1.6 (The complex characteristic polynomial).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.circulant_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CirculantCharpoly.circulant_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive order n and arbitrary complex generating vector v, the characteristic polynomial is the product over all Fourier modes of X minus the mode value. The invertible discrete Fourier transform supplies a basis of Fourier vectors. The eigenvector equations give a diagonal matrix in that basis, so the product includes all algebraic multiplicities.

**Definition 1.7 (Real residue entries).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant`

*Formalization.* `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For order 2m+1 and f on the natural numbers, the entry at a,b is f evaluated at the least nonnegative residue of a-b. Values of f outside this residue range are irrelevant.

**Definition 1.8 (Real cosine mode values).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.cosineValue`

*Formalization.* `D5/S3/Quantum/Matrix/CirculantCharpoly.cosineValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real mode indexed by j is f(0) plus twice the sum from l=1 to m of f(l) cos(2 pi j l/(2m+1)).

**Theorem 1.9 (One constant factor and squared cosine factors).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume f(2m+1-k)=f(k) for each k from 1 to 2m. The characteristic polynomial equals the constant-mode linear factor times the product of the squared linear factors of modes 1 through m. Pairing a residue with its negative gives the cosine formula, and pairing opposite mode indices gives the squares. Injectivity of real-to-complex polynomial mapping transfers the complex identity to real coefficients. The statement includes m=0 and allows coincident mode values.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.circulant_charpoly`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.circulant_mulVec_fourier`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.cosineValue`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.fourierBasis`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.fourierValue`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.fourierVector`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant_charpoly`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.root`
- Dependency: [D5/S3/Quantum/Dynamics/PolygonalFourierCouplings](../Dynamics/PolygonalFourierCouplings.md)
