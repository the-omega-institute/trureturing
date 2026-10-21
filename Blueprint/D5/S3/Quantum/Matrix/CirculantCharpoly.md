# Circulants and odd cosine pairing

## Abstract

Fourier modes factor circulant characteristic polynomials.

**Theorem 1.1 (Complex circulant factorization).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.circulant_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CirculantCharpoly.circulant_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

The characteristic polynomial of a complex circulant is the product of X minus its discrete Fourier values. This theorem is existing repository content reused from the Roldan circulant energy development.

**Theorem 1.2 (Reality of even Fourier values).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.dft_real_of_even`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CirculantCharpoly.dft_real_of_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

The discrete Fourier value of an even real function is real. This theorem is existing repository content reused from the Roldan circulant energy development.

**Theorem 1.3 (Real circulant factorization).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.real_circulant_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CirculantCharpoly.real_circulant_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

An even real circulant has the product of X minus the real parts of its Fourier values. This theorem is existing repository content reused from the Roldan circulant energy development.

**Definition 1.4 (Real residue entries).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant`

*Formalization.* `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

For order 2m+1, the circulant entry is f at the least nonnegative residue.

**Definition 1.5 (Cosine mode values).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.cosineValue`

*Formalization.* `D5/S3/Quantum/Matrix/CirculantCharpoly.cosineValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

The real mode is f(0) plus twice the cosine sum from one through m.

**Theorem 1.6 (Odd paired factorization).**

Lean statement: `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

For an even generating function, the odd real characteristic polynomial has one constant factor and squared factors for modes one through m. Pairing opposite residues gives the cosine formula and pairing opposite modes gives the squares. This odd pairing factorization is proved here.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.circulant_charpoly`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.cosineValue`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.dft_real_of_even`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.realCirculant_charpoly`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantCharpoly.real_circulant_charpoly`
- Dependency: [D5/S3/Quantum/Dynamics/PolygonalFourierCouplings](../Dynamics/PolygonalFourierCouplings.md)
