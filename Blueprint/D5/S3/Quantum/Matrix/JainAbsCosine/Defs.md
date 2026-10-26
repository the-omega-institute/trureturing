# Odd order absolute cosine powers

## Abstract

Absolute cosine matrix powers and their Fourier modes. The matrix and conjecture are those of Jain.

**Definition 1.1 (Angular step).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.angle`

*Formalization.* `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.angle` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

For order 2m+1 the angular step is pi divided by 2m+1.

**Definition 1.2 (Entrywise real powers).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.absCosPow`

*Formalization.* `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.absCosPow` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

The matrix entry at a,b is the real power r of the absolute value of cos((a-b) pi/(2m+1)).

**Definition 1.3 (Real Fourier mode).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.modeValue`

*Formalization.* `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.modeValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

The j-th mode is one plus twice the sum over l from one to m of cos(2jl pi/(2m+1)) times cos(l pi/(2m+1)) to the real power r.

**Definition 1.4 (Even root product).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.rootProduct`

*Formalization.* `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.rootProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

The product over s less than j of r-2s records the proposed roots and their signs.

**Definition 1.5 (Nonzero eigenvalue multiplicity).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.claim`

*Formalization.* `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Tanvi Jain (2017). *Hadamard powers of some positive matrices*. DOI: [10.1016/j.laa.2016.06.030](https://doi.org/10.1016/j.laa.2016.06.030). URL: <https://doi.org/10.1016/j.laa.2016.06.030>.

*Commentary.*

For m at least one and nonnegative r, every nonzero root of the characteristic polynomial other than mode zero has root multiplicity exactly two.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.absCosPow`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.angle`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.modeValue`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/Defs.rootProduct`
