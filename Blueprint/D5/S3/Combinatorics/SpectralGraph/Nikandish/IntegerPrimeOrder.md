# Exact prime orders for signed integer arithmetic

## Abstract

Exact prime orders for signed integer arithmetic

Source: supplied PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02; the exact original source names and attribution are retained in the Lean module. All source parameter domains, prerequisites and failed-method boundaries remain binding. Necessary tests do not imply integrality, and general four-prime/higher-prime Q3 and academic approval/publication boundaries remain open.

**Theorem 1.1 (Exact divisibility order equals the valuation).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder.valuation_of_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder.valuation_of_exact` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The exact-order predicate handles arbitrary signed integers and is connected to padicValInt, rather than being an answer-encoding premise.

**Theorem 1.2 (Constructed integer unit after exact prime scaling).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder.unit_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder.unit_decomposition` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

A quotient witness and nondivisibility are both produced from the original exact order.

**Theorem 1.3 (Two orders coincide under a strictly higher remainder).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder.equal_of_high_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder.equal_of_high_remainder` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

This general integer lemma is consumed by the full shared-prime root proof, with all exponent comparisons established there.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder.equal_of_high_remainder`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder.unit_decomposition`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/Nikandish/IntegerPrimeOrder.valuation_of_exact`
