# An executable full certificate at arbitrary accuracy

## Abstract

An executable full certificate at arbitrary accuracy.

**Theorem 1.1 (All rational polynomials and signed shifts).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural radius R, rational shift s and positive rational requested width eta, every pair of finite rational coefficient lists produces a successful full Boolean certificate. The produced rational bounds enclose the genuine full Lebesgue translation energy of literalRationalTest and have width strictly less than eta.

The theorem also quantifies over every pair of rational polynomials p and q: finite lists representing them exist, and the same executable list producer satisfies the complete certificate statement for p and q. The polynomial representation theorem is used only in the proof; it is not an opaque decision in the list algorithm.

The executable depth rule is Nat.log 2 (Nat.ceil (2C/eta))+1. The requested binary precision is computed from eta. Separate logarithmic depth budgets bound the mesh contribution Cl L^2/2^d and scalar contribution Ce L/2^m by strict half-widths. Structural all-cell acceptance, exact index alignment and the hull mass bounds prove full checker success without assuming it.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate`
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Generic/CellCertificate](CellCertificate.md)
