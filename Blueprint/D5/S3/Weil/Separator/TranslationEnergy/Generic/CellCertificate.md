# Generic rational cell construction

## Abstract

Generic rational cell construction.

**Theorem 1.1 (Acceptance and shrinking width).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Generic/CellCertificate.cell_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Generic/CellCertificate.cell_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural R, rational shift s, mesh depth d, scalar precision m, actual canonical cell [a,b] and two finite rational coefficient lists, the constructed unrounded payload passes the canonical cell checker. Empty lists are normalized to [0]; nonempty lists are preserved. The singleton-base Horner parser returns exactly the evenized normalized lists.

With B=2R+|s|+1, let Ap,Aq be the Horner amplitude budgets and Dp,Dq their slope budgets. The norm-square width is at most Cl(b-a)+Ce*2^-m, where Cl=4Ap(18Ap/R+2Dp)+4Aq(18Aq/R+2Dq) and Ce=16(Ap^2+Aq^2).

The two real component products use all four signed endpoint corners. Opposite endpoints enclose each translation difference, and the sign-safe square intervals are summed to form the exact norm-square payload.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Generic/CellCertificate.cell_certificate`
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/CutoffIntervals](../CutoffIntervals.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Integral](../Integral.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/Polynomial/HornerIntervals](../Polynomial/HornerIntervals.md)
- Dependency: [D5/S3/Weil/Separator/TranslationEnergy/SignedSquares](../SignedSquares.md)
