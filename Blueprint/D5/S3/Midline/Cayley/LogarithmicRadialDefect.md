# Logarithmic Radial Defect

## Abstract

The logarithmic Cayley radius detects the midline and reverses under the mirror.

**Theorem 1.1 (Logarithmic radial defect and mirror reversal).**

$$\begin{gathered}\forall Z: \operatorname{ZeroData},\\{}(\forall n, \beta(\rho_{n}) = \frac{1}{2} \log (\frac{\Vert \rho_{n}-1\Vert^{2}}{\Vert \rho_{n}\Vert^{2}})) \land\\{}(\operatorname{AllZerosOnMidline}(Z) \Leftrightarrow \forall n, \beta(\rho_{n}) = 0) \land\\{}(\forall n, \Vert c(\operatorname{mirror}(\rho_{n}))\Vert = \Vert c(\rho_{n})\Vert^{-1}) \land\\{}(\forall n, \beta(\operatorname{mirror}(\rho_{n})) = -\beta(\rho_{n})).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Midline/Cayley/LogarithmicRadialDefect.logarithmic_radial_defect_and_mirror` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Z be the canonical exhaustive, duplicate-free source-zero carrier. For a complex point rho, c(rho) is the imported Cayley coefficient (rho - 1)/rho, and beta(rho) is log |c(rho)|.

The first public conjunct rewrites beta on every indexed source zero as one half the logarithm of the squared-norm ratio. The second applies the canonical Cayley unitarity criterion to identify simultaneous vanishing with the global midline predicate.

The remaining public conjuncts state reciprocal Cayley norm and logarithmic sign reversal under the imported conjugate-reflection mirror. The open-strip fields stored in ZeroData exclude both zero and one, so the coefficient norm used in the midline argument is positive.

Pinned Mathlib supplies the logarithm-of-a-square and logarithm-of-an-inverse identities. The mirror norm calculation uses the canonical complex conjugation norm identity rather than introducing a second reflection.

## References

- Truth anchor: `D5/S3/Midline/Cayley/LogarithmicRadialDefect.logarithmic_radial_defect_and_mirror`
- Dependency: [D5/S3/Midline/Cayley/CayleyUnitarityDefect](CayleyUnitarityDefect.md)
- Dependency: [D5/S3/Weil/ReflectionLedger](../../Weil/ReflectionLedger.md)
