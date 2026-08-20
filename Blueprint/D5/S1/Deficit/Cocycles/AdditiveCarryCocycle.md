# Additive Section Carry

## Abstract

A section of an additive quotient produces an associative carry defect.

**Theorem 1.1 (An additive section carry satisfies the cocycle identity).**

$$\kappa_{s}(a,b) + \kappa_{s}(a+b,c) =\\\kappa_{s}(b,c) + \kappa_{s}(a,b+c).$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Cocycles/AdditiveCarryCocycle.section_carry_cocycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be an additive quotient map and let s be a set-theoretic right-inverse section. The carry is constructed as s(a)+s(b)-s(a+b), and the section law places it in the kernel of q.

For all quotient values a, b, and c, the sum of the carries for (a,b) and (a+b,c) equals the sum for (b,c) and (a,b+c). The proof expands the four carries, rewrites by associativity, and cancels the section values.

## References

- Truth anchor: `D5/S1/Deficit/Cocycles/AdditiveCarryCocycle.section_carry_cocycle`
