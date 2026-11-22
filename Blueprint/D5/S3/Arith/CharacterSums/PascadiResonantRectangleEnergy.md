# Complete dual energy on a literal resonant rectangle

## Abstract

The complete normalized dual energy on a literal resonant rectangle is bounded by nine times the prime times the square of its side bound.

**Definition 1.1 (The full prime-square frequency average).**

$$\operatorname{E}\left(R, c\right)=\frac{\sum_{f\in \operatorname{DualFrequency}\left(q\right)} \lvert\sum_{u\in \operatorname{S}\left(R\right)} \operatorname{c}\left(u\right) \operatorname{K}\left(u, f\right)\rvert^2}{q^4}$$

*Formalization.* `D5/S3/Arith/CharacterSums/PascadiResonantRectangleEnergy.normalizedRectangleEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let p be prime, q = p², and fix the literal integer pivot set in R. A pivot (a,b) maps to u = ((rho a + sigma b)/p, (s a − r b)/p) reduced modulo q. The equation r rho + s sigma = p and the literal resonance make the divisions exact. S(R) is the resulting reduced pivot set.

K is the full dual character kernel with the common mask chi. Its fibre consists of all points (x,y) for which a, b, x, y, h−x−y, x+y, h−x and h−y are units modulo q and g a b x y (h−x−y) = h modulo q. The complete sum runs over two independent two-coordinate frequencies, so its denominator is q⁴.

**Theorem 1.2 (A uniform complete-energy bound).**

$$\forall R, c, \operatorname{CoefficientBound}\left(R, c\right) \implies \operatorname{E}\left(R, c\right)\le9 p A^2$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiResonantRectangleEnergy.complete_resonant_rectangle_energy_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

R fixes a prime p > 3, an integer p ≤ A < p², a primitive pair (r,s), and integers rho and sigma with r rho + s sigma = p. The literal pivots have unit coordinates and lie in the closed rectangle [L,L+A] × [M,M+A]; each satisfies p divides s a − r b. The parameters g,h are modulo q and g is a unit. Both the common mask and the tested coefficients have modulus at most one at each retained pivot.

Reduction is injective on these literal coordinates. At most two lower roots occur for each first coordinate. A smooth lower root allows at most p lifts, because the free upper digit determines the other, and the only possible singular lower root has at most p² lifts. Thus each fibre has at most 3p² points. The resonant box contains at most 3A²/p distinct pivots, including both endpoints. The exact complete energy identity now gives the bound.

The result is about the complete frequency sum, not a weighted RMS or a normalized concentration bound on a short window.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiResonantRectangleEnergy.complete_resonant_rectangle_energy_le`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiResonantRectangleEnergy.normalizedRectangleEnergy`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiDualPivotOrthogonality](PascadiDualPivotOrthogonality.md)
