# Uniform bound at actual cutoffs

## Abstract

Uniform Landau control of the positive zeta ordinate sum under RH.

**Theorem 1.1 (A uniform bound for the inclusive positive zero sum).**

Lean statement: `D5/S3/Weil/ZetaExplicit/LandauUniformCutoff.actual_cutoff_landau_envelope`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaExplicit/LandauUniformCutoff.actual_cutoff_landau_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Riemann hypothesis. For real V>1 and t nonzero, sum exp(i*t*Im(rho)) with analytic multiplicity over the zeros with 0<Im(rho)<=V. An absolute positive constant times V+exp(|t|/2)*(1+|t|)^2+log(V)/|t| bounds the norm.

The cutoff is empty for 1<V<=6. For V>6 choose a nearby zero-free height and use the rectangle with bottom at 1, left edge at -1/4 and right edge at 1+1/log(3x), where x=exp(|t|). The argument principle counts the zeros with their multiplicities. Reflection extends the square-logarithmic top bound to the full edge. The bottom is bounded on a compact zero-free segment, and the two vertical integrals have uniform bounds.

After division by sqrt(x), the top-edge term sqrt(x)*log(V+9)^2 is controlled by V+sqrt(x)*(1+log(x))^2. Split at x=V. The zeros crossed between the chosen height and V lie in a bounded window and their total multiplicity is O(log(V+9)). Conjugation supplies negative frequencies.

For the harmonic collision theorem, take C from the inclusive cutoff bound and add exp(|t|/2)*(1+log(V)) to the right-hand side inside the factor C. This term is nonnegative for V>1. Both statements use the same positiveCutoff, analytic multiplicity and phase for every t with 0<|t|. Apply harmonic_zeta_collision_limit with that estimate and its stated cutoff and resolution hypotheses. Gonek's prime-power main term concerns the explicit formula.

## References

- Truth anchor: `D5/S3/Weil/ZetaExplicit/LandauUniformCutoff.actual_cutoff_landau_envelope`
- Dependency: [D5/S3/Weil/Mertens/Cryptids/DigammaBinet](../Mertens/Cryptids/DigammaBinet.md)
- Dependency: [D5/S3/Weil/Mertens/Cryptids/HorizontalBounds/Integral](../Mertens/Cryptids/HorizontalBounds/Integral.md)
- Dependency: [D5/S3/Weil/Mertens/Cryptids/VonMangoldtCount/Foundation](../Mertens/Cryptids/VonMangoldtCount/Foundation.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHHarmonicPairMoment](../Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHHarmonicPairMoment.md)
- Dependency: [D5/S3/Weil/ZetaExplicit/LandauLeftVertical](LandauLeftVertical.md)
- Dependency: [D5/S3/Weil/ZetaExplicit/LandauRightVertical](LandauRightVertical.md)
