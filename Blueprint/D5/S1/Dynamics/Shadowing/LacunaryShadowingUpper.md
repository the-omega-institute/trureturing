# One fixed finite set traces every pseudo-orbit

## Abstract

One fixed finite set traces every pseudo-orbit

The explicit phase masks repair every natural-time pseudo-orbit, preserving its observed windows and the common initial window.

**Theorem 1.1 (Neighborhood (m-1)-shadowing).**

Lean statement: `D5/S1/Dynamics/Shadowing/LacunaryShadowingUpper.lacunary_neighborhood_upper`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/LacunaryShadowingUpper.lacunary_neighborhood_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each accuracy choose a finite signed window using the genuine compatible product metric. The phase-cover theorem constructs a scale K and m-1 masks. A sufficiently accurate pseudo-orbit has a signed diagonal agreeing with each observed window, including the negative initial coordinates. Short progression constraints already hold in this diagonal; long constraints become legal after masking because no mask retains three vertices. All masked whole configurations belong to X_m. Their single finite set has cardinality at most m-1 and initial diameter below the prescribed accuracy. At every natural time one of these same configurations preserves the entire current window. No supplied mask-existence or tracing-count assumption remains in the theorem.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/LacunaryShadowingUpper.lacunary_neighborhood_upper`
- Dependency: [D5/S1/Dynamics/Shadowing/LacunaryPhaseCover](LacunaryPhaseCover.md)
- Dependency: [D5/S1/Dynamics/Shadowing/LacunaryProgressionSubshift](LacunaryProgressionSubshift.md)
