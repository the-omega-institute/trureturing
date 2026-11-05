# The exact complete local occurrence window

## Abstract

The exact complete local occurrence window.

**Theorem 1.1 (The exact complete local occurrence window).**

Lean statement: `D5/S3/Weil/ZeroData/ActualGaussianLocalWindow.mem_localWindow`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroData/ActualGaussianLocalWindow.mem_localWindow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

localWindow(gamma) starts from actualData.symmetricIndices(abs(gamma)+7), expands every finite analytic-multiplicity fiber, maps through actualOccurrenceEquiv and filters by abs(im(rho)-gamma)<=6. The actual strip gives spectralRadius(rho)<=abs(im(rho))+1. This proves the exact membership equivalence, including both distance-six boundary points.

For any finite occurrence set with abs(im(rho))<=T, its cardinality is at most T^2 times the inverse-square mass, hence at most 2*T^2. Taking T=gamma+10 for gamma>0 gives card(localWindow(gamma))<=2*(gamma+10)^2. ActualGaussianDirectTail uses both the exact membership and this count to select the original finite Cassel time. No local-finiteness or multiplicity premise is added.

## References

- Truth anchor: `D5/S3/Weil/ZeroData/ActualGaussianLocalWindow.mem_localWindow`
- Dependency: [D5/S3/Weil/ZeroData/ActualGaussianZeroSum](ActualGaussianZeroSum.md)
