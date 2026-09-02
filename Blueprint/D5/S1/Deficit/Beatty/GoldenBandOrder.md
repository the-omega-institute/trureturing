# Golden Band Strict Order

## Abstract

The structural zero and pole occur in strict order inside the golden band.

**Theorem 1.1 (The golden structural zero and pole are strictly ordered).**

$$\frac{1}{2\times\varphi^{3}} < structuralZero \land \left(structuralZero < structuralPole \land structuralPole < \frac{1}{\varphi^{2}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/GoldenBandOrder.golden_band_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The module imports phi from the frozen S1 GoldenObserverRoute and does not define a second golden ratio. It transcribes only the two constants used here from Hearts: structuralZero=1/(2*phi^2) and structuralPole=1/phi^3. The frontier Hearts module is not imported.

Pinned Mathlib gives 1<phi<2, positivity of powers, and reversal of strict order under positive reciprocals. Those facts prove all three strict comparisons by ordered-field arithmetic, without using either open heart.

The resulting order places the structural zero and structural pole inside the factorization window required by the golden observer route.

## References

- Truth anchor: `D5/S1/Deficit/Beatty/GoldenBandOrder.golden_band_order`
- Dependency: [D5/S1/Deficit/Beatty/GoldenObserverRoute](GoldenObserverRoute.md)
