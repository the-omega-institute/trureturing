# Mechanical Readout Order

## Abstract

Actual rotation bits determine order-preserving weights and an isometric geometric completion with exact finite-precision cost.

**Definition 1.1 (Additive numerical readout of actual letters).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutOrder.weightedPrefix`

*Formalization.* `D5/S1/Words/Mechanical/MechanicalReadoutOrder.weightedPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sum uses the existing lowerMechanicalLetter evaluated on a real slope and phase. The weight sequence is arbitrary and real-valued. At slopes in [0,1), each letter is a genuine binary observation.

**Theorem 1.2 (Exact local order-preservation criterion).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutOrder.local_order_iff_decreasing_weights`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutOrder.local_order_iff_decreasing_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every fixed irrational slope in (0,1), and for every nonempty finite horizon m+1, the weighted readout is nondecreasing under all sufficiently small upward slope changes at every phase exactly when the weights decrease and the last weight is nonnegative. Necessity intersects an arbitrary proposed monotonicity radius with the actual geometric chamber, then constructs a phase in each nonempty swept interval. The realized adjacent exchanges force each weight drop, and the last-bit interval forces the terminal sign. Sufficiency proves the finite summation-by-parts identity on actual cumulative floors and uses their order. No arbitrary binary-pattern realizability or weight-order assumption is hidden in the forward direction. Summation by parts is prior mathematics. Its shared actual-floor identity is also consumed by the geometric completion theorem in this same owner.

**Definition 1.3 (Geometric completion of actual binary letters).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutOrder.geometricReadout`

*Formalization.* `D5/S1/Words/Mechanical/MechanicalReadoutOrder.geometricReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The infinite sum uses the actual mechanical letters with weights (1-r)*r^k. For r in [0,1), the main theorem proves convergence, integrability, and a uniform tail. Binary positional weighting is r=1/2; r=0 is included without a special-case assumption.

**Theorem 1.4 (Actual readout integration, L1 distance and mixed precision).**

Lean statement: `D5/S1/Words/Mechanical/MechanicalReadoutOrder.geometric_readout_isometric_completion`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/MechanicalReadoutOrder.geometric_readout_isometric_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r in [0,1) and slopes alpha,beta in [0,1), the completed readouts are integrable on the uniform unit phase interval, with a nonnegative pointwise truncation tail at most r^n. The finite integrated absolute distance is (1-r^n)*abs(beta-alpha), and the infinite distance is exactly abs(beta-alpha). If beta<=alpha, the mixed completed/finite error is exactly alpha-beta*(1-r^n). The proof integrates each actual shifted floor through its carry interval, derives every letter mean, shares the actual-floor summation-by-parts order argument, proves summability and tails by positive series comparison, and applies dominated convergence. No expectation, convergence, integrability, or distance formula is assumed. The result is a concrete integral identity, not a declaration that a single scalar sample decodes every infinite word.

## References

- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutOrder.geometricReadout`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutOrder.geometric_readout_isometric_completion`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutOrder.local_order_iff_decreasing_weights`
- Truth anchor: `D5/S1/Words/Mechanical/MechanicalReadoutOrder.weightedPrefix`
- Dependency: [D5/S1/Words/Mechanical/MechanicalSlopeSensitivity](MechanicalSlopeSensitivity.md)
