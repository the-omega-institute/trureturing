# DendriteObstruction - TentObstruction

## Abstract

A continuous interval map has bounded folding depth.

**Theorem 1.1 (Two inverse branches of the tent map).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/TentObstruction.continuumTent_half`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/TentObstruction.continuumTent_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t in the closed unit interval, the tent map min(2t,2-2t) sends both t/2 and 1-t/2 to t. These two affine branches are the formulas used to paste the successive folding functions.

**Theorem 1.2 (A continuous interval map has bounded folding depth).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/TentObstruction.no_unbounded_tent_lifts`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/TentObstruction.no_unbounded_tent_lifts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let h be continuous on the closed real unit interval. It is impossible that, for every natural depth m, h equals the m-fold tent iterate of a continuous u on that same interval with u(0)=0 and u(1)=2/3.

At the dyadic grid j/2^m, the m-fold tent iterate equals the parity of j. First hitting times of increasing levels form a strictly increasing family, by the intermediate value theorem and compact minimum attainment. Arbitrarily deep lifts therefore give arbitrarily many consecutive alternating values zero and one of the fixed function h. Uniform continuity separates successive times by a fixed positive distance. Summing these gaps exceeds the length of the unit interval.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/TentObstruction.continuumTent_half`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/TentObstruction.no_unbounded_tent_lifts`
