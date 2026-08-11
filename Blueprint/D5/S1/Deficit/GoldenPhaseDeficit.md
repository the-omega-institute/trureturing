# Golden Phase Classification of the Beatty Deficit

## Abstract

The golden Beatty deficit is classified exactly by two phase-sum thresholds.

**Theorem 1.1 (Two phase thresholds determine all three deficit values).**

$$c(v_1, v_2)=+1 \Leftrightarrow theta(v_1)+theta(v_2)<\varphi^{-1},\quad c(v_1, v_2)=-1 \Leftrightarrow \varphi\leq theta(v_1)+theta(v_2),\quad c(v_1, v_2)=0 \Leftrightarrow \varphi^{-1}\leq theta(v_1)+theta(v_2)<\varphi$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/GoldenPhaseDeficit.golden_phase_deficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two natural indices, take the fractional parts of their shifted golden orbits and add them. The additive coboundary of the canonical golden Beatty shift equals plus one exactly below the inverse-golden threshold, equals minus one exactly at or above the golden-ratio threshold, and equals zero throughout the half-open band between those thresholds. Thus the phase sum determines the deficit value, which is strictly stronger than merely knowing that three values are possible.

The proof is new glue over pinned Mathlib floor arithmetic. Expanding each real input into its integer floor and fractional part rewrites the Beatty coboundary as minus one minus the floor of the phase sum less the golden ratio. The standard bounds on fractional parts and the identity that the inverse golden ratio is the golden ratio less one then identify the floor as minus two, minus one, or zero on the three regions. Mathlib provides the component identities but no declaration with these two phase thresholds; the source atom's classification is therefore proved here rather than wrapped.

## References

- Truth anchor: `D5/S1/Deficit/GoldenPhaseDeficit.golden_phase_deficit`
