# Short return width transport

## Abstract

Short return lengths, phase divisibility, and contraction width estimates.

These are abstract arithmetic estimates for the final step of a short-return argument. All lengths and periods are natural numbers; division of natural numbers means floor division, and natural subtraction is truncated at zero. The contraction, root width d and piece width w are real numbers.

**Lemma 1.1 (Phase divisibility bounds the synchronization length).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \left(0 < p \land \left(p \mid a \land \left(p \mid b \land \left(a \le n \land b \le 2 \cdot n - 1\right)\right)\right)\right) \Rightarrow lcm\left(a, b\right) \le p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.synchronized_length_le_phase_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Writing a=p alpha and b=p gamma gives lcm(a,b)=p lcm(alpha,gamma). The two quotient bounds and lcm(alpha,gamma)<=alpha gamma give the stated estimate. Zero lengths are allowed in this arithmetic lemma.

**Lemma 1.2 (The contraction ratio decreases with the positive scale).**

$$\forall g \in \mathbb{R},\; \forall L \in \mathbb{N},\; \forall M \in \mathbb{N},\; \left(0 < g \land \left(g < 1 \land \left(0 < L \land L \le M\right)\right)\right) \Rightarrow \frac{g^{M}}{1 - g^{M}} \le \frac{g^{L}}{1 - g^{L}}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.contraction_ratio_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The larger exponent decreases the numerator and increases the denominator. Both denominators are positive. Equality of the two scales is included.

**Theorem 1.3 (Transport a synchronized packing estimate to the uniform scale).**

$$\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall g \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall w \in \mathbb{R},\; \left(0 < g \land \left(g < 1 \land \left(0 \le d \land \left(\left(0 < p \land \left(p \mid a \land \left(p \mid b \land \left(a \le n \land b \le 2 \cdot n - 1\right)\right)\right)\right) \land \left(0 < a \land \left(0 < b \land g^{lcm\left(a, b\right)} \cdot d \le \left(1 - g^{lcm\left(a, b\right)}\right) \cdot w\right)\right)\right)\right)\right)\right) \Rightarrow \frac{g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}}{1 - g^{p \cdot \lfloor\frac{n}{p}\rfloor \cdot \lfloor\frac{2 \cdot n - 1}{p}\rfloor}} \cdot d \le w$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put M=p floor(n/p) floor((2n-1)/p). For a pair of positive return lengths, the supplied packing inequality at L=lcm(a,b) first yields w>=g^L d/(1-g^L). The phase bound gives L<=M, and the preceding monotonicity lemma transports this to w>=g^M d/(1-g^M). Nonnegative d suffices; for an actual guard-root width d is positive. The packing premise itself forces w to be nonnegative, so a separate sign hypothesis on w is unnecessary.

To obtain Proposition 51.3 for every original piece, one still needs actual returns at each basepoint with a<=n and b<=2n-1 whose first words differ after LCM synchronization, period divisibility from the second projection, and the original full-cylinder packing inequality. The coherence and phase characterization in CoherentReturnPathTemplates does not by itself supply these short returns or the packing inequality. The SevenCycleCoherence modules concern a particular original paired graph and do not supply the general bridge. These estimates assert neither the required SCC/source bridge nor existence of a graph realization.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.contraction_ratio_antitone`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.short_return_width_lower_bound`
- Truth anchor: `D5/S1/Words/ReturnWords/ShortReturnWidthTransport.synchronized_length_le_phase_bound`
