# Forward displacement without wrapping

## Abstract

Fractional phases add their forward displacement when the sum stays below one.

**Definition 1.1 (orbitPhase).**

$$\forall \operatorname{alpha}: \operatorname{Real}, \forall \operatorname{i}: \operatorname{Nat}, \operatorname{orbitPhase} \operatorname{alpha} \operatorname{i} = (\operatorname{Int.fract} (((\operatorname{i} + 1 : \operatorname{Nat}) : \operatorname{Real}) \cdot \operatorname{alpha}))$$

*Formalization.* `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.orbitPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula holds for the stated real parameters and natural indices. Natural subtraction is truncated; all casts retain their displayed codomains.

**Theorem 1.2 (irrational nat mul fract ne zero).**

$$\forall \operatorname{alpha}: \operatorname{Real}, (\operatorname{Irrational} \operatorname{alpha})\Rightarrow\forall \operatorname{k}: \operatorname{Nat}, (0 < \operatorname{k})\Rightarrow\operatorname{Int.fract} ((\operatorname{k} : \operatorname{Real}) \cdot \operatorname{alpha}) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.irrational_nat_mul_fract_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula holds for the stated real parameters and natural indices. Natural subtraction is truncated; all casts retain their displayed codomains.

**Theorem 1.3 (exists orbit phase mem Ioo).**

$$\forall \operatorname{alpha}: \operatorname{Real}, \forall \operatorname{a}: \operatorname{Real}, \forall \operatorname{b}: \operatorname{Real}, (\operatorname{Irrational} \operatorname{alpha})\Rightarrow(0 \leq \operatorname{a})\Rightarrow(\operatorname{a} < \operatorname{b})\Rightarrow(\operatorname{b} \leq 1)\Rightarrow\exists \operatorname{i} , \operatorname{orbitPhase} \operatorname{alpha} \operatorname{i} \in \operatorname{Ioo} \operatorname{a} \operatorname{b}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.exists_orbit_phase_mem_Ioo` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula holds for the stated real parameters and natural indices. Natural subtraction is truncated; all casts retain their displayed codomains.

**Theorem 1.4 (fract add displacement of wrap).**

$$\forall \operatorname{alpha}: \operatorname{Real}, \forall \operatorname{x}: \operatorname{Real}, (\operatorname{Irrational} \operatorname{alpha})\Rightarrow\forall \operatorname{k}: \operatorname{Nat}, (0 < \operatorname{k})\Rightarrow(\operatorname{x} < 1)\Rightarrow(1 \leq \operatorname{x} + \operatorname{forwardDisplacement} \operatorname{alpha} \operatorname{k})\Rightarrow\operatorname{Int.fract} (\operatorname{x} + (\operatorname{k} : \operatorname{Real}) \cdot \operatorname{alpha}) = \operatorname{x} - \operatorname{backwardDisplacement} \operatorname{alpha} \operatorname{k}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_wrap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula holds for the stated real parameters and natural indices. Natural subtraction is truncated; all casts retain their displayed codomains.

**Theorem 1.5 (Fractional addition without wrapping).**

$$\forall alpha \in \mathrm{Real},\; \forall x \in \mathrm{Real},\; \forall k \in \mathrm{Nat},\; (0 \le x) \Rightarrow (x + \operatorname{forwardDisplacement}\left(alpha, k\right) < 1) \Rightarrow \operatorname{Int}.\operatorname{fract}\left(x + (\operatorname{Nat}.\operatorname{cast}\left(k\right) : \mathrm{Real}) \cdot alpha\right) = x + \operatorname{forwardDisplacement}\left(alpha, k\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_no_wrap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real alpha and x and a natural k, if x is nonnegative and x plus forwardDisplacement alpha k is less than one, the fractional part of x plus k times alpha equals that sum.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.exists_orbit_phase_mem_Ioo`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_no_wrap`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.fract_add_displacement_of_wrap`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.irrational_nat_mul_fract_ne_zero`
- Truth anchor: `D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore.orbitPhase`
