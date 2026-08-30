# Golden Observer Beatty Route

## Abstract

The golden observer exponent has sqrt-five drift and exactly two golden step sizes.

**Theorem 1.1 (The golden observer has sqrt-five drift and two golden distances).**

$$(\forall v \in \mathbb{N},\\\operatorname{beta}\left(v\right) = \sqrt{5}\times v + \operatorname{r}\left(v\right) \land \operatorname{r}\left(v\right) = {\varphi - 1} - \operatorname{fract}\left({{v+1}\times\varphi}\right) \land\\\operatorname{r}\left(v\right) \in (\varphi - 2, \varphi - 1] \land \operatorname{beta}\left(v+1\right) - \operatorname{beta}\left(v\right) \in \left\{\varphi, \varphi^{2}\right\} \land\\(\operatorname{beta}\left(v+1\right) - \operatorname{beta}\left(v\right) = \varphi \iff \operatorname{beatty}\left(v+1\right) - \operatorname{beatty}\left(v\right) = 1)) \land\\\operatorname{beta}\left(2\right) - \operatorname{beta}\left(1\right) = \varphi.$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/GoldenObserverRoute.golden_observer_route_w_c1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here phi=(1+sqrt(5))/2, psi=1-phi, beatty(v)=floor((v+1)phi)-1, beta(v)=beatty(v)-v psi, and r is the displayed fractional remainder. These four definitions are transcribed from the frozen Hearts module; the proof module does not import that frontier.

Splitting a real number into its integer floor and fractional part gives the drift formula and the left-open, right-closed remainder window. The floor increment lies between one and two because 1<phi<2. Subtracting psi then turns those two integer increments into phi and phi squared, respectively.

This is the Appendix III correction of W-C1. The superseded distance pair involving sqrt(5)+phi-2 and sqrt(5)+phi-1 is not asserted. The final equality records the requested beta(2)-beta(1)=phi anchor.

Pinned Mathlib and the repository were searched before proving. Mathlib supplies the floor, fractional-part, and golden-ratio component laws, but neither source contains this observer-specific conjunction.

## References

- Truth anchor: `D5/S1/Deficit/Beatty/GoldenObserverRoute.golden_observer_route_w_c1`
