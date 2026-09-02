# Golden Cofinal Positivity

## Abstract

Positivity on cofinal golden support layers reaches every compact Weil test.

**Theorem 1.1 (Cofinal support-layer positivity is global).**

$$\begin{aligned}\forall L0: \operatorname{Real}\left(\right),\\Q: \operatorname{WeilTestFunction}\left(\right) \to \operatorname{Real}\left(\right),\\\operatorname{Tendsto}\left(\operatorname{goldenSupportRadius}\left(L0\right), \operatorname{atTop}\left(\right), \operatorname{atTop}\left(\right)\right) \land \left(\forall n \in \operatorname{Nat}\left(\right), f \in \operatorname{WeilTestFunction}\left(\right),\; f \in \operatorname{supportLayer}\left(\operatorname{goldenSupportRadius}\left(L0, n\right)\right) \Rightarrow 0 \le Q\left(f\right)\right) \Rightarrow\\\forall f \in \operatorname{WeilTestFunction}\left(\right),\; 0 \le Q\left(f\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CofinalSupport/GoldenCofinalPositivity.golden_cofinal_positivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the canonical compactly supported Weil-test space. The radius at level n is L0 times phi to the power 2n, and supportLayer(R) consists exactly of tests whose function support is contained in [-R,R]. If these radii tend to infinity and Q is nonnegative on every corresponding layer, then Q is nonnegative on every Weil test.

## References

- Truth anchor: `D5/S3/Weil/CofinalSupport/GoldenCofinalPositivity.golden_cofinal_positivity`
