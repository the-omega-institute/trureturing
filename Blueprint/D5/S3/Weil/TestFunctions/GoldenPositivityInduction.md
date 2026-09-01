# Golden Positivity Induction

## Abstract

A two-step positive recurrence propagates through a chosen cofinal support schedule.

**Theorem 1.1 (Recurrent-layer positivity reaches every compact Weil test).**

$$\begin{aligned}\forall L: \operatorname{Nat}\left(\right) \to \operatorname{Real}\left(\right),\\Q: \operatorname{WeilTestFunction}\left(\right) \to \operatorname{Real}\left(\right),\\\operatorname{let} Layer(n) := \left\{\forall x \in \operatorname{Real}\left(\right),\; f\left(x\right) \ne 0 \Rightarrow \left|x\right| \le L\left(n\right) \mid f \in \operatorname{WeilTestFunction}\left(\right)\right\},\\\forall A: \forall n \in \operatorname{Nat}\left(\right),\; \operatorname{Layer}\left(n + 2\right) \to \operatorname{Layer}\left(n + 1\right),\\B: \forall n \in \operatorname{Nat}\left(\right),\; \operatorname{Layer}\left(n + 2\right) \to \operatorname{Layer}\left(n\right), R: \forall n \in \operatorname{Nat}\left(\right),\; \operatorname{Layer}\left(n + 2\right) \to \operatorname{Real}\left(\right),\\\left(\forall n \in \operatorname{Nat}\left(\right),\; 0 < L\left(n\right)\right) \land \left(\left(\forall n \in \operatorname{Nat}\left(\right),\; L\left(n + 2\right) = L\left(n + 1\right) + L\left(n\right)\right) \land \left(\left(\forall f \in \operatorname{Layer}\left(0\right),\; 0 \le Q\left(\operatorname{val}\left(f\right)\right)\right) \land \left(\left(\forall f \in \operatorname{Layer}\left(1\right),\; 0 \le Q\left(\operatorname{val}\left(f\right)\right)\right) \land \left(\left(\forall n \in \operatorname{Nat}\left(\right), f \in \operatorname{Layer}\left(n + 2\right),\; Q\left(\operatorname{val}\left(f\right)\right) = Q\left(\operatorname{val}\left(\operatorname{A}\left(n, f\right)\right)\right) + Q\left(\operatorname{val}\left(\operatorname{B}\left(n, f\right)\right)\right) + \operatorname{R}\left(n, f\right)\right) \land \left(\forall n \in \operatorname{Nat}\left(\right), f \in \operatorname{Layer}\left(n + 2\right),\; 0 \le \operatorname{R}\left(n, f\right)\right)\right)\right)\right)\right) \Rightarrow\\\left(\forall n \in \operatorname{Nat}\left(\right), f \in \operatorname{Layer}\left(n\right),\; 0 \le Q\left(\operatorname{val}\left(f\right)\right)\right) \land \left(\forall f \in \operatorname{WeilTestFunction}\left(\right),\; 0 \le Q\left(f\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/GoldenPositivityInduction.golden_positivity_induction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the canonical compactly supported Weil-test space. The chosen positive support schedule satisfies L(n+2)=L(n+1)+L(n), the source relation (1219.1). Layer n consists of tests supported within radius L(n). Two-step induction proves positivity on every layer, and cofinality derived from positivity and the recurrence places every Weil test in one of those layers.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/GoldenPositivityInduction.golden_positivity_induction`
