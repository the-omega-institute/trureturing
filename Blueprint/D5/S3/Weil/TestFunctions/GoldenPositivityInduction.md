# Golden Positivity Induction

## Abstract

A two-step positive recurrence propagates through cofinal Fibonacci support layers.

**Theorem 1.1 (Fibonacci-layer positivity reaches every compact Weil test).**

$$\begin{aligned}\forall Q: \operatorname{WeilTestFunction}\left(\right) \to \operatorname{Real}\left(\right),\\\operatorname{let} Layer(n) := \left\{\forall x \in \operatorname{Real}\left(\right),\; f\left(x\right) \ne 0 \Rightarrow \left|x\right| \le \operatorname{fib}\left(n + 5\right) \mid f \in \operatorname{WeilTestFunction}\left(\right)\right\},\\\forall A: \forall n \in \operatorname{Nat}\left(\right),\; \operatorname{Layer}\left(n + 2\right) \to \operatorname{Layer}\left(n + 1\right),\\B: \forall n \in \operatorname{Nat}\left(\right),\; \operatorname{Layer}\left(n + 2\right) \to \operatorname{Layer}\left(n\right), R: \forall n \in \operatorname{Nat}\left(\right),\; \operatorname{Layer}\left(n + 2\right) \to \operatorname{Real}\left(\right),\\\left(\forall f \in \operatorname{Layer}\left(0\right),\; 0 \le Q\left(\operatorname{val}\left(f\right)\right)\right) \land \left(\left(\forall f \in \operatorname{Layer}\left(1\right),\; 0 \le Q\left(\operatorname{val}\left(f\right)\right)\right) \land \left(\left(\forall n \in \operatorname{Nat}\left(\right), f \in \operatorname{Layer}\left(n + 2\right),\; Q\left(\operatorname{val}\left(f\right)\right) = Q\left(\operatorname{val}\left(\operatorname{A}\left(n, f\right)\right)\right) + Q\left(\operatorname{val}\left(\operatorname{B}\left(n, f\right)\right)\right) + \operatorname{R}\left(n, f\right)\right) \land \left(\forall n \in \operatorname{Nat}\left(\right), f \in \operatorname{Layer}\left(n + 2\right),\; 0 \le \operatorname{R}\left(n, f\right)\right)\right)\right) \Rightarrow\\\left(\forall n \in \operatorname{Nat}\left(\right), f \in \operatorname{Layer}\left(n\right),\; 0 \le Q\left(\operatorname{val}\left(f\right)\right)\right) \land \left(\forall f \in \operatorname{WeilTestFunction}\left(\right),\; 0 \le Q\left(f\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/GoldenPositivityInduction.golden_positivity_induction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the canonical compactly supported Weil-test space. Layer n consists of tests supported within the Fibonacci radius fib(n+5). Two-step induction proves positivity on every layer, and compact support together with Fibonacci cofinality places every Weil test in one of those layers.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/GoldenPositivityInduction.golden_positivity_induction`
