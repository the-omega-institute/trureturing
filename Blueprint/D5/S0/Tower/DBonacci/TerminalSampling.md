# Terminal Fair-Bit Sampling

## Abstract

Finite first-hit fair-bit executions return native legal words almost surely.

A word is a literal Boolean function on Fin h. The native scanner has fuel further consecutive true bits available; false resets fuel to maxTrue, and true decreases positive fuel. CompletionCount is the cardinality of this native completion layer. The original order k and tail length s correspond to maxTrue=k-1 and fuel=k-1-s. The output budget h and source cursor are separate.

A draw decodes consecutive h-bit blocks from one iid fair Boolean tape. It rejects integers outside the completion range and keeps the first accepted integer. Every retry advances the source cursor by h while preserving the output state. Acceptance emits one bit, advances past its block, and reduces the remaining output budget. The zero threshold is the count after a false bit.

**Theorem 1.1 (Literal executions and consumed-source cylinders).**

$$\forall m \in N,\; \forall f \in N,\; \forall h \in N,\; \forall c \in N,\; \forall e \in N,\; \forall w \in \operatorname{Words}\left(h\right),\; \forall a \in \mathit{Tape},\; \begin{aligned}\operatorname{Run}\left(m, a, f, h, c, w, e\right) \Leftrightarrow \operatorname{sample}\left(m, a, f, h, c\right) = \operatorname{some}\left(w, e\right)\\\operatorname{sample}\left(m, a, f, h, c\right) = \operatorname{some}\left(w, e\right) \Rightarrow \left(\operatorname{Legal}\left(m, f, h, w\right) \land \left(c \le e \land \left(\operatorname{Replay}\left(m, a, f, h, c, w, e\right) \land \operatorname{mu}\left(\operatorname{Intersection}\left(\operatorname{Cylinder}\left(c, e, a\right), \operatorname{Result}\left(m, f, h, c, w, e\right)\right)\right) = \frac{1}{2}^{e - c}\right)\right)\right)\\\forall t \in N,\; \forall x \in \operatorname{Fin}\left(2^{h}\right),\; \operatorname{draw}\left(h, \operatorname{C}\left(m, f, h\right), c, a\right) = \operatorname{some}\left(t, x\right) \Leftrightarrow \left(\operatorname{AcceptedAt}\left(h, \operatorname{C}\left(m, f, h\right), c, a, t\right) \land \operatorname{readBlock}\left(h, c + t \cdot h, a\right) = x\right)\\\forall t \in N,\; \forall x \in \operatorname{Fin}\left(2^{h}\right),\; x < \operatorname{C}\left(m, f, h\right) \Rightarrow \left(\operatorname{MeasurableSet}\left(\operatorname{Draw}\left(h, \operatorname{C}\left(m, f, h\right), c, t, x\right)\right) \land \operatorname{mu}\left(\operatorname{Draw}\left(h, \operatorname{C}\left(m, f, h\right), c, t, x\right)\right) = \frac{\frac{2^{h} - \operatorname{C}\left(m, f, h\right)}{2^{h}}^{t}}{2^{h}}\right)\\\forall x \in \operatorname{Fin}\left(2^{h}\right),\; x < \operatorname{C}\left(m, f, h\right) \Rightarrow \left(\operatorname{MeasurableSet}\left(\operatorname{AcceptedValue}\left(h, \operatorname{C}\left(m, f, h\right), c, x\right)\right) \land \operatorname{mu}\left(\operatorname{AcceptedValue}\left(h, \operatorname{C}\left(m, f, h\right), c, x\right)\right) = \frac{1}{\operatorname{C}\left(m, f, h\right)}\right)\\\operatorname{MeasurableSet}\left(\operatorname{RejectedForever}\left(h, \operatorname{C}\left(m, f, h\right), c\right)\right) \land \operatorname{mu}\left(\operatorname{RejectedForever}\left(h, \operatorname{C}\left(m, f, h\right), c\right)\right) = 0\\\forall q \in N,\; h = q + 1 \Rightarrow \left(\operatorname{MeasurableSet}\left(\operatorname{ZeroBranch}\left(m, f, h, c\right)\right) \land \operatorname{mu}\left(\operatorname{ZeroBranch}\left(m, f, h, c\right)\right) = \frac{\operatorname{C}\left(m, m, q\right)}{\operatorname{C}\left(m, f, h\right)}\right)\\\operatorname{MeasurableSet}\left(\operatorname{Result}\left(m, f, h, c, w, e\right)\right) \land \operatorname{MeasurableSet}\left(\operatorname{Return}\left(m, f, h, c, w\right)\right)\\\operatorname{MeasurableSample}\left(m, f, h, c\right)\\\operatorname{Illegal}\left(m, f, h, w\right) \Rightarrow \operatorname{mu}\left(\operatorname{Return}\left(m, f, h, c, w\right)\right) = 0\\\operatorname{mu}\left(\operatorname{SuccessfulLegalReturn}\left(m, f, h, c\right)\right) = 1\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/TerminalSampling.terminal_sampling_execution_cylinders` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Run relation and partial sample evaluator return the same word and final cursor. Returned words pass the native scanner, and agreement on the consumed source interval preserves the full result. A consumed interval of length L has fair mass 2^(-L).

In the formula, N denotes natural numbers, Words(h) is Fin h to Bool, C(m,f,h) is completionCount, and mu is fairTape. Legal and Illegal mean the native scanner returns true and false. Result fixes word and final cursor; Return existentially quantifies the final cursor. Draw fixes retry and accepted integer; AcceptedValue existentially quantifies retry. RejectedForever means draw is none. ZeroBranch is the union of draws whose integer is below C(m,m,h-1). Cylinder is traceCylinder. Replay quantifies every tape agreeing on [c,e), preserving sample's full result. MeasurableSample uses the discrete Option codomain. SuccessfulLegalReturn is the event that some word and finite cursor are returned and that word is native legal. All rows of the displayed statement hold jointly.

Writing D for the completion count and Q=2^h, acceptance of a specified integer at retry t has mass ((Q-D)/Q)^t/Q. Summing the disjoint retry events gives each accepted integer mass 1/D. D is positive and at most Q by the native cardinality results. Infinite rejection has mass zero.

Every returned-word event is measurable. Illegal words have empty return events. A countable simultaneous acceptance event at all fixed states and cursors, followed by induction on h, proves whole termination almost surely. At h=0 the evaluator returns the unique empty word without drawing a branch. The denotation is noncomputable and partial; it supplies no deterministic uniform retry or fair-bit bound.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/TerminalSampling.terminal_sampling_execution_cylinders`
- Dependency: [D5/S0/Tower/DBonacci/Values](Values.md)
