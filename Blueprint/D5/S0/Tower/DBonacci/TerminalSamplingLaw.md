# Uniform Legal Terminal Law

## Abstract

Adaptive first-hit fair-bit sampling is uniform on native legal terminal words.

For each native live state, CompletionCount counts literal legal completions of the remaining actual output length. The empty layer has one word. The next false branch has count C(maxTrue,q); a true branch, when fuel is positive, has count C(fuel-1,q). Their sum is the current count. With zero fuel the true branch is forbidden.

**Theorem 1.1 (Adaptive composition and the uniform completion law).**

$$\forall m \in \mathit{Nat},\; \begin{aligned}\forall f \in \mathit{Nat},\; \forall h \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall w \in \operatorname{Words}\left(h\right),\; \operatorname{mu}\left(\operatorname{Return}\left(m, f, h, c, w\right)\right) = \operatorname{if}\left(\operatorname{Legal}\left(m, f, h, w\right), \frac{1}{\operatorname{C}\left(m, f, h\right)}, 0\right)\\\forall f \in \mathit{Nat},\; \forall h \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall w \in \operatorname{Words}\left(h\right),\; \operatorname{mu}\left(\operatorname{Return}\left(m, f, h, c, w\right)\right) = \operatorname{ConditionalFairWordMass}\left(m, f, h, w\right)\\\forall f \in \mathit{Nat},\; \forall q \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall t \in \mathit{Nat},\; \forall x \in \operatorname{Fin}\left(2^{q + 1}\right),\; \forall w \in \operatorname{Words}\left(q\right),\; \operatorname{mu}\left(\operatorname{Intersection}\left(\operatorname{Draw}\left(q + 1, \operatorname{C}\left(m, f, q + 1\right), c, t, x\right), \operatorname{Return}\left(m, \operatorname{if}\left(\operatorname{AtLeast}\left(x, \operatorname{C}\left(m, m, q\right)\right), f - 1, m\right), q, c + \left(t + 1\right) \cdot \left(q + 1\right), w\right)\right)\right) = \operatorname{mu}\left(\operatorname{Draw}\left(q + 1, \operatorname{C}\left(m, f, q + 1\right), c, t, x\right)\right) \cdot \operatorname{mu}\left(\operatorname{Return}\left(m, \operatorname{if}\left(\operatorname{AtLeast}\left(x, \operatorname{C}\left(m, m, q\right)\right), f - 1, m\right), q, c + \left(t + 1\right) \cdot \left(q + 1\right), w\right)\right)\\\forall N \in \mathit{Nat},\; \forall c \in \mathit{Nat},\; \forall w \in \operatorname{Words}\left(N\right),\; \operatorname{mu}\left(\operatorname{Return}\left(m, m, N, c, w\right)\right) = \operatorname{if}\left(\operatorname{Legal}\left(m, m, N, w\right), \frac{1}{\operatorname{dbonacci}\left(m + 1, N + 2\right)}, 0\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Tower/DBonacci/TerminalSamplingLaw.terminal_sampling_uniform_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every fixed first-accepted draw (t,x), the consumed cursor is cursor+(t+1)(q+1). Its event depends only on the finite source prefix before that cursor. Native replay identifies the continuation event with an event of the unused suffix. Independence of these disjoint iid coordinate families proves exact event factorization on the same tape.

Nat denotes natural numbers, Words(h) is Fin h to Bool, C(m,f,h) is completionCount and mu is fairTape. Return is the event that sample returns the displayed word with some finite final cursor. Draw fixes the first accepted retry and integer. Legal is native runAdmissible=true. ConditionalFairWordMass is the mass of the singleton word under the iid fair Fin h word measure conditioned on that native legal set. AtLeast compares integer values; subtraction is natural subtraction. The four displayed rows hold jointly, for every listed parameter.

A returned-word event is the disjoint union over accepted branch integers and retry indices of the corresponding draw-and-continuation events. Summing over retries gives integer mass 1/C. There are exactly C(next) accepted integers selecting the requested next bit. Induction on the remaining output length cancels C(next) against the continuation mass 1/C(next). The resulting path mass is 1/C(initial), including the empty terminal word and forced-zero branches.

For maxTrue=k-1 and initial fuel=k-1, the native full-budget count is dbonacci k (N+2). Every legal length-N word therefore has mass 1/G_N, and every illegal word has mass zero. The same returned-word law equals the iid fair length-N word law conditioned on native legality. All branch choices use the concrete fair-bit rejection evaluator; infinite retries are exceptional. The state retains N's remaining output budget and does not define a stationary law on tail state alone.

## References

- Truth anchor: `D5/S0/Tower/DBonacci/TerminalSamplingLaw.terminal_sampling_uniform_law`
- Dependency: [D5/S0/Tower/DBonacci/TerminalSampling](TerminalSampling.md)
