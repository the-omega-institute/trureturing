# Delayed Pulse Memory Gap

## Abstract

Delayed pulses have exact static and all-time finite-memory minima.

Let m and H be natural numbers. The source state n advances to n+1, and its real output o_m(n) is one when n=m and zero otherwise. Let 0 <= epsilon < 1/2. All correctness conditions quantify over every initial n, and times include zero.

**Theorem 1.1 (Exact static and all-time memory minima).**

$$\begin{gathered}\forall m,H\in\mathbb{N}, \forall \varepsilon\in\mathbb{R}, 0\leq\varepsilon<\frac{1}{2}\Rightarrow\\\operatorname{StaticCorrect}(m, H, \varepsilon, \operatorname{staticEncode}(m, H), \operatorname{staticDecode}(m, H))\land\\\operatorname{IsLeast}(\operatorname{staticSizes}(m, H, \varepsilon), \operatorname{min}(H, m)+2)\land\\\operatorname{UpdaterCorrect}(m, \varepsilon, \operatorname{machineEncode}(m), \operatorname{machineUpdate}(m), \operatorname{machineReadout}(m))\land\\\operatorname{IsLeast}(\operatorname{updaterSizes}(m, \varepsilon), m+2)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/DelayedPulseMemoryGap.delayed_pulse_memory_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

StaticCorrect(m,H,epsilon,e,D) means that |D(e(n),t)-o_m(n+t)| <= epsilon for every n and every t <= H. The set staticSizes consists of card(C) for finite types C admitting such an encoder e and decoder D. There is no requirement to update a static label.

Write K=min(H,m). The attaining carrier is Fin(K+2). The encoder stores m-n when n <= m and m-n <= H; otherwise it stores K+1. The decoder outputs one precisely when its label equals t and t <= K. This reproduces every window response exactly.

For each j from zero through K, the initial state m-j produces a pulse at window time j. The initial state m+1 gives the silent response. Any two of these K+2 responses differ by one at a window time, so their labels cannot coincide: a shared real prediction would force 1 <= 2 epsilon. Injectivity gives the lower bound.

UpdaterCorrect(m,epsilon,e,U,r) means that |r(U^[t](e(n)))-o_m(n+t)| <= epsilon for every n and every natural time t. The set updaterSizes consists of card(Q) for finite types Q admitting one fixed encoder, update and readout satisfying this condition.

The attaining carrier is Fin(m+2). Encode n as min(n,m+1), update q to min(q+1,m+1), and output one exactly at state m. The state m+1 is absorbing. Induction gives the exact invariant U^[t](e(n))=min(n+t,m+1), hence exact outputs at every time.

For any initial states i<j among zero through m+1, continue for m-i steps. The output from i is one and the output from j is zero. If their encodings agreed, the updater would give the same prediction at this time, again contradicting epsilon < 1/2. Thus all m+2 encodings must be distinct.

Both minima include m=0 and epsilon=0; the static result also includes H=0. Keeping H fixed and increasing m makes the difference between the two minimum counts arbitrarily large.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/DelayedPulseMemoryGap.delayed_pulse_memory_gap`
