# Terminal Clock Compression

## Abstract

A known dyadic sensor protocol admits exact decoding from its final phase and bit, with a sharp bound on attained clock labels.

Let d be a natural number, P=2^(d+1), and b a known bit. Protocol(d+1) is the binary controller type: each node waits a finite natural number of events and selects its continuation from the acquired raw bit. Correct(p) means that execution from time zero returns r for every r<P, using at most d+1 queries. The raw sensor reads floor((bP+r+n)/P) modulo two. These are the same controllers and sensors used for dyadic forward waiting.

For a fixed controller p and initial bit b, let N(r) be the time of its final query, S(r)=N(r) mod P, Y(r) its final raw bit, and T(r)=(S(r),Y(r)). Put R={r in N : r<P}, O={(s,y) in N x Fin(2) : s<P and s mod 2=1}, and c(t)=floor(N(2t)/P). Define a(s)=floor((P-1-s)/2) and D(s,y)=2a(s)+(y+b+c(a(s))) mod 2. The plus signs in the correction equal subtraction modulo two.

For a clock summary phi:N->Z, let L(phi)={phi(N(r)):r in R}; only attained labels are counted. Write phase(P) for the map n->n mod P. The decoder knows p and b. Its bound counts neither the description of p, the computation of c, nor storage during acquisition. The record T contains the phase latched at the final query; an elapsed-time variable that is not part of the record cannot be used in this decoding relation.

**Theorem 1.1 (The exact terminal encoding and attained clock bound).**

$$\forall d \in \mathbb{N},\; \forall b \in \operatorname{Fin}\left(2\right),\; \forall P \in \mathbb{N},\; P = 2^{d + 1} \Rightarrow \left(\forall p \in \operatorname{Protocol}\left(d + 1\right),\; \operatorname{Correct}\left(p\right) \Rightarrow \left(\left(\forall t \in \mathbb{N},\; t < 2^{d} \Rightarrow \left(\operatorname{N}\left(2 \cdot t\right) = \operatorname{N}\left(2 \cdot t + 1\right) \land \left(\operatorname{S}\left(2 \cdot t\right) = P - 1 - 2 \cdot t \land \left(\forall u \in \mathbb{N},\; u < 2 \Rightarrow \operatorname{Y}\left(2 \cdot t + u\right) = \operatorname{mod}\left(b + \operatorname{c}\left(t\right) + u, 2\right)\right)\right)\right)\right) \land \left(\left(\forall r \in \mathbb{N},\; r < P \Rightarrow \operatorname{D}\left(\operatorname{S}\left(r\right), \operatorname{Y}\left(r\right)\right) = r\right) \land \left(\operatorname{BijOn}\left(T, R, O\right) \land \left(\operatorname{card}\left(\operatorname{L}\left(\operatorname{phase}\left(P\right)\right)\right) = 2^{d} \land \left(\forall Z \in Type,\; \forall phi \in \mathbb{N} \to Z,\; \forall recover \in Z \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{N}\right),\; \left(\forall r \in \mathbb{N},\; r < P \Rightarrow \operatorname{recover}\left(\operatorname{phi}\left(\operatorname{N}\left(r\right)\right), \operatorname{Y}\left(r\right)\right) = r\right) \Rightarrow 2^{d} \le \operatorname{card}\left(\operatorname{L}\left(phi\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/TerminalClockCompression.terminal_pair_fiber_bijection_and_clock_injectivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Capacity saturation forces midpoint cuts. Induction through the threshold tree gives a common final-query time for each adjacent pair and forces its terminal phase. The final bit recovers the remaining source bit after correction. Choosing a source with final bit zero in every pair forces distinct clock labels for distinct pair indices.

Let early be the raw-bit version of the earliest midpoint controller: at every interval it waits for the first forward occurrence of the midpoint phase. Write N_early and c_early for its completion time and period quotient, and wt(t) for the number of ones in the binary expansion of t. Since t<2^d, this is also its d-bit binary weight. The following identity makes the period correction computable from the recovered t.

**Theorem 1.2 (Earliest midpoint completion time).**

$$\forall d \in \mathbb{N},\; \forall b \in \operatorname{Fin}\left(2\right),\; \forall P \in \mathbb{N},\; P = 2^{d + 1} \Rightarrow \left(\forall t \in \mathbb{N},\; \forall u \in \mathbb{N},\; \left(t < 2^{d} \land u < 2\right) \Rightarrow \left(\operatorname{Nearly}\left(2 \cdot t + u\right) = P - 1 + P \cdot \operatorname{wt}\left(t\right) - 2 \cdot t \land \operatorname{cearly}\left(t\right) = \operatorname{wt}\left(t\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Budget/TerminalClockCompression.earliest_midpoint_terminal_time` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the remaining depth tracks the exact waiting increments. The upper-half branch adds one binary digit of value one and one complete period to the time identity. Division by P leaves the binary weight because the remaining phase lies between zero and P.

## References

- Truth anchor: `D5/S3/Observer/Budget/TerminalClockCompression.earliest_midpoint_terminal_time`
- Truth anchor: `D5/S3/Observer/Budget/TerminalClockCompression.terminal_pair_fiber_bijection_and_clock_injectivity`
- Dependency: [D5/S3/Observer/Budget/DyadicForwardWaitingOptimality](DyadicForwardWaitingOptimality.md)
