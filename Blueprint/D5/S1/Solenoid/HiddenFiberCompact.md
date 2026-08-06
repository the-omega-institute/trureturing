# Hidden Fiber Compactness

## Abstract

The hidden fiber is closed, compact, and sequentially compact coordinatewise.

**Theorem 1.1 (The hidden fiber is compact in every equivalent sense).**

$$\mathrm{IsClosed}\left(\mathrm{setOf}\left(\forall x0 \in \mathrm{Type},\; \mathrm{projection}\left(\mathit{x0}\right) = 0\right)\right) \land \left(\mathrm{IsCompact}\left(\mathrm{univ}\right) \land \mathrm{IsSeqCompact}\left(\mathrm{univ}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/HiddenFiberCompact.hiddenFiber_closed_compact_seqCompact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Continuity of the visible projection makes its zero fiber closed. The ambient solenoid is compact, so the fiber is compact. Its countable product topology is first countable, hence compactness gives a convergent subsequence; the formal coordinatewise convergence equivalence identifies this with the diagonal, layer-by-layer limit.
