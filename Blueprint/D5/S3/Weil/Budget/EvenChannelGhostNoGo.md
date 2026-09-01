# Even-Channel Ghost No-Go

## Abstract

A shared positive square update preserves even positivity while it can force the odd channel below zero.

**Proposition 1.1 (Nonnegative updates preserve the even channel).**

$$\forall q_{+}, c, C \in \mathbb{R},\ (0 \le q_{+} \land 0 \le c) \Rightarrow 0 \le q_{+} + c \cdot C^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/EvenChannelGhostNoGo.even_channel_update_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real square models the squared modulus of the even-channel coefficient. Its product with a nonnegative update is nonnegative, so adding it preserves a nonnegative base value.

**Proposition 1.2 (A nonzero odd coefficient admits a destructive positive update).**

$$\forall q_{-}, S \in \mathbb{R},\ S \neq 0 \Rightarrow \exists c \in \mathbb{R},\ 0 < c \land q_{-} - c \cdot S^{2} < 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/EvenChannelGhostNoGo.odd_channel_update_eventually_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real initial odd value, the proof constructs the positive coefficient (q-minus squared plus one) divided by S squared. This remains positive even when the initial value is less than minus one.

**Theorem 1.3 (Even positivity alone cannot exclude the odd ghost).**

$$\begin{gathered}\forall q_{+}, q_{-}, C, S \in \mathbb{R},\\{}(0 \le q_{+} \land S \neq 0) \Rightarrow\\{}\exists c \in \mathbb{R}, 0 < c \land\\{}0 \le q_{+} + c \cdot C^{2} \land\\{}q_{-} - c \cdot S^{2} < 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/EvenChannelGhostNoGo.even_channel_ghost_no_go` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the initial even channel is nonnegative and the odd coefficient is nonzero, one explicitly constructed positive coefficient simultaneously leaves the even update nonnegative and makes the odd update strictly negative.

This is an abstract real-algebra statement: C squared and S squared represent the real squared moduli of the analytic channel coefficients. It does not formalize a general Krein-Bochner representation, a Hilbert-Polya realization, or the zeta-specific sufficiency of even Weil tests.

**Proposition 1.4 (The odd margin condition is exact).**

$$\forall q_{-}, c, S \in \mathbb{R},\ c \cdot S^{2} \le q_{-} \Leftrightarrow 0 \le q_{-} - c \cdot S^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/EvenChannelGhostNoGo.odd_channel_margin_iff_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The old odd value has enough margin precisely when it dominates the subtracted square update; this is equivalent to the updated odd channel remaining nonnegative.

**Proposition 1.5 (One concrete coefficient preserves even and breaks odd).**

$$0 < 2 \land 1 \neq 0 \land 0 \le 1 + 2 \cdot 1^{2} \land 1 - 2 \cdot 1^{2} < 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/EvenChannelGhostNoGo.concrete_same_coefficient_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At q-plus = q-minus = C = S = 1 and c = 2, the even update is three while the odd update is minus one.

**Proposition 1.6 (The zero odd coefficient is a necessary exception).**

$$0 < 100 \land 0 \le 1 - 100 \cdot 0^{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/EvenChannelGhostNoGo.zero_odd_coefficient_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At S = 0 and c = 100, the odd update remains one. This concrete counterexample records why the main theorem requires S to be nonzero.

## References

- Truth anchor: `D5/S3/Weil/Budget/EvenChannelGhostNoGo.concrete_same_coefficient_witness`
- Truth anchor: `D5/S3/Weil/Budget/EvenChannelGhostNoGo.even_channel_ghost_no_go`
- Truth anchor: `D5/S3/Weil/Budget/EvenChannelGhostNoGo.even_channel_update_nonnegative`
- Truth anchor: `D5/S3/Weil/Budget/EvenChannelGhostNoGo.odd_channel_margin_iff_nonnegative`
- Truth anchor: `D5/S3/Weil/Budget/EvenChannelGhostNoGo.odd_channel_update_eventually_negative`
- Truth anchor: `D5/S3/Weil/Budget/EvenChannelGhostNoGo.zero_odd_coefficient_counterexample`
