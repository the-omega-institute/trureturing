# Time-Bounded Two-Point Price Frontier

## Abstract

Finite bounded search constructs a target with incomparable fast-long and short-slow witnesses.

**Theorem 1.1 (Bounded diagonalization forces a two-point price frontier).**

$$\begin{gathered}\forall Witness: \operatorname{Type}, [\operatorname{DecidableEq}\left(Witness\right)], M: \operatorname{TimePricedMachine}\left(Witness\right),\\{}(\forall l: \mathbb{N}, l \geq 2, \forall p, \operatorname{runWord}\left(M, l, p, \operatorname{T}\left(M, l\right)\right) = \operatorname{diagonalWord}\left(M, l\right) \Rightarrow l / 2 < \operatorname{length}\left(p\right)) \land\\{}(\forall l: \mathbb{N}, l \geq 2, \forall u, \operatorname{implements}\left(M, l, u, \operatorname{diagonalWord}\left(M, l\right)\right) \land \operatorname{runtime}\left(M, l, u\right) \leq \operatorname{t}\left(M, l\right) \Rightarrow l / 2 - \operatorname{overhead}\left(M, l\right) \leq \operatorname{KBounded}\left(M, l, u\right)) \land\\{}(\forall l: \mathbb{N}, l \geq \operatorname{max}\left(2, \operatorname{marginIndex}\left(M\right)\right), \forall u, \operatorname{implements}\left(M, l, u, \operatorname{diagonalWord}\left(M, l\right)\right) \land \operatorname{KBounded}\left(M, l, u\right) \leq l / 4 \Rightarrow \operatorname{t}\left(M, l\right) < \operatorname{runtime}\left(M, l, u\right)) \land\\{}(\forall l: \mathbb{N}, \operatorname{implements}\left(M, l, \operatorname{tableWitness}\left(M, l\right), \operatorname{diagonalWord}\left(M, l\right)\right) \land \operatorname{KBounded}\left(M, l, \operatorname{tableWitness}\left(M, l\right)\right) \leq l + \operatorname{tableOverhead}\left(M, l\right) \land \operatorname{runtime}\left(M, l, \operatorname{tableWitness}\left(M, l\right)\right) \leq l) \land\\{}(\forall l: \mathbb{N}, \operatorname{implements}\left(M, l, \operatorname{enumeratorWitness}\left(M, l\right), \operatorname{diagonalWord}\left(M, l\right)\right) \land \operatorname{KBounded}\left(M, l, \operatorname{enumeratorWitness}\left(M, l\right)\right) \leq \operatorname{enumeratorCost}\left(M\right) \land \operatorname{t}\left(M, l\right) < \operatorname{runtime}\left(M, l, \operatorname{enumeratorWitness}\left(M, l\right)\right)) \land\\{}(\forall l: \mathbb{N}, l \geq \operatorname{max}\left(2, \operatorname{marginIndex}\left(M\right)\right), \operatorname{KBounded}\left(M, l, \operatorname{enumeratorWitness}\left(M, l\right)\right) < \operatorname{KBounded}\left(M, l, \operatorname{tableWitness}\left(M, l\right)\right) \land \operatorname{runtime}\left(M, l, \operatorname{tableWitness}\left(M, l\right)\right) < \operatorname{runtime}\left(M, l, \operatorname{enumeratorWitness}\left(M, l\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/TimeBoundedTwoPointPrice.time_bounded_two_point_price_frontier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each length l at least two, diagonalWord is the least binary word outside the bounded-time outputs of all programs of length at most floor(l/2). There are exactly 2^(floor(l/2)+1)-1 such programs, fewer than the 2^l targets, so the finite complement is nonempty.

The bounded evaluators are total functions. Decidable witness equality makes each fixed-length program layer finite and searchable, while encodeWitness supplies a terminating upper bound. Thus KBounded is an executable least description length rather than a classical infimum.

A fixed-overhead compiler sends any fast valid witness description to a bounded description of its target. Escape from every half-length code therefore gives the displayed half-length lower bound. The explicit quarter-margin condition makes its contrapositive say that every eventually quarter-short witness is slow.

The machine interface supplies concrete table and enumerator codes and their successful bounded runs. Their verified price and time bounds give strict incomparability at every length beyond the common margin.

The informal logarithmic time factor is represented by the total natural number expression log_2(t(l)+1), avoiding the zero-input convention. The source's O(log l) loss is replaced by the exact quarter-margin hypothesis used by the proof.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/TimeBoundedTwoPointPrice.time_bounded_two_point_price_frontier`
