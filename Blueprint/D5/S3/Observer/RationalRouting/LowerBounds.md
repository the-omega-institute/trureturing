# Incompatible attained grids

## Abstract

Original recovery requires at least two acquired actions and at least four preset actions.

Use the same positive-rational source, chronological L and R, two-band prior, complete dyadic floor ports and finite instruction-run relation. An action cap bounds the final chronological word on every terminating prior run. A preset controller's final words follow one common schedule: letter k equals schedule(k). Pauses, local computations, exponents, read counts and early stopping remain report-dependent. The lower bound even allows arbitrary, rather than just effectively generated, public schedules.

**Theorem 1.1 (Universal action lower bounds).**

$$\operatorname{Correct}(C,V)\land \operatorname{InjOn}(V,P)\longrightarrow (\forall h, \operatorname{Cap}\left(C, h\right)\longrightarrow2\leq h)\land (\forall v,h, \operatorname{Preset}\left(C, v\right)\land\operatorname{Cap}\left(C, h\right)\longrightarrow4\leq h)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/RationalRouting/LowerBounds.original_action_lower_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every state type, output type, common initial state and deterministic instruction function, let the original target be injective on the whole prior and require finite correct completion everywhere. Every uniform action cap h is then at least 2. If all completed words follow one common public schedule, h is at least 4. Quantification is over all those controllers; it is not restricted to a displayed implementation or an assumed replay certificate.

Every endpoint run must contain an actual grid read. At lengths at most three the only qualifying prefixes for 1/6 are LL and LLR, and those for 2/3 are RL and RLR. The rational denominator at a grid divides a power of two. Exact arithmetic for all fifteen words of lengths zero through three leaves precisely those routes; every excluded denominator has an odd prime divisor. Prefixes at actual reads remain prefixes of the final word, including across arbitrary local steps and adaptive reads.

No qualifying prefix has length zero or one. With at most three actions the endpoint 1/6 therefore requires first letter L, whereas 2/3 requires first letter R. A common preset schedule cannot have both first letters. This obstruction concerns actual noncommuting source actions and an injective original output; a band bit alone is not the target.

## References

- Truth anchor: `D5/S3/Observer/RationalRouting/LowerBounds.original_action_lower_bounds`
- Dependency: [D5/S3/Observer/RationalRouting/Source](Source.md)
