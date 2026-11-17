# From raw histories to the actual source solution

## Abstract

Actual raw integrated cooling solutions satisfy Appendix (5) and the concrete shifted-kernel history convolution, whose integrability is derived.

Write E for the concrete finite-sum quasi-exponential, and k(r)=E(r-tau). The source is Santos, arXiv:2611.12328v1, Appendix (5). Fix a positive delay at most exp(-1), an individual preparation start a at most zero, equilibrium q and final bath temperature c. The raw sample satisfies the finite-Lebesgue integrated DDE. Its raw bath is q strictly before a and c strictly after zero. Values at the two endpoints are unrestricted.

**Definition 1.1 (The finite-Lebesgue Appendix input).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution.AppendixSolution`

*Formalization.* `D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution.AppendixSolution` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sample has its pointwise constant past, satisfies Appendix (5) at every t at least a, and the weighted preparation integral at time zero is Lebesgue integrable. Separate bath integrability and sample regularity are not fields of this definition.

**Theorem 1.2 (Appendix (5) and the complete equilibrium tail).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution.raw_history_solution_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution.raw_history_solution_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every t at least a, T(t) equals c plus (q-c)E(t-a) plus the integral from a to min(0,t) of (b(s)-c)k(t-s). This is the literal Appendix formula with a equal to minus the individual preparation length. At every nonnegative t it also equals c plus the integral over all positive ages u of k(t+u)(b(-u)-c). That integrand is integrable. Neither the convolution identity nor its integrability is assumed as a sample field.

The proof first derives continuity and absolute continuity from the integrated DDE. Integration by parts against E(t-s-tau), with the derivative kink split at s=t-tau, cancels the delayed sample integrals after a change of variables. The remaining equilibrium segment gives qE(t-a). Subtracting the constant bath contribution and truncating the postzero deviation gives Appendix (5). Reflection turns the finite preparation integral into positive ages. The exact kernel tail-mass theorem supplies the omitted equilibrium tail (q-c)E(t-a).

All sample equalities are pointwise. The bath is the original raw representative, so an individual pointwise supremum h can be imposed on it without replacing it by an essential supremum. Each sample can use its own a and q. No common preparation length, step-function restriction or convolution hypothesis is introduced.

**Theorem 1.3 (Appendix (5) is equivalent to the integrated DDE).**

Lean statement: `D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution.appendix5_iff_integrated`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution.appendix5_iff_integrated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the stated delay range and equilibrium and final-bath conditions, a raw sample satisfies the finite-Lebesgue Appendix definition if and only if it satisfies the integrated DDE. To recover integrability of the bath on the preparation interval, multiply the defined weighted integrand at time zero by the continuous reciprocal of the positive concrete kernel, then add c. The final constant bath supplies the remaining finite intervals. The method-of-steps theorem constructs an integrated sample. Its Appendix representation agrees pointwise with the given sample, which therefore is that integrated solution. The integrated-to-Appendix direction uses the derived bath integrability and the actual kernel representation. Thus neither direction assumes sample regularity or an unproved solution field.

The source does not fix an integral convention. Proper-Riemann and all-source inclusion remain unproved obligations, as do the precise ordinary-time/quench converse, complete event admissibility and the actual globally optimized balanced synchronous comparator. This is intermediate mathematics and makes no solved-problem or novelty claim.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution.AppendixSolution`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution.appendix5_iff_integrated`
- Truth anchor: `D5/S3/StatisticalMechanics/DelayedCooling/HistorySolution.raw_history_solution_bridge`
- Dependency: [D5/S3/StatisticalMechanics/DelayedCooling/ShiftOrder](ShiftOrder.md)
- Dependency: [D5/S3/StatisticalMechanics/DelayedCooling/Volterra](Volterra.md)
