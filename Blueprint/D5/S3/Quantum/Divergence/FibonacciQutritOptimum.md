# Fibonacci qutrit Umegaki optimum

## Abstract

Exact retained Umegaki relative entropy for the four Fibonacci likelihood classes under qutrit encoding.

**Theorem 1.1 (Attained maximum over all CPTP encoders).**

Lean statement: `D5/S3/Quantum/Divergence/FibonacciQutritOptimum.isGreatest_channel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/FibonacciQutritOptimum.isGreatest_channel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Exact Fibonacci qutrit Umegaki optimum*. URL: <https://github.com/the-omega-institute/trureturing>.

*Acknowledgement.* trureturing research synthesis (2026). *Singular support reduction for the Fibonacci qutrit Umegaki comparison*. URL: <https://github.com/the-omega-institute/trureturing>.

*Acknowledgement.* trureturing research synthesis (2026). *Supported joint convexity and the Fibonacci mixed-qubit margin*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The two input density matrices are diagonal on four classes, with weights p = (88, 25, 28, 0)/141 and q = (66, 15, 12, 48)/141. For every CPTP encoder to a three-dimensional space, the retained Umegaki relative entropy is at most (113/141) log(113/81) + (28/141) log(7/3) nats. This is the greatest element of the set of output scores, including the support-aware extended definition.

These four classes correspond to the distinct ratios 4/3, 5/3, 7/3 and 0. Grouping equal likelihood ratios means summing p and q separately within each class. Within a class the two conditional laws coincide whenever its p mass is positive, and the q-conditional law suffices to reconstruct a class of zero p mass. The Lean theorem takes the resulting four diagonal weights as its inputs.

On diagonal inputs a channel acts by mixing its density-state preparations of the four diagonal basis states. The pointwise bound pᵢ ≤ (7/3)qᵢ and positivity of those preparations show that the reference kernel lies in the numerator kernel. Thus the extended entropy equals its finite trace-log branch. A singular positive-class reference reduces to a common qubit and retains the null-class log loss. The mixed-qubit overlap deficit bounds the qubit score. A positive definite positive-class reference reaching the benchmark would admit a strictly better preparation with positive-class rank at most two.

For attainment, use orthogonal qutrit rays P, Q and R. Prepare P on classes 4/3 and 5/3, Q on class 7/3 and R on class 0. The commuting outputs have weights (113, 28, 0)/141 and (81, 12, 48)/141. The finite preparation construction makes this a CPTP encoder on the entire input matrix algebra.

**Theorem 1.2 (Necessary equality conditions on the preparations).**

Lean statement: `D5/S3/Quantum/Divergence/FibonacciQutritOptimum.channel_equality_conditions`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/FibonacciQutritOptimum.channel_equality_conditions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* trureturing research synthesis (2026). *Exact Fibonacci qutrit Umegaki optimum*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

At the optimum the positive-class reference is singular. The 4/3 and 5/3 basis preparations coincide. The common preparation, the 7/3 preparation and the zero-likelihood preparation have pairwise zero matrix products, so their supports are pairwise orthogonal.

Optimality forces both nonnegative overlap terms and the null-class log loss to vanish. Trace-one positivity converts unit overlap into equality, and zero overlap into a zero matrix product. Positive coefficients then place the support of the null-class preparation in the kernel of each positive-class preparation.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/FibonacciQutritOptimum.channel_equality_conditions`
- Truth anchor: `D5/S3/Quantum/Divergence/FibonacciQutritOptimum.isGreatest_channel`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Divergence/FannesRootFidelityHolevo](FannesRootFidelityHolevo.md)
- Dependency: [D5/S3/Quantum/Divergence/FibonacciQutritBenchmark](FibonacciQutritBenchmark.md)
- Dependency: [D5/S3/Quantum/Divergence/FibonacciQutritSingularSupport](FibonacciQutritSingularSupport.md)
- Dependency: [D5/S3/Quantum/Divergence/Qubit/FibonacciMixedQubit](Qubit/FibonacciMixedQubit.md)
- Dependency: [D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy](SupportAwareRelativeEntropy.md)
- Dependency: [D5/S3/Quantum/Foundation/FinitePreparationChannel](../Foundation/FinitePreparationChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurements/FiniteMemoryHistoryCapacity](../Measurements/FiniteMemoryHistoryCapacity.md)
- Dependency: [D5/S3/Quantum/Recovery/DiagonalRecordCapacity](../Recovery/DiagonalRecordCapacity.md)
- Dependency: [D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation](../Subentropy/StrongSubadditivityRefutation.md)
