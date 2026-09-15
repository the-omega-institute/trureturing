# Stephan's Maximum Even Partition-Product Recurrence

## Abstract

The greatest even product of partition parts triples when the total increases by three.

In the formulas, partitionProducts(n) is the family of products of the parts of partitions of n, while evenPartitionProducts(n) is its subfamily of even products. IsGreatest records both attainment and an upper bound for every member of the corresponding family.

**Definition 1.1 (The unconstrained maximum partition product).**

$$(\operatorname{classicalMaximumProduct}\left(0\right) = 1) \land ((\operatorname{classicalMaximumProduct}\left(1\right) = 1) \land ((\operatorname{classicalMaximumProduct}\left(2\right) = 2) \land ((\operatorname{classicalMaximumProduct}\left(3\right) = 3) \land ((\operatorname{classicalMaximumProduct}\left(4\right) = 4) \land (\forall n \in \mathrm{Nat},\; \operatorname{classicalMaximumProduct}\left(n + 5\right) = 3 \cdot \operatorname{classicalMaximumProduct}\left(n + 2\right))))))$$

*Formalization.* `D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.classicalMaximumProduct` (`✓ std3`).

*Citation.* Jon Perry; Ralf Stephan (2004). *OEIS A091915, Maximum of even products of partitions of n*. URL: <https://oeis.org/A091915>.

*Commentary.*

The values at totals zero through four are 1, 1, 2, 3, and 4. Thereafter the recurrence removes three from the total and multiplies the value by three. This is the classical A000792 maximum without a parity constraint.

**Theorem 1.2 (The classical unconstrained extremal theorem).**

$$\forall n \in \mathrm{Nat},\; \operatorname{IsGreatest}\left(\operatorname{partitionProducts}\left(n\right), \operatorname{classicalMaximumProduct}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.classicalMaximumProduct_isGreatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jon Perry; Ralf Stephan (2004). *OEIS A091915, Maximum of even products of partitions of n*. URL: <https://oeis.org/A091915>.

*Commentary.*

For every natural total n, classicalMaximumProduct(n) is attained by a partition of n and bounds the product of every partition of n. The theorem is stated publicly as the unconstrained extremal result used by the parity-constrained argument.

**Theorem 1.3 (Stephan's even-product recurrence).**

$$\forall n \in \mathrm{Nat},\; (6 < n) \Rightarrow (\exists a \in \mathrm{Nat},\; (\operatorname{IsGreatest}\left(\operatorname{evenPartitionProducts}\left(n\right), a\right)) \land (\operatorname{IsGreatest}\left(\operatorname{evenPartitionProducts}\left(n + 3\right), 3 \cdot a\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a091915-stephan-even-product-partition-recurrence` (proved) by `D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a091915-stephan-even-product-partition-recurrence","declaration_gid":"D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jon Perry; Ralf Stephan (2004). *OEIS A091915, Maximum of even products of partitions of n*. URL: <https://oeis.org/A091915>.

*Commentary.*

For n greater than six, there is a greatest even partition product a at total n, and 3a is the greatest even partition product at n+3. For residues two and one modulo three the unconstrained optima 2 times a power of three and 4 times a power of three are even. For residue zero the unconstrained power of three is odd, so the even constraint binds and the sharp value is 8 times a power of three. Each branch is multiplied by three after adding three.

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.classicalMaximumProduct`
- Truth anchor: `D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.classicalMaximumProduct_isGreatest`
- Truth anchor: `D5/S1/Recurrence/Partitions/StephanEvenProductPartitionRecurrence.result`
