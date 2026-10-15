# Attained complete-word widths

## Abstract

NativeSuppliedWidth

An Installation of positive width w has an arbitrary finite type of complete mutable states and an injection of all of them into the no-adjacent-ones words of length w. Each state selects a fixed literal and a successor for every raw Read reply, a genuine Update successor, a fixed-output halt, or an arbitrary deterministic source-blind internal step. Every primitive response changes at most one bit, with hold allowed. Internal transitions have no additional bit-change restriction. All states, including unreachable ones, are encoded and counted.

Feasible(S,T,w) asserts that such an installation is correct on every independent original assignment and every entry from zero through T on the single supplied skeleton. StaticFeasible additionally requires zero actual Updates on every promised successful run. The inverse capacity d(n), for positive n, is the existing stage dimension at n minus one: it is the least d with n at most fib(d+2). Thus it counts the full admissible word space. The minima a(S,T) and s(S,T) range over the entire respective classes.

Generality I: the substitution, binary no-adjacent-ones language, Fibonacci capacity and golden-ratio base are fixed. The bounds are uniform over every supplied skeleton, even leaf count and finite lag promise within this family. The logarithmic estimate relies on the instance supplier AxisConvergence.goldenRatio_pow_div_le_fib_succ; extending it to other recurrences or quadratic families requires further results.

**Theorem 1.1 (Native members of both full classes).**

$$\forall S: Source, (\forall T: Nat, ((\operatorname{mod}\left(\operatorname{length}\left(S\right), 2\right) = 0) \implies ((\operatorname{Feasible}\left(S, T, (\operatorname{dimension}\left(\operatorname{length}\left(S\right)\right)) + (7)\right)) \land (\operatorname{StaticFeasible}\left(S, T, (\operatorname{dimension}\left((\operatorname{length}\left(S\right))((\operatorname{div}\left((T) + (1), 2\right)) + (1))\right)) + (7)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth.native_upper_members` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For even h, set K=(T+1)/2 and M=h(K+1). The active and static full-table encodings are injected on every installed state and satisfy every typed primitive row, including all four raw replies. The existing original-source native executions are connected to Run in both directions. Sourcewise termination and deterministic output then give correctness, and the static table's rows exclude every actual Update. These concrete members establish nonemptiness without assuming abstract upper bounds. Since an actual source has positive leaf count, even h implies h at least two.

**Theorem 1.2 (Attainment and inverse-capacity bounds).**

$$\forall S: Source, (\forall T: Nat, ((\operatorname{mod}\left(\operatorname{length}\left(S\right), 2\right) = 0) \implies ((\operatorname{Feasible}\left(S, T, \operatorname{activeMinimum}\left(S, T\right)\right)) \land ((\forall w: Nat, ((\operatorname{Feasible}\left(S, T, w\right)) \implies (\operatorname{activeMinimum}\left(S, T\right) \leq w))) \land ((\operatorname{StaticFeasible}\left(S, T, \operatorname{staticMinimum}\left(S, T\right)\right)) \land ((\forall w: Nat, ((\operatorname{StaticFeasible}\left(S, T, w\right)) \implies (\operatorname{staticMinimum}\left(S, T\right) \leq w))) \land ((\operatorname{capacity}\left((\operatorname{length}\left(S\right)) + (2)\right) \leq \operatorname{activeMinimum}\left(S, T\right)) \land ((\operatorname{activeMinimum}\left(S, T\right) \leq (\operatorname{capacity}\left((\operatorname{length}\left(S\right)) + (1)\right)) + (7)) \land (((\operatorname{capacity}\left((\operatorname{length}\left(S\right)) + (1)\right)) + (7) \leq (\operatorname{capacity}\left((\operatorname{length}\left(S\right)) + (2)\right)) + (7)) \land ((\operatorname{capacity}\left(((\operatorname{length}\left(S\right))(\operatorname{div}\left((T) + (3), 3\right))) + (2)\right) \leq \operatorname{staticMinimum}\left(S, T\right)) \land ((\operatorname{staticMinimum}\left(S, T\right) \leq (\operatorname{capacity}\left(((\operatorname{length}\left(S\right))((\operatorname{div}\left((T) + (1), 2\right)) + (1))) + (1)\right)) + (7)) \land ((\operatorname{capacity}\left(((\operatorname{length}\left(S\right))((\operatorname{div}\left((T) + (1), 2\right)) + (1))) + (1)\right)) + (7) \leq (\operatorname{capacity}\left(((\operatorname{length}\left(S\right))(\operatorname{div}\left((T) + (3), 3\right))) + (2)\right)) + (9)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth.minimum_width_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The well-ordering of natural widths gives an attained least width in each nonempty full class. The distinct-query and static-cover counts give their lower capacity bounds. The delivered native members give the upper bounds. Capacity is monotone, and the Fibonacci recurrence gives d(2n) at most d(n)+2. Since K+1 is at most twice r=(T+3)/3, this gives the final static additive constant nine. The domain retains even h and the full lag interval for all supplied shapes.

**Theorem 1.3 (Uniform coefficient one).**

$$\forall S: Source, (\forall T: Nat, ((\operatorname{mod}\left(\operatorname{length}\left(S\right), 2\right) = 0) \implies ((\lvert \operatorname{activeMinimum}\left(S, T\right) - \operatorname{logb}\left(phi, \operatorname{length}\left(S\right)\right)\rvert  \leq 10) \land (\lvert \operatorname{staticMinimum}\left(S, T\right) - \operatorname{logb}\left(phi, (\operatorname{length}\left(S\right))((T) + (1))\right)\rvert  \leq 10))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth.uniform_logarithmic_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing golden-ratio power lower bound and the pinned Fibonacci identity bound fib(d+2) between phi to the power d and phi to the power d+1. Minimality of inverse capacity then places d(n) within one of log base phi of n. Combining the attained-width bounds with capacity doubling gives absolute error at most ten for both displayed logarithms. Ten is a proved uniform constant, independent of the skeleton, its unequal original leaf depths, h, and T. These estimates concern word width; they imply no optimum for other resource coordinates or physical cost.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth.minimum_width_bounds`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth.native_upper_members`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedWidth.uniform_logarithmic_width`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSuppliedComparison](NativeSuppliedComparison.md)
- Dependency: [D5/S3/Axis/AxisConvergence](../../../Axis/AxisConvergence.md)
