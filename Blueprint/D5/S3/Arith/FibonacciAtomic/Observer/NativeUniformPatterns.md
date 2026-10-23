# NativeUniformPatterns

## Abstract

Uniform native pattern and frontier words

A fixed token language represents Boolean leaves, pairing and reached frontier placeholders. The depth-indexed native Pattern and dependent Frontier carriers are erased only through exact reconstruction equations. No source tree or feasible source witness enters the factories. Depth and class count are arbitrary natural numbers. The factories preserve the existing enumeration order, early leaves, depth-zero frontier and the zero-class vector.

The matching Reg mirror proves typed whole-family reconstruction, variation, role sensitivity and actual observational dependence on the complete infinite domain. Contract source-selection coordinates and raw source-occurrence binding remain unregistered. No validated four-slot audit status is claimed.

**Definition 1.1 (patternWord).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.patternWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.patternWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A native pattern becomes its structural preorder constructor word. Placeholder 0 denotes a frontier position rather than a source value; its actual address is recovered structurally.

**Definition 1.2 (familyWord).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.familyWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.familyWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pattern family is represented by a finite vector in the unchanged sorted old-class order.

**Theorem 1.3 (uniform pattern words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.uniform_pattern_words`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.uniform_pattern_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One primitive recursive patternWords factory, before the depth quantifier, equals patternList d mapped through patternWord for every d. This is consumed by the uniform family factory.

**Theorem 1.4 (uniform frontier words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.uniform_frontier_words`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.uniform_frontier_words` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One primitive recursive parser frontierWords returns exactly frontierList p mapped through frontierAddress p for every native depth pattern. Its fold equation is proved by structural induction. The actual variable-table factory consumes this result.

**Theorem 1.5 (uniform pattern families).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.uniform_pattern_families`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.uniform_pattern_families` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One primitive recursive vector factory on class count and depth returns exactly allPatterns C d mapped through familyWord. A dependent List.pi enumeration equation proves fidelity to the native family. The common-input cell materializer consumes this result.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.familyWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.patternWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.uniform_frontier_words`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.uniform_pattern_families`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.uniform_pattern_words`
- Dependency: [D5/S0/Computability/PreorderTreeEvaluation](../../../../S0/Computability/PreorderTreeEvaluation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth](NativeSerialDepth.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeWholeRowPlan](NativeWholeRowPlan.md)
