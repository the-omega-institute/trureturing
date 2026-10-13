# NativeUniformAnalysis

## Abstract

NativeUniformAnalysis

The exact serialization retains every raw pattern cell, its original variable table, feasibility, symbolic exterior, reached addresses, ordered pair plans, pass flag and summed template cost. The whole bundle preserves all four native summary fields and K0 = 2*k*(2^d-1) + maximum feasible-cell template cost. Empty sums and no feasible cells use the original native zero conventions.

**Definition 1.1 (templateLeaves).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.templateLeaves`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.templateLeaves` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count Boolean leaves in a template word, matching the native ground-template cost rather than the number of constructor tokens.

**Definition 1.2 (codedCellBudget).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.codedCellBudget`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.codedCellBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum every stored binding template cost over the ordered pair plans, retaining repeated bindings.

**Definition 1.3 (exteriorHasVariable).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.exteriorHasVariable`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.exteriorHasVariable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Test whether the symbolic exterior still contains any residual ordinal variable.

**Definition 1.4 (materializeCell).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.materializeCell`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.materializeCell` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retain the pattern words, variable keys, finite-history feasibility flag, exact symbolic exterior and reached-address order, pair codes, pass flag and template budget. The synthetic history filling assigns the fixed Boolean leaf to each residual variable; old legality tests the entire disequality list.

**Definition 1.5 (nativeCellCode).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.nativeCellCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.nativeCellCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The reference serialization retains the native feasible flag, symbolic exterior, ordered reached addresses, pair plans, pass flag and full template budget for each raw cell.

**Definition 1.6 (nativeAnalysisCode).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.nativeAnalysisCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.nativeAnalysisCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retain all raw cells in their native order together with the four existing analyze fields and the native K0 value. This reference bundle has no epoch argument.

**Definition 1.7 (materializeAnalysis).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.materializeAnalysis`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.materializeAnalysis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parse the common input and enumerate its complete raw cell list. Retain every cell, filter by computed feasibility, and aggregate raw and feasible counts, the universal pass flag and the maximum template budget. The budget projection is twice the class count times two to the required depth minus one, plus the template maximum. Malformed encodings return none. Contradictory histories remain valid computational inputs.

**Theorem 1.8 (materialize_analysis_exact).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.materialize_analysis_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.materialize_analysis_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every encoded common input yields exactly the full original native analysis serialization and K0, uniformly in the unused epoch N. All raw cells remain present with their feasibility flags.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.codedCellBudget`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.exteriorHasVariable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.materializeAnalysis`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.materializeCell`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.materialize_analysis_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.nativeAnalysisCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.nativeCellCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.templateLeaves`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax](NativeUniformSyntax.md)
