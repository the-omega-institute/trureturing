# NativeUniformSyntax

## Abstract

NativeUniformSyntax

Original old-class names and frontier addresses determine the finite syntax. Repeated class occurrences share their reconstructed term, and the complete old-disequality list stays separate from the singleton equation sent to unification. The original native presentation is connected to finite ordinals through its actual variable-list enumeration.

**Theorem 1.1 (tree_of_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.tree_of_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.tree_of_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixed preorder codes admit primitive recursive leaf construction. Leaf construction supplies the syntax and tree algorithms.

**Theorem 1.2 (tree_mul_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.tree_mul_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.tree_mul_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixed preorder codes admit primitive recursive binary construction. The construction joins serialized subtrees without changing order.

**Definition 1.3 (prefixKeys).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.prefixKeys`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.prefixKeys` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Prefix the original frontier address without changing its old class label.

**Definition 1.4 (ordinalTerm).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.ordinalTerm`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.ordinalTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Replace each original class-address key by its position in the cell variable table, retaining every Boolean constructor and repeated occurrence.

**Definition 1.5 (oldCode).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.oldCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.oldCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Parse the class pattern word and reconstruct its original frontier keys. Missing class words and malformed pattern words return none.

**Definition 1.6 (cellSyntax).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.cellSyntax`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.cellSyntax` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the sorted native class names, exact pattern-family words and the original variable-key list.

**Definition 1.7 (cellTerm).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.cellTerm`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.cellTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Translate a native cell term through its original keys and their ordinals.

**Definition 1.8 (wholeCode).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.wholeCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.wholeCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Expand every occurrence of an old class with the same class term. Boolean leaves and the ordered tree structure remain explicit.

**Theorem 1.9 (whole_code_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.whole_code_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.whole_code_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The structural expansion of a finite literal row is primitive recursive in its finite pattern and variable tables.

**Theorem 1.10 (whole_code_exact).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.whole_code_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.whole_code_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reconstruction through the original class table produces exactly the ordinal translation of the native whole term, preserving repeated class occurrences.

**Definition 1.11 (namePairs).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.namePairs`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.namePairs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List every pair of distinct old numeric classes once, in native class order with the smaller name first.

**Definition 1.12 (traverseCodes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.traverseCodes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.traverseCodes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Traverse a finite list in order, returning none if any component is malformed. The finite cursor proof uses computable natural-number recursion and permits computable callbacks.

**Theorem 1.13 (traverse_computable).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.traverse_computable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.traverse_computable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite traversal of computable partial callbacks is computable and preserves list order. The explicit cursor and natural recursion allow a merely computable native solver.

**Theorem 1.14 (traverse_map_exact).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.traverse_map_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.traverse_map_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An exact component correspondence transports through ordered traversal. This correspondence relates generated finite words to native pattern families and pair plans.

**Definition 1.15 (deltaCode).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.deltaCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.deltaCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reconstruct the complete ordered old-disequality list from class pattern words. These pairs are checked after unifying a singleton new equality; they are never supplied as extra equalities.

**Theorem 1.16 (delta_code_exact).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.delta_code_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.delta_code_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generated old inequalities coincide with the entire native ordered disequality list after variable translation.

**Theorem 1.17 (delta_code_computable).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.delta_code_computable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.delta_code_computable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Computably reconstruct every ordered old-disequality pair using the same class terms used by the whole row.

**Theorem 1.18 (syntax_legal_code_exact).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.syntax_legal_code_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.syntax_legal_code_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full ordinal disequality test is equivalent to native syntax legality, using injectivity of original class-address coordinates. No old disequality is dropped or passed to the unifier as an equality.

**Definition 1.19 (nativePairCode).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.nativePairCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.nativePairCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Serialize the native plan with original cell ordinals, both addresses, the exact branch and ordered ground template words.

**Theorem 1.20 (native_pair_exact).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.native_pair_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.native_pair_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original native pattern cell, the computable singleton-equation plan equals the exact original presentation plan, including the fully composed action and actual bound-variable domain.

**Theorem 1.21 (cell_term_rename).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.cell_term_rename`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.cell_term_rename` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The syntax reconstruction agrees with renaming each original variable by its unique position in the native variable list. This equality connects syntax to presentation transport.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.cellSyntax`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.cellTerm`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.cell_term_rename`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.deltaCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.delta_code_computable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.delta_code_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.namePairs`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.nativePairCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.native_pair_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.oldCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.ordinalTerm`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.prefixKeys`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.syntax_legal_code_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.traverseCodes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.traverse_computable`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.traverse_map_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.tree_mul_prim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.tree_of_prim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.wholeCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.whole_code_exact`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax.whole_code_prim`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPlan](NativeUniformPlan.md)
