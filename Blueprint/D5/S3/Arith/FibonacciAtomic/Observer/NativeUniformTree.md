# NativeUniformTree

## Abstract

NativeUniformTree

All tree operations use fixed preorder codes. Decreasing recursion carries addresses through symbolic cutting, and finite iteration evaluates each actual history epoch. The computation accepts every finite address and history without a consistency premise.

**Theorem 1.1 (term_at_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.term_at_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.term_at_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive recursive address navigation returns exactly the original native subtree option on every finite term and address.

**Theorem 1.2 (tree_word_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.tree_word_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.tree_word_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed tree instance makes its preorder constructor word primitive recursive. The constructor word supplies recursion measures and output words.

**Theorem 1.3 (symbolic_exterior_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.symbolic_exterior_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.symbolic_exterior_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive recursion on decreasing subtree words constructs the exact symbolic exterior while carrying original inherited addresses. Cut holes and every residual variable are retained.

**Theorem 1.4 (readout_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.readout_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.readout_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original native four-valued readout is primitive recursive on every finite address and actual Source, including the empty address and blocked suffixes.

**Theorem 1.5 (substitution_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.substitution_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.substitution_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original leaf substitution, extended over actual ordered pairs, is primitive recursive on the fixed native tree representation. Natural iteration evaluates arbitrary supplied counts.

**Theorem 1.6 (history_consistent_prim).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.history_consistent_prim`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.history_consistent_prim` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Primitive recursion computes each requested substitution epoch and exact readout, then checks every finite history entry. Empty histories, repeated observations, absent replies and inconsistent histories remain in scope.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.history_consistent_prim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.readout_prim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.substitution_prim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.symbolic_exterior_prim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.term_at_prim`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.tree_word_prim`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformSyntax](NativeUniformSyntax.md)
