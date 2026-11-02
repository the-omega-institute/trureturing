# Certified exact original-node memoization

## Abstract

Certified exact original-node memoization

Eight exact original decoder equations support transparent memoization. Each stored complete output carries a proof for its exact input; the lookup proposal is checked against the whole key before reuse.

The module has instance generality because its concrete decoder size, symmetry actions and eight literal keys belong to the original EJM DAG. The nested ExactMemo statements remain quantified over arbitrary key and output types, including function-valued outputs. The concrete application reduces original node decoding in suffix checks.

Original suffix consumers use check_eq_original to transport a memoized decision to the unchanged Accepted proposition. Every caller retains the entire remaining fuel, original finite index, actual cache and partial assignment. The function equality supplies no context's acceptance by itself.

Only complete decoder outputs are shared. Bound leaves still test the current cache lower bound; symmetry leaves still test domination on the current partial assignment; splits still update the full cache and partial assignment along all four actual values. Equal node keys do not transfer acceptance between distinct contexts.

Bound-constructor soundness follows the argument used in Tail442V2.Helper. Split soundness uses the existing FiniteCachedSymmetryDAGReplay.checked_split_node theorem. The three symmetry receipts compare the complete original Cut, and split equations retain every child of the literal node.

The eight full-node equations are the numeric-reduction premises. Every other key falls back to the original decoder. A successful suffix decision must still establish all original acceptance predicates for its own context; decoder equality does not replace those decisions.

**Definition 1.1 (Exact input and complete output certificate).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.Receipt`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.Receipt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A receipt stores an input, an output and a proof that the output equals the actual function at that exact input. The output type is arbitrary, so a literal node may contain a child function.

**Definition 1.2 (Select a certified output or evaluate the original function).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoStep`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Any selector may return no receipt or propose a receipt. Reuse first requires equality of the complete receipt input and the actual key. A missing or mismatched proposal evaluates the original function. No property of the selector is assumed.

**Theorem 1.3 (Exact memoization preserves every output).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoStep_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoStep_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary key and output types with decidable key equality, every selector and every input, memoStep equals the original function. The proof uses the receipt equation only after complete input equality. No equality instance for outputs is required.

**Theorem 1.4 (The memoized and original functions are equal).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoStep_fun_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoStep_fun_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Function extensionality turns the pointwise receipt soundness theorem into equality of the complete functions. This is a computation-preserving equality, not an acceptance assertion.

**Definition 1.5 (The complete original EJM node type).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.ReplayNode`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.ReplayNode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The node type retains the original DAG size, twenty coordinates, four values and complete original symmetry Cut. Split nodes retain the whole child function.

**Definition 1.6 (Keep remaining fuel and the original finite index).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.Key`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.Key` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The memo key is the pair of a natural remaining fuel and the original finite node index. Fuel remains part of the key because the original split decoder checks its coordinate against remaining fuel.

**Definition 1.7 (Read the original fuel-indexed decoder).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.actual`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.actual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual function applies the unchanged EJMOriginalGlobalDAGData.nodes to both components of the complete key.

**Definition 1.8 (Original node index zero).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.zeroIndex`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.zeroIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the finite original DAG index zero. Its receipt certifies decoder output only; each caller still computes its own acceptance predicate.

**Definition 1.9 (Every value has original child index zero).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.zeroChildren`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.zeroChildren` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal child function sends each of the four values to the original node zero. It records all four edges, including their multiplicity.

**Definition 1.10 (Literal bound constructor).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.boundNode`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.boundNode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proposed output is the bound constructor. The checker still evaluates its lower-bound comparison on the current full cache.

**Definition 1.11 (Coordinate eighteen with four zero children).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.split18Node`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.split18Node` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal split retains original coordinate eighteen and the entire constant-zero child function.

**Definition 1.12 (Coordinate nineteen with four zero children).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.split19Node`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.split19Node` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal split retains original coordinate nineteen and the entire constant-zero child function.

**Definition 1.13 (Tag twenty-four with pivot twelve).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry12`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry12` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete original Cut is decoded from tag twenty-four and pivot twelve. The tag selects source action one and outcome action zero.

**Definition 1.14 (Tag twenty-four with pivot thirteen).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry13`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry13` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete original Cut uses the same source and outcome actions with original pivot thirteen.

**Definition 1.15 (Tag twenty-four with pivot fourteen).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry14`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry14` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The complete original Cut uses the same source and outcome actions with original pivot fourteen.

**Definition 1.16 (Literal symmetry node with pivot twelve).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry12Node`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry12Node` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The node contains the complete symmetry12 Cut. Domination is still checked against each actual partial assignment.

**Definition 1.17 (Literal symmetry node with pivot thirteen).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry13Node`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry13Node` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The node contains the complete symmetry13 Cut. Its action and pivot are retained in full.

**Definition 1.18 (Literal symmetry node with pivot fourteen).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry14Node`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry14Node` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The node contains the complete symmetry14 Cut. The memo shares decoder output, while each occurrence keeps its original domination check.

**Theorem 1.19 (Fuel two and node zero decode to bound).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_0`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exact remaining fuel two and original index zero, the unchanged original decoder equals the complete bound literal. The proof recovers constructor equality from the kernel-checked bound-constructor receipt.

**Theorem 1.20 (Fuel one and node zero decode to bound).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_1_0`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_1_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exact remaining fuel one and original index zero, the unchanged original decoder equals the bound literal.

**Theorem 1.21 (Fuel three and node 442 give the full coordinate-eighteen split).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_442`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_442` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original node at remaining fuel three and index 442 equals the split at coordinate eighteen with zero as every value child. The existing checked_split_node soundness theorem retains the whole child function.

**Theorem 1.22 (Fuel three and node zero decode to bound).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_0`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exact remaining fuel three and original index zero, the unchanged original decoder equals the bound literal.

**Theorem 1.23 (Fuel three and node 112 retain the pivot-thirteen symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_112`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_112` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original node equals the complete tag-twenty-four, pivot-thirteen symmetry literal. The private checker compares the entire Cut, including its source action, outcome action and pivot.

**Theorem 1.24 (Fuel four and node 295 retain the pivot-twelve symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_4_295`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_4_295` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original node at remaining fuel four and index 295 equals the complete tag-twenty-four, pivot-twelve symmetry literal.

**Theorem 1.25 (Fuel two and node 57 retain the pivot-fourteen symmetry).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_57`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_57` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original node at remaining fuel two and index 57 equals the complete tag-twenty-four, pivot-fourteen symmetry literal.

**Theorem 1.26 (Fuel two and node 33 give the full coordinate-nineteen split).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_33`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_33` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original node at remaining fuel two and index 33 equals the split at coordinate nineteen with zero as every value child. Its finite receipt checks the coordinate and every child.

**Definition 1.27 (Certified complete output for fuel 2 and node 0).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_2_0`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_2_0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent receipt stores exact key (2, 0) and its full bound literal. Its correctness field is the symmetric form of node_2_0; the proof field supplies no executable selector authority.

**Definition 1.28 (Certified complete output for fuel 1 and node 0).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_1_0`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_1_0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent receipt stores exact key (1, 0) and its full bound literal. Its correctness field is the symmetric form of node_1_0; the proof field supplies no executable selector authority.

**Definition 1.29 (Certified complete output for fuel 3 and node 442).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_3_442`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_3_442` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent receipt stores exact key (3, 442) and its full coordinate-eighteen split literal. Its correctness field is the symmetric form of node_3_442; the proof field supplies no executable selector authority.

**Definition 1.30 (Certified complete output for fuel 3 and node 0).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_3_0`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_3_0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent receipt stores exact key (3, 0) and its full bound literal. Its correctness field is the symmetric form of node_3_0; the proof field supplies no executable selector authority.

**Definition 1.31 (Certified complete output for fuel 3 and node 112).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_3_112`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_3_112` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent receipt stores exact key (3, 112) and its full pivot-thirteen symmetry literal. Its correctness field is the symmetric form of node_3_112; the proof field supplies no executable selector authority.

**Definition 1.32 (Certified complete output for fuel 4 and node 295).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_4_295`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_4_295` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent receipt stores exact key (4, 295) and its full pivot-twelve symmetry literal. Its correctness field is the symmetric form of node_4_295; the proof field supplies no executable selector authority.

**Definition 1.33 (Certified complete output for fuel 2 and node 57).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_2_57`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_2_57` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent receipt stores exact key (2, 57) and its full pivot-fourteen symmetry literal. Its correctness field is the symmetric form of node_2_57; the proof field supplies no executable selector authority.

**Definition 1.34 (Certified complete output for fuel 2 and node 33).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_2_33`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_2_33` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent receipt stores exact key (2, 33) and its full coordinate-nineteen split literal. Its correctness field is the symmetric form of node_2_33; the proof field supplies no executable selector authority.

**Definition 1.35 (Propose exactly eight original decoder receipts).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.lookup`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.lookup` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent selector proposes the eight listed fuel-index pairs and returns no receipt elsewhere. ExactMemo.memoStep independently checks the whole key before reuse, so selector correctness is not a soundness premise.

**Definition 1.36 (Use literals on certified hits and the original decoder on every miss).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoNodes`

*Formalization.* `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoNodes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The transparent memoized decoder evaluates the exact receipt mechanism on the full fuel-index pair. No actual cache, partial assignment or acceptance theorem appears in the memo key or the stored outputs.

**Theorem 1.37 (Every memoized node equals its complete original node).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoNodes_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoNodes_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural fuel and every original finite index, memoNodes equals the unchanged original nodes decoder. The equation covers hits, misses, mismatches and all fuel values.

**Theorem 1.38 (Equality of the whole fuel-indexed decoder functions).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.nodes_fun_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.nodes_fun_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two applications of function extensionality turn pointwise node equality into equality of the complete original and memoized decoder functions. All original constructor fields, including child functions, are preserved.

**Theorem 1.39 (The complete actual-context checker is unchanged).**

Lean statement: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.check_eq_original`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.check_eq_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every remaining fuel, original index, full cache and full partial assignment, the existing checker using memoNodes equals the checker using the original decoder. Function congruence preserves the original step, lower, domination predicate, scale and exhaustive value branches without unfolding the fallback decoder in this transport proof.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.Key`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.Receipt`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.ReplayNode`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.actual`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.boundNode`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.check_eq_original`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.lookup`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoNodes`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoNodes_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoStep`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoStep_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.memoStep_fun_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_1_0`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_0`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_33`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_2_57`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_0`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_112`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_3_442`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.node_4_295`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.nodes_fun_eq`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_1_0`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_2_0`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_2_33`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_2_57`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_3_0`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_3_112`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_3_442`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.receipt_4_295`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.split18Node`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.split19Node`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry12`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry12Node`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry13`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry13Node`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry14`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.symmetry14Node`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.zeroChildren`
- Truth anchor: `D5/S3/Quantum/Entanglement/EJM/EJMOriginalNodeMemo.zeroIndex`
- Dependency: [D5/S3/Quantum/Entanglement/EJM/EJMOriginalReplayAssembly](EJMOriginalReplayAssembly.md)
