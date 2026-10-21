# Numbered finite-window transport

## Abstract

Exact state histories and words of canonical numbered windows.

**Theorem 1.1 (Realization on the exact canonical window).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport.history_trace`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport.history_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an incoming lift L, a bilateral numbered path x and a compatible state history r, lifting the canonical length-d window ending at r(i+d) returns r(i), for every natural d including zero and every signed i. The endpoint is the source of x(i+d).

The successor proof applies the canonical tail relation, identifies the intermediate state subtype by Subtype.ext, transports the actual first edge along adjacency, and applies the supplied one-edge compatibility. This identifies realization on the exact canonical dependent window, rather than on an unspecified path with the same length or endpoints.

**Theorem 1.2 (Exact numbered window tabulation).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport.window_word`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport.window_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The word of window(x,d,i) is List.ofFn(j : Fin d => x(i+j)). Zero gives the empty word. In the successor step equality elimination recovers the actual first edge including its number; the tail relation and List.ofFn_succ identify the complete shifted word. Endpoints, length and lift action alone do not determine these numbered coordinates.

**Theorem 1.3 (Dependent reversal preserves the exact reversed word).**

Lean statement: `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport.reverse_word`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport.reverse_word` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every endpoint-indexed finite path alpha, pathWord(reverseFinitePath alpha) is reverse(pathWord alpha) mapped by endpoint reversal, retaining every parallel-edge number. The successor applies the original word_appendPath relation, the arbitrary-tail reversal relation and the list reversal laws.

Combining this reversal relation with canonical window tabulation gives the signed past word reverse(List.ofFn(j : Fin d => x(i-j-1))). The canonical history relation supplies the state identifications in Full62.certificate_formulas; the future and past word relations supply the exact words in Full62.whole_certificate. All relations include d=0 and arbitrary signed i.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport.history_trace`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport.reverse_word`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced/FiniteWindowWordTransport.window_word`
- Dependency: [D5/S3/ConceptDynamics/Coding/OriginalAlignedBalanced](../OriginalAlignedBalanced.md)
