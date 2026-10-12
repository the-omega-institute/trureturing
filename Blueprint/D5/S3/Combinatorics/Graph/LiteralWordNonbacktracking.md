# Literal Group Traces Exclude Immediate Backtracking

## Abstract

A literal group-product trace recovers a walk's length and successive labels; distinct consecutive involutions exclude immediate backtracking.

Let G be a group, V a type, F a simple graph on V and val any function from V to G. Let w be an actual F walk from a to b, and word a list of elements of G. mapSupport(w,val) is w.support.map(val). scanFrom(val(a),word) is List.scanl with step (x,r) mapped to x*r, including the initial value. getVert(w,i) denotes the actual vertex at natural position i, and letter(word,i) is the list entry at i under the displayed bound. Neither injectivity of val nor a Cayley graph structure on F is assumed.

**Theorem 1.1 (The Literal Trace Determines the Walk Length).**

$$\forall G \in \mathrm{Type},\; [\mathrm{Group}\left(G\right)] \forall V \in \mathrm{Type},\; \forall F \in \mathrm{SimpleGraph}\left(V\right),\; \forall val \in V \to G,\; \forall a \in V,\; \forall b \in V,\; \forall w \in \mathrm{Walk}\left(F, a, b\right),\; \forall word \in \mathrm{List}\left(G\right),\; (\mathrm{mapSupport}\left(w, val\right) = \mathrm{scanFrom}\left(\mathrm{apply}\left(val, a\right), word\right)) \Rightarrow (\mathrm{length}\left(w\right) = \mathrm{length}\left(word\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LiteralWordNonbacktracking.trace_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the mapped full support equals the literal scan, w has exactly as many edges as word has letters. Both lists contain one more entry than those lengths, so equality of their lengths gives the result.

**Theorem 1.2 (The Literal Trace Determines Each Group Step).**

$$\forall G \in \mathrm{Type},\; [\mathrm{Group}\left(G\right)] \forall V \in \mathrm{Type},\; \forall F \in \mathrm{SimpleGraph}\left(V\right),\; \forall val \in V \to G,\; \forall a \in V,\; \forall b \in V,\; \forall w \in \mathrm{Walk}\left(F, a, b\right),\; \forall word \in \mathrm{List}\left(G\right),\; (\mathrm{mapSupport}\left(w, val\right) = \mathrm{scanFrom}\left(\mathrm{apply}\left(val, a\right), word\right)) \Rightarrow (\forall i \in \mathrm{Nat},\; (i < \mathrm{length}\left(word\right)) \Rightarrow (\mathrm{apply}\left(val, \mathrm{getVert}\left(w, i + 1\right)\right) = \mathrm{apply}\left(val, \mathrm{getVert}\left(w, i\right)\right) \cdot \mathrm{letter}\left(word, i\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LiteralWordNonbacktracking.trace_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every index i below word.length, val(getVert(w,i+1)) is val(getVert(w,i))*letter(word,i). The length identity places both vertices within the support, and the scan's successor equation supplies this step.

**Theorem 1.3 (Distinct Consecutive Involutions Exclude Backtracking).**

$$\forall G \in \mathrm{Type},\; [\mathrm{Group}\left(G\right)] \forall V \in \mathrm{Type},\; \forall F \in \mathrm{SimpleGraph}\left(V\right),\; \forall val \in V \to G,\; \forall a \in V,\; \forall b \in V,\; \forall w \in \mathrm{Walk}\left(F, a, b\right),\; \forall word \in \mathrm{List}\left(G\right),\; ((\mathrm{mapSupport}\left(w, val\right) = \mathrm{scanFrom}\left(\mathrm{apply}\left(val, a\right), word\right)) \land ((\forall x \in G,\; (x \in word) \Rightarrow (x \cdot x = 1)) \land (\forall i \in \mathrm{Nat},\; (i + 1 < \mathrm{length}\left(word\right)) \Rightarrow (\mathrm{letter}\left(word, i\right) \ne \mathrm{letter}\left(word, i + 1\right))))) \Rightarrow (\forall i \in \mathrm{Nat},\; (i + 2 \le \mathrm{length}\left(w\right)) \Rightarrow (\mathrm{getVert}\left(w, i\right) \ne \mathrm{getVert}\left(w, i + 2\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LiteralWordNonbacktracking.trace_nonbacktracking` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the exact full support trace, that each letter x satisfies x*x=1, and that consecutive letters differ. Then the actual vertices at i and i+2 differ whenever i+2 is within w.length. If they coincided, mapping their equality through val and using the two exact steps would give x*y=1. Multiplication by the involutive second letter forces x=y, contradicting the consecutive-letter hypothesis.

This result applies to any actual graph walk with such a trace. It proves exclusion of immediate backtracking. Simplicity and complete component coverage require additional graph conditions, such as the degree and leaf hypotheses for leaf walks.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LiteralWordNonbacktracking.trace_length`
- Truth anchor: `D5/S3/Combinatorics/Graph/LiteralWordNonbacktracking.trace_nonbacktracking`
- Truth anchor: `D5/S3/Combinatorics/Graph/LiteralWordNonbacktracking.trace_step`
