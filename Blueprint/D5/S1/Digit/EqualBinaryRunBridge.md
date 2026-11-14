# Equal Binary Run Pairs

## Abstract

Unique positive-part encodings of literal maximal binary run pairs; the A386705 recurrence remains a target.

The source is the full OEIS A386705 record at https://raw.githubusercontent.com/oeis/oeisdata/30c383550c8059b1712df8e32827d3b203765933/seq/A386/A386705.seq. Its NAME is: a(n) = sum of the 2^(n-1) even positive integers having bit length 2*n and in which, when written in binary, each run of 0's is of exactly the same length as the run of 1's immediately before it. Its FORMULA is: Empirical: a(n) = 12*a(n-1) - 36*a(n-2) + 32*a(n-3), with a(1) = 2, a(2) = 22, a(3) = 192. The A166751 comment already associates zero runs with compositions. The construction below does not claim that observation as new.

All indices and represented positive integers are natural numbers. bits(m) reverses Nat.digits 2 m, giving the canonical most significant digit first word. splitBy with Boolean equality forms the actual maximal constant runs. Matched([]) is true; Matched([r]) is false; Matched(o::z::rest) requires every entry of o to be one, every entry of z to be zero, equal lengths, and Matched(rest). Every run returned by splitBy is nonempty. On a positive even canonical binary word, this says exactly that each maximal zero run matches the preceding maximal one run.

Literal(n,m) requires m positive and even, bits(m) of length exactly 2*n, and Matched of its maximal runs. row(n) filters the finite set of naturals below 2^(2*n) by Literal(n,m). The digit bound is proved in mem_row_iff, so this bound omits no literal member. a(n) sums the distinct members of row(n), casting each member to the integers. All arithmetic in the target recurrence is integer arithmetic; natural subtraction is used only in indices under n>=4.

blockRuns([]) is empty. blockRuns(k::ks) consists of k ones, then k zeros, then blockRuns(ks). word(ks) flattens this list of runs. Positive(ks) below means every member is strictly positive. The proved maximal-run identity uses Mathlib's splitBy_flatten and its chain conditions, including the zero-to-one boundaries between successive pairs. Reconstruction uses the literal Matched predicate; equal encoded words have equal maximal runs and hence equal part lists.

**Theorem 1.1 (Unique literal encoding).**

$$\forall n \in Nat,\; \forall m \in Nat,\; m \in row\left(n\right) \iff 0 < m \land \left(Even\left(m\right) \land \left(\exists p \in List\left(Nat\right),\; \left(Positive\left(p\right) \land \left(sum\left(p\right) = n \land bits\left(m\right) = word\left(p\right)\right)\right) \land \left(\forall q \in List\left(Nat\right),\; \left(Positive\left(q\right) \land \left(sum\left(q\right) = n \land bits\left(m\right) = word\left(q\right)\right)\right) \Rightarrow q = p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/EqualBinaryRunBridge.mem_row_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is a membership characterization for the actual set of integers. It proves existence and uniqueness of positive part lengths; it assumes neither a composition count nor an identity for the sum over those lengths. Positivity and evenness of the represented integer remain explicit on both sides.

**Definition 1.2 (Complete recurrence target).**

$$FullClaim \iff a\left(1\right) = 2 \land \left(a\left(2\right) = 22 \land \left(a\left(3\right) = 192 \land \left(\forall n \in Nat,\; 4 \le n \Rightarrow a\left(n\right) = 12 \cdot a\left(n - 1\right) - 36 \cdot a\left(n - 2\right) + 32 \cdot a\left(n - 3\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/EqualBinaryRunBridge.FullClaim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FullClaim is a proposition definition, not a proved theorem. The three initial values and the recurrence for every n>=4 remain unproved here. Further work must transport the distinct integer sum through the unique encoding, derive its weighted first-part identity, and prove the integer recurrence. No finite-prefix result substitutes for this target.

## References

- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.FullClaim`
- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.mem_row_iff`
