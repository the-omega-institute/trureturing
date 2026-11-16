# Equal Binary Run Pairs

## Abstract

Literal maximal binary run pairs have unique positive-part encodings, and their distinct integer sums satisfy the A386705 recurrence.

The source is the full OEIS A386705 record at https://raw.githubusercontent.com/oeis/oeisdata/30c383550c8059b1712df8e32827d3b203765933/seq/A386/A386705.seq. Its NAME is: a(n) = sum of the 2^(n-1) even positive integers having bit length 2*n and in which, when written in binary, each run of 0's is of exactly the same length as the run of 1's immediately before it. Its FORMULA is: Empirical: a(n) = 12*a(n-1) - 36*a(n-2) + 32*a(n-3), with a(1) = 2, a(2) = 22, a(3) = 192. The A166751 comment already associates zero runs with compositions. The construction below does not claim that observation as new.

All indices and represented positive integers are natural numbers. bits(m) reverses Nat.digits 2 m, giving the canonical most significant digit first word. splitBy with Boolean equality forms the actual maximal constant runs. Matched([]) is true; Matched([r]) is false; Matched(o::z::rest) requires every entry of o to be one, every entry of z to be zero, equal lengths, and Matched(rest). Every run returned by splitBy is nonempty. On a positive even canonical binary word, this says exactly that each maximal zero run matches the preceding maximal one run.

Literal(n,m) requires m positive and even, bits(m) of length exactly 2*n, and Matched of its maximal runs. row(n) filters the finite set of naturals below 2^(2*n) by Literal(n,m). The digit bound is proved in mem_row_iff, so this bound omits no literal member. a(n) sums the distinct members of row(n), casting each member to the integers. All arithmetic in the target recurrence is integer arithmetic; natural subtraction is used only in indices under n>=4.

blockRuns([]) is empty. blockRuns(k::ks) consists of k ones, then k zeros, then blockRuns(ks). word(ks) flattens this list of runs. Positive(ks) below means every member is strictly positive. The proved maximal-run identity uses Mathlib's splitBy_flatten and its chain conditions, including the zero-to-one boundaries between successive pairs. Reconstruction uses the literal Matched predicate; equal encoded words have equal maximal runs and hence equal part lists.

Decoding word(ks) with Nat.ofDigits recovers exactly its canonical bits when all parts are positive. A nonempty such word starts in one and ends in zero, so its decoded integer is positive and even. The finite set parts(n) is the image of Mathlib's Composition(n) under its blocks projection. Its members are precisely the positive lists summing to n; composition_card supplies its cardinality. The all-ones digit identity is reused directly from ones_value in D5.S1.Words.DoubleTailShuffleSupport. For n>0, row(n) is the image of parts(n) under decoding, and decoding is injective on that set. Consequently a(n) equals the integer sum of decoded composition words with no repeated integer counted twice.

For n>=1, write W(n) for the sum of decoded words over parts(n), T(n) for the sum of decoded tails, E(n) for the sum of 2^k*4^r, where k is the first part and r is the sum of the remaining parts, and U(n)=4^n*2^(n-1). Every composition of n+1 is uniquely either 1::ks or grow(ks), for a composition ks of n; grow increments the first part. These two images are disjoint. The decoded value of k::ks is (4^k-2^k)*4^sum(ks)+value(ks), in the integers. Summing over the two images gives W(n+1)=5W(n)+2U(n)+2E(n)-3T(n), T(n+1)=W(n)+T(n), E(n+1)=2U(n)+2E(n), and U(n+1)=8U(n). The initial data W(1)=2, T(1)=0, E(1)=2 yield the invariant W(n)-T(n)+E(n)=U(n). Thus W(n+1)=2W(n)-E(n)+5U(n); eliminating E and U proves W(n+3)=12W(n+2)-36W(n+1)+32W(n). The same identities give W(2)=22 and W(3)=192. The injective sum transport identifies W(n) with the literal a(n), rather than defining a(n) by these equations.

**Definition 1.1 (Canonical binary digits).**

$$\forall m \in Nat,\; bits\left(m\right) = \operatorname{List.reverse}\left(\operatorname{Nat.digits}\left(2, m\right)\right)$$

*Formalization.* `D5/S1/Digit/EqualBinaryRunBridge.bits` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Xausa (2025). *OEIS A386705: sums of even integers with equally paired maximal binary runs*. URL: <https://oeis.org/A386705>.

*Commentary.*

The result is a list of natural-number digits in most significant digit first order. The definition includes m=0, whose digit list is empty.

**Definition 1.2 (Matching successive run pairs).**

$$\begin{aligned}Matched\left([]\right) \iff True\\\forall r \in List\left(Nat\right),\; Matched\left(\operatorname{List.cons}\left(r, []\right)\right) \iff False\\\forall o \in List\left(Nat\right),\; \forall z \in List\left(Nat\right),\; \forall rest \in List\left(List\left(Nat\right)\right),\; Matched\left(\operatorname{List.cons}\left(o, \operatorname{List.cons}\left(z, rest\right)\right)\right) \iff \left(\forall d \in Nat,\; d \in o \Rightarrow d = 1\right) \land \left(\left(\forall d \in Nat,\; d \in z \Rightarrow d = 0\right) \land \left(\operatorname{List.length}\left(o\right) = \operatorname{List.length}\left(z\right) \land Matched\left(rest\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Digit/EqualBinaryRunBridge.Matched` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Xausa (2025). *OEIS A386705: sums of even integers with equally paired maximal binary runs*. URL: <https://oeis.org/A386705>.

*Commentary.*

These three equations cover every list of runs. The singleton case is false. The paired case does not itself require nonempty runs: empty runs are allowed here. Nonemptiness in Literal comes from splitting the canonical word into maximal runs.

**Definition 1.3 (Literal source membership).**

$$\forall n \in Nat,\; \forall m \in Nat,\; Literal\left(n, m\right) \iff 0 < m \land \left(Even\left(m\right) \land \left(\operatorname{List.length}\left(bits\left(m\right)\right) = 2 \cdot n \land Matched\left(\operatorname{List.splitBy}\left(\lambda (x: Nat) (y: Nat) \mapsto (\operatorname{BEq.beq}\left(x, y\right): Bool), bits\left(m\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/EqualBinaryRunBridge.Literal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Xausa (2025). *OEIS A386705: sums of even integers with equally paired maximal binary runs*. URL: <https://oeis.org/A386705>.

*Commentary.*

The Boolean comparator BEq.beq tests equality of natural-number digits. List.splitBy retains the word order and groups adjacent equal digits. Both n and m range over all naturals, including zero; positivity is an explicit conjunct.

**Definition 1.4 (Finite set of literal integers).**

$$\forall n \in Nat,\; row\left(n\right) = \operatorname{Finset.filter}\left(Literal\left(n\right), \operatorname{Finset.range}\left(2^{2 \cdot n}\right)\right)$$

*Formalization.* `D5/S1/Digit/EqualBinaryRunBridge.row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Xausa (2025). *OEIS A386705: sums of even integers with equally paired maximal binary runs*. URL: <https://oeis.org/A386705>.

*Commentary.*

The result has type Finset Nat. Finset.range excludes its upper bound, and Finset.filter keeps exactly those members satisfying Literal. This includes row zero.

**Definition 1.5 (Distinct integer sum).**

$$\forall n \in Nat,\; a\left(n\right) = \sum_{(m: Nat) \in row\left(n\right)} (m: \mathbb{Z})$$

*Formalization.* `D5/S1/Digit/EqualBinaryRunBridge.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Xausa (2025). *OEIS A386705: sums of even integers with equally paired maximal binary runs*. URL: <https://oeis.org/A386705>.

*Commentary.*

The sum is indexed by the finite set row(n), so each natural-number member occurs once. Each summand is explicitly cast to the integers; an empty row has sum zero.

**Definition 1.6 (Ordered one-zero block pairs).**

$$\begin{aligned}blockRuns\left([]\right) = []\\\forall k \in Nat,\; \forall ks \in List\left(Nat\right),\; blockRuns\left(\operatorname{List.cons}\left(k, ks\right)\right) = \operatorname{List.cons}\left(\operatorname{List.replicate}\left(k, 1\right), \operatorname{List.cons}\left(\operatorname{List.replicate}\left(k, 0\right), blockRuns\left(ks\right)\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Digit/EqualBinaryRunBridge.blockRuns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Xausa (2025). *OEIS A386705: sums of even integers with equally paired maximal binary runs*. URL: <https://oeis.org/A386705>.

*Commentary.*

List.cons prepends one whole run. Each part contributes its run of ones before its run of zeros. The equations apply to every natural k, including k=0, which contributes two empty runs; no positivity hypothesis is imposed by this definition.

**Definition 1.7 (Concatenated block word).**

$$\forall ks \in List\left(Nat\right),\; word\left(ks\right) = \operatorname{List.flatten}\left(blockRuns\left(ks\right)\right)$$

*Formalization.* `D5/S1/Digit/EqualBinaryRunBridge.word` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paolo Xausa (2025). *OEIS A386705: sums of even integers with equally paired maximal binary runs*. URL: <https://oeis.org/A386705>.

*Commentary.*

The input is any list of natural part lengths. List.flatten concatenates its runs in order, including empty runs; the empty input gives the empty word.

**Theorem 1.8 (Unique literal encoding).**

$$\forall n \in Nat,\; \forall m \in Nat,\; m \in row\left(n\right) \iff 0 < m \land \left(Even\left(m\right) \land \left(\exists p \in List\left(Nat\right),\; \left(Positive\left(p\right) \land \left(sum\left(p\right) = n \land bits\left(m\right) = word\left(p\right)\right)\right) \land \left(\forall q \in List\left(Nat\right),\; \left(Positive\left(q\right) \land \left(sum\left(q\right) = n \land bits\left(m\right) = word\left(q\right)\right)\right) \Rightarrow q = p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/EqualBinaryRunBridge.mem_row_iff` (`✓ std3`). ∎

*Citation.* Paolo Xausa (2025). *OEIS A386705: sums of even integers with equally paired maximal binary runs*. URL: <https://oeis.org/A386705>.

*Commentary.*

This is a membership characterization for the actual set of integers. It proves existence and uniqueness of positive part lengths; it assumes neither a composition count nor an identity for the sum over those lengths. Positivity and evenness of the represented integer remain explicit on both sides.

**Definition 1.9 (Complete recurrence target).**

$$FullClaim \iff a\left(1\right) = 2 \land \left(a\left(2\right) = 22 \land \left(a\left(3\right) = 192 \land \left(\forall n \in Nat,\; 4 \le n \Rightarrow a\left(n\right) = 12 \cdot a\left(n - 1\right) - 36 \cdot a\left(n - 2\right) + 32 \cdot a\left(n - 3\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Digit/EqualBinaryRunBridge.FullClaim` (`✓ std3`).

*Citation.* Paolo Xausa (2025). *OEIS A386705: sums of even integers with equally paired maximal binary runs*. URL: <https://oeis.org/A386705>.

*Commentary.*

FullClaim names the complete conjunction. The theorem full_claim below proves it without assuming a recurrence, a composition count, or a weighted sum identity. The composition count is supplied by Mathlib and the weighted identities are derived from the finite composition split.

**Theorem 1.10 (Complete literal recurrence).**

$$a\left(1\right) = 2 \land \left(a\left(2\right) = 22 \land \left(a\left(3\right) = 192 \land \left(\forall n \in Nat,\; 4 \le n \Rightarrow a\left(n\right) = 12 \cdot a\left(n - 1\right) - 36 \cdot a\left(n - 2\right) + 32 \cdot a\left(n - 3\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/EqualBinaryRunBridge.full_claim` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a386705-equal-binary-run-sum-recurrence` (proved) by `D5/S1/Digit/EqualBinaryRunBridge.full_claim`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a386705-equal-binary-run-sum-recurrence","declaration_gid":"D5/S1/Digit/EqualBinaryRunBridge.full_claim","resolution_kind":"proved"} -->

*Citation.* Paolo Xausa (2025). *OEIS A386705: sums of even integers with equally paired maximal binary runs*. URL: <https://oeis.org/A386705>.

*Commentary.*

The three initial values and the recurrence hold for the actual distinct positive even integers with canonical bit length 2*n and equally paired maximal runs. Natural indices express every integer index n>=1 exactly; the recurrence guard n>=4 makes each shifted index positive. Every subtraction of sequence values is in the integers. This is a universal theorem, not finite-prefix verification. The source's empirical formula and the known composition relation are distinguished from the kernel-checked derivation.

## References

- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.FullClaim`
- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.Literal`
- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.Matched`
- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.a`
- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.bits`
- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.blockRuns`
- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.full_claim`
- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.mem_row_iff`
- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.row`
- Truth anchor: `D5/S1/Digit/EqualBinaryRunBridge.word`
- Dependency: [D5/S1/Words/DoubleTailShuffleSupport](../Words/DoubleTailShuffleSupport.md)
