# KBonacci Fixed Paid Records

## Abstract

Complete minimal-window endpoint-pattern classification for actual fixed acquisition and all paid readings.

For every k at least two, Fin k indexes the actual tail states. A preparation supplies the same unknown strictly positive real vector c, and all runs use the same unknown nonzero nonnegative reader l. The world and initial outer-product target are those of KBonacci Prefix Completion.

**Definition 1.1 (base).**

$$\forall k: \mathbb{N}, 2 \leq k \implies \operatorname{start}(\operatorname{base}(k)) = 0 \land \forall s: \operatorname{Fin}(k), \operatorname{step}(\operatorname{base}(k), s, \operatorname{false}()) = \operatorname{some}(0) \land \operatorname{step}(\operatorname{base}(k), s, \operatorname{true}()) = \operatorname{ite}(s+1 < k, \operatorname{some}(s+1), \operatorname{none}())$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.base` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A zero bit resets a live tail to zero. A one bit increases a tail s to s + 1 when that value is smaller than k and rejects otherwise. The initial tail is zero. Rejection is absorbing under word execution.

**Definition 1.2 (live).**

$$\forall k: \mathbb{N}, 2 \leq k \implies \forall u: \operatorname{List}(\operatorname{Bool}()), \forall i: \operatorname{Fin}(k), \forall s: \operatorname{Fin}(k), \operatorname{live}(u, i, s) = \operatorname{ite}(\operatorname{evalFrom}(\operatorname{base}(k), s, u) = \operatorname{some}(i), 1, 0)$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.live` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual word transfer has entry one exactly when the automaton takes source tail s to target tail i; otherwise its entry is zero. A reader returning zero is unrelated to this automaton rejection test.

**Definition 1.3 (Window).**

$$\forall k: \mathbb{N}, 2 \leq k \implies \operatorname{Window}(k) = \{u: \operatorname{List}(\operatorname{Bool}()) \Vert \operatorname{length}(u) = k+1 \land \operatorname{evalFrom}(\operatorname{base}(k), 0, u) \neq \operatorname{none}()\}$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.Window` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every action is a literal binary word of length k + 1 that avoids the forbidden internal run of k ones. Legality is checked from tail zero and does not require that the word preserve the current object at a seam.

**Definition 1.4 (Arrangement).**

$$\forall k: \mathbb{N}, 2 \leq k \implies \operatorname{Arrangement}(k) = \operatorname{List}(\operatorname{List}(\operatorname{Window}(k)))$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.Arrangement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The outer list is the finite ordered preparation sequence. Each inner list is the fixed finite sequence of actual windows on that object, followed by stopping and abandoning it. Empty and repeated runs are retained. There is no upper bound on the number of preparations and no dependence on read values.

**Definition 1.5 (windows).**

$$\forall k: \mathbb{N}, 2 \leq k \implies \forall A: \operatorname{Arrangement}(k), \operatorname{windows}(A) = \sum_{h \in A}\operatorname{length}(h)$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.windows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each window is counted once, even if it repeats a value, kills the object or acts on an already zero object. The preparation count is the outer-list length, and the total paid-reading count is that length plus windows(A).

**Definition 1.6 (terminalReads).**

$$\forall k: \mathbb{N}, 2 \leq k \implies \forall l: \operatorname{Fin}(k) \to \mathbb{R}, \forall x: \operatorname{Fin}(k) \to \mathbb{R}, \forall h: \operatorname{List}(\operatorname{Window}(k)), \operatorname{terminalReads}(l, x, \operatorname{nil}()) = \operatorname{nil}() \land \forall u: \operatorname{Window}(k), \operatorname{terminalReads}(l, x, \operatorname{cons}(u, h)) = \operatorname{cons}(\operatorname{dot}(l, \operatorname{mulVec}(\operatorname{live}(u), x)), \operatorname{terminalReads}(l, \operatorname{mulVec}(\operatorname{live}(u), x), h))$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.terminalReads` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On each next window u, form y = live(u) x, append the compulsory scalar l dot y, and continue from y. The empty window sequence has no terminal readings. This recursion retains the killing-window reading and every subsequent paid zero.

**Definition 1.7 (paidRecord).**

$$\forall k: \mathbb{N}, 2 \leq k \implies \forall A: \operatorname{Arrangement}(k), \forall w: \operatorname{World}(k), \operatorname{paidRecord}(A, w) = (A, \operatorname{map}(h \mapsto (\operatorname{initial}(w), \operatorname{terminalReads}(\operatorname{ell}(w), \operatorname{c}(w), h)), A))$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.paidRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PaidRun(w) consists of the compulsory initial value sum c_i l_i and the terminalReads list starting from c. The literal arrangement is also part of the record, so the full ordered action and read history is retained. Each repeated initial value is still present and paid.

**Definition 1.8 (label).**

$$\forall k: \mathbb{N}, 2 \leq k \implies \forall u: \operatorname{List}(\operatorname{Bool}()), \forall r: \operatorname{Fin}(k), \forall t: \operatorname{Fin}(k), \operatorname{label}(u) = \operatorname{some}((r,t)) \iff \operatorname{live}(u) = \operatorname{endpoint}(k-1-r, t)$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The endpoint E(p,t) has entry one precisely when its row i equals t and its source column s satisfies s + p < k; all other entries are zero. When the actual cumulative word operator is this nonzero endpoint, its label is (k - 1 - p,t), representing source prefix length j = k - p. Otherwise the label is none. Only nonempty window prefixes are used; their operator is either zero or such an endpoint by the actual endpoint theorem.

**Definition 1.9 (surviving).**

$$\forall k: \mathbb{N}, 2 \leq k \implies \forall A: \operatorname{Arrangement}(k), \forall q: \operatorname{Fin}(k) \times \operatorname{Fin}(k), q \in \operatorname{surviving}(A) \iff \exists u: \operatorname{List}(\operatorname{Bool}()), u \in \operatorname{flatMap}(\operatorname{wordPrefixes}(), A) \land \operatorname{label}(u) = \operatorname{some}(q)$$

*Formalization.* `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.surviving` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take every nonempty cumulative window prefix in every run in order, extract its actual endpoint label, discard none and then remove repetitions. A surviving object has the form C_j e_t with C_j strictly positive. Thus its label survives even when l_t = 0. Label selection depends only on the literal arrangement and object survival.

**Theorem 1.10 (The exact classification for every legal fixed arrangement).**

$$\forall k: \mathbb{N}, 3 \leq k \implies \forall A: \operatorname{Arrangement}(k), \operatorname{windows}(A) = k(k-1) \implies ((\exists f: \operatorname{Arrangement}(k) \times \operatorname{List}(\mathbb{R} \times \operatorname{List}(\mathbb{R})) \to \operatorname{Matrix}(\operatorname{Fin}(k), \operatorname{Fin}(k), \mathbb{R}), \forall w: \operatorname{World}(k), \operatorname{apply}(f, \operatorname{paidRecord}(A, w)) = \operatorname{target}(w)) \iff \operatorname{surviving}(A) = \operatorname{offDiagonal}(k))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.complete_source_12_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source set S0 consists of (j,t) with 1 <= j <= k, 0 <= t < k and j different from t + 1. The Lean row index is r = j - 1, so S0 is exactly offDiagonal(k). The theorem quantifies over every finite arrangement with exactly k(k - 1) windows, without assuming a correct decoder in the arrangement type.

Actual sequential readings equal the readings of the literal cumulative words: word concatenation composes the actual transfer matrices in chronological order. Every long cumulative word either rejects every source tail or equals an endpoint. Consequently every terminal value is its surviving C_j l_t or a constant zero, and equality of full ordered records is equivalent to equality of the initial reading and the selected distinct prefix products.

The number of distinct surviving labels is at most the number of paid windows. Necessity applies the whole-domain prefix-pattern classification to that set, including singleton and adjacent two-column support collisions. Sufficiency applies off-diagonal completion after extracting the already paid entries from their fixed record positions. Reordering only occurs inside final decoding.

The factorization theorem extends a fiber-constant target to an arbitrary function on all record values, including values outside the attainable range. No continuity, measurability or computability condition is imposed. Positive objects and nonzero nonnegative readers inhabit the world type for every k in scope.

The result identifies the initial outer product, not the absolute factors or the cumulative action operator. It does not classify a unique action order, run grouping or preparation count, and asserts no adaptive, noisy, finite-precision, physical-preparation or dimension-two extension.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.Arrangement`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.Window`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.base`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.complete_source_12_2`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.label`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.live`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.paidRecord`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.surviving`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.terminalReads`
- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciFixedPaidRecord.windows`
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciActualEndpointOperators](../../../S1/Words/AdmissibleWords/KBonacciActualEndpointOperators.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion](KBonacciPrefixCompletion.md)
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/UniversalSufficiencyFactorization](../Sufficiency/UniversalSufficiencyFactorization.md)
