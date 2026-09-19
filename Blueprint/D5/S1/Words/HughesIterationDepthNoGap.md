# Iteration-Depth No-Gap for Literal Insertion

## Abstract

Literal fixed-degree insertion has a gap-free spectrum of minimum iteration depths.

Hughes defines k-insertion by interleaving k source factors with k+1 base factors, allowing every factor to be empty. Iteration keeps the same positive degree throughout a history. The result below settles the arbitrary-language conjecture stated in Section 10, not the finite-language Theorem 8 or the insertion-degree conjecture in Section 11.

**Definition 1.1 (Languages of finite words).**

$$\forall alpha \in \operatorname{Type},\; Language\left(alpha\right) = Set\left(List\left(alpha\right)\right)$$

*Formalization.* `D5/S1/Words/HughesIterationDepthNoGap.Language` (`✓ std3`).

*Citation.* Charles E. Hughes (2026). *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*. URL: <https://arxiv.org/abs/2608.27755v1>.

*Commentary.*

A language over an alphabet is an arbitrary set of finite lists. No finiteness condition is imposed on the language itself.

**Definition 1.2 (Literal fixed-degree insertion).**

$$\forall alpha \in \operatorname{Type},\; \forall k \in \mathbb{N},\; \forall A \in Language\left(alpha\right),\; \forall B \in Language\left(alpha\right),\; \forall w \in List\left(alpha\right),\; w \in fixedDegreeInsertion\left(k, A, B\right) \Leftrightarrow \left(\exists pieces \in List\left(Prod\left(List\left(alpha\right), List\left(alpha\right)\right)\right),\; length\left(pieces\right) = k \land \left(\exists tail \in List\left(alpha\right),\; baseWord\left(pieces, tail\right) \in B \land \left(sourceWord\left(pieces\right) \in A \land pairOutput\left(pieces, tail\right) = w\right)\right)\right)$$

*Formalization.* `D5/S1/Words/HughesIterationDepthNoGap.fixedDegreeInsertion` (`✓ std3`).

*Citation.* Charles E. Hughes (2026). *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*. URL: <https://arxiv.org/abs/2608.27755v1>.

*Commentary.*

A list of k pairs records x_i and y_i, and the final tail records x_(k+1). The x-pieces concatenate to a base word, the y-pieces concatenate to a source word, and pairwise interleaving followed by the tail is the output. Empty lists are allowed in every position.

**Definition 1.3 (Iteration at one fixed degree).**

$$\forall alpha \in \operatorname{Type},\; \forall k \in \mathbb{N},\; \forall A \in Language\left(alpha\right),\; \forall B \in Language\left(alpha\right),\; fixedDegreeIterate\left(k, A, B, 0\right) = B \land \left(\forall m \in \mathbb{N},\; fixedDegreeIterate\left(k, A, B, m + 1\right) = fixedDegreeInsertion\left(k, A, fixedDegreeIterate\left(k, A, B, m\right)\right)\right)$$

*Formalization.* `D5/S1/Words/HughesIterationDepthNoGap.fixedDegreeIterate` (`✓ std3`).

*Citation.* Charles E. Hughes (2026). *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*. URL: <https://arxiv.org/abs/2608.27755v1>.

*Commentary.*

Stage zero is B. Every successor inserts A into the preceding stage using the same degree k.

**Definition 1.4 (Appearance at an iteration stage).**

$$\forall alpha \in \operatorname{Type},\; \forall A \in Language\left(alpha\right),\; \forall B \in Language\left(alpha\right),\; \forall w \in List\left(alpha\right),\; \forall m \in \mathbb{N},\; appearsAt\left(A, B, w, m\right) \Leftrightarrow \left(\exists k \in \mathbb{N},\; 0 < k \land w \in fixedDegreeIterate\left(k, A, B, m\right)\right)$$

*Formalization.* `D5/S1/Words/HughesIterationDepthNoGap.appearsAt` (`✓ std3`).

*Citation.* Charles E. Hughes (2026). *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*. URL: <https://arxiv.org/abs/2608.27755v1>.

*Commentary.*

A word appears at stage m when one positive degree k produces it at that stage. The existential degree may depend on the word and stage.

**Definition 1.5 (Minimum iteration depth).**

$$\forall alpha \in \operatorname{Type},\; \forall A \in Language\left(alpha\right),\; \forall B \in Language\left(alpha\right),\; \forall w \in List\left(alpha\right),\; \forall m \in \mathbb{N},\; hasIterationDepth\left(A, B, w, m\right) \Leftrightarrow \left(appearsAt\left(A, B, w, m\right) \land \left(\forall n \in \mathbb{N},\; n < m \Rightarrow \left(\neg appearsAt\left(A, B, w, n\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/HughesIterationDepthNoGap.hasIterationDepth` (`✓ std3`).

*Citation.* Charles E. Hughes (2026). *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*. URL: <https://arxiv.org/abs/2608.27755v1>.

*Commentary.*

Depth m means appearance at m together with nonappearance at every smaller stage, exactly retaining the minimum convention from the source.

**Definition 1.6 (Attained minimum depths).**

$$\forall alpha \in \operatorname{Type},\; \forall A \in Language\left(alpha\right),\; \forall B \in Language\left(alpha\right),\; \forall m \in \mathbb{N},\; m \in iterationDepthSpectrum\left(A, B\right) \Leftrightarrow \left(\exists w \in List\left(alpha\right),\; hasIterationDepth\left(A, B, w, m\right)\right)$$

*Formalization.* `D5/S1/Words/HughesIterationDepthNoGap.iterationDepthSpectrum` (`✓ std3`).

*Citation.* Charles E. Hughes (2026). *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*. URL: <https://arxiv.org/abs/2608.27755v1>.

*Commentary.*

The spectrum contains exactly those natural numbers realized as the minimum iteration depth of some finite word.

**Definition 1.7 (The source depth origin).**

$$closedSourceZero = 0$$

*Formalization.* `D5/S1/Words/HughesIterationDepthNoGap.closedSourceZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The published minimum depth is zero-based. This Fin 2 value is the actual source coordinate used by the theorem and its finite information arena.

**Definition 1.8 (Spectrum at a selected origin).**

$$\forall alpha \in \operatorname{Type},\; \forall origin \in Fin\left(2\right),\; \forall A \in Language\left(alpha\right),\; \forall B \in Language\left(alpha\right),\; \forall n \in \mathbb{N},\; n \in iterationDepthSpectrumAt\left(origin, A, B\right) \Leftrightarrow \left(\exists m \in \mathbb{N},\; m \in iterationDepthSpectrum\left(A, B\right) \land n = m + val\left(origin\right)\right)$$

*Formalization.* `D5/S1/Words/HughesIterationDepthNoGap.iterationDepthSpectrumAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Changing the origin adds its natural coordinate to every actual minimum depth. At closedSourceZero this is extensionally equal to the published spectrum.

**Theorem 1.9 (No gaps in the arbitrary-language spectrum).**

$$\forall alpha \in \operatorname{Type},\; Finite\left(alpha\right) \Rightarrow \left(\forall A \in Language\left(alpha\right),\; \forall B \in Language\left(alpha\right),\; \forall r \in \mathbb{N},\; r \in iterationDepthSpectrumAt\left(closedSourceZero, A, B\right) \Rightarrow \left(\forall q \in \mathbb{N},\; q \le r \Rightarrow q \in iterationDepthSpectrumAt\left(closedSourceZero, A, B\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/HughesIterationDepthNoGap.result` (`✓ std3`). ∎

*Resolves.* `Problems/hughes-iteration-depth-no-gap` (proved) by `D5/S1/Words/HughesIterationDepthNoGap.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hughes-iteration-depth-no-gap","declaration_gid":"D5/S1/Words/HughesIterationDepthNoGap.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Charles E. Hughes (2026). *Undecidability of Adjacent Equality for Insertion, Shuffle, and Crossover Language Operations*. URL: <https://arxiv.org/abs/2608.27755v1>.

*Commentary.*

For every finite alphabet and arbitrary languages A and B, any attained depth r forces every q at most r to be attained. From a minimum-depth successor word, the proof extracts its predecessor. If that predecessor appeared too early at degree j, both histories lift to max(k,j) by padding with empty factor pairs, producing the original word too early. Induction then descends through every smaller depth. The argument includes empty languages, epsilon-only languages, and empty alphabets.

## References

- Truth anchor: `D5/S1/Words/HughesIterationDepthNoGap.Language`
- Truth anchor: `D5/S1/Words/HughesIterationDepthNoGap.appearsAt`
- Truth anchor: `D5/S1/Words/HughesIterationDepthNoGap.closedSourceZero`
- Truth anchor: `D5/S1/Words/HughesIterationDepthNoGap.fixedDegreeInsertion`
- Truth anchor: `D5/S1/Words/HughesIterationDepthNoGap.fixedDegreeIterate`
- Truth anchor: `D5/S1/Words/HughesIterationDepthNoGap.hasIterationDepth`
- Truth anchor: `D5/S1/Words/HughesIterationDepthNoGap.iterationDepthSpectrum`
- Truth anchor: `D5/S1/Words/HughesIterationDepthNoGap.iterationDepthSpectrumAt`
- Truth anchor: `D5/S1/Words/HughesIterationDepthNoGap.result`
