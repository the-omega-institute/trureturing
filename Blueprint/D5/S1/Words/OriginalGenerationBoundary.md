# Original Generation Boundary

## Abstract

The third Fibonacci substitution iterate is conjugate to the two block images through 01.

**Definition 1.1 (The two block images).**

Lean statement: `D5/S1/Words/OriginalGenerationBoundary.tau`

*Formalization.* `D5/S1/Words/OriginalGenerationBoundary.tau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With false representing 0 and true representing 1, tau maps 0 to B5 = 00101 and 1 to B3 = 001.

**Definition 1.2 (The third iterate in the source alphabet).**

Lean statement: `D5/S1/Words/OriginalGenerationBoundary.sigmaThree`

*Formalization.* `D5/S1/Words/OriginalGenerationBoundary.sigmaThree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical GoldenGapWord.subst maps true to [true, false] and false to [true]. Complementing input and output letters gives sigma(0) = 01 and sigma(1) = 0. sigmaThree complements the input word, applies FibonacciIncidence.iterate three times, and complements the result. Since Bool complement is an involution, this is the third iterate of sigma.

**Definition 1.3 (Concatenating the block images).**

Lean statement: `D5/S1/Words/OriginalGenerationBoundary.tauWord`

*Formalization.* `D5/S1/Words/OriginalGenerationBoundary.tauWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

tauWord concatenates tau's images in the order of an arbitrary finite Bool word.

**Theorem 1.4 (Abstract finite-word boundary conjugacy).**

$$\forall w \in \operatorname{List} \operatorname{Bool},\; (sigmaThree\left(w\right)) ++ ([false, true]) = ([false, true]) ++ (tauWord\left(w\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/OriginalGenerationBoundary.original_generation_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite word w, sigmaThree(w) followed by 01 equals 01 followed by tauWord(w). The two letter identities extend by induction over w: the boundary moves past each substituted letter. This is the abstract conjugacy clause of Proposition 51.2 of Atomic Generation and Acquisition IV. It does not identify w with return types acquired from the specified source, locate source markers or a cursor, or establish the actual prefix equation W_m = U_K tau(w) 00. Those claims require a source and acquisition bridge. The displayed conjugating word is 01; the acquisition marker 00 has a different role. No bracketed tree or edit history is reconstructed.

## References

- Truth anchor: `D5/S1/Words/OriginalGenerationBoundary.original_generation_boundary`
- Truth anchor: `D5/S1/Words/OriginalGenerationBoundary.sigmaThree`
- Truth anchor: `D5/S1/Words/OriginalGenerationBoundary.tau`
- Truth anchor: `D5/S1/Words/OriginalGenerationBoundary.tauWord`
- Dependency: [D5/S1/Words/FibonacciIncidence](FibonacciIncidence.md)
