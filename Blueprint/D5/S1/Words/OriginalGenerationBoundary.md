# Original Generation Boundary

## Abstract

The original finite return word is transported through an explicit 01 boundary.

**Definition 1.1 (The original frontier morphism).**

Lean statement: `D5/S1/Words/OriginalGenerationBoundary.sigma`

*Formalization.* `D5/S1/Words/OriginalGenerationBoundary.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sigma maps 0 to 01 and 1 to 0 on the explicit Bool word alphabet.

**Definition 1.2 (The marker-to-marker morphism).**

Lean statement: `D5/S1/Words/OriginalGenerationBoundary.tau`

*Formalization.* `D5/S1/Words/OriginalGenerationBoundary.tau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

tau maps 0 to B5 = 00101 and 1 to B3 = 001, with the source orientation retained.

**Definition 1.3 (Applying a finite word morphism).**

Lean statement: `D5/S1/Words/OriginalGenerationBoundary.apply`

*Formalization.* `D5/S1/Words/OriginalGenerationBoundary.apply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A morphism is applied letter by letter and the finite images are concatenated.

**Definition 1.4 (The finite marker-to-marker segment).**

Lean statement: `D5/S1/Words/OriginalGenerationBoundary.tauWord`

*Formalization.* `D5/S1/Words/OriginalGenerationBoundary.tauWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

tauWord is the marker-to-marker segment obtained from an acquired finite return-type word.

**Definition 1.5 (The retained finite prefix).**

Lean statement: `D5/S1/Words/OriginalGenerationBoundary.finitePrefix`

*Formalization.* `D5/S1/Words/OriginalGenerationBoundary.finitePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite prefix keeps the U_K prefix, appends the marker segment, and closes with 00.

**Theorem 1.6 (Original generation through the explicit word boundary).**

$$\forall uK \in \operatorname{List} \operatorname{Bool},\; \forall w \in \operatorname{List} \operatorname{Bool},\; (sigmaThree\left(w\right)) ++ ([false, true]) = ([false, true]) ++ (tauWord\left(w\right)) \land finitePrefix\left(uK, w\right) = ((uK) ++ (tauWord\left(w\right))) ++ ([false, false])$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/OriginalGenerationBoundary.original_generation_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite return-type word, the third iterate of sigma is conjugate to tau through the displayed 01 boundary. The same theorem records the finite prefix identity with the distinct closing 00 marker. The statement is about explicit frontier words and does not assert a bracketed-tree or edit-history equality.

## References

- Truth anchor: `D5/S1/Words/OriginalGenerationBoundary.apply`
- Truth anchor: `D5/S1/Words/OriginalGenerationBoundary.finitePrefix`
- Truth anchor: `D5/S1/Words/OriginalGenerationBoundary.original_generation_boundary`
- Truth anchor: `D5/S1/Words/OriginalGenerationBoundary.sigma`
- Truth anchor: `D5/S1/Words/OriginalGenerationBoundary.tau`
- Truth anchor: `D5/S1/Words/OriginalGenerationBoundary.tauWord`
