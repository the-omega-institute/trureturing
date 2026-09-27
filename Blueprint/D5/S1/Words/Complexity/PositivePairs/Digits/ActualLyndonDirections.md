# ActualLyndonDirections

## Abstract

Actual Lyndon words index independent directions in the full positive-pair family.

For each length r, ActualLyndonWord is the subtype of actual words of length r that satisfy IsLyndon. The module publicly installs a lifted linear order on this subtype and, for finite A, a Fintype instance obtained by injection into length-r vectors. These two anonymous public instances support the cardinality and deterministic selection below; the digit construction itself is a repository result, not a claim attributed to the cited paper.

**Definition 1.1 (Actual Lyndon words of a fixed length).**

$$\forall A,r, \operatorname{ActualLyndonWord}\left(A, r\right) = \operatorname{subtype}\left(w, \operatorname{length}\left(w\right) = r\land\operatorname{IsLyndon}\left(w\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections.ActualLyndonWord` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For linearly ordered A and r:N, ActualLyndonWord A r is the subtype of lists w with w.length=r and IsLyndon w.

**Definition 1.2 (The actual Lyndon-word count).**

$$\forall A,r, \operatorname{actualLyndonCount}\left(A, r\right) = \operatorname{card}\left(\operatorname{ActualLyndonWord}\left(A, r\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections.actualLyndonCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For finite linearly ordered A, actualLyndonCount A r is Fintype.card (ActualLyndonWord A r), not an independent proxy parameter.

**Definition 1.3 (Selected independent actual directions).**

$$\forall r,\operatorname{selectedDirection}\left(r\right):\operatorname{Fin}\left(\operatorname{actualLyndonCount}\left(A, r\right)\right)\Rightarrow\operatorname{PositivePairIndex}\left(A, r\right), \operatorname{LinearIndependent}\left(Q, \operatorname{lambda}\left(i, \operatorname{actualLeadingDifference}\left(r, \operatorname{selectedDirection}\left(r, i\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections.selectedDirection` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arman Nilforoushan; Farzad Parvaresh (2026). *Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters*. DOI: [10.48550/arXiv.2609.23106](https://doi.org/10.48550/arXiv.2609.23106). URL: <https://arxiv.org/html/2609.23106v1>.

*Commentary.*

For each r, selectedDirection chooses one PositivePairIndex A r for every element of Fin(actualLyndonCount A r), with the resulting actualLeadingDifference family linearly independent over Q.

## References

- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections.ActualLyndonWord`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections.actualLyndonCount`
- Truth anchor: `D5/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections.selectedDirection`
- Dependency: [D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading](../../LyndonBrackets/LyndonBracketLeading.md)
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyBracketSpan](../Span/FullFamilyBracketSpan.md)
