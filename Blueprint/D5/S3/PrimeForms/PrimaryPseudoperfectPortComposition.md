# Primary Pseudoperfect Port Composition

## Abstract

Coprime products obey a quotient-derivative product rule whose residual ports compose exactly.

**Definition 1.1 (Port residual).**

$$\operatorname{Delta}\left(R, C, B\right) = CB - R\operatorname{d}\left(B\right).$$

*Formalization.* `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.portDelta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The port residual is natural subtraction of the charged quotient sum from the scaled factor.

**Theorem 1.2 (Coprime product rule for the quotient derivative).**

$$\operatorname{Coprime}\left(A, B\right) \Rightarrow \operatorname{d}\left(AB\right) = A\operatorname{d}\left(B\right) + B\operatorname{d}\left(A\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.squarefreeDeriv_mul_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coprimality makes the prime-factor sets disjoint. Quotients indexed by a factor of A scale by B, while quotients indexed by a factor of B scale by A.

**Theorem 1.3 (Ports compose across coprime factors).**

$$\operatorname{Coprime}\left(A, B\right) \Rightarrow \operatorname{Delta}\left(R, C, AB\right) = \operatorname{Delta}\left(RA, \operatorname{Delta}\left(R, C, A\right), B\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.portDelta_mul_of_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coprime product rule separates the two derivative charges. Distributivity over natural subtraction and successive subtraction then give the same result even when a residual reaches zero.

**Theorem 1.4 (Coprime squarefree extension criterion).**

$$\operatorname{IsPPN}\left(K\right) \land \operatorname{Squarefree}\left(C\right) \land 1 < C \land \operatorname{Coprime}\left(K, C\right) \Rightarrow (\operatorname{IsPPN}\left(KC\right) \Leftrightarrow C - K\operatorname{d}\left(C\right) = 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.isPPN_mul_squarefree_coprime_iff_portDelta_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squarefreeness and nontriviality pass to the coprime product. Substituting the two quotient identities and cancelling the common term reduces primary pseudoperfectness to a unit port residual.

## References

- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.isPPN_mul_squarefree_coprime_iff_portDelta_eq_one`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.portDelta`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.portDelta_mul_of_coprime`
- Truth anchor: `D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.squarefreeDeriv_mul_of_coprime`
- Dependency: [D5/S3/PrimeForms/PrimaryPseudoperfectPorts](PrimaryPseudoperfectPorts.md)
