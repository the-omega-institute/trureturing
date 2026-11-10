# Hanna's Modulo-Six Conjecture

## Abstract

Every normalized solution of Hanna's system has coefficients avoiding one and five modulo six beyond degree one.

PowerSeries is the ring of formal power series and X is its indeterminate. The expression PowerSeries.subst(u,f) means f(u(X)); the inner series is the first argument. The coefficient operator coeff(n,A) extracts the coefficient of X to the power n. The integer z is cast to the rationals when compared with a rational coefficient.

**Definition 1.1 (The separate modulo-six assertion).**

$$claim = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 < n) \implies (\exists z: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (z: \mathbb{Q})) \land ((\operatorname{emod}\left(z, 6\right) \neq 1) \land (\operatorname{emod}\left(z, 6\right) \neq 5))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaA378258ModSix.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2024). *OEIS A378258, a compositional square root and dyadic parity*. URL: <https://oeis.org/A378258>.

*Commentary.*

The unpaginated OEIS A378258 Comments state: "Conjecture: a(n) is not congruent to 1 nor 5 (mod 6) for n > 1." IsGF is the original HannaA378258SquareRootParity.IsGF over rational formal power series. It requires constant coefficient zero, linear coefficient one, A=B+5A squared, and B(A-A squared)=X for some rational series B. A normalized solution exists, and the conclusion covers every such solution and every natural degree strictly greater than one. The symbol emod denotes Int.emod and uses the nonnegative remainder modulo six.

**Theorem 1.2 (Exclusion of the two residues).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsGF}\left(A\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsGF}\left(A\right)) \implies (\forall n: \mathbb{N}, (1 < n) \implies (\exists z: \mathbb{Z}, (\operatorname{coeff}\left(n, A\right) = (z: \mathbb{Q})) \land ((\operatorname{emod}\left(z, 6\right) \neq 1) \land (\operatorname{emod}\left(z, 6\right) \neq 5)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaA378258ModSix.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a378258-hanna-mod-six` (proved) by `D5/S1/Recurrence/Invariants/HannaA378258ModSix.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a378258-hanna-mod-six","declaration_gid":"D5/S1/Recurrence/Invariants/HannaA378258ModSix.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2024). *OEIS A378258, a compositional square root and dyadic parity*. URL: <https://oeis.org/A378258>.

*Commentary.*

Reuse the frozen existence, integrality and dyadic-parity result. An integer coefficient lift of any normalized rational solution satisfies (F-5F squared) composed with (F-F squared)=X, because the integer-to-rational coefficient map is injective and commutes with substitution at zero constant term. Modulo three, F+F squared and F-F squared are compositional inverses. For any commutative domain in which two is nonzero, this normalized inverse-pair system has at most one solution: composition with F+F squared produces a normalized Catalan solution; Mathlib uniqueness of the compositional inverse of X-X squared identifies these solutions, and the existing half_unique identifies their auxiliary compositional square roots. The unit 1+F+G then identifies F and G. Swapping the two inverse series and conjugating by X mapped to minus X makes -F(-X) another solution. Uniqueness therefore proves F=-F(-X), rather than assuming symmetry. Every even-degree coefficient vanishes modulo three. If the original integer coefficient is odd, frozen dyadic parity makes its degree a power of two; a power of two greater than one is even, so that coefficient is divisible by three. An even integer, or an odd integer divisible by three, cannot have remainder one or five modulo six. Degree zero enters the coefficient lift via normalization; degree one is excluded by the source conjecture. No finite truncation is used. The derivation reuses existing algebraic interfaces; it claims no global priority. The source-family registration reconstructs the complete original claim, proves whole-family variation and sensitivity, and witnesses coefficient dependence at degrees two and three of an actual normalized solution. Its continuation is unknown; no claim of undecidability or inexhaustibility follows. This delivery awaits independent review and freezing.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA378258ModSix.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaA378258ModSix.result`
- Dependency: [D5/S1/Recurrence/Invariants/HannaA378258SquareRootParity](HannaA378258SquareRootParity.md)
