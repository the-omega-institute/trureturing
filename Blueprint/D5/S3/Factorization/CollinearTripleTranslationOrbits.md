# Collinear Triple Translation Orbits

## Abstract

Translation orbits prove the square-divisibility conjecture in OEIS A146557.

Peter Bala's July 24, 2025 conjecture concerns unordered triples of points modulo n. No two points may have the same first coordinate or the same second coordinate. Collinearity means the difference determinant vanishes modulo n, including when n is composite.

**Definition 1.1 (The square grid).**

$$\operatorname{Point}\left(n\right) = \operatorname{ZMod}\left(n\right) \times \operatorname{ZMod}\left(n\right)$$

*Formalization.* `D5/S3/Factorization/CollinearTripleTranslationOrbits.Point` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Peter Bala; Max Alekseyev (2025). *OEIS A146557 collinear triple divisibility conjecture*. URL: <https://oeis.org/A146557>.

*Commentary.*

Both coordinates lie in the ring of integers modulo n.

**Definition 1.2 (Admissible three-element sets).**

$$\begin{aligned}\operatorname{IsCollinearTriple}\left(S\right) \iff \operatorname{card}\left(S\right) = 3 \land\\\operatorname{InjOn}\left(fst, S\right) \land \operatorname{InjOn}\left(snd, S\right) \land\\\forall p,q,r \in S, (q_{1}-p_{1})(r_{2}-p_{2}) = (r_{1}-p_{1})(q_{2}-p_{2})\end{aligned}$$

*Formalization.* `D5/S3/Factorization/CollinearTripleTranslationOrbits.IsCollinearTriple` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Peter Bala; Max Alekseyev (2025). *OEIS A146557 collinear triple divisibility conjecture*. URL: <https://oeis.org/A146557>.

*Commentary.*

The two coordinate projections are injective on S. The determinant identity is required for every p, q, r in S; repeated points satisfy it automatically, and permuting distinct points preserves its vanishing.

**Definition 1.3 (The objects being counted).**

$$\operatorname{Triple}\left(n\right) = \{ S \in \operatorname{Finset}\left(\operatorname{Point}\left(n\right)\right) \mid \operatorname{IsCollinearTriple}\left(S\right) \}$$

*Formalization.* `D5/S3/Factorization/CollinearTripleTranslationOrbits.Triple` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Peter Bala; Max Alekseyev (2025). *OEIS A146557 collinear triple divisibility conjecture*. URL: <https://oeis.org/A146557>.

*Commentary.*

An object is a finite set, not an ordered tuple. Its cardinal condition is exactly three, so each unordered configuration contributes once.

**Theorem 1.4 (The A146557 divisibility conjecture).**

$$\forall n \in \mathbb{N}, 0 < n \implies \neg (3 \mid n) \implies n^{2} \mid \operatorname{card}\left(\operatorname{Triple}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/CollinearTripleTranslationOrbits.square_dvd_card_collinear_triples` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a146557-collinear-triple-divisibility` (proved) by `D5/S3/Factorization/CollinearTripleTranslationOrbits.square_dvd_card_collinear_triples`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a146557-collinear-triple-divisibility","declaration_gid":"D5/S3/Factorization/CollinearTripleTranslationOrbits.square_dvd_card_collinear_triples","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Peter Bala; Max Alekseyev (2025). *OEIS A146557 collinear triple divisibility conjecture*. URL: <https://oeis.org/A146557>.

*Commentary.*

Translation preserves coordinate injectivity and every coordinate difference, so it acts on these sets. If translation by t fixes S, summing its three elements before and after translation gives sum(S)=3t+sum(S), hence 3t=0. Since 3 is coprime to n, it is a unit modulo n, and both coordinates of t are zero. The action is therefore free. The standard free-action equivalence identifies the set of configurations with its orbit quotient times the translation group. The latter has n squared elements, proving the divisibility for every positive n not divisible by three.

## References

- Truth anchor: `D5/S3/Factorization/CollinearTripleTranslationOrbits.IsCollinearTriple`
- Truth anchor: `D5/S3/Factorization/CollinearTripleTranslationOrbits.Point`
- Truth anchor: `D5/S3/Factorization/CollinearTripleTranslationOrbits.Triple`
- Truth anchor: `D5/S3/Factorization/CollinearTripleTranslationOrbits.square_dvd_card_collinear_triples`
