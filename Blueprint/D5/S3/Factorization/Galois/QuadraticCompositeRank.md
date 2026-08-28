# Quadratic Composite Rank

## Abstract

The concrete independent two-radical composite has rank four and Klein symmetry.

**Theorem 1.1 (The empty radical family is the trivial extension).**

$$[\mathbb{Q}:\mathbb{Q}] = 1 \land \lvert\operatorname{Gal}(\mathbb{Q}, \mathbb{Q})\rvert = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticCompositeRank.rank_zero_case` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r = 0 the field is Q itself, its degree is one, and its Galois group has one element. This explicitly audits the empty family.

**Theorem 1.2 (One nonsquare radical gives a quadratic extension).**

$$[\mathbb{Q}(\sqrt{2}):\mathbb{Q}] = 2 \land \lvert\operatorname{Gal}(\mathbb{Q}(\sqrt{2}), \mathbb{Q})\rvert = 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticCompositeRank.rank_one_case` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The named SqrtTwoField is Mathlib's quadratic-algebra model of Q(sqrt 2). Its coordinate basis gives degree two, while identity and conjugation exhaust its two base automorphisms.

**Theorem 1.3 (Two independent concrete radicals give degree four).**

$$[\mathbb{Q}(\sqrt{2}, \sqrt{3}):\mathbb{Q}] = 4.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticCompositeRank.sqrt_two_sqrt_three_rank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source theorem stated only its conclusions and supplied no premises. This formalization makes K = Q, r = 2, and the radicals 2 and 3 explicit.

The private nonsquare proofs verify that 2 is not a square in Q and 3 is not a square in Q(sqrt 2). Mathlib's two quadratic ranks then multiply to four.

Pinned Mathlib has no theorem for a square-class-independent family in K*/(K*)^2. General r is therefore not claimed; the mandatory r = 2 concrete case is complete.

**Theorem 1.4 (The four base automorphisms form the Klein four-group).**

$$\operatorname{Gal}(\mathbb{Q}(\sqrt{2}, \sqrt{3}), \mathbb{Q}) \sim C_{2} \times C_{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticCompositeRank.sqrt_two_sqrt_three_galois_group` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changing either radical's sign gives four distinct automorphisms. The degree bound proves there are no others, and their squares are identity. Mathlib's IsKleinFour classification supplies the multiplicative equivalence.

Characteristic zero is used here to keep each root distinct from its negative. Primality of 2 and 3 is not a hypothesis; only the explicit nonsquare calculations carry the proof.

**Lemma 1.5 (A square radicand makes the extension trivial).**

$$[\mathbb{Q}(\sqrt{4}):\mathbb{Q}] = 1 \land [\mathbb{Q}(\sqrt{4}):\mathbb{Q}] \neq 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticCompositeRank.square_radicand_independence_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a = 4, the chosen square root 2 already belongs to Q. Its adjoining field is the bottom field and has degree one rather than two. This is the r = 1 failure of square-class independence.

**Lemma 1.6 (Radicals differing by a square factor collapse).**

$$\sqrt{8} = 2\sqrt{2},\\{}[\mathbb{Q}(\sqrt{2}, \sqrt{8}):\mathbb{Q}] = 2 \land [\mathbb{Q}(\sqrt{2}, \sqrt{8}):\mathbb{Q}] \neq 4.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticCompositeRank.square_class_independence_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inside Q(sqrt 2), the named sqrtEight is 2 sqrt 2 and squares to 8. Adjoining sqrt 2 and sqrt 8 therefore gives the same degree-two field, not degree four. This is the required sharpness witness.

**Lemma 1.7 (Characteristic two identifies both sign choices).**

$$1 = -1 \in \mathbb{F_{2}} \land \operatorname{Negation}(\mathbb{F_{2}}) = identity.$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/QuadraticCompositeRank.characteristic_two_sign_separation_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In ZMod 2, one equals negative one and negation is the identity map. Thus the sign-change construction used to separate the four automorphisms cannot be transferred to characteristic two.

## References

- Truth anchor: `D5/S3/Factorization/Galois/QuadraticCompositeRank.characteristic_two_sign_separation_is_necessary`
- Truth anchor: `D5/S3/Factorization/Galois/QuadraticCompositeRank.rank_one_case`
- Truth anchor: `D5/S3/Factorization/Galois/QuadraticCompositeRank.rank_zero_case`
- Truth anchor: `D5/S3/Factorization/Galois/QuadraticCompositeRank.sqrt_two_sqrt_three_galois_group`
- Truth anchor: `D5/S3/Factorization/Galois/QuadraticCompositeRank.sqrt_two_sqrt_three_rank`
- Truth anchor: `D5/S3/Factorization/Galois/QuadraticCompositeRank.square_class_independence_is_necessary`
- Truth anchor: `D5/S3/Factorization/Galois/QuadraticCompositeRank.square_radicand_independence_is_necessary`
