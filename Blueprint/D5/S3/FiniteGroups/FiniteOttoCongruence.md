# Finite Otto congruence quotients are cancellative

## Abstract

Finite semigroups with an Otto congruence have cancellative quotients.

**Definition 1.1 (Otto conjugacy).**

$$\forall (S: Type*), [\operatorname{Semigroup}\left(S\right)] \forall (a: S), \forall (b: S), \operatorname{Otto}\left(a, b\right) \iff \exists g, h: S, a \cdot g = g \cdot b \land b \cdot h = h \cdot a$$

*Formalization.* `D5/S3/FiniteGroups/FiniteOttoCongruence.Otto` (`✓ std3`).

*Citation.* Trevor Jack (2026). *Answering Five Open Problems Involving Semigroup Conjugacy*. DOI: [10.1007/s00233-026-10614-w](https://doi.org/10.1007/s00233-026-10614-w). URL: <https://arxiv.org/abs/2411.16284>.

*Commentary.*

Jack, Section 2, p. 2: "∀a, b ∈ S (a ∼o b ⇔ ag = gb and bh = ha for some g, h ∈ S)." Otto(a,b) uses two witnesses from S itself; no identity element is adjoined. S is an arbitrary semigroup, with no nonemptiness assumption.

**Definition 1.2 (Compatibility with multiplication).**

$$\forall (S: Type*), [\operatorname{Semigroup}\left(S\right)] \operatorname{OttoIsCongruence}\left(S\right) \iff (\forall (a: S), \forall (b: S), \forall (c: S), \forall (d: S), \operatorname{Otto}\left(a, b\right) \Rightarrow \operatorname{Otto}\left(c, d\right) \Rightarrow \operatorname{Otto}\left(a \cdot c, b \cdot d\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteOttoCongruence.OttoIsCongruence` (`✓ std3`).

*Citation.* Trevor Jack (2026). *Answering Five Open Problems Involving Semigroup Conjugacy*. DOI: [10.1007/s00233-026-10614-w](https://doi.org/10.1007/s00233-026-10614-w). URL: <https://arxiv.org/abs/2411.16284>.

*Commentary.*

Otto conjugacy is an equivalence relation for every semigroup. Its being a congruence means that multiplication respects two pairs of related elements. This is the congruence condition in Jack's Section 9, Problem 9.4, p. 14.

**Definition 1.3 (Cancellation of classes).**

$$\forall (S: Type*), [\operatorname{Semigroup}\left(S\right)] \operatorname{QuotientCancelative}\left(S\right) \iff ((\forall (a: S), \forall (b: S), \forall (c: S), \operatorname{Otto}\left(a \cdot b, a \cdot c\right) \Rightarrow \operatorname{Otto}\left(b, c\right)) \land (\forall (a: S), \forall (b: S), \forall (c: S), \operatorname{Otto}\left(b \cdot a, c \cdot a\right) \Rightarrow \operatorname{Otto}\left(b, c\right)))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteOttoCongruence.QuotientCancelative` (`✓ std3`).

*Citation.* Trevor Jack (2026). *Answering Five Open Problems Involving Semigroup Conjugacy*. DOI: [10.1007/s00233-026-10614-w](https://doi.org/10.1007/s00233-026-10614-w). URL: <https://arxiv.org/abs/2411.16284>.

*Commentary.*

The first conjunct is left cancellation and the second is right cancellation, expressed on representatives. When Otto conjugacy is a congruence, these are exactly the two cancellation laws of the quotient semigroup. The spelling cancelative follows Jack's Section 9, Problem 9.4, p. 14.

**Definition 1.4 (The negative answer to Problem 9.4).**

$$claim \iff (\forall (S: Type), [\operatorname{Semigroup}\left(S\right)] [\operatorname{Finite}\left(S\right)] \operatorname{OttoIsCongruence}\left(S\right) \Rightarrow \operatorname{QuotientCancelative}\left(S\right))$$

*Formalization.* `D5/S3/FiniteGroups/FiniteOttoCongruence.claim` (`✓ std3`).

*Citation.* Trevor Jack (2026). *Answering Five Open Problems Involving Semigroup Conjugacy*. DOI: [10.1007/s00233-026-10614-w](https://doi.org/10.1007/s00233-026-10614-w). URL: <https://arxiv.org/abs/2411.16284>.

*Commentary.*

Jack, Section 9, Problem 9.4, p. 14: "Is there a finite semigroup for which ∼o is a congruence and S/∼o is not cancelative?" The proposition gives the negative answer: for every finite semigroup S, multiplication compatibility of Otto conjugacy implies both cancellation laws on classes. Type denotes the small carrier universe; Finite imposes no chosen enumeration. Empty carriers satisfy the statement vacuously.

**Theorem 1.5 (Every finite Otto congruence quotient is cancellative).**

$$\forall (S: Type), [\operatorname{Semigroup}\left(S\right)] [\operatorname{Finite}\left(S\right)] \operatorname{OttoIsCongruence}\left(S\right) \Rightarrow \operatorname{QuotientCancelative}\left(S\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/FiniteOttoCongruence.result` (`✓ std3`). ∎

*Resolves.* `Problems/jack-2024-finite-otto-congruence` (proved) by `D5/S3/FiniteGroups/FiniteOttoCongruence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jack-2024-finite-otto-congruence","declaration_gid":"D5/S3/FiniteGroups/FiniteOttoCongruence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Trevor Jack (2026). *Answering Five Open Problems Involving Semigroup Conjugacy*. DOI: [10.1007/s00233-026-10614-w](https://doi.org/10.1007/s00233-026-10614-w). URL: <https://arxiv.org/abs/2411.16284>.

*Commentary.*

Every element of a finite semigroup has an idempotent positive power. All idempotents are Otto-conjugate, using the products ef and fe as witnesses. If an idempotent power of a is a to the n, then a is Otto-conjugate to a to the n plus one. Multiplication compatibility therefore makes the common idempotent class a two-sided identity. The preceding positive power supplies an inverse class, proving left cancellation. The relation between ab and ba, witnessed by a and b, transfers this to right cancellation.

## References

- Truth anchor: `D5/S3/FiniteGroups/FiniteOttoCongruence.Otto`
- Truth anchor: `D5/S3/FiniteGroups/FiniteOttoCongruence.OttoIsCongruence`
- Truth anchor: `D5/S3/FiniteGroups/FiniteOttoCongruence.QuotientCancelative`
- Truth anchor: `D5/S3/FiniteGroups/FiniteOttoCongruence.claim`
- Truth anchor: `D5/S3/FiniteGroups/FiniteOttoCongruence.result`
- Dependency: [D5/S0/Certificates/Algebra/BergmanQuestion15Refutation](../../S0/Certificates/Algebra/BergmanQuestion15Refutation.md)
