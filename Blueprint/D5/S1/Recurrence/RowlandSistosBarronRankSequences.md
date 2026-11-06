# Infinitely Many Rank Sequences of Initial Rank Three

## Abstract

Parameter-dependent coefficient cancellation gives infinitely many rank sequences.

**Definition 1.1 (An eventual recurrence).**

$$\forall (s: \mathbb{N} \to \mathbb{Z}), \forall (r: \mathbb{N}), (\operatorname{HasRecurrence}\left(s, r\right)) \Leftrightarrow (\exists (E: \operatorname{LinearRecurrence}\left(\mathbb{Q}\right)), (E.\operatorname{order} = r) \land \left((\forall (h: 0 < E.\operatorname{order}), E.\operatorname{coeffs}\left(\langle0,h\rangle\right) \ne 0) \land (\exists (N: \mathbb{N}), E.\operatorname{IsSolution}\left(\operatorname{fun} (n: \mathbb{N}) \mapsto ((s\left(n + N\right): \mathbb{Q}))\right))\right))$$

*Formalization.* `D5/S1/Recurrence/RowlandSistosBarronRankSequences.HasRecurrence` (`✓ std3`).

*Citation.* Eric Rowland and Jesús Sistos Barrón (2025). *Complexity of powers of a constant-recursive sequence*. DOI: [10.48550/arXiv.2501.14643](https://doi.org/10.48550/arXiv.2501.14643). URL: <https://arxiv.org/abs/2501.14643v1>.

*Commentary.*

Section 2, page 3: “First, a constant-recursive sequence is one which satisfies a recurrence equation of the form s(n + r) = c_{r−1} s(n + r − 1) + · · · + c_1 s(n + 1) + c_0 s(n). for any sufficiently large n, where the coefficients (c_{r−1}, . . . , c_0) are all constants and c_0 ≠ 0.” Here s takes integer values, the coefficients are rational, E.coeffs i is c_i, and E.IsSolution applies to the tail n ↦ s(n + N). At order zero, the condition on coefficients is vacuous and the sequence is eventually zero.

**Definition 1.2 (Constant-recursive integer sequences).**

$$\forall (s: \mathbb{N} \to \mathbb{Z}), (\operatorname{IsConstantRecursive}\left(s\right)) \Leftrightarrow (\exists (r: \mathbb{N}), \operatorname{HasRecurrence}\left(s, r\right))$$

*Formalization.* `D5/S1/Recurrence/RowlandSistosBarronRankSequences.IsConstantRecursive` (`✓ std3`).

*Citation.* Eric Rowland and Jesús Sistos Barrón (2025). *Complexity of powers of a constant-recursive sequence*. DOI: [10.48550/arXiv.2501.14643](https://doi.org/10.48550/arXiv.2501.14643). URL: <https://arxiv.org/abs/2501.14643v1>.

*Commentary.*

Section 2, page 3: “First, a constant-recursive sequence is one which satisfies a recurrence equation of the form s(n + r) = c_{r−1} s(n + r − 1) + · · · + c_1 s(n + 1) + c_0 s(n). for any sufficiently large n, where the coefficients (c_{r−1}, . . . , c_0) are all constants and c_0 ≠ 0.” Existence of an order r expresses this property through HasRecurrence.

**Definition 1.3 (The least recurrence order).**

$$\forall (s: \mathbb{N} \to \mathbb{Z}), \operatorname{rank}\left(s\right) = \operatorname{sInf}\left(\{r: \mathbb{N} \mid (\operatorname{HasRecurrence}\left(s, r\right))\}\right)$$

*Formalization.* `D5/S1/Recurrence/RowlandSistosBarronRankSequences.rank` (`✓ std3`).

*Citation.* Eric Rowland and Jesús Sistos Barrón (2025). *Complexity of powers of a constant-recursive sequence*. DOI: [10.48550/arXiv.2501.14643](https://doi.org/10.48550/arXiv.2501.14643). URL: <https://arxiv.org/abs/2501.14643v1>.

*Commentary.*

Section 2, page 3: “Every constant-recursive sequence satisfies infinitely many recurrences, but there is only one of minimal size, that we define to be the rank of s(n), and denote it by rank s.” The natural infimum gives that least order whenever a recurrence exists; its value on an empty set of orders is zero.

**Definition 1.4 (Ranks of positive powers).**

$$\forall (s: \mathbb{N} \to \mathbb{Z}), \operatorname{rankSequence}\left(s\right) = \operatorname{fun} (M: \mathbb{N}^{+}) \mapsto (\operatorname{rank}\left(\operatorname{fun} (n: \mathbb{N}) \mapsto (s\left(n\right)^{(M: \mathbb{N})})\right))$$

*Formalization.* `D5/S1/Recurrence/RowlandSistosBarronRankSequences.rankSequence` (`✓ std3`).

*Citation.* Eric Rowland and Jesús Sistos Barrón (2025). *Complexity of powers of a constant-recursive sequence*. DOI: [10.48550/arXiv.2501.14643](https://doi.org/10.48550/arXiv.2501.14643). URL: <https://arxiv.org/abs/2501.14643v1>.

*Commentary.*

Section 1, page 2: “We say that a sequence of integers is a rank sequence if it arises as (rank s(n)^M)_{M≥1} for some constant-recursive integer sequence s(n)_{n≥0}.” The exponent M ranges over positive naturals. Equality means agreement at every positive exponent, including finite initial segments.

**Definition 1.5 (The fixed-rank finiteness conjecture).**

$$(claim) \Leftrightarrow (\forall (r: \mathbb{N}), (1 \le r) \Rightarrow (\operatorname{Set}.\operatorname{Finite}\left(\{R: \mathbb{N}^{+} \to \mathbb{N} \mid (\exists (s: \mathbb{N} \to \mathbb{Z}), (\operatorname{IsConstantRecursive}\left(s\right)) \land \left((\operatorname{rank}\left(s\right) = r) \land (R = \operatorname{rankSequence}\left(s\right))\right))\}\right)))$$

*Formalization.* `D5/S1/Recurrence/RowlandSistosBarronRankSequences.claim` (`✓ std3`).

*Citation.* Eric Rowland and Jesús Sistos Barrón (2025). *Complexity of powers of a constant-recursive sequence*. DOI: [10.48550/arXiv.2501.14643](https://doi.org/10.48550/arXiv.2501.14643). URL: <https://arxiv.org/abs/2501.14643v1>.

*Commentary.*

Section 1, page 2: “For each r ≥ 1, we conjecture that there are only finitely many rank sequences associated with sequences s(n)_{n≥0} of rank r, and we are interested in enumerating them.” The set contains exactly the functions R : ℕ+ → ℕ equal to rankSequence s for a constant-recursive integer sequence s of rank r; r ranges over all positive natural numbers.

**Theorem 1.6 (The finiteness conjecture is false).**

$$\neg (\forall (r: \mathbb{N}), (1 \le r) \Rightarrow (\operatorname{Set}.\operatorname{Finite}\left(\{R: \mathbb{N}^{+} \to \mathbb{N} \mid (\exists (s: \mathbb{N} \to \mathbb{Z}), (\operatorname{IsConstantRecursive}\left(s\right)) \land \left((\operatorname{rank}\left(s\right) = r) \land (R = \operatorname{rankSequence}\left(s\right))\right))\}\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/RowlandSistosBarronRankSequences.result` (`✓ std3`). ∎

*Resolves.* `Problems/rowland-sistos-barron-2025-rank-sequences` (refuted) by `D5/S1/Recurrence/RowlandSistosBarronRankSequences.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rowland-sistos-barron-2025-rank-sequences","declaration_gid":"D5/S1/Recurrence/RowlandSistosBarronRankSequences.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Eric Rowland and Jesús Sistos Barrón (2025). *Complexity of powers of a constant-recursive sequence*. DOI: [10.48550/arXiv.2501.14643](https://doi.org/10.48550/arXiv.2501.14643). URL: <https://arxiv.org/abs/2501.14643v1>.

*Commentary.*

For each natural p ≥ 3, s_p(n) = p·8^n − 4^n − 2^n has rank three. The rank of its M-th power is the number of nonzero coefficients of (1 + X − pX²)^M. For fixed M, each coefficient in degrees zero through 2M is a nonzero polynomial in p: at p = −1 all those coefficients are positive. Thus only finitely many natural parameters cause any cancellation at that exponent. For every p, the coefficient of X² vanishes at M = 2p + 1. If two parameters give the same rank sequence, the second must therefore belong to a finite exceptional set determined by the first. Finite fibres and infinitely many parameters contradict finiteness at initial rank three. This argument does not determine the first cancellation or settle the questions about general rank sequences and eventual pseudo-polynomial behaviour.

## References

- Truth anchor: `D5/S1/Recurrence/RowlandSistosBarronRankSequences.HasRecurrence`
- Truth anchor: `D5/S1/Recurrence/RowlandSistosBarronRankSequences.IsConstantRecursive`
- Truth anchor: `D5/S1/Recurrence/RowlandSistosBarronRankSequences.claim`
- Truth anchor: `D5/S1/Recurrence/RowlandSistosBarronRankSequences.rank`
- Truth anchor: `D5/S1/Recurrence/RowlandSistosBarronRankSequences.rankSequence`
- Truth anchor: `D5/S1/Recurrence/RowlandSistosBarronRankSequences.result`
