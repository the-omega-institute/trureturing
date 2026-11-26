# Notik's real Golomb minimizers

## Abstract

All normalized real Golomb minimizers at eight, nine, and ten marks are integral.

**Definition 1.1 (Attainment, lower bound, and integrality at equality).**

$$\forall n: \mathbb{N}, \forall T: \mathbb{Z}, \operatorname{MinimumAt} (n, T) \iff (\exists z: \operatorname{Fin} (n+1) \to \mathbb{Z}, z(0) = 0 \land z(n) = T \land G(\iota(z))) \land (\forall x: \operatorname{Fin} (n+1) \to \mathbb{R}, G(x) \implies \iota(T) \leq L(x)) \land (\forall x: \operatorname{Fin} (n+1) \to \mathbb{R}, (G(x) \land x(0) = 0 \land L(x) = \iota(T)) \implies \forall i: \operatorname{Fin} (n+1), \exists z: \mathbb{Z}, x(i) = \iota(z))$$

*Formalization.* `D5/S3/Combinatorics/Golomb/NotikMinimizers.MinimumAt` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

For n gaps there are n + 1 marks, indexed from zero to n. G denotes the real ruler predicate, L(x) is the last mark minus the first, and iota is the coordinatewise integer-to-real cast on a tuple or the integer-to-real cast on a single value. The lower bound applies to every real ruler, and integrality is asserted with the first mark fixed at zero.

**Theorem 1.2 (The minimum-length real and integer rulers coincide at all three sizes).**

$$\operatorname{MinimumAt} (7, 34) \land \operatorname{MinimumAt} (8, 44) \land \operatorname{MinimumAt} (9, 55)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Golomb/NotikMinimizers.result` (`✓ std3`). ∎

*Resolves.* `Problems/notik-real-golomb-minimizers` (proved) by `D5/S3/Combinatorics/Golomb/NotikMinimizers.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"notik-real-golomb-minimizers","declaration_gid":"D5/S3/Combinatorics/Golomb/NotikMinimizers.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

Esther Notik's Section 10 asks whether the shortest real rulers at eight, nine, and ten marks are precisely the optimal integer rulers. The three lengths are 34, 44, and 55. Strictly ordered integer tuples with distinct distances satisfy real unit separation. This gives the reverse inclusion after the lower bounds and integral attainment have fixed the same minimum lengths.

Notik's bound trees have 3,823, 15,929, and 18,425 nodes in size order. The replay uses the archived bounds for five through seven marks and extends the collection of smaller bounds after proving each new length. Each root check joins the subtree equations in branch order, using the inherited rows and the certificates for all 349, 1,235, and 1,209 tied leaves.

A feasible optimum follows a branch in one of its two orientations. Every positively weighted row at a tied leaf is tight. The certificates use these rows and the separation constraints to force each gap to be an integer, or to exclude the remaining cases. Reversing the gap order preserves integrality, and summing the gaps recovers the normalized marks. Lean checks the tree and table literals. Archive decoding and the construction of the equality certificates take place outside Lean.

## References

- Truth anchor: `D5/S3/Combinatorics/Golomb/NotikMinimizers.MinimumAt`
- Truth anchor: `D5/S3/Combinatorics/Golomb/NotikMinimizers.result`
