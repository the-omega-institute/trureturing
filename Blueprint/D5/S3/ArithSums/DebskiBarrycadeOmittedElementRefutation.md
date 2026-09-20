# Refutation of the printed barrycade relation

## Abstract

The printed i >= 3 relation in Conjecture 2 (2) is false at i = 3.

**Definition 1.1 (The partial-sum set).**

$$\forall mu \in \mathrm{Nat} \to \mathrm{Nat},\; \operatorname{partialSums}\left(mu\right) = \{s | \exists k \in \mathrm{Nat},\; s = \sum_{i \in \operatorname{range}\left(k + 1\right)} \operatorname{mu}\left(i\right)\}$$

*Formalization.* `D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.partialSums` (`✓ std3`).

*Citation.* Michał Dębski; Jarosław Grytczuk; Paweł Naroski; Bartłomiej Pawlik; Jakub Przybyło; Małgorzata Śleszyńska-Nowak (2026). *Finite and infinite barrycades*. DOI: [10.48550/arXiv.2609.18476](https://doi.org/10.48550/arXiv.2609.18476). URL: <https://arxiv.org/abs/2609.18476v1>.

*Commentary.*

For a sequence mu, partialSums is the set of sums of its first k+1 entries. This is the paper's S_mu notation.

**Definition 1.2 (The greedy row).**

$$\forall r \in \mathrm{Nat}, k \in \mathrm{Nat},\; \operatorname{row}\left(r, k\right) = \operatorname{sInf}\left(\{a | (0 < a) \land \left((\forall i \in \operatorname{Fin}\left(k\right),\; \operatorname{row}\left(r, \operatorname{val}\left(i\right)\right) \ne a) \land (\neg (\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{row}\left(r, \operatorname{val}\left(i\right)\right) + a \in \cup_{j : \{j < r\}} \operatorname{partialSums}\left((\lambda n \mapsto \operatorname{row}\left(\operatorname{val}\left(j\right), n\right))\right)))\right)\}\right)$$

*Formalization.* `D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.row` (`✓ std3`).

*Citation.* Michał Dębski; Jarosław Grytczuk; Paweł Naroski; Bartłomiej Pawlik; Jakub Przybyło; Małgorzata Śleszyńska-Nowak (2026). *Finite and infinite barrycades*. DOI: [10.48550/arXiv.2609.18476](https://doi.org/10.48550/arXiv.2609.18476). URL: <https://arxiv.org/abs/2609.18476v1>.

*Commentary.*

row r k is the infimum of the positive entries not used in the first k positions of row r and whose new partial sum is absent from all earlier rows. The prefix is indexed by Fin k; the equivalent range notation is shown in the Lean fidelity example.

**Definition 1.3 (Printed Conjecture 2 (2)).**

$$\forall i \in \mathrm{Nat},\; (3 \le i) \Rightarrow (\forall n \in \mathrm{Nat},\; (\operatorname{IsLeast}\left(\{m | (0 < m) \land (\forall k \in \mathrm{Nat},\; \operatorname{row}\left(i - 1, k\right) \ne m)\}, n\right)) \Rightarrow (\operatorname{row}\left(i - 1, 0\right) = n + 1))$$

*Formalization.* `D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.claim` (`✓ std3`).

*Citation.* Michał Dębski; Jarosław Grytczuk; Paweł Naroski; Bartłomiej Pawlik; Jakub Przybyło; Małgorzata Śleszyńska-Nowak (2026). *Finite and infinite barrycades*. DOI: [10.48550/arXiv.2609.18476](https://doi.org/10.48550/arXiv.2609.18476). URL: <https://arxiv.org/abs/2609.18476v1>.

*Commentary.*

The paper says: "A1(i) is the smallest number that is omitted in the quasi-permutation rho_i" and "A2(i) = rho_i(1)". Algorithm 1 line 7 says: "Choose the smallest positive integer a such that a is not in U and s + a is not in P_(r-1)." Conjecture 2 (2) then prints A2(i) = A1(i) + 1 for every i >= 3.

**Theorem 1.4 (The printed relation is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/debski-barrycade-omitted-element-refutation` (refuted) by `D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"debski-barrycade-omitted-element-refutation","declaration_gid":"D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

The repository proves that rho_3 = (4, 3, 1, 5, 6, ...) omits 2 and starts with 4. Its least omitted positive integer is therefore 2, so the relation would require 4 = 3 and fails at i = 3.

## References

- Truth anchor: `D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.claim`
- Truth anchor: `D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.partialSums`
- Truth anchor: `D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.result`
- Truth anchor: `D5/S3/ArithSums/DebskiBarrycadeOmittedElementRefutation.row`
