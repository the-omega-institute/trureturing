# Unary Neighborhood Minimality Refuted

## Abstract

Binary words refute unary minimality for condensed and super condensed neighborhoods.

**Definition 1.1 (Alignment columns).**

$$\forall \alpha: Type, \operatorname{Column}\left(\alpha\right): Type; both: \alpha\to\alpha\to\operatorname{Column}\left(\alpha\right); top: \alpha\to\operatorname{Column}\left(\alpha\right); bottom: \alpha\to\operatorname{Column}\left(\alpha\right)$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.Column` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

A column has two letters, a top letter and a gap, or a gap and a bottom letter. There is no constructor for a pair of gaps.

**Definition 1.2 (Alignments).**

$$\forall \alpha: Type, \operatorname{Alignment}\left(\alpha\right) = \operatorname{List}\left(\operatorname{Column}\left(\alpha\right)\right)$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.Alignment` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

An alignment is a list of columns in left-to-right order.

**Definition 1.3 (First row of an alignment).**

$$\forall \alpha: Type, (\operatorname{topRow}\left([]\right) = []) \land (\forall A \in \operatorname{Alignment}\left(\alpha\right),\; \forall x \in \alpha,\; \forall y \in \alpha,\; (\operatorname{topRow}\left(\operatorname{cons}\left(\operatorname{both}\left(x, y\right), A\right)\right) = \operatorname{cons}\left(x, \operatorname{topRow}\left(A\right)\right)) \land \left((\operatorname{topRow}\left(\operatorname{cons}\left(\operatorname{top}\left(x\right), A\right)\right) = \operatorname{cons}\left(x, \operatorname{topRow}\left(A\right)\right)) \land (\operatorname{topRow}\left(\operatorname{cons}\left(\operatorname{bottom}\left(y\right), A\right)\right) = \operatorname{topRow}\left(A\right))\right))$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.topRow` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

The first row removes each gap from the top positions of the columns.

**Definition 1.4 (Second row of an alignment).**

$$\forall \alpha: Type, (\operatorname{bottomRow}\left([]\right) = []) \land (\forall A \in \operatorname{Alignment}\left(\alpha\right),\; \forall x \in \alpha,\; \forall y \in \alpha,\; (\operatorname{bottomRow}\left(\operatorname{cons}\left(\operatorname{both}\left(x, y\right), A\right)\right) = \operatorname{cons}\left(y, \operatorname{bottomRow}\left(A\right)\right)) \land \left((\operatorname{bottomRow}\left(\operatorname{cons}\left(\operatorname{top}\left(x\right), A\right)\right) = \operatorname{bottomRow}\left(A\right)) \land (\operatorname{bottomRow}\left(\operatorname{cons}\left(\operatorname{bottom}\left(y\right), A\right)\right) = \operatorname{cons}\left(y, \operatorname{bottomRow}\left(A\right)\right))\right))$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.bottomRow` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

The second row removes each gap from the bottom positions of the columns.

**Definition 1.5 (Cost of an alignment).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], (\operatorname{cost}\left([]\right) = 0) \land (\forall A \in \operatorname{Alignment}\left(\alpha\right),\; \forall x \in \alpha,\; \forall y \in \alpha,\; (\operatorname{cost}\left(\operatorname{cons}\left(\operatorname{both}\left(x, y\right), A\right)\right) = \operatorname{ite}\left(x = y, 0, 1\right) + \operatorname{cost}\left(A\right)) \land \left((\operatorname{cost}\left(\operatorname{cons}\left(\operatorname{top}\left(x\right), A\right)\right) = 1 + \operatorname{cost}\left(A\right)) \land (\operatorname{cost}\left(\operatorname{cons}\left(\operatorname{bottom}\left(y\right), A\right)\right) = 1 + \operatorname{cost}\left(A\right))\right))$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.cost` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

Equal paired letters cost zero, unequal paired letters cost one, and each gap column costs one.

**Definition 1.6 (Minimum alignment cost).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], \forall u \in \operatorname{List}\left(\alpha\right),\; \forall v \in \operatorname{List}\left(\alpha\right),\; \operatorname{dlev}\left(u, v\right) = \operatorname{sInf}\left(\{c: \mathrm{Nat} \mid \exists A \in \operatorname{Alignment}\left(\alpha\right),\; (\operatorname{topRow}\left(A\right) = u) \land \left((\operatorname{bottomRow}\left(A\right) = v) \land (\operatorname{cost}\left(A\right) = c)\right)\}\right)$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.dlev` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

The paper defines edit distance by edit operations and states that it equals the minimum cost of an alignment. Here dlev is the stated alignment characterization: sInf is the infimum of the natural alignment costs, not an executable evaluation. A separate edit-script datatype is not defined.

**Definition 1.7 (Dynamic-programming distance).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], (\forall ys \in \operatorname{List}\left(\alpha\right),\; \operatorname{levenshtein}\left([], ys\right) = \operatorname{length}\left(ys\right)) \land \left((\forall xs \in \operatorname{List}\left(\alpha\right),\; \operatorname{levenshtein}\left(xs, []\right) = \operatorname{length}\left(xs\right)) \land (\forall x \in \alpha,\; \forall y \in \alpha,\; \forall xs \in \operatorname{List}\left(\alpha\right),\; \forall ys \in \operatorname{List}\left(\alpha\right),\; \operatorname{levenshtein}\left(\operatorname{cons}\left(x, xs\right), \operatorname{cons}\left(y, ys\right)\right) = \operatorname{min}\left(\operatorname{levenshtein}\left(xs, \operatorname{cons}\left(y, ys\right)\right) + 1, \operatorname{min}\left(\operatorname{levenshtein}\left(\operatorname{cons}\left(x, xs\right), ys\right) + 1, \operatorname{levenshtein}\left(xs, ys\right) + \operatorname{ite}\left(x = y, 0, 1\right)\right)\right))\right)$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.levenshtein` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

The Wagner--Fischer recurrence computes the distance by deletion, insertion, and substitution steps. Its fuel is the sum of the two word lengths.

**Theorem 1.8 (The recurrence computes minimum alignment cost).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], \forall u \in \operatorname{List}\left(\alpha\right),\; \forall v \in \operatorname{List}\left(\alpha\right),\; \operatorname{levenshtein}\left(u, v\right) = \operatorname{dlev}\left(u, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.levenshtein_eq_dlev` (`✓ std3`). ∎

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

Every alignment costs at least the recurrence value, and an alignment attaining that value can be constructed along a minimizing branch.

**Definition 1.9 (The Levenshtein neighborhood).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], \forall w \in \operatorname{List}\left(\alpha\right),\; \forall d \in \mathrm{Nat},\; \operatorname{neighborhood}\left(w, d\right) = \{x: \operatorname{List}\left(\alpha\right) \mid \operatorname{dlev}\left(x, w\right) \le d\}$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.neighborhood` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

Equation (2.1) is represented literally as the set of words whose distance from w is at most d.

**Definition 1.10 (The condensed neighborhood).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], \forall w \in \operatorname{List}\left(\alpha\right),\; \forall d \in \mathrm{Nat},\; \operatorname{condensed}\left(w, d\right) = \{x: \operatorname{List}\left(\alpha\right) \mid (x \in \operatorname{neighborhood}\left(w, d\right)) \land (\forall y \in \operatorname{List}\left(\alpha\right),\; (\operatorname{IsPrefix}\left(y, x\right)) \Rightarrow ((y \ne x) \Rightarrow (\neg (y \in \operatorname{neighborhood}\left(w, d\right)))))\}$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.condensed` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

Equation (2.2) retains exactly the neighborhood words with no distinct prefix in the same neighborhood. IsPrefix(y,x) is Lean's y <+: x relation.

**Definition 1.11 (The super condensed neighborhood).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], \forall w \in \operatorname{List}\left(\alpha\right),\; \forall d \in \mathrm{Nat},\; \operatorname{superCondensed}\left(w, d\right) = \{x: \operatorname{List}\left(\alpha\right) \mid (x \in \operatorname{neighborhood}\left(w, d\right)) \land (\forall y \in \operatorname{List}\left(\alpha\right),\; (\operatorname{IsInfix}\left(y, x\right)) \Rightarrow ((y \ne x) \Rightarrow (\neg (y \in \operatorname{neighborhood}\left(w, d\right)))))\}$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.superCondensed` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

Equation (2.3) retains exactly the neighborhood words with no distinct contiguous subword in the same neighborhood. IsInfix(y,x) is Lean's y <:+: x relation.

**Definition 1.12 (Condensed unary minimality).**

$$(claimCondensed) \Leftrightarrow (\forall \alpha: Type, [\operatorname{Fintype}\left(\alpha\right)], [\operatorname{DecidableEq}\left(\alpha\right)], \forall n \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall a \in \alpha,\; \forall w \in \operatorname{List}\left(\alpha\right),\; (\operatorname{length}\left(w\right) = n) \Rightarrow (\lvert \operatorname{condensed}\left(\operatorname{replicate}\left(n, a\right), d\right) \rvert \le \lvert \operatorname{condensed}\left(w, d\right) \rvert))$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimCondensed` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

The closing question reads: "It was also shown in [6] that unary words have the smallest neighborhoods among all words of the same length over a given alphabet, thus leading to lower bounds for the size of neighborhoods. It is thus natural to ask if a similar property holds for condensed and super condensed neighborhoods, namely that unary words have the smallest condensed or super condensed neighborhoods." The definitions read: "N(w, d) = {x ∈ Σ* | d_lev(x, w) ≤ d}" (2.1); "CN(w, d) = N(w, d) \ N(w, d)Σ⁺" (2.2); and "SCN(w, d) = N(w, d) \ (Σ*N(w, d)Σ⁺ ∪ Σ⁺N(w, d)Σ*)" (2.3). The displayed proposition is the condensed half of that question, with no restriction on d.

**Theorem 1.13 (The condensed claim fails at n = 3 and d = 2).**

$$\neg claimCondensed$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed` (`✓ std3`). ∎

*Resolves.* `Problems/chauve-zhang-unary-neighborhood-minimality` (refuted) by `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chauve-zhang-unary-neighborhood-minimality","declaration_gid":"D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Over the binary alphabet, CN(000,2) is {0, 10, 110}, while CN(001,2) is {0, 1}. Their cardinalities are three and two, so 000 does not minimize the condensed neighborhood.

**Definition 1.14 (Super condensed unary minimality).**

$$(claimSuperCondensed) \Leftrightarrow (\forall \alpha: Type, [\operatorname{Fintype}\left(\alpha\right)], [\operatorname{DecidableEq}\left(\alpha\right)], \forall n \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall a \in \alpha,\; \forall w \in \operatorname{List}\left(\alpha\right),\; (\operatorname{length}\left(w\right) = n) \Rightarrow (\lvert \operatorname{superCondensed}\left(\operatorname{replicate}\left(n, a\right), d\right) \rvert \le \lvert \operatorname{superCondensed}\left(w, d\right) \rvert))$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimSuperCondensed` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

The closing question reads: "It was also shown in [6] that unary words have the smallest neighborhoods among all words of the same length over a given alphabet, thus leading to lower bounds for the size of neighborhoods. It is thus natural to ask if a similar property holds for condensed and super condensed neighborhoods, namely that unary words have the smallest condensed or super condensed neighborhoods." The definitions read: "N(w, d) = {x ∈ Σ* | d_lev(x, w) ≤ d}" (2.1); "CN(w, d) = N(w, d) \ N(w, d)Σ⁺" (2.2); and "SCN(w, d) = N(w, d) \ (Σ*N(w, d)Σ⁺ ∪ Σ⁺N(w, d)Σ*)" (2.3). The displayed proposition is the super condensed half of that question, with no restriction on d.

**Theorem 1.15 (The super condensed claim fails at n = 4 and d = 1).**

$$\neg claimSuperCondensed$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultSuperCondensed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over the binary alphabet, SCN(0000,1) is {000, 0010, 0100}, while SCN(0011,1) is {001, 011}. Their cardinalities are three and two, so 0000 does not minimize the super condensed neighborhood.

## References

- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.Alignment`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.Column`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.bottomRow`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimCondensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimSuperCondensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.condensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.cost`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.dlev`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.levenshtein`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.levenshtein_eq_dlev`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.neighborhood`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultSuperCondensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.superCondensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.topRow`
