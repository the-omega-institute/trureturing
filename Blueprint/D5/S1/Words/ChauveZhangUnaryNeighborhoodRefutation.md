# Unary Neighborhood Minimality Refuted

## Abstract

Binary words refute unary minimality for condensed and super condensed neighborhoods.

**Definition 1.1 (Levenshtein distance).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], (\forall ys \in \operatorname{List}\left(\alpha\right),\; \operatorname{levenshtein}\left([], ys\right) = \operatorname{length}\left(ys\right)) \land \left((\forall xs \in \operatorname{List}\left(\alpha\right),\; \operatorname{levenshtein}\left(xs, []\right) = \operatorname{length}\left(xs\right)) \land (\forall x \in \alpha,\; \forall y \in \alpha,\; \forall xs \in \operatorname{List}\left(\alpha\right),\; \forall ys \in \operatorname{List}\left(\alpha\right),\; \operatorname{levenshtein}\left(\operatorname{cons}\left(x, xs\right), \operatorname{cons}\left(y, ys\right)\right) = \operatorname{min}\left(\operatorname{levenshtein}\left(xs, \operatorname{cons}\left(y, ys\right)\right) + 1, \operatorname{min}\left(\operatorname{levenshtein}\left(\operatorname{cons}\left(x, xs\right), ys\right) + 1, \operatorname{levenshtein}\left(xs, ys\right) + \operatorname{ite}\left(x = y, 0, 1\right)\right)\right))\right)$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.levenshtein` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

The executable distance uses the Wagner--Fischer recurrence with insertion, deletion, and substitution cost one. ASSUMED-UNVERIFIED: no edit-script datatype or proof that this recurrence equals the minimum edit-script cost is formalized here.

**Definition 1.2 (The Levenshtein neighborhood).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], \forall w \in \operatorname{List}\left(\alpha\right),\; \forall d \in \mathrm{Nat},\; \operatorname{neighborhood}\left(w, d\right) = \{x: \operatorname{List}\left(\alpha\right) \mid \operatorname{levenshtein}\left(x, w\right) \le d\}$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.neighborhood` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

Equation (2.1) is represented literally as the set of words whose distance from w is at most d.

**Definition 1.3 (The condensed neighborhood).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], \forall w \in \operatorname{List}\left(\alpha\right),\; \forall d \in \mathrm{Nat},\; \operatorname{condensed}\left(w, d\right) = \{x: \operatorname{List}\left(\alpha\right) \mid (x \in \operatorname{neighborhood}\left(w, d\right)) \land (\forall y \in \operatorname{List}\left(\alpha\right),\; (\operatorname{IsPrefix}\left(y, x\right)) \Rightarrow ((y \ne x) \Rightarrow (\neg y \in \operatorname{neighborhood}\left(w, d\right))))\}$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.condensed` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

Equation (2.2) retains exactly the neighborhood words with no distinct prefix in the same neighborhood. IsPrefix(y,x) is Lean's y <+: x relation.

**Definition 1.4 (The super condensed neighborhood).**

$$\forall \alpha: Type, [\operatorname{DecidableEq}\left(\alpha\right)], \forall w \in \operatorname{List}\left(\alpha\right),\; \forall d \in \mathrm{Nat},\; \operatorname{superCondensed}\left(w, d\right) = \{x: \operatorname{List}\left(\alpha\right) \mid (x \in \operatorname{neighborhood}\left(w, d\right)) \land (\forall y \in \operatorname{List}\left(\alpha\right),\; (\operatorname{IsInfix}\left(y, x\right)) \Rightarrow ((y \ne x) \Rightarrow (\neg y \in \operatorname{neighborhood}\left(w, d\right))))\}$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.superCondensed` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

Equation (2.3) retains exactly the neighborhood words with no distinct contiguous subword in the same neighborhood. IsInfix(y,x) is Lean's y <:+: x relation.

**Definition 1.5 (Condensed unary minimality).**

$$(claimCondensed) \Leftrightarrow (\forall \alpha: Type, [\operatorname{Fintype}\left(\alpha\right)], [\operatorname{DecidableEq}\left(\alpha\right)], \forall n \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall a \in \alpha,\; \forall w \in \operatorname{List}\left(\alpha\right),\; (\operatorname{length}\left(w\right) = n) \Rightarrow (\lvert \operatorname{condensed}\left(\operatorname{replicate}\left(n, a\right), d\right) \rvert \le \lvert \operatorname{condensed}\left(w, d\right) \rvert))$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimCondensed` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

The closing question reads: "It is thus natural to ask if a similar property holds for condensed and super condensed neighborhoods, namely that unary words have the smallest condensed or super condensed neighborhoods." The definitions read: "N(w, d) = {x ∈ Σ* | d_lev(x, w) ≤ d}" (2.1); "CN(w, d) = N(w, d) \ N(w, d)Σ⁺" (2.2); and "SCN(w, d) = N(w, d) \ (Σ*N(w, d)Σ⁺ ∪ Σ⁺N(w, d)Σ*)" (2.3). The displayed proposition is the condensed half of that question, with no restriction on d.

**Theorem 1.6 (The condensed claim fails at n = 3 and d = 2).**

$$\neg claimCondensed$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over the binary alphabet, CN(000,2) is {0, 10, 110}, while CN(001,2) is {0, 1}. Their cardinalities are three and two, so 000 does not minimize the condensed neighborhood.

**Definition 1.7 (Super condensed unary minimality).**

$$(claimSuperCondensed) \Leftrightarrow (\forall \alpha: Type, [\operatorname{Fintype}\left(\alpha\right)], [\operatorname{DecidableEq}\left(\alpha\right)], \forall n \in \mathrm{Nat},\; \forall d \in \mathrm{Nat},\; \forall a \in \alpha,\; \forall w \in \operatorname{List}\left(\alpha\right),\; (\operatorname{length}\left(w\right) = n) \Rightarrow (\lvert \operatorname{superCondensed}\left(\operatorname{replicate}\left(n, a\right), d\right) \rvert \le \lvert \operatorname{superCondensed}\left(w, d\right) \rvert))$$

*Formalization.* `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimSuperCondensed` (`✓ std3`).

*Citation.* Cedric Chauve, Louxin Zhang (2025). *On the size of the neighborhoods of a word*. DOI: [10.48550/arXiv.2505.13796](https://doi.org/10.48550/arXiv.2505.13796). URL: <https://arxiv.org/abs/2505.13796v2>.

*Commentary.*

The closing question reads: "It is thus natural to ask if a similar property holds for condensed and super condensed neighborhoods, namely that unary words have the smallest condensed or super condensed neighborhoods." The definitions read: "N(w, d) = {x ∈ Σ* | d_lev(x, w) ≤ d}" (2.1); "CN(w, d) = N(w, d) \ N(w, d)Σ⁺" (2.2); and "SCN(w, d) = N(w, d) \ (Σ*N(w, d)Σ⁺ ∪ Σ⁺N(w, d)Σ*)" (2.3). The displayed proposition is the super condensed half of that question, with no restriction on d.

**Theorem 1.8 (The super condensed claim fails at n = 4 and d = 1).**

$$\neg claimSuperCondensed$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultSuperCondensed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over the binary alphabet, SCN(0000,1) is {000, 0010, 0100}, while SCN(0011,1) is {001, 011}. Their cardinalities are three and two, so 0000 does not minimize the super condensed neighborhood.

## References

- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimCondensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.claimSuperCondensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.condensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.levenshtein`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.neighborhood`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultSuperCondensed`
- Truth anchor: `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.superCondensed`
