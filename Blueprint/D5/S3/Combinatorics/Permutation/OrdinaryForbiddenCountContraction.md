# Ordinary contraction of forbidden counts

## Abstract

Ordinary deletion contracts the actual front and back forbidden counts by the corresponding first high-prefix cardinalities.

Positions and row labels are zero-based. For K columns, sigma permutes K plus one rows and pi permutes K column labels. At column i the front row is sigma(pi(i)), and the back row is sigma(pi(i)+1): increment the position pi(i) before evaluating sigma. The distinguished back endpoint is the actual row sigma(0).

**Definition 1.1 (Eligibility at both thresholds).**

Lean statement: `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.Eligible`

*Formalization.* `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.Eligible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For every column i, the front row label is strictly below F(i) and the back row label is strictly below G(i).

**Definition 1.2 (Actual forbidden front targets).**

Lean statement: `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.Front`

*Formalization.* `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.Front` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For a column i, collect exactly the ordinary columns j with i less than j, front row at i strictly below front row at j, pi(j) strictly below pi(i), and F(i) at most the front row label at j. There is no distinguished front target.

**Definition 1.3 (Actual forbidden back targets and endpoint).**

Lean statement: `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.Back`

*Formalization.* `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.Back` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For a column i, an ordinary target some j belongs exactly when i is less than j, back row at i is strictly below back row at j, pi(j) is strictly below pi(i), and G(i) is at most the back row label at j. The target none belongs exactly when the back row at i is strictly below sigma(0) and G(i) is at most sigma(0). Thus none represents the distinguished target at the endpoint, with its actual row sigma(0), and has no column label.

**Definition 1.4 (The two forbidden cardinalities).**

Lean statement: `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.ForbiddenCount`

*Formalization.* `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.ForbiddenCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

The first coordinate is the sum over all columns i of the cardinality of Front at i; the second coordinate is the corresponding sum of the cardinalities of Back. These count the actual restricted target sets, including the distinguished target in the back coordinate.

**Theorem 1.5 (Both exact ordinary contraction equations).**

Lean statement: `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.ordinary_forbidden_count_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.ordinary_forbidden_count_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For every natural number n, let F and G map Fin(n plus one) to natural numbers, let sigma permute Fin(n plus two), and let pi permute Fin(n plus one). Assume hF: F is monotone; hG: G is monotone; hFG: F(i) is at most G(i) for every i; and hel: Eligible F G sigma pi. Set t to pi(0), Ft(i) to F(i plus one) minus one, and Gt(i) to G(i plus one) minus one for i in Fin(n), using natural subtraction. Let s be the existing cut of sigma at row position t, and p the existing cut of pi at position zero. These tails permute Fin(n plus one) and Fin(n), respectively. Both equalities hold jointly: the first coordinate of ForbiddenCount F G sigma pi equals the first coordinate of ForbiddenCount Ft Gt s p plus the cardinality of the row positions u in Fin(n plus two) with u less than t and F(0) at most sigma(u); the second coordinate of ForbiddenCount F G sigma pi equals the second coordinate of ForbiddenCount Ft Gt s p plus the cardinality of the row positions u in Fin(n plus two) with u less than t and G(0) at most sigma(u). Ordinary deletion leaves the tail eligible. The front target map j to pi(j) and the back target map none to zero, some j to pi(j) plus one give bijections onto the respective high row prefixes. Increasing position and label deletion transports the surviving high-prefix sets to the tail, and summing separates the first column. The case n equal to zero has a one-row, zero-column tail. The first position t equal to zero has an empty prefix, and the final column position t equal to n still has its successor row at n plus one.

For every admissible board with n plus one columns, let its zero-based row lengths lambda and mu be antitone, with mu(i) at most lambda(i), lambda(i) at most n plus one minus i, and mu(i) at most n minus i. Set F(i) to n plus two minus lambda(i) and G(i) to n plus two minus mu(i). These thresholds are monotone with F(i) at most G(i), and the theorem applies to every eligible permutation pair on this board. The tail thresholds become n plus one minus lambda(i plus one) and n plus one minus mu(i plus one). In one-based row labels, the two added cardinalities count the prefix rows strictly above the first front and back thresholds, respectively.

These are the two ordinary forbidden-count equations. The repaired low-row replacement, its full eligibility and bijection laws, and the repaired integer weight increment d plus b require additional results.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.Back`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.Eligible`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.ForbiddenCount`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.Front`
- Truth anchor: `D5/S3/Combinatorics/Permutation/OrdinaryForbiddenCountContraction.ordinary_forbidden_count_contraction`
- Dependency: [D5/S3/Combinatorics/Permutation/CoupledRepairedLeftInverse](CoupledRepairedLeftInverse.md)
