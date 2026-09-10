# The average-path conjecture of A380392

## Abstract

The exact average number of all-one monotone paths in binary square matrices.

**Theorem 1.1 (Mean number of paths).**

$$\forall n\in\mathbb{N}, 1 \le n \implies \frac{\sum_{M\in\mathcal{M}_n}\operatorname{pathCount}\left(M\right)}{2^{n \cdot n}} = \frac{\operatorname{choose}\left(2n-2, n-1\right)}{2^{2n-1}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Paths/MonotoneOnePaths.mean_monotone_one_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Tyler Rascoe (2025). *A380392 — binary matrices counted by their South-East paths of ones*. URL: <https://oeis.org/A380392>.

*Commentary.*

For n at least 1, a binary matrix assigns a Boolean to each of its n squared cells. In the formula, M_n is the set of all such matrices and choose is the binomial coefficient. Every matrix receives equal weight. The function pathCount counts paths from the top left to the bottom right whose visited cells are all true. Every step moves exactly one cell east or south; both endpoints are included.

For a square of side k+1, a path is encoded by the k east-step positions among 2k steps. At time t its coordinates count the east and south steps in the prefix. Their sum is t, so different times give different cells. Each path therefore visits 2k+1 cells.

Fix a path. Arbitrary Boolean assignments on the remaining k squared cells extend uniquely to matrices supporting that path, by filling its cells with true. Exchanging the finite sums over matrices and paths gives the binomial number of paths times the number of such assignments. Dividing by the number of all matrices gives the formula. At n=1 the only path visits the single cell. The theorem makes no claim about the zero-size row or the full distribution of path counts.

## References

- Truth anchor: `D5/S3/Arith/Paths/MonotoneOnePaths.mean_monotone_one_paths`
