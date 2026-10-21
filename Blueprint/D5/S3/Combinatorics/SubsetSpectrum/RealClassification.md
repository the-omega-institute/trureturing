# Classification of real even-subset spectra

## Abstract

Odd-length real even-subset spectra classify coefficients up to even zero-sum sign permutations.

**Theorem 1.1 (The full odd-length classification).**

$$\forall m \in \mathrm{Nat},\; \left(3 \le m \land \operatorname{Odd}\left(m\right)\right) \Rightarrow \left(\forall b \in \operatorname{Fin}\left(m\right) \to \mathrm{Real},\; \forall c \in \operatorname{Fin}\left(m\right) \to \mathrm{Real},\; \operatorname{E}\left(b\right) = \operatorname{E}\left(c\right) \Leftrightarrow \left(\exists sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(m\right)\right),\; \exists I \in \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right),\; \operatorname{Even}\left(\operatorname{card}\left(I\right)\right) \land \left(\operatorname{sum}\left(I, b\right) = 0 \land \left(\forall i \in \operatorname{Fin}\left(m\right),\; \left(i \in I \Rightarrow \operatorname{c}\left(\operatorname{sigma}\left(i\right)\right) = -\operatorname{b}\left(i\right)\right) \land \left(\left(\neg i \in I\right) \Rightarrow \operatorname{c}\left(\operatorname{sigma}\left(i\right)\right) = \operatorname{b}\left(i\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SubsetSpectrum/RealClassification.real_even_spectrum_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Manjul Bhargava (2026). *The existence and uniqueness of magic-faced hypercubes, and applications to Khajuraho most-perfect magic squares, cubes, and hypercubes*. URL: <https://arxiv.org/html/2609.26762v1>.

*Commentary.*

For every odd m at least three and arbitrary real families b,c on Fin m, the even occurrence spectra are equal if and only if there exist a permutation sigma of Fin m and an index set I with even cardinality and sum_I b=0 such that c(sigma i)=-b(i) on I and c(sigma i)=b(i) off I. All zero and repeated coefficients remain in scope. The first moment and complement reflection recover the full spectra; their minima determine the signed normalization. Nonnegative recovery then matches absolute-value occurrences by a permutation. Equality of totals forces the flip sum to vanish. If its parity is odd, a zero coefficient permits a parity repair; without a zero coefficient, the unique minimizing subset prevents odd parity. Conversely, symmetric difference with an even zero-sum index set preserves all even subset sums and their multiplicities.

## References

- Truth anchor: `D5/S3/Combinatorics/SubsetSpectrum/RealClassification.real_even_spectrum_classification`
- Dependency: [D5/S3/Combinatorics/SubsetSpectrum/NonnegativeRecovery](NonnegativeRecovery.md)
- Dependency: [D5/S3/Combinatorics/SubsetSpectrum/SignAction](SignAction.md)
