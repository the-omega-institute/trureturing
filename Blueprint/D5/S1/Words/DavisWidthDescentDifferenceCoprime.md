# Davis's Coprime Width-Descent Difference Formula

## Abstract

Coprime-width descent differences have a shifted Eulerian distribution.

All sizes and widths are natural numbers. Perm(Fin(n)) is the symmetric group on positions 0 through n-1. The symbol q^z denotes the Laurent monomial T(z), and every finite sum is taken in the Laurent polynomial ring over the integers.

**Definition 1.1 (Width-k descents).**

$$\forall n \in \mathrm{Nat}, k \in \mathrm{Nat}, sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{widthDescents}\left(k, sigma\right) = \left|\left\{i \in \operatorname{Fin}\left(n\right) \mid (\operatorname{val}\left(i\right) + k < n) \land (\operatorname{apply}\left(sigma, \operatorname{val}\left(i\right) + k\right) < \operatorname{apply}\left(sigma, i\right))\right\}\right|$$

*Formalization.* `D5/S1/Words/DavisWidthDescentDifferenceCoprime.widthDescents` (`✓ std3`).

*Citation.* Robert Davis (2017). *Width-k Generalizations of Classical Permutation Statistics*. DOI: [10.48550/arXiv.1701.04788](https://doi.org/10.48550/arXiv.1701.04788). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL20/Davis/davis6.pdf>.

*Commentary.*

A position i contributes exactly when val(i)+k<n and the value at i is greater than the value k positions later. This is the zero-based form of the paper's index range [n-k].

**Definition 1.2 (The Eulerian polynomial as a descent enumerator).**

$$\forall m \in \mathrm{Nat},\; \operatorname{eulerian}\left(m\right) = \sum_{tau \in \operatorname{Perm}\left(\operatorname{Fin}\left(m\right)\right)} q^{(\operatorname{widthDescents}\left(1, tau\right): \mathrm{Int})}$$

*Formalization.* `D5/S1/Words/DavisWidthDescentDifferenceCoprime.eulerian` (`✓ std3`).

*Citation.* Robert Davis (2017). *Width-k Generalizations of Classical Permutation Statistics*. DOI: [10.48550/arXiv.1701.04788](https://doi.org/10.48550/arXiv.1701.04788). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL20/Davis/davis6.pdf>.

*Commentary.*

The exponent is the ordinary width-one descent count. The paper identifies this descent generating function with A_m by MacMahon's theorem. Its separate infinite-series characterization is not used here.

**Definition 1.3 (The width-descent difference polynomial).**

$$\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; \operatorname{G}\left(n, k\right) = \sum_{sigma \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right)} q^{(\operatorname{widthDescents}\left(k, sigma\right): \mathrm{Int}) - (\operatorname{widthDescents}\left(n - k, sigma\right): \mathrm{Int})}$$

*Formalization.* `D5/S1/Words/DavisWidthDescentDifferenceCoprime.G` (`✓ std3`).

*Citation.* Robert Davis (2017). *Width-k Generalizations of Classical Permutation Statistics*. DOI: [10.48550/arXiv.1701.04788](https://doi.org/10.48550/arXiv.1701.04788). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL20/Davis/davis6.pdf>.

*Commentary.*

For each permutation, the Laurent exponent is the integer difference between the width-k descent count and the width-(n-k) descent count.

**Definition 1.4 (Davis's Conjecture 9).**

$$claim \Leftrightarrow (\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; (1 \le k) \Rightarrow ((k < n) \Rightarrow ((\operatorname{Coprime}\left(k, n\right)) \Rightarrow (\operatorname{G}\left(n, k\right) = (n: \operatorname{LaurentPolynomial}\left(\mathrm{Int}\right)) \cdot q^{1 - (k: \mathrm{Int})} \cdot \operatorname{eulerian}\left(n - 1\right)))))$$

*Formalization.* `D5/S1/Words/DavisWidthDescentDifferenceCoprime.claim` (`✓ std3`).

*Citation.* Robert Davis (2017). *Width-k Generalizations of Classical Permutation Statistics*. DOI: [10.48550/arXiv.1701.04788](https://doi.org/10.48550/arXiv.1701.04788). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL20/Davis/davis6.pdf>.

*Commentary.*

The printed statement is: "Conjecture 9. If gcd(k, n) = 1, then G_{n,k}(q) = nq^{1-k}A_{n-1}(q)." The surrounding paragraph gives the range 1 <= k < n. The displayed formula uses the paper's own identification of A_{n-1} with its descent generating function.

**Theorem 1.5 (The coprime-width formula).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/DavisWidthDescentDifferenceCoprime.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robert Davis (2017). *Width-k Generalizations of Classical Permutation Statistics*. DOI: [10.48550/arXiv.1701.04788](https://doi.org/10.48550/arXiv.1701.04788). URL: <https://cs.uwaterloo.ca/journals/JIS/VOL20/Davis/davis6.pdf>.

*Commentary.*

Multiplication by k modulo n first reindexes the width comparisons into one cycle. Rotating a permutation until its maximum is last then decomposes the cyclic descent enumerator into n copies of the ordinary descent enumerator on n-1 letters, with one additional descent.

## References

- Truth anchor: `D5/S1/Words/DavisWidthDescentDifferenceCoprime.G`
- Truth anchor: `D5/S1/Words/DavisWidthDescentDifferenceCoprime.claim`
- Truth anchor: `D5/S1/Words/DavisWidthDescentDifferenceCoprime.eulerian`
- Truth anchor: `D5/S1/Words/DavisWidthDescentDifferenceCoprime.result`
- Truth anchor: `D5/S1/Words/DavisWidthDescentDifferenceCoprime.widthDescents`
