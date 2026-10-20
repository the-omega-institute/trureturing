# The Steiner characteristic polynomial peaks beyond n minus one

## Abstract

The path on sixteen vertices refutes the proposed Steiner coefficient peak.

**Definition 1.1 (Steiner distance on a path).**

$$\forall n \in \operatorname{Nat},\; \forall S \in \operatorname{Finset}\left(\operatorname{Nat}\right),\; \operatorname{steiner}\left(n, S\right) = \operatorname{sInf}\left(\{ k: \operatorname{Nat} \mid \exists a \in \operatorname{Nat},\; \exists b \in \operatorname{Nat},\; (1 \le a) \land ((a \le b) \land ((b \le n) \land ((b - a = k) \land (\forall v \in \operatorname{Nat},\; (v \in S) \Rightarrow ((a \le v) \land (v \le b)))))) \}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.steiner` (`✓ std3`).

*Citation.* S. Jana; I. Mahato; S. Sivasubramanian (2025). *Unimodality and peak location of the characteristic polynomials of two distance matrices of trees*. DOI: [10.1007/s40314-025-03163-5](https://doi.org/10.1007/s40314-025-03163-5). URL: <https://arxiv.org/abs/2407.03309v1>.

*Commentary.*

Page 3 states: “the entry of 𝔇_2(T) corresponding to the row {i,j} and column {k,l} is the minimum number of edges among all connected subtrees of T whose vertex set contains the four vertices i, j, k and l.” On the path with vertices 1 through n, connected subtrees are intervals from a to b and have b−a edges. The infimum is taken in Nat; all subtraction below is natural subtraction.

**Definition 1.2 (The ordered path basis).**

$$\forall n \in \operatorname{Nat},\; \forall t \in \operatorname{Fin}\left((2 \cdot n - 3)\right),\; \operatorname{basis}\left(n, t\right) = \operatorname{if} \operatorname{Nat}.\operatorname{mod}\left(\operatorname{val}\left(t\right), 2\right) = 0 \operatorname{then} \{ \operatorname{Nat}.\operatorname{div}\left(\operatorname{val}\left(t\right), 2\right) + 1, \operatorname{Nat}.\operatorname{div}\left(\operatorname{val}\left(t\right), 2\right) + 2 \} \operatorname{else} \{ \operatorname{Nat}.\operatorname{div}\left(\operatorname{val}\left(t\right), 2\right) + 1, \operatorname{Nat}.\operatorname{div}\left(\operatorname{val}\left(t\right), 2\right) + 3 \}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.basis` (`✓ std3`).

*Citation.* S. Jana; I. Mahato; S. Sivasubramanian (2025). *Unimodality and peak location of the characteristic polynomials of two distance matrices of trees*. DOI: [10.1007/s40314-025-03163-5](https://doi.org/10.1007/s40314-025-03163-5). URL: <https://arxiv.org/abs/2407.03309v1>.

*Commentary.*

Remark 23, page 14, states: “Let P_n be the path on n vertices with edges e_i = {i, i+1} for i = 1, …, n−1. Let B = (e_1, f_1, e_2, f_2, …, e_{n−2}, f_{n−2}, e_{n−1}) be the ordered basis for the row space of 𝔇_2(P_n) where f_j = {j, j+2}, for j = 1, …, n−2.” Even zero-based indices enumerate the edges e_i and odd indices enumerate the pairs f_j. Nat.div and Nat.mod denote integer quotient and remainder.

**Definition 1.3 (The principal Steiner distance matrix).**

$$\forall n \in \operatorname{Nat},\; \operatorname{D}\left(n\right): \operatorname{Matrix}\left(\operatorname{Fin}\left((2 \cdot n - 3)\right), \operatorname{Fin}\left((2 \cdot n - 3)\right), \operatorname{Int}\right) = (\operatorname{fun} t: \operatorname{Fin}\left((2 \cdot n - 3)\right), u: \operatorname{Fin}\left((2 \cdot n - 3)\right) \mapsto (\operatorname{steiner}\left(n, \operatorname{basis}\left(n, t\right) \cup \operatorname{basis}\left(n, u\right)\right): \operatorname{Int}))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.D` (`✓ std3`).

*Citation.* S. Jana; I. Mahato; S. Sivasubramanian (2025). *Unimodality and peak location of the characteristic polynomials of two distance matrices of trees*. DOI: [10.1007/s40314-025-03163-5](https://doi.org/10.1007/s40314-025-03163-5). URL: <https://arxiv.org/abs/2407.03309v1>.

*Commentary.*

Page 14 states: “We denote by 𝔇_{P_n} the matrix 𝔇_2(P_n)[B, B], that is, 𝔇_{P_n} := 𝔇_2(P_n)[B, B].” Its integer entry is the Steiner distance of the union of the row and column pairs; repeated vertices are counted only once.

**Definition 1.4 (Conjecture 29).**

$$\operatorname{claim} = (\forall n \in \operatorname{Nat},\; (5 < n) \Rightarrow (\forall ell \in \operatorname{Nat},\; (ell \le 2 \cdot n - 4) \Rightarrow ((\forall i \in \operatorname{Nat},\; (i \le 2 \cdot n - 4) \Rightarrow (\lvert \operatorname{Polynomial}.\operatorname{coeff}\left(\operatorname{Matrix}.\operatorname{charpoly}\left(\operatorname{D}\left(n\right)\right), i\right) \rvert \le \lvert \operatorname{Polynomial}.\operatorname{coeff}\left(\operatorname{Matrix}.\operatorname{charpoly}\left(\operatorname{D}\left(n\right)\right), ell\right) \rvert)) \Rightarrow (ell = n - 1))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.claim` (`✓ std3`).

*Citation.* S. Jana; I. Mahato; S. Sivasubramanian (2025). *Unimodality and peak location of the characteristic polynomials of two distance matrices of trees*. DOI: [10.1007/s40314-025-03163-5](https://doi.org/10.1007/s40314-025-03163-5). URL: <https://arxiv.org/abs/2407.03309v1>.

*Commentary.*

Conjecture 29, page 18, states: “For a path P_n on n > 5 vertices, if CharPoly_{𝔇_{P_n}}(x) = Σ_{i=0}^{2n−3} a_i x^i and |a_ℓ| = max{|a_0|, |a_1|, …, |a_{2n−4}|}, then ℓ = n − 1.” Matrix.charpoly is det(xI−D); the quantified inequalities express attainment of the maximum over precisely the nonleading coefficients, from zero through 2n−4.

**Theorem 1.5 (Refutation at sixteen vertices).**

$$\neg (\forall n \in \operatorname{Nat},\; (5 < n) \Rightarrow (\forall ell \in \operatorname{Nat},\; (ell \le 2 \cdot n - 4) \Rightarrow ((\forall i \in \operatorname{Nat},\; (i \le 2 \cdot n - 4) \Rightarrow (\lvert \operatorname{Polynomial}.\operatorname{coeff}\left(\operatorname{Matrix}.\operatorname{charpoly}\left(\operatorname{D}\left(n\right)\right), i\right) \rvert \le \lvert \operatorname{Polynomial}.\operatorname{coeff}\left(\operatorname{Matrix}.\operatorname{charpoly}\left(\operatorname{D}\left(n\right)\right), ell\right) \rvert)) \Rightarrow (ell = n - 1))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/jana-mahato-sivasubramanian-2025-steiner-path-peak` (refuted) by `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jana-mahato-sivasubramanian-2025-steiner-path-peak","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* S. Jana; I. Mahato; S. Sivasubramanian (2025). *Unimodality and peak location of the characteristic polynomials of two distance matrices of trees*. DOI: [10.1007/s40314-025-03163-5](https://doi.org/10.1007/s40314-025-03163-5). URL: <https://arxiv.org/abs/2407.03309v1>.

*Commentary.*

For n=16, the coefficient magnitudes at indices 15 and 16 are 939602445008 and 956326515118. The latter dominates all coefficients at indices zero through 28, while 16 differs from 16−1. The exact coefficient vector in ascending order is (−15, −813, −20869, −337481, −3858223, −33170333, −222721740, −1197384332, −5242633806, −18915546250, −56691343231, −141862420523, −297217763703, −521743703045, −766504605632, −939602445008, −956326515118, −802497798666, −549972018662, −304018467998, −133385920554, −45480785950, −11720987416, −2198470872, −284539268, −23452364, −1076103, −20755, −43, 1). The interval formula evaluates the matrix entries. An integer matrix K satisfies A K = K C for the coefficient companion matrix C, and a left inverse of K modulo seven proves its determinant nonzero. Characteristic-polynomial invariance and the coefficient multiplication theorem then identify the polynomial. This refutes the proposed exact peak; it leaves the source's upper bound and its separate coefficient identities unaffected. The exact peak for unbounded n remains an open question.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.D`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.basis`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.steiner`
- Dependency: [D5/S3/Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial](../../Constants/Moments/CoefficientDrivenJacobiCharacteristicPolynomial.md)
