# Two measurement settings suffice for quantum advantage in random access codes

## Abstract

For every n and d at least two, a d-dimensional random access code with two projective measurement settings strictly outperforms every classical strategy with shared randomness.

Fin(n) denotes the indices 0 through n minus one. A word x is a function from Fin(n) to Fin(d). Alice receives a uniformly chosen word and sends one d-dimensional system; Bob receives a uniformly chosen index j and guesses x(j). The annotations (n : ℝ) and (d : ℝ) denote the natural-number casts to the reals. Complex conjugation is denoted by an overline and is Lean's star on ℂ; star on vectors acts coordinatewise. All sums range over the displayed finite domains.

**Definition 1.1 (The deterministic classical value).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (E: ((\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)) \to \operatorname{Fin}\left(d\right))), (\forall (D: (\operatorname{Fin}\left(d\right) \to (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)))), (\operatorname{deterministicValue}\left(n, d, E, D\right) = \frac{1}{((n: \mathbb{R}) \cdot (d: \mathbb{R})^{n})} \cdot \sum_{x: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right))} (\sum_{j: \operatorname{Fin}\left(n\right)} (\operatorname{ite}\left(D\left(E\left(x\right)\right)\left(j\right) = x\left(j\right), (1: \mathbb{R}), (0: \mathbb{R})\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.deterministicValue` (`✓ std3`).

*Citation.* Andris Ambainis; Dmitry Kravchenko; Sk Sazim; Joonwoo Bae; Ashutosh Rai (2024). *Quantum advantages in (n,d)↦1 random access codes*. DOI: [10.1088/1367-2630/ad9bdf](https://doi.org/10.1088/1367-2630/ad9bdf). URL: <https://arxiv.org/abs/1510.03045v4>.

*Commentary.*

The encoder E sends one alphabet symbol and the decoder D returns a symbol for each received symbol and query. The conditional ite returns one when its condition holds and zero otherwise, both in ℝ. The factor 1/(n d^n) averages over words and queries, as in Section 2, Eq. (4), and Section 3.1 of the source. This real-valued definition has no positivity hypotheses on n or d; division by zero has its usual totalized field value zero.

**Definition 1.2 (A classical strategy with shared randomness).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\operatorname{ClassicalStrategy}\left(n, d\right) = \{ (\Lambda: \operatorname{Type}), [\operatorname{Fintype}\left(\Lambda\right)], (p: (\Lambda \to \mathbb{R})), (E: (\Lambda \to ((\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)) \to \operatorname{Fin}\left(d\right)))), (D: (\Lambda \to (\operatorname{Fin}\left(d\right) \to (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right))))) \mid (\forall (\lambda: \Lambda), (0 \le p\left(\lambda\right))) \land (\sum_{\lambda: \Lambda} (p\left(\lambda\right)) = 1) \}))$$

*Formalization.* `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.ClassicalStrategy` (`✓ std3`).

*Citation.* Andris Ambainis; Dmitry Kravchenko; Sk Sazim; Joonwoo Bae; Ashutosh Rai (2024). *Quantum advantages in (n,d)↦1 random access codes*. DOI: [10.1088/1367-2630/ad9bdf](https://doi.org/10.1088/1367-2630/ad9bdf). URL: <https://arxiv.org/abs/1510.03045v4>.

*Commentary.*

The displayed record consists of a type Λ, a chosen finite enumeration of Λ, weights p, and encoder and decoder families E and D. Each weight is nonnegative and their sum is one. For a shared value λ, E(λ) and D(λ) form a deterministic strategy. The record fields are Λ, finite, weight, nonneg, total, encode and decode, with p, E and D denoting weight, encode and decode. The bracketed Fintype is the field named finite; nonneg and total are the displayed nonnegativity and sum-one conditions. This is the finite shared-randomness description in Section 3.1.

**Definition 1.3 (The value of a classical mixture).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (S: \operatorname{ClassicalStrategy}\left(n, d\right)), (\operatorname{classicalValue}\left(S\right) = \sum_{\lambda: \Lambda\left(S\right)} (\operatorname{weight}\left(S\right)\left(\lambda\right) \cdot \operatorname{deterministicValue}\left(n, d, \operatorname{encode}\left(S\right)\left(\lambda\right), \operatorname{decode}\left(S\right)\left(\lambda\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.classicalValue` (`✓ std3`).

*Citation.* Andris Ambainis; Dmitry Kravchenko; Sk Sazim; Joonwoo Bae; Ashutosh Rai (2024). *Quantum advantages in (n,d)↦1 random access codes*. DOI: [10.1088/1367-2630/ad9bdf](https://doi.org/10.1088/1367-2630/ad9bdf). URL: <https://arxiv.org/abs/1510.03045v4>.

*Commentary.*

The value is the weighted average of the deterministic values. Here Λ(S), finite(S), weight(S), nonneg(S), total(S), encode(S) and decode(S) are the field projections. The sum uses the enumeration finite(S) of Λ(S). Shared randomness therefore forms a convex combination of deterministic success probabilities, as in Section 3.1.

**Definition 1.4 (The quantum value for two settings).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (\psi: ((\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)) \to (\operatorname{Fin}\left(d\right) \to \mathbb{C}))), (\forall (U: (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), (\forall (s: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), (\operatorname{quantumValue}\left(n, d, \psi, U, s\right) = \frac{1}{((n: \mathbb{R}) \cdot (d: \mathbb{R})^{n})} \cdot \sum_{x: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right))} (\sum_{j: \operatorname{Fin}\left(n\right)} (\left\lVert \sum_{k: \operatorname{Fin}\left(d\right)} (\overline{U\left(s\left(j\right)\right)\left(k, x\left(j\right)\right)} \cdot \psi\left(x\right)\left(k\right)) \right\rVert^{2})))))))$$

*Formalization.* `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.quantumValue` (`✓ std3`).

*Citation.* Andris Ambainis; Dmitry Kravchenko; Sk Sazim; Joonwoo Bae; Ashutosh Rai (2024). *Quantum advantages in (n,d)↦1 random access codes*. DOI: [10.1088/1367-2630/ad9bdf](https://doi.org/10.1088/1367-2630/ad9bdf). URL: <https://arxiv.org/abs/1510.03045v4>.

*Commentary.*

For query j, Bob uses setting s(j); the measurement vector for a correct outcome is column x(j) of U(s(j)). The inner sum is the inner product of that column with psi(x), conjugating the column entries. This is Lean's dotProduct of the starred column with psi(x), with no further conjugation in dotProduct itself. The norm is the complex norm, equal to the modulus. Its square is the Born probability when psi(x) is a unit vector and the two matrices are unitary. These conditions are imposed in claim; quantumValue itself is defined for arbitrary vectors and matrices. The normalization is again that of Section 2, Eq. (4).

**Definition 1.5 (Strict advantage for every pair of parameters).**

$$\operatorname{claim} \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), ((2 \le n) \Rightarrow ((2 \le d) \Rightarrow (\exists (\psi: ((\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right)) \to (\operatorname{Fin}\left(d\right) \to \mathbb{C}))), (\exists (U: (\operatorname{Fin}\left(2\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right))), (\exists (s: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2\right))), ((\forall (x: (\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(d\right))), (\sum_{k: \operatorname{Fin}\left(d\right)} (\overline{\psi\left(x\right)\left(k\right)} \cdot \psi\left(x\right)\left(k\right)) = (1: \mathbb{C}))) \land ((\forall (i: \operatorname{Fin}\left(2\right)), (U\left(i\right) \in \operatorname{Matrix}.\operatorname{unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right))) \land (\forall (S: \operatorname{ClassicalStrategy}\left(n, d\right)), (\operatorname{classicalValue}\left(S\right) < \operatorname{quantumValue}\left(n, d, \psi, U, s\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.claim` (`✓ std3`).

*Citation.* Andris Ambainis; Dmitry Kravchenko; Sk Sazim; Joonwoo Bae; Ashutosh Rai (2024). *Quantum advantages in (n,d)↦1 random access codes*. DOI: [10.1088/1367-2630/ad9bdf](https://doi.org/10.1088/1367-2630/ad9bdf). URL: <https://arxiv.org/abs/1510.03045v4>.

*Commentary.*

For every n and d at least two, one encoding by complex unit vectors, two unitary matrices and one setting choice per query simultaneously give a value strictly greater than that of every finite classical mixture. The unit-vector condition is an equality in ℂ, with the sum of conjugate-coordinate products equal to the complex number one. Matrix.unitaryGroup consists of d by d complex unitary matrices. This states the general quantum-advantage question and its two-setting resource requirement from Section 5 of the source.

**Theorem 1.6 (A construction giving strict advantage).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.result` (`✓ std3`). ∎

*Resolves.* `Problems/ambainis-2024-random-access-code-two-setting-advantage` (proved) by `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ambainis-2024-random-access-code-two-setting-advantage","declaration_gid":"D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andris Ambainis; Dmitry Kravchenko; Sk Sazim; Joonwoo Bae; Ashutosh Rai (2024). *Quantum advantages in (n,d)↦1 random access codes*. DOI: [10.1088/1367-2630/ad9bdf](https://doi.org/10.1088/1367-2630/ad9bdf). URL: <https://arxiv.org/abs/1510.03045v4>.

*Commentary.*

For a fixed classical decoder, the best encoder chooses a row with the largest number of matches with the word. If a decoder column omits a symbol, replace one occurrence of a repeated symbol by that missing symbol. Holding the other input coordinates fixed, the scores for the repeated and missing symbols together do not decrease; all other scores stay the same. Each exchange reduces the total number of missing symbols, so eventually every column is a permutation. Relabeling the alphabet separately at each coordinate then gives identity decoding. Majority encoding attains the resulting classical optimum C(n,d), equal to 1/(n d^n) times the sum over words x of the largest number of occurrences of a single symbol in x. Convex combinations cannot exceed this optimum, in agreement with the classical benchmark of Ambainis, Kravchenko, Sazim, Bae and Rai.

Take U(0) = I, the identity matrix, and U(1) = F, where F has first two by two block [[3/5, 4/5], [4/5, -3/5]] and is the identity on the remaining coordinates. Real matrix entries and encoding coordinates are included in ℂ by Complex.ofReal. The columns of F are an orthonormal rotated basis. Use this basis for the last query and the standard basis for every other query. For a fixed prefix z of length n minus one, let N(i) count symbol i, let m be the largest count and let M be the set of maximisers. If f(b) is column b of F, project f(b) onto the coordinates in M and normalize the projection. When the projection is zero, use any standard basis vector with index in M. The score on word (z,b), summed over queries, is m plus the squared norm of that projection. Summing over b gives d m + |M|, exactly the sum of the largest symbol counts of the words (z,b). Averaging over prefixes proves that this baseline encoding has value C(n,d).

Write e(i) for the standard basis vector at index i. Change only the encoding of the all-zero word 0^n to (2n e(0) + e(1))/sqrt(4n^2 + 1). Its old score, summed over queries, is n - 1 + 9/25. The new score is ((n - 1) 4n^2 + (6n + 4)^2/25)/(4n^2 + 1). The gain is (23n + 32)/(25(4n^2 + 1)), which is strictly positive. The average value therefore increases by this gain divided by n d^n, while all other word scores are preserved. The resulting two-setting quantum value exceeds C(n,d) and hence the value of every classical strategy.

## References

- Truth anchor: `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.ClassicalStrategy`
- Truth anchor: `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.claim`
- Truth anchor: `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.classicalValue`
- Truth anchor: `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.deterministicValue`
- Truth anchor: `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.quantumValue`
- Truth anchor: `D5/S3/Quantum/Information/RandomAccessCodeTwoSettingAdvantage.result`
