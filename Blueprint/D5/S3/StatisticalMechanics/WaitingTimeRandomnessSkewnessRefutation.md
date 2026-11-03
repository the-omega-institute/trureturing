# Waiting-time randomness and skewness on two enzyme routes

## Abstract

An eight-state enzyme network has waiting-time skewness at most two and randomness greater than one.

Source line numbers refer to skewkurtstatkinarxiv.tex in Barato and Seifert, arXiv:1510.03279v1.

**Definition 1.1 (The generator before product release).**

$$\forall (m: \mathbb{N}), (\forall (k: (\operatorname{Fin}\left(m\right)) \to ((\operatorname{Fin}\left(m\right)) \to (\mathbb{R}))), (\forall (p: \operatorname{Fin}\left(m\right)), (\forall (r: \operatorname{Fin}\left(m\right)), ((\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.cemetery}\left(k, p, r\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)) = (\lambda (i: \operatorname{Fin}\left(m\right)) \mapsto ((\lambda (j: \operatorname{Fin}\left(m\right)) \mapsto (\operatorname{ite}\left((i = j), -(\sum_{l: \operatorname{Fin}\left(m\right)} (\operatorname{ite}\left((i = l), (0: \mathbb{R}), k\left(i, l\right)\right))), \operatorname{ite}\left(((i = p) \land (j = r)), (0: \mathbb{R}), k\left(i, j\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.cemetery` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andre C. Barato, Udo Seifert (2015). *Skewness and Kurtosis in Statistical Kinetics*. DOI: [10.1103/PhysRevLett.115.188103](https://doi.org/10.1103/PhysRevLett.115.188103). URL: <https://arxiv.org/abs/1510.03279v1>.

*Commentary.*

The states are Fin m and k i j is the transition rate from i to j. The diagonal is minus the sum of the off-diagonal exit rates. For distinct p and r, the marked off-diagonal entry is set to zero while its contribution to the exit rate remains on the diagonal. This sends probability to an absorbing cemetery state. This gives a first-passage description of the cycle completion at product release in Barato and Seifert, TeX lines 110–117 and 133–136. The formula also defines a matrix for arbitrary k, p and r, including p = r.

**Definition 1.2 (The first-passage moment vectors).**

$$\forall (m: \mathbb{N}), (\forall (k: (\operatorname{Fin}\left(m\right)) \to ((\operatorname{Fin}\left(m\right)) \to (\mathbb{R}))), (\forall (p: \operatorname{Fin}\left(m\right)), (\forall (r: \operatorname{Fin}\left(m\right)), (\forall (t: \mathbb{N}), ((\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.moment}\left(k, p, r\right)\left(t\right): (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})) = \operatorname{Nat.rec}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(m\right), (1: \mathbb{R})\right), (\lambda (n: \mathbb{N}) \mapsto ((\lambda (v: (\operatorname{Fin}\left(m\right)) \to (\mathbb{R})) \mapsto (((\operatorname{Nat.cast}\left((n + 1: \mathbb{N})\right): \mathbb{R})) \cdot (\operatorname{Matrix.mulVec}\left(\operatorname{Inv.inv}\left(-(\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.cemetery}\left(k, p, r\right))\right), v\right)))))), t\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.moment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andre C. Barato, Udo Seifert (2015). *Skewness and Kurtosis in Statistical Kinetics*. DOI: [10.1103/PhysRevLett.115.188103](https://doi.org/10.1103/PhysRevLett.115.188103). URL: <https://arxiv.org/abs/1510.03279v1>.

*Commentary.*

The zeroth moment is the constant vector one. Each next moment is obtained by multiplying the preceding vector by the inverse of the negative cemetery generator and by the next natural number, cast to a real scalar. When that matrix is invertible, this is the linear system saying that the negative generator applied to the next moment equals the preceding moment multiplied by its order. In the first-passage reading, the component at r is the moment of the completion time starting just after release. This is the first-passage reading of the moments defined in Barato and Seifert, TeX lines 133–136; the definition uses matrix inversion and natural recursion rather than an integral over a stochastic process. It is total even for singular matrices.

**Definition 1.3 (The variance at the reset state).**

$$\forall (m: \mathbb{N}), (\forall (k: (\operatorname{Fin}\left(m\right)) \to ((\operatorname{Fin}\left(m\right)) \to (\mathbb{R}))), (\forall (p: \operatorname{Fin}\left(m\right)), (\forall (r: \operatorname{Fin}\left(m\right)), ((\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.variance}\left(k, p, r\right): \mathbb{R}) = \operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.moment}\left(k, p, r\right)\left((2: \mathbb{N}), r\right) - (\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.moment}\left(k, p, r\right)\left((1: \mathbb{N}), r\right))^{2}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.variance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andre C. Barato, Udo Seifert (2015). *Skewness and Kurtosis in Statistical Kinetics*. DOI: [10.1103/PhysRevLett.115.188103](https://doi.org/10.1103/PhysRevLett.115.188103). URL: <https://arxiv.org/abs/1510.03279v1>.

*Commentary.*

At the reset state r, subtract the square of the first moment from the second moment. This expresses the variance in the first-passage moment vectors, corresponding to the squared standard deviation in Barato and Seifert, TeX line 142. Positivity is a separate hypothesis of the proposed inequality.

**Definition 1.4 (The randomness parameter).**

$$\forall (m: \mathbb{N}), (\forall (k: (\operatorname{Fin}\left(m\right)) \to ((\operatorname{Fin}\left(m\right)) \to (\mathbb{R}))), (\forall (p: \operatorname{Fin}\left(m\right)), (\forall (r: \operatorname{Fin}\left(m\right)), ((\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.randomness}\left(k, p, r\right): \mathbb{R}) = \frac{\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.variance}\left(k, p, r\right)}{(\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.moment}\left(k, p, r\right)\left((1: \mathbb{N}), r\right))^{2}}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.randomness` (`✓ std3`).

*Citation.* Andre C. Barato, Udo Seifert (2015). *Skewness and Kurtosis in Statistical Kinetics*. DOI: [10.1103/PhysRevLett.115.188103](https://doi.org/10.1103/PhysRevLett.115.188103). URL: <https://arxiv.org/abs/1510.03279v1>.

*Commentary.*

Divide the variance by the square of the mean completion time at r. This is the randomness parameter of Barato and Seifert, TeX lines 138–142, expressed in the first-passage moments.

**Definition 1.5 (The standardized third central moment).**

$$\forall (m: \mathbb{N}), (\forall (k: (\operatorname{Fin}\left(m\right)) \to ((\operatorname{Fin}\left(m\right)) \to (\mathbb{R}))), (\forall (p: \operatorname{Fin}\left(m\right)), (\forall (r: \operatorname{Fin}\left(m\right)), ((\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.skewness}\left(k, p, r\right): \mathbb{R}) = \frac{\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.moment}\left(k, p, r\right)\left((3: \mathbb{N}), r\right) - (3: \mathbb{R}) \cdot \operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.moment}\left(k, p, r\right)\left((1: \mathbb{N}), r\right) \cdot \operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.variance}\left(k, p, r\right) - (\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.moment}\left(k, p, r\right)\left((1: \mathbb{N}), r\right))^{3}}{(\operatorname{Real.sqrt}\left(\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.variance}\left(k, p, r\right)\right))^{3}}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.skewness` (`✓ std3`).

*Citation.* Andre C. Barato, Udo Seifert (2015). *Skewness and Kurtosis in Statistical Kinetics*. DOI: [10.1103/PhysRevLett.115.188103](https://doi.org/10.1103/PhysRevLett.115.188103). URL: <https://arxiv.org/abs/1510.03279v1>.

*Commentary.*

Subtract three times the mean times the variance and the cube of the mean from the third moment, then divide by the cube of the square root of the variance. This is the skewness of Barato and Seifert, TeX lines 142–145. All quantities are evaluated at the reset state r.

**Definition 1.6 (Finite networks with an accessible product transition).**

$$\forall (m: \mathbb{N}), (\forall (k: (\operatorname{Fin}\left(m\right)) \to ((\operatorname{Fin}\left(m\right)) \to (\mathbb{R}))), (\forall (p: \operatorname{Fin}\left(m\right)), (\forall (r: \operatorname{Fin}\left(m\right)), ((\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.IsNetwork}\left(k, p, r\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(m\right)), (\forall (j: \operatorname{Fin}\left(m\right)), ((i \ne j) \to ((0: \mathbb{R}) \le k\left(i, j\right))))) \land (((0: \mathbb{R}) < k\left(p, r\right)) \land (\forall (i: \operatorname{Fin}\left(m\right)), (\operatorname{Relation.ReflTransGen}\left((\lambda (i: \operatorname{Fin}\left(m\right)) \mapsto ((\lambda (j: \operatorname{Fin}\left(m\right)) \mapsto ((0: \mathbb{R}) < k\left(i, j\right))))), i, p\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.IsNetwork` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andre C. Barato, Udo Seifert (2015). *Skewness and Kurtosis in Statistical Kinetics*. DOI: [10.1103/PhysRevLett.115.188103](https://doi.org/10.1103/PhysRevLett.115.188103). URL: <https://arxiv.org/abs/1510.03279v1>.

*Commentary.*

Off-diagonal transition rates are nonnegative, the marked rate from p to r is positive, and every state can reach p along a finite path of positive transition rates. Reachability includes the path of length zero. These conditions specify the finite network used for the first-passage reading of cycle completion in Barato and Seifert, TeX lines 110–117 and 133–136. The predicate imposes no diagonal-rate condition or distinctness condition on p and r.

**Definition 1.7 (The proposed implication for arbitrary networks).**

$$(\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.claim}) \Leftrightarrow (\forall (m: \mathbb{N}), (\forall (k: (\operatorname{Fin}\left(m\right)) \to ((\operatorname{Fin}\left(m\right)) \to (\mathbb{R}))), (\forall (p: \operatorname{Fin}\left(m\right)), (\forall (r: \operatorname{Fin}\left(m\right)), ((\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.IsNetwork}\left(k, p, r\right)) \to (((0: \mathbb{R}) < \operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.variance}\left(k, p, r\right)) \to ((\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.skewness}\left(k, p, r\right) \le (2: \mathbb{R})) \to (\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.randomness}\left(k, p, r\right) \le (1: \mathbb{R})))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andre C. Barato, Udo Seifert (2015). *Skewness and Kurtosis in Statistical Kinetics*. DOI: [10.1103/PhysRevLett.115.188103](https://doi.org/10.1103/PhysRevLett.115.188103). URL: <https://arxiv.org/abs/1510.03279v1>.

*Commentary.*

For every finite network with positive variance, skewness at most two is asserted to imply randomness at most one. Barato and Seifert report this ordering numerically for their two-cycle example in TeX lines 341–352 and its off-pathway case in lines 354–357, and ask in line 358 whether it holds for arbitrary networks beyond a single cycle. The displayed proposition gives that implication the finite-network and first-passage meaning defined above.

**Theorem 1.8 (Two routes violate the implication).**

$$\neg (\forall (m: \mathbb{N}), (\forall (k: (\operatorname{Fin}\left(m\right)) \to ((\operatorname{Fin}\left(m\right)) \to (\mathbb{R}))), (\forall (p: \operatorname{Fin}\left(m\right)), (\forall (r: \operatorname{Fin}\left(m\right)), ((\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.IsNetwork}\left(k, p, r\right)) \to (((0: \mathbb{R}) < \operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.variance}\left(k, p, r\right)) \to ((\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.skewness}\left(k, p, r\right) \le (2: \mathbb{R})) \to (\operatorname{D5.S3.StatisticalMechanics.WaitingTimeRandomnessSkewnessRefutation.randomness}\left(k, p, r\right) \le (1: \mathbb{R})))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/barato-seifert-2015-waiting-time-randomness-skewness-refutation` (refuted) by `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"barato-seifert-2015-waiting-time-randomness-skewness-refutation","declaration_gid":"D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andre C. Barato, Udo Seifert (2015). *Skewness and Kurtosis in Statistical Kinetics*. DOI: [10.1103/PhysRevLett.115.188103](https://doi.org/10.1103/PhysRevLett.115.188103). URL: <https://arxiv.org/abs/1510.03279v1>.

*Commentary.*

Use the eight states 0 through 7, with marked release from 7 to 0. The nonzero transition rates are 75 from 0 to 1, 25 from 0 to 2, 25 from 1 to 7, 5 on each of the transitions from 2 to 3, from 3 to 4, from 4 to 5, from 5 to 6 and from 6 to 7, and 25 from 7 to 0. All other entries are zero. These rates are nonnegative, the marked rate is positive, and each state reaches 7: states 2 through 6 follow the chain, state 1 jumps directly to 7, state 0 goes through 1, and state 7 uses the path of length zero.

Negating the cemetery generator gives an upper triangular matrix with diagonal entries 100, 25, 5, 5, 5, 5, 5 and 25. Its off-diagonal entries are the negatives of the listed rates except that the marked entry is zero. Its determinant is the product of the nonzero diagonal entries, so it is invertible. Consequently, a vector mapped by this matrix to n + 1 times the nth moment vector must be the next moment vector.

Starting from the constant vector one, three successive matrix-vector identities give the first moment vector (33/100, 2/25, 26/25, 21/25, 16/25, 11/25, 6/25, 1/25), the second moment vector (1673/5000, 6/625, 802/625, 542/625, 332/625, 172/625, 62/625, 2/625), and the third moment vector (234843/500000, 24/15625, 28656/15625, 16626/15625, 8496/15625, 3516/15625, 936/15625, 6/15625). Their components at the reset state 0 are respectively 33/100, 1673/5000 and 234843/500000.

The variance is therefore 2257/10000 and the randomness parameter is 2257/1089, which is greater than one. For the skewness, the square root of 2257/10000 is positive and is at least 19/40, since the square of 19/40 is at most 2257/10000. Cubing preserves this bound. The third central moment is 105153/500000, which is at most twice the cube of 19/40, and hence at most twice the cube of the square root of the variance. After multiplying by the positive denominator, this is precisely the inequality that the skewness is at most two.

The proposed universal implication, applied to these eight states, the marked transition, the positive variance and the skewness bound, would give randomness at most one. This contradicts the strict lower bound just obtained. The argument concerns the first-passage moment definition above and refutes the randomness-versus-skewness implication asked about in Barato and Seifert, TeX lines 350–358.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.IsNetwork`
- Truth anchor: `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.cemetery`
- Truth anchor: `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.moment`
- Truth anchor: `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.randomness`
- Truth anchor: `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.skewness`
- Truth anchor: `D5/S3/StatisticalMechanics/WaitingTimeRandomnessSkewnessRefutation.variance`
