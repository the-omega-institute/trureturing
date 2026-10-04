# The equiprobable pretty-good-measurement comparison of Cha and Lee fails

## Abstract

Cha and Lee (arXiv:2507.05778, Quantum Information Processing 25, 310) compare two upper bounds on the optimal success probability of minimum-error state discrimination, one built from the pretty good measurement on all states and one built from it on the active set I_+ of labels with nonzero optimal effects. For equal priors they conjecture (|I_+| - 1)(P^PGM_+ - 1/N) <= (N - 1)(P^PGM - 1/N). Three positive definite qubit states with rational entries violate it.

**Definition 1.1 (The success probability).**

$$\forall d, N : \mathbb{N}, \forall rho, E : \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \operatorname{success}\left(rho, E\right) = \sum_{i \in \operatorname{Fin}\left(N\right)} \operatorname{Re}\left(\operatorname{tr}\left(\frac{1}{N} \cdot rho\left(i\right) \cdot E\left(i\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.success` (`✓ std3`).

*Citation.* Hyunho Cha, Jungwoo Lee (2026). *Structural perspectives from quantum states and measurements in optimal state discrimination*. DOI: [10.1007/s11128-026-05335-6](https://doi.org/10.1007/s11128-026-05335-6). URL: <https://arxiv.org/abs/2507.05778v2>.

*Commentary.*

For the equiprobable ensemble sigma_i = rho_i / N, the success probability of the POVM E is sum_i tr(sigma_i E_i); the real part reads this real trace.

**Definition 1.2 (The pretty good measurement on a set of labels).**

$$\forall d, N : \mathbb{N}, \forall rho : \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right), \forall A : \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right), \operatorname{pgmScore}\left(rho, A\right) = \sum_{i \in A} \operatorname{Re}\left(\operatorname{tr}\left(\frac{1}{N} \cdot rho\left(i\right) \cdot (\sum_{j \in A} \frac{1}{N} \cdot rho\left(j\right))^{-\frac{1}{2}} \cdot \frac{1}{N} \cdot rho\left(i\right) \cdot (\sum_{j \in A} \frac{1}{N} \cdot rho\left(j\right))^{-\frac{1}{2}}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.pgmScore` (`✓ std3`).

*Citation.* Hyunho Cha, Jungwoo Lee (2026). *Structural perspectives from quantum states and measurements in optimal state discrimination*. DOI: [10.1007/s11128-026-05335-6](https://doi.org/10.1007/s11128-026-05335-6). URL: <https://arxiv.org/abs/2507.05778v2>.

*Commentary.*

For a set A of labels, S_A = sum_{j in A} sigma_j and the pretty good measurement has effects S_A^{-1/2} sigma_i S_A^{-1/2} for i in A; its score keeps the original weights sigma_i = rho_i / N. S_A^{-1/2} is the continuous-functional-calculus power. With A all labels this is P^PGM; with A = I_+ it is P^PGM_+.

**Definition 1.3 (The conjectured comparison).**

$$(claim) \Leftrightarrow (\forall k, N : \mathbb{N}, \forall rho : \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(k + 1\right), \operatorname{Fin}\left(k + 1\right), \mathbb{C}\right), (0 < N) \Rightarrow (((\forall i : \operatorname{Fin}\left(N\right), \operatorname{PosDef}\left(rho\left(i\right)\right)) \land (\forall i : \operatorname{Fin}\left(N\right), \operatorname{tr}\left(rho\left(i\right)\right) = 1)) \Rightarrow (\exists E : \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(k + 1\right), \operatorname{Fin}\left(k + 1\right), \mathbb{C}\right), ((\operatorname{finitePOVM}\left(E\right)) \land (\forall F : \operatorname{Fin}\left(N\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(k + 1\right), \operatorname{Fin}\left(k + 1\right), \mathbb{C}\right), (\operatorname{finitePOVM}\left(F\right)) \Rightarrow (\operatorname{success}\left(rho, F\right) \le \operatorname{success}\left(rho, E\right)))) \land (\forall A : \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right), (A = \ \{i \mid E\left(i\right) \ne 0\ \}) \Rightarrow ((|A| - 1) \cdot (\operatorname{pgmScore}\left(rho, A\right) - \frac{1}{N}) \le (N - 1) \cdot (\operatorname{pgmScore}\left(rho, \operatorname{univ}\left(\operatorname{Fin}\left(N\right)\right)\right) - \frac{1}{N}))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.claim` (`✓ std3`).

*Citation.* Hyunho Cha, Jungwoo Lee (2026). *Structural perspectives from quantum states and measurements in optimal state discrimination*. DOI: [10.1007/s11128-026-05335-6](https://doi.org/10.1007/s11128-026-05335-6). URL: <https://arxiv.org/abs/2507.05778v2>.

*Commentary.*

Journal Eq. (18) for equal priors, with I_+ the set of labels whose optimal effect is nonzero. POVMs are the frozen finitePOVM: positive semidefinite effects on C^(k+1) that sum to the identity. The encoding asks for some optimal POVM, the weakest reading of the optimal POVM, and restricts to N >= 1 positive definite states, for which every nonempty S_A is invertible.

**Definition 1.4 (The three states).**

$$((rho\left(0\right) = \operatorname{mat}\left(\frac{400}{401}, \frac{18}{401}, \frac{18}{401}, \frac{1}{401}\right)) \land (rho\left(1\right) = \operatorname{mat}\left(\frac{400}{401}, -\frac{18}{401}, -\frac{18}{401}, \frac{1}{401}\right))) \land (rho\left(2\right) = \operatorname{mat}\left(\frac{47963}{48922}, 0, 0, \frac{959}{48922}\right))$$

*Formalization.* `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.rho` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hyunho Cha, Jungwoo Lee (2026). *Structural perspectives from quantum states and measurements in optimal state discrimination*. DOI: [10.1007/s11128-026-05335-6](https://doi.org/10.1007/s11128-026-05335-6). URL: <https://arxiv.org/abs/2507.05778v2>.

*Commentary.*

Three positive definite qubit density matrices with rational entries; mat(a, b, c, e) is the 2 x 2 matrix with rows (a, b) and (c, e).

**Theorem 1.5 (The comparison fails for three qubit states).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/cha-2026-equiprobable-pgm-active-set` (refuted) by `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cha-2026-equiprobable-pgm-active-set","declaration_gid":"D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hyunho Cha, Jungwoo Lee (2026). *Structural perspectives from quantum states and measurements in optimal state discrimination*. DOI: [10.1007/s11128-026-05335-6](https://doi.org/10.1007/s11128-026-05335-6). URL: <https://arxiv.org/abs/2507.05778v2>.

*Commentary.*

Take N = 3, d = 2 and sigma_i = rho_i / 3. The matrix Gamma = diag(418, 19)/1203 has Gamma - sigma_1 = (6/401)(1, -1)(1, -1)^T, Gamma - sigma_2 = (6/401)(1, 1)(1, 1)^T and Gamma - sigma_3 = diag(1011, 453)/48922, all positive semidefinite. Hence every POVM satisfies sum_i tr(sigma_i E_i) = tr(Gamma) - sum_i tr((Gamma - sigma_i) E_i) <= tr(Gamma) = 437/1203, and the projectors (1/2)(1, 1)(1, 1)^T, (1/2)(1, -1)(1, -1)^T with E_3 = 0 attain it. For an optimal POVM every term tr((Gamma - sigma_i) E_i) vanishes. Since Gamma - sigma_3 is at least (453/48922) I, E_3 = 0; and E_1 = 0 or E_2 = 0 would leave tr(Gamma - sigma_j) = 12/401. So I_+ = {1, 2}. Then S = diag(121, 1)/122 and S_+ = diag(800, 2)/1203, whose inverse square roots are diagonal; P^PGM = 20192347/58370763 and P^PGM_+ = 2167/6015, and (2 - 1)(P^PGM_+ - 1/3) - (3 - 1)(P^PGM - 1/3) = 168714/97284605 > 0.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.pgmScore`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.result`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.rho`
- Truth anchor: `D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.success`
- Dependency: [D5/S3/Estimation/TransmissivityTwoPointProbeRefutation](../../Estimation/TransmissivityTwoPointProbeRefutation.md)
