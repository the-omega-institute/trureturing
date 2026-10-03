# Negativity is not the partial transpose distance to the PPT states

## Abstract

Ganardi, Miller, Paterek and Zukowski (arXiv:2111.11887, Quantum 6, 654) conjecture that the partial transpose distance d_T(rho, sigma) = ||rho^{T_B} - sigma^{T_B}||_1 / 2 from every state rho to the PPT states has infimum equal to the negativity N(rho) = (||rho^{T_B}||_1 - 1)/2. The equality fails: a rank-five two-qutrit state has negativity 1/34, while its distance to every PPT state is at least 2/51.

**Definition 1.1 (The conjectured equality).**

$$(claim) \Leftrightarrow (\forall d : \mathbb{N}, \forall rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right), (\operatorname{IsDensity}\left(rho\right)) \Rightarrow (\operatorname{sInf}\left(\ \{t \mid \exists sigma : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right), (\operatorname{IsDensity}\left(sigma\right)) \land ((\operatorname{PosSemidef}\left(\operatorname{partialTransposeB}\left(sigma\right)\right)) \land (t = \frac{\operatorname{traceNorm}\left(\operatorname{partialTransposeB}\left(rho\right) - \operatorname{partialTransposeB}\left(sigma\right)\right)}{2}))\ \}\right) = \frac{\operatorname{traceNorm}\left(\operatorname{partialTransposeB}\left(rho\right)\right) - 1}{2}))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.claim` (`✓ std3`).

*Citation.* Ray Ganardi; Marek Miller; Tomasz Paterek; Marek Żukowski (2022). *Hierarchy of correlation quantifiers comparable to negativity*. DOI: [10.22331/q-2022-02-16-654](https://doi.org/10.22331/q-2022-02-16-654). URL: <https://arxiv.org/abs/2111.11887v2>.

*Commentary.*

For a state rho on C^d (x) C^d, rho^{T_B} is the partial transposition on the second factor (the existing partialTransposeB) and ||A||_1 = Re Tr sqrt(A^dagger A) is the existing trace norm. The partial transpose distance is d_T(rho, sigma) = ||rho^{T_B} - sigma^{T_B}||_1 / 2, the PPT states are the density matrices sigma with sigma^{T_B} positive semidefinite, and the negativity is N(rho) = (||rho^{T_B}||_1 - 1)/2. Conjecture 1 of the paper states that the infimum of d_T(rho, sigma) over the PPT states equals N(rho) for every density matrix rho; the displayed statement is its case of equal local dimensions.

**Definition 1.2 (The counterexample state).**

$$witness = \frac{1}{34} \cdot ((|00\rangle + |11\rangle + 4 \cdot |22\rangle)(\langle00| + \langle11| + 4 \cdot \langle22|) + 4 \cdot (|02\rangle\langle02| + |20\rangle\langle20| + |12\rangle\langle12| + |21\rangle\langle21|))$$

*Formalization.* `D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.witness` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ray Ganardi; Marek Miller; Tomasz Paterek; Marek Żukowski (2022). *Hierarchy of correlation quantifiers comparable to negativity*. DOI: [10.22331/q-2022-02-16-654](https://doi.org/10.22331/q-2022-02-16-654). URL: <https://arxiv.org/abs/2111.11887v2>.

*Commentary.*

The state is R/34 on two qutrits, with R = |v><v| + 4 (|02><02| + |20><20| + |12><12| + |21><21|) and v = |00> + |11> + 4 |22>. It is positive semidefinite with trace one and rank five.

**Theorem 1.3 (The conjectured equality fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ganardi-2022-negativity-ppt-distance` (refuted) by `D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ganardi-2022-negativity-ppt-distance","declaration_gid":"D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ray Ganardi; Marek Miller; Tomasz Paterek; Marek Żukowski (2022). *Hierarchy of correlation quantifiers comparable to negativity*. DOI: [10.22331/q-2022-02-16-654](https://doi.org/10.22331/q-2022-02-16-654). URL: <https://arxiv.org/abs/2111.11887v2>.

*Commentary.*

Let c = |01> - |10>. The partial transpose of the state is P - |c><c|/68, where P is a sum of positive rank-one and diagonal terms of trace 35/34, so the triangle inequality bounds its trace norm by 36/34 and the negativity by 1/34. The matrices U_1 (the signs -1 on 00, 01, 10, 11, 22 and +1 on 02, 20, 12, 21), U_2 (equal to -1 except for the swaps of 02 with 20 and of 12 with 21) and U_3 (equal to U_2 except for +1 on 22) are unitary, so Re Tr(U_k X) is at most ||X||_1 for every X, and so is Re Tr(F X) for F = U_1/3 + U_2/6 + U_3/2. Against the partial transpose of the state, F has trace 7/17. With b = 2|00> + 2|11> - |22>, every matrix sigma satisfies Tr(F sigma^{T_B}) = Tr(sigma)/3 - <b|sigma|b>/3 - 4<c|sigma^{T_B}|c>/3, so for every PPT state the real part is at most 1/3. Hence the partial transpose distance to every PPT state is at least (7/17 - 1/3)/2 = 2/51, the set of PPT states contains |00><00|, and the infimum is at least 2/51 > 1/34.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.result`
- Truth anchor: `D5/S3/Quantum/Entanglement/NegativityPartialTransposeDistanceRefutation.witness`
- Dependency: [D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation](StructuredNegativityCoincidenceRefutation.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
