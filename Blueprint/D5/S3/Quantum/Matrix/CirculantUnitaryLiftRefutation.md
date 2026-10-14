# Circulant unitary lifting fails at order ten

## Abstract

A circulant unistochastic matrix of order ten has no circulant unitary lift.

Matrices use zero-based indices in Fin d. Subtraction in Fin d is modulo d. Matrix.circulant z has entry z(i−j). The predicates IsCirculant and IsUnistochastic are those of CirculantBraceletNonUnistochastic: a real matrix is circulant when it equals Matrix.circulant v for some real vector v, and it is unistochastic when it equals RHLinalg.normSqMatrix U for some U in Matrix.unitaryGroup. The latter matrix has entries ‖U i j‖².

**Definition 1.1 (Circulant unitary lifts).**

$$\forall (d: \mathbb{N}), \forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right)), \operatorname{HasCirculantLift}\left(B\right) = \exists (z: \operatorname{Fin}\left(d\right) \to \mathbb{C}), (\operatorname{Matrix.circulant}\left(z\right) \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{Fin}\left(d\right), \mathbb{C}\right)) \land (B = \operatorname{RHLinalg.normSqMatrix}\left(\operatorname{Matrix.circulant}\left(z\right)\right))$$

*Formalization.* `D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.HasCirculantLift` (`✓ std3`).

*Citation.* Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski (2021). *Algebraic and geometric structures inside the Birkhoff polytope*. DOI: [10.1063/5.0046581](https://doi.org/10.1063/5.0046581). URL: <https://arxiv.org/abs/2101.11288>.

*Commentary.*

Definition 6, page 4: "The set of d × d doubly circulant unistochastic matrices Cd² consists of these circulant unistochastic matrices for which there exists the corresponding unitary matrix that is circulant." The vector z describes this complex circulant unitary matrix. Its squared norms must agree with every entry of B.

**Definition 1.2 (The circulant lifting conjecture).**

$$claim = \forall (d: \mathbb{N}), \forall (B: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{R}\right)), (\operatorname{CirculantBraceletNonUnistochastic.IsCirculant}\left(B\right)) \Rightarrow ((\operatorname{CirculantBraceletNonUnistochastic.IsUnistochastic}\left(B\right)) \Rightarrow (\operatorname{HasCirculantLift}\left(B\right)))$$

*Formalization.* `D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.claim` (`✓ std3`).

*Citation.* Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski (2021). *Algebraic and geometric structures inside the Birkhoff polytope*. DOI: [10.1063/5.0046581](https://doi.org/10.1063/5.0046581). URL: <https://arxiv.org/abs/2101.11288>.

*Commentary.*

Section IV, Conjecture 19, page 11: "The sets Cd ∩ Ud and Cd² coincide for all d, i.e., for every circulant unistochastic matrix it is possible to find a corresponding circulant unitary matrix." The formula quantifies over every natural d and every real d × d matrix B. A circulant unitary lift gives both circulantness and unistochasticity, so the displayed implication expresses the remaining inclusion in the asserted equality.

**Theorem 1.3 (A ten-dimensional refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/rajchel-korzekwa-puchala-zyczkowski-2021-conjecture19-circulant-lift` (refuted) by `D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rajchel-korzekwa-puchala-zyczkowski-2021-conjecture19-circulant-lift","declaration_gid":"D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Grzegorz Rajchel-Mieldzioć, Kamil Korzekwa, Zbigniew Puchała, Karol Życzkowski (2021). *Algebraic and geometric structures inside the Birkhoff polytope*. DOI: [10.1063/5.0046581](https://doi.org/10.1063/5.0046581). URL: <https://arxiv.org/abs/2101.11288>.

*Commentary.*

The real matrix B has first row (9,4,0,0,4,0,4,0,0,4)/25 and is circulant. Write i=5a+r and j=5b+s with a,b in {0,1} and r,s in {0,1,2,3,4}. Set Q(i,j)=(−1)^a 1[s=r+1 modulo 5]−(−1)^b 1[r=s+1 modulo 5], W=3I+2Q and U=W/5. The integer identity WWᵀ=25I makes U unitary, and RHLinalg.normSqMatrix U=B. A circulant unitary with these squared norms would have coefficients z nonzero exactly at {0,1,9,4,6}. Its row equations at shifts 1,4,3 are z(0)conj(z(9))+z(1)conj(z(0))=0, z(0)conj(z(6))+z(4)conj(z(0))=0, and z(4)conj(z(1))+z(9)conj(z(6))=0. Conjugating the first and combining it with the second gives z(9)conj(z(6))=z(4)conj(z(1)). The third therefore forces 2z(9)conj(z(6))=0, contradicting the nonzero coefficients. The obstruction concerns dimension ten. Lemma 18's result for d≤4 and the source's spectral characterization of doubly circulant matrices retain their stated scopes.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.HasCirculantLift`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/CirculantUnitaryLiftRefutation.result`
- Dependency: [D5/S3/Quantum/Matrix/CirculantBraceletNonUnistochastic](CirculantBraceletNonUnistochastic.md)
