# The sharp upper endpoint of the Zhang–Jing power block

## Abstract

The power block characterizes normality for 1/2 ≤ a < 1, including singular matrices; at a = 1 it is positive semidefinite for every matrix.

**Definition 1.1 (The source's unresolved closed interval).**

$$(claim) \Leftrightarrow ((\forall (a: \mathbb{R}), (\frac{1}{2} \le a) \Rightarrow ((a \le 1) \Rightarrow (\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block}\left((fun (x: \mathbb{R}) \mapsto x^{2 \cdot a}), (fun (x: \mathbb{R}) \mapsto x^{2 \cdot (1 - a)}), A\right)\right)) \Leftrightarrow (\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A = A \cdot \operatorname{Matrix.conjTranspose}\left(A\right))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.claim` (`✓ std3`).

*Citation.* Feng Zhang; Hefang Jing (2025). *More inequalities for positive semidefinite matrices*. DOI: [10.13001/ela.2025.9201](https://doi.org/10.13001/ela.2025.9201). URL: <https://doi.org/10.13001/ela.2025.9201>.

*Commentary.*

After Remark 2.13, p. 601: “Due to the limitations of our research method, we cannot solve the problem that Theorem 2.3 holds for 1/2 ≤ a ≤ 1.” The proposition expands the equivalence over every real a in that interval, every natural dimension n, and every complex square matrix A. The matrix functions use Real.rpow, with x⁰ = 1. PosSemidef means positive semidefinite, and normality means Aᴴ A = A Aᴴ.

**Theorem 1.2 (The extension to a = 1 fails).**

$$\neg (\forall (a: \mathbb{R}), (\frac{1}{2} \le a) \Rightarrow ((a \le 1) \Rightarrow (\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block}\left((fun (x: \mathbb{R}) \mapsto x^{2 \cdot a}), (fun (x: \mathbb{R}) \mapsto x^{2 \cdot (1 - a)}), A\right)\right)) \Leftrightarrow (\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A = A \cdot \operatorname{Matrix.conjTranspose}\left(A\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-jing-2025-block-criterion-power-case-theorem-2-3` (refuted) by `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-jing-2025-block-criterion-power-case-theorem-2-3","declaration_gid":"D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Feng Zhang; Hefang Jing (2025). *More inequalities for positive semidefinite matrices*. DOI: [10.13001/ela.2025.9201](https://doi.org/10.13001/ela.2025.9201). URL: <https://doi.org/10.13001/ela.2025.9201>.

*Commentary.*

At a = 1 the diagonal corners are Aᴴ A and I, so the block is Qᴴ Q for Q = [A,I], padded by zero rows to form a square matrix. It is positive semidefinite for every A. For A = [[0,1],[2,0]], the (0,0) entries of Aᴴ A and A Aᴴ are 4 and 1. Thus A is nonnormal and the universal equivalence on the closed interval is false.

## Application below the upper endpoint

$$
\forall (a: \mathbb{R}), (\frac{1}{2} \le a) \Rightarrow ((a < 1) \Rightarrow (\forall (n: \mathbb{N}), \forall (A: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right)), (\operatorname{Matrix.PosSemidef}\left(\operatorname{D5.S3.Quantum.Matrix.ZhangJingBlockNormalityRefutation.block}\left((fun (x: \mathbb{R}) \mapsto x^{2 \cdot a}), (fun (x: \mathbb{R}) \mapsto x^{2 \cdot (1 - a)}), A\right)\right)) \Leftrightarrow (\operatorname{Matrix.conjTranspose}\left(A\right) \cdot A = A \cdot \operatorname{Matrix.conjTranspose}\left(A\right))))
$$

The strict interval is a substantive application of existing results, with the following literal scope. The parameter a is any real number with both guards, n is any natural number including zero, and A is any complex square matrix, including singular matrices. There is no Nonempty, invertibility, positive singular-value, commutativity or additional continuity assumption. Put f(x) = Real.rpow x (2a) and g(x) = Real.rpow x (2(1−a)). The canonical ZhangJingBlockNormalityRefutation.block is exactly Matrix.fromBlocks (cfc f (CFC.sqrt (Aᴴ A))) Aᴴ A (cfc g (CFC.sqrt (Aᴴ A))); normality is the displayed equality.

Use D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues on this same A. With dᵢ = Real.sqrt(eigenvalues(Aᴴ A)ᵢ), dᵢ ≥ 0, D = diag(dᵢ), it supplies unitary V,W and A = V D Wᴴ. Unitary cancellation gives Aᴴ A = W D² Wᴴ and A Aᴴ = V D² Vᴴ. CFC.sqrt_eq_real_sqrt, cfcₙ_eq_cfc with Real.sqrt_zero, the canonical D5.S3.Quantum.Information.RenyiInformationCombiningOrderThree.cfc_unitary_diagonal, and Real.sqrt_sq give |A| = W D Wᴴ. The SVD supplier requires only Fintype and DecidableEq on Fin n, with no nonzero dimension or rank restriction. Its physlib-source attribution and Apache-2.0 license remain those of its canonical owner.

Set U = Wᴴ V, F = diag(dᵢ^(2a)), G = diag(dᵢ^(2(1−a))) and T = diag(W,V). T is unitary. Applying the same canonical CFC transport to f and g on the same d gives Tᴴ block(f,g,A) T = [[F,D],[D,Uᴴ G U]]. Matrix.IsUnit.posSemidef_star_left_conjugate_iff therefore identifies positivity of the original block with positivity of this coordinate block. These are two functions of one actual singular-value realization, not independently selected spectra.

For the forward direction put P = diag(dᵢ^(1−2a)). Entrywise PF = D and PD = G. For dᵢ > 0 these follow from Real.rpow_add. For dᵢ = 0 the factors dᵢ^(2a) and dᵢ^(2(1−a)) vanish because both exponents are positive. At a = 1/2, P has 0^0 = 1 on the zero fiber, and both products still vanish; for a > 1/2, Real.zero_rpow at the nonzero negative exponent gives Pᵢᵢ = 0 there. Thus no inverse of F or invertible Schur complement is required.

Let L = [[−P,0],[I,0]]. Matrix.PosSemidef.conjTranspose_mul_mul_same and direct block multiplication yield Lᴴ [[F,D],[D,Uᴴ G U]] L = diag(Uᴴ G U−G,0). Matrix.PosSemidef.submatrix gives Uᴴ G U−G positive semidefinite. Matrix.trace_units_conj' makes its trace zero; Matrix.PosSemidef.trace_eq_zero_iff makes it zero. By commute_unitary_iff_star_left_conjugate, U G = G U. At each entry with Uᵢⱼ ≠ 0 cancel that scalar, then apply Real.rpow_left_inj to the nonnegative dᵢ,dⱼ with exponent 2(1−a) ≠ 0. Entries with Uᵢⱼ = 0 vanish directly. Hence U D = D U. The same entrywise argument with exponent 2, together with the two Gram identities above and unitary cancellation, equates U D = D U with Aᴴ A = A Aᴴ. This proves positivity implies normality.

For the reverse direction, normality and the Gram identities give commutation with D², and exponent-2 injectivity gives U D = D U. Commute.cfc_real applied to g, with D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal, gives Uᴴ G U = G. Set X = diag(dᵢ^a), Y = diag(dᵢ^(1−a)). Real.rpow_add' applies also at zero because the sums 2a, 2(1−a), and 1 are nonzero: X² = F, Y² = G, XY = YX = D. Thus [[F,D],[D,G]] is Qᴴ Q for the padded row Q = [X,Y], and Matrix.posSemidef_conjTranspose_mul_self makes it positive semidefinite. Unitary transport returns the original block's positivity. This proves normality implies positivity.

Every construction also applies to Fin 0: the matrix and index equalities are empty and no choice of an index or positive rank is used. The half endpoint and zero singular values are included in both directions. At a = 1, g is constant and the injectivity step fails exactly as in the retained refutation. The published lower interval 0 ≤ a ≤ 1/2 is literature-attested Theorem 2.3, not independently formalized here. Parameters outside [0,1], infinite-dimensional operators, a general functional injectivity repair and a new singular-matrix classification are outside this application. The earlier Question 2.14 scalar-pair refutation is distinct.

The application introduces no retained positive theorem, GID, resolution marker or audit wrapper. The canonical CFC supplier's dependent/pointwise arena, exact reconstruction, whole-family intervention and sensitivity audit remains unfinished; removing an application declaration does not finish that audit. Literature completeness and priority remain ASSUMED-UNVERIFIED.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/ZhangJingPowerCaseSettlement.result`
- Dependency: [D5/S3/Quantum/Matrix/ZhangJingBlockNormalityRefutation](ZhangJingBlockNormalityRefutation.md)
