# Density-independent boundedness in fixed dimension

## Abstract

The Alhasan–Fawwaz quotient is bounded by dimension independently of every positive definite density.

**Definition 1.1 (The original quotient set).**

$$(\forall iota: Type, [Fintype(iota)] [DecidableEq(iota)] (\forall rho: Matrix(iota, iota, \mathbb{C}), (\forall q: \mathbb{R}, q \in quotientValues(rho) \iff (\exists A: Matrix(iota, iota, \mathbb{C}), (\exists B: Matrix(iota, iota, \mathbb{C}), (PosSemidef(A) \land (IsHermitian(B) \land ((A + i B) \neq 0 \land q = \frac{\Re(Tr(rho A))}{\Re(Tr(rho abs((A + i B))))}))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.quotientValues` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

For an arbitrary finite index type iota, bornProbability(rho,Y) is the existing unnormalized complex trace Tr(rho Y). The set consists exactly of real q obtained from A positive semidefinite, B Hermitian, and A+iB nonzero. Both traces are projected to their real parts. Positivity of rho makes the denominator strictly positive. The definition is Section 5.12 of arXiv:2610.34388v1, with the standing positive definite density convention of Section 3.1.

**Definition 1.2 (The real supremum).**

$$(\forall iota: Type, [Fintype(iota)] [DecidableEq(iota)] (\forall rho: Matrix(iota, iota, \mathbb{C}), a(rho) = sSup(quotientValues(rho))))$$

*Formalization.* `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

The real supremum uses the same set, with no trace-one premise. The result proves nonemptiness and an upper bound before applying real completeness; no totalized empty supremum is used.

**Theorem 1.3 (The matrix inequality).**

$$(\forall iota: Type, [Fintype(iota)] [DecidableEq(iota)] (\forall A: Matrix(iota, iota, \mathbb{C}), (\forall B: Matrix(iota, iota, \mathbb{C}), ((PosSemidef(A) \land IsHermitian(B)) \Rightarrow A \le card(iota) abs((A + i B))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.accretive_le_card_abs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

For every finite index type and all A positive semidefinite and B Hermitian, A is at most card(iota) times the actual CFC modulus of A+iB in Loewner order. Diagonalize P=|A+iB|, rather than A+iB. If P e_j=s_j e_j in an orthonormal basis, then s_j is nonnegative and the square identity gives norm(X e_j)=s_j. The real part of the quadratic form of X is that of A, so Cauchy–Schwarz gives h_j=inner(e_j,A e_j) at most s_j. For Q=sqrt(A), expand any v in the same basis. Triangle inequality and finite Cauchy–Schwarz bound norm(Q v) squared by card(iota) times the sum of norm(z_j) squared h_j, and hence by card(iota) times inner(v,P v). Zero eigenvalues and the zero-dimensional case remain included; no singular value is inverted.

**Definition 1.4 (The original boundedness question).**

$$(\forall n: \mathbb{N}, (1 \le n \Rightarrow (\exists C: \mathbb{R}, (0 \le C \land (\forall rho: Matrix(Fin(n), Fin(n), \mathbb{C}), (PosDef(rho) \Rightarrow (Nonempty(quotientValues(rho)) \land (IsLUB(quotientValues(rho), a(rho)) \land a(rho) \le C))))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

For every positive dimension there exists one finite real bound before the quantifier over positive definite densities. The quotient set must be nonempty and its real supremum must be a least upper bound.

**Theorem 1.5 (The complete fixed-dimension boundedness assertion).**

$$(\forall n: \mathbb{N}, (1 \le n \Rightarrow (\exists C: \mathbb{R}, (0 \le C \land (\forall rho: Matrix(Fin(n), Fin(n), \mathbb{C}), (PosDef(rho) \Rightarrow (Nonempty(quotientValues(rho)) \land (IsLUB(quotientValues(rho), a(rho)) \land a(rho) \le C))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/abed-nikolaeva-novikov-2026-af-density-bound` (proved) by `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"abed-nikolaeva-novikov-2026-af-density-bound","declaration_gid":"D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sami Abdullah Abed; Irina Nikolaeva; Andrej Novikov (2026). *How characterisations of traces and central elements fail: sharp violation constants via Michelson contrast and noncentrality*. DOI: [10.48550/arXiv.2610.34388](https://doi.org/10.48550/arXiv.2610.34388). URL: <https://arxiv.org/abs/2610.34388v1>.

*Commentary.*

This answers the selected sentence of Section 11.2(5), original owner #22774: “Is a bounded on M_n(C) independently of rho?” For each natural n at least one, the real witness C equals n and is nonnegative. For every positive definite rho, the proof establishes that every admissible denominator is strictly positive, one belongs to the exact quotient set, every quotient lies between zero and C, a(rho) is the actual least upper bound, and 1 is at most a(rho), which is at most C. Trace pairing with a PSD matrix is nonnegative by the reused RHLinalg theorem. For strict positivity, factor rho=Y*Y with Y invertible and P=Q squared; cyclicity identifies Tr(rho P) with Tr((YQ)*(YQ)). Vanishing forces Q=0 and P=0. Since X is nonzero, its actual modulus is nonzero. The identity A=I, B=0 gives one. Nonempty bounded real sets have a genuine least upper bound. The density need not have trace one; its condition number never appears. Singular X, n=1 and arbitrary positive density scales are covered. The source's dimension-two result, condition-dependent estimates and separate sharpness or factor questions are not claimed as new consequences. Worldwide novelty and the original Alhasan–Fawwaz article remain unverified.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.a`
- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.accretive_le_card_abs`
- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.quotientValues`
- Truth anchor: `D5/S3/Quantum/Matrix/AbedNikolaevaNovikovAFDensityBound.result`
- Dependency: [D5/S3/Quantum/FiniteDimensional](../FiniteDimensional.md)
