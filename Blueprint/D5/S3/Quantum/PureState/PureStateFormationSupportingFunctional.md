# A supporting functional at every pure bipartite state

## Abstract

In every finite-dimensional bipartite system, each pure state admits a Hermitian supporting functional for the entanglement of formation.

Let Alice and Bob have positive dimensions a and b. Fin(a) and Fin(b) label their bases by 0 through a - 1 and 0 through b - 1: a source index (i,j) in the ranges 1 through a and 1 through b corresponds to (i - 1,j - 1) here. Vectors are functions on Fin(a) times Fin(b), and matrices have rows and columns in that same product. Both even and odd positive dimensions are included, independently on each factor.

**Definition 1.1 (The supporting-functional assertion).**

$$\operatorname{claim} \Leftrightarrow (\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), ((1 \le a) \Rightarrow ((1 \le b) \Rightarrow (\forall (\psi: ((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right)) \to \mathbb{C})), ((\sum_{(x: (\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right)))} (\left|\psi\left(x\right)\right|^{2}) = 1) \Rightarrow (\exists (W: \operatorname{Matrix}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right)), (\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right)), \mathbb{C}\right)), ((\operatorname{IsHermitian}\left(W\right)) \land ((\operatorname{Re}\left(\operatorname{Tr}\left(W \cdot \operatorname{rankOneDensity}\left(\psi\right)\right)\right) = \operatorname{vonNeumannEntropy}\left(\operatorname{marginalRight}\left(\operatorname{pureDensityState}\left(\psi\right)\right)\right)) \land ((\left(E_{F}\right)\left(\operatorname{pureDensityState}\left(\psi\right)\right) = \operatorname{ENNReal.ofReal}\left(\operatorname{Re}\left(\operatorname{Tr}\left(W \cdot \operatorname{rankOneDensity}\left(\psi\right)\right)\right)\right)) \land (\forall (\sigma: \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right)), (\operatorname{ENNReal.ofReal}\left(\operatorname{Re}\left(\operatorname{Tr}\left(W \cdot \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(\sigma\right)\right)\right)\right)\right) \le \left(E_{F}\right)\left(\sigma\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.claim` (`✓ std3`).

*Citation.* A. S. Holevo; M. E. Shirokov (2026). *Log-Sobolev inequality, von Neumann entropy and Entanglement of Formation*. URL: <https://arxiv.org/abs/2609.12667v3>.

*Commentary.*

Holevo and Shirokov ask in the Introduction and Section 3.1 whether the entanglement of formation has a supporting affine functional at every pure state of a finite-dimensional composite system. The assertion below uses a Hermitian matrix W to represent that functional by the real part of Tr(W sigma). On the trace-one state space this representation also includes an affine constant, by adding a scalar multiple of the identity to W.

The normalization is the squared vector norm, equivalently star(psi) dot psi = 1. rankOneDensity(psi) has entry psi(i,j) times the complex conjugate of psi(k,l). pureDensityState(psi) is the density state with that matrix; its unit-norm proof argument is supplied by the displayed normalization and suppressed in the formula. marginalRight traces out Bob and retains Alice. DensityState consists of positive semidefinite matrices of trace one, and CStarMatrix.ofMatrix.symm(val(sigma)) is the underlying matrix.

The symbol E with subscript F denotes E_F, the infimum of the average marginal entropy over all finite pure ensembles with the prescribed average state. In the entropy definition, CFC.log applies the natural real logarithm by functional calculus. Its spectral expression uses the eigenvalues of the Hermitian underlying density matrix, indexed by n; every zero eigenvalue contributes zero.

$$
\forall (n: Type), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)], (\forall (\rho: \operatorname{DensityState}\left(n\right)), (\operatorname{vonNeumannEntropy}\left(\rho\right) = -(\operatorname{Re}\left(\operatorname{Tr}\left(\operatorname{val}\left(\rho\right) \cdot \operatorname{CFC.log}\left(\operatorname{val}\left(\rho\right)\right)\right)\right)))))
$$

$$
\forall (n: Type), ([\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)], (\forall (\rho: \operatorname{DensityState}\left(n\right)), (\operatorname{vonNeumannEntropy}\left(\rho\right) = \sum_{(i: n)} (\operatorname{Real.negMulLog}\left(\operatorname{eigenvalues}\left(\operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(\rho\right)\right)\right)\left(i\right)\right)))))
$$

$$
(\forall (t: \mathbb{R}), (\operatorname{Real.negMulLog}\left(t\right) = (-t) \cdot \operatorname{Real.log}\left(t\right))) \land ((\operatorname{Real.log}\left(0\right) = 0) \land (0 \cdot \operatorname{Real.log}\left(0\right) = 0))
$$

The marginal traces out Bob. The coefficient matrix M represents a joint vector, mass is its squared norm, and Pure(a,b) consists of the coefficient matrices of mass one.

$$
\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (\sigma: \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right)), (\forall (i: \operatorname{Fin}\left(a\right)), (\forall (j: \operatorname{Fin}\left(a\right)), (\operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(\operatorname{marginalRight}\left(\sigma\right)\right)\right)\left(i, j\right) = \sum_{(k: \operatorname{Fin}\left(b\right))} (\operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(\sigma\right)\right)\left((i, k), (j, k)\right)))))))
$$

$$
\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\operatorname{Coeff}\left(a, b\right) = \operatorname{Matrix}\left(\operatorname{Fin}\left(a\right), \operatorname{Fin}\left(b\right), \mathbb{C}\right)))
$$

$$
\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (M: \operatorname{Coeff}\left(a, b\right)), (\operatorname{mass}\left(M\right) = \sum_{(i: \operatorname{Fin}\left(a\right))} (\sum_{(j: \operatorname{Fin}\left(b\right))} (\operatorname{normSq}\left(M\left(i, j\right)\right))))))
$$

$$
\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\operatorname{Pure}\left(a, b\right) = \{(M: \operatorname{Coeff}\left(a, b\right)) \mid (\operatorname{mass}\left(M\right) = 1)\}))
$$

An Ensemble(n,sigma) consists of probabilities p and normalized pure coefficient matrices q with the displayed average. Complex(p(i)) is the real-to-complex coercion; multiplying a matrix by this scalar denotes scalar multiplication. The lambda expression uncurries a coefficient matrix. For an ensemble e, p(e) and psi(e) are its probability and pure-vector projections. The normalization in Pure supplies the suppressed proof argument of pureDensityState.

$$
\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (\sigma: \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right)), (\operatorname{Ensemble}\left(n, \sigma\right) = \{((p, q): ((\operatorname{Fin}\left(n\right) \to \mathbb{R}) \times (\operatorname{Fin}\left(n\right) \to \operatorname{Pure}\left(a, b\right)))) \mid ((\forall (i: \operatorname{Fin}\left(n\right)), (0 \le p\left(i\right))) \land ((\sum_{(i: \operatorname{Fin}\left(n\right))} (p\left(i\right)) = 1) \land (\sum_{(i: \operatorname{Fin}\left(n\right))} (\operatorname{Complex}\left(p\left(i\right)\right) \cdot \operatorname{rankOneDensity}\left((\lambda (x: (\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))), (\operatorname{val}\left(q\left(i\right)\right)\left(\operatorname{fst}\left(x\right), \operatorname{snd}\left(x\right)\right)))\right)) = \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(\sigma\right)\right))))\}))))
$$

$$
\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (\sigma: \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right)), (\forall (e: \operatorname{Ensemble}\left(n, \sigma\right)), (\operatorname{cost}\left(e\right) = \sum_{(i: \operatorname{Fin}\left(n\right))} (\operatorname{p}\left(e\right)\left(i\right) \cdot \operatorname{vonNeumannEntropy}\left(\operatorname{marginalRight}\left(\operatorname{pureDensityState}\left((\lambda (x: (\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))), (\operatorname{val}\left(\psi\left(e\right)\left(i\right)\right)\left(\operatorname{fst}\left(x\right), \operatorname{snd}\left(x\right)\right)))\right)\right)\right)))))))
$$

E_F takes values in ENNReal, the extended nonnegative reals. Both infima are taken in ENNReal, and ENNReal.ofReal is applied to the whole real ensemble cost inside the infima. ENNReal.ofReal(x) is max(x,0) in that space. In the claim, it is applied to the whole real trace value in both the pure-state equality and the comparison for every sigma. The real equality with the marginal entropy is stated separately from the equality after ofReal, so the value at the pure state retains its sign information.

$$
\forall (a: \mathbb{N}), (\forall (b: \mathbb{N}), (\forall (\sigma: \operatorname{DensityState}\left((\operatorname{Fin}\left(a\right) \times \operatorname{Fin}\left(b\right))\right)), (\left(E_{F}\right)\left(\sigma\right) = \operatorname{inf}_{(n: \mathbb{N})} (\operatorname{inf}_{(e: \operatorname{Ensemble}\left(n, \sigma\right))} (\operatorname{ENNReal.ofReal}\left(\operatorname{cost}\left(e\right)\right))))))
$$

**Theorem 1.2 (The assertion holds in all finite dimensions).**

$$\operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.result` (`✓ std3`). ∎

*Resolves.* `Problems/holevo-shirokov-2026-pure-state-formation-supporting-functional` (proved) by `D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"holevo-shirokov-2026-pure-state-formation-supporting-functional","declaration_gid":"D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. S. Holevo; M. E. Shirokov (2026). *Log-Sobolev inequality, von Neumann entropy and Entanglement of Formation*. URL: <https://arxiv.org/abs/2609.12667v3>.

*Commentary.*

The construction answers the question of Holevo and Shirokov. Put P = |psi><psi| and R = Tr_B(P), and write log-zero(R) for spectral application of the real logarithm, set to zero at a zero eigenvalue. If r(i) are the eigenvalues of R, take c to be the sum of their reciprocals, with reciprocal zero at zero. Thus c is nonnegative and c r(i) is at least one whenever r(i) is positive.

For r >= 0, 0 <= t <= 1 and c >= 0 with c r >= 1 when r > 0, the scalar logarithmic inequality gives -t log-zero(r) - (t - r) - c(t - r)^2 <= -t log(t), where the right side is zero at t = 0. For positive r and t this follows from log(t/r) <= t/r - 1 and 1/r <= c. The cases r = 0 and t = 0 follow separately from nonnegativity and c r >= 1, respectively.

For any density matrix T on Alice's space, average this scalar inequality over the two eigenbases with weights w(i,j) = |<e(i),u(j)>|^2. The overlap matrix is doubly stochastic: every row and column sums to one. The linear term cancels because both spectra sum to one, the logarithmic term becomes -Re Tr(log-zero(R) T), and the weighted squared differences become the squared Hilbert-Schmidt distance. Consequently S(T) >= -Re Tr(log-zero(R) T) - c ||T - R||_HS^2.

Cauchy-Schwarz in Bob's index gives ||Tr_B(X)||_HS^2 <= b ||X||_HS^2 for every joint matrix X. For a pure density Q, ||Q - P||_HS^2 = 2(1 - Re Tr(PQ)). Set K = 2bc and W = -log-zero(R) tensor I_B - K(I_AB - P). This W is Hermitian. The partial-trace bound and the entropy estimate give Re Tr(WQ) <= S(Tr_B(Q)), with equality Re Tr(WP) = S(R) at Q = P.

For every finite pure ensemble with average sigma, linearity of the trace and the pure-state inequality bound Re Tr(W sigma) by its average marginal entropy. Applying ofReal and taking the infimum over all these ensembles proves the bound by E_F(sigma). At P, the one-element ensemble gives the reverse inequality, hence E_F(P) = ofReal(Re Tr(WP)). Together with the real equality at P, these are precisely the clauses of claim.

## References

- Truth anchor: `D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.claim`
- Truth anchor: `D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.result`
- Dependency: [D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation](../Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
