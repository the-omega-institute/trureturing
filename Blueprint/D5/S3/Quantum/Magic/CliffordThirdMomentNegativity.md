# A negative Clifford third-moment expectation

## Abstract

Zhu, Mao and Yi define the third-moment expectation kappa of a normalized qudit state against a stochastic Lagrangian subspace. The pointwise bound in their Conjecture 2 fails in prime dimension eleven: a one-qudit state has expectation -1196/64000. This refutes that clause and hence the conjecture as printed; the aggregate clauses are not separately refuted.

**Definition 1.1 (Stochastic Lagrangian subspaces).**

$$\forall d : \mathbb{N}, \forall T : \operatorname{Submodule}\left(\operatorname{ZMod}\left(d\right), ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)) \times ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right))\right), (\operatorname{IsStochasticLagrangian}\left(d, T\right)) \Leftrightarrow ((\forall p : ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)) \times ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)), (p \in T) \Rightarrow (\sum_{k : \operatorname{Fin}\left(3\right)} (\operatorname{fst}\left(p\right)\left(k\right) \cdot \operatorname{fst}\left(p\right)\left(k\right)) - \sum_{k : \operatorname{Fin}\left(3\right)} (\operatorname{snd}\left(p\right)\left(k\right) \cdot \operatorname{snd}\left(p\right)\left(k\right)) = 0)) \land ((\operatorname{finrank}\left(\operatorname{ZMod}\left(d\right), T\right) = 3) \land (((k : \operatorname{Fin}\left(3\right) \mapsto 1), (k : \operatorname{Fin}\left(3\right) \mapsto 1)) \in T)))$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.IsStochasticLagrangian` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

For three copies, the quadratic form is x dot x minus y dot y. A stochastic Lagrangian subspace is isotropic for this form, has dimension three, and contains the pair of all-ones vectors.

**Definition 1.2 (The tensor-power operator).**

$$\forall d : \mathbb{N}, \forall n : \mathbb{N}, \forall T : \operatorname{Submodule}\left(\operatorname{ZMod}\left(d\right), ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)) \times ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right))\right), \forall X : (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right), \forall Y : (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right), \operatorname{R}\left(d, n, T, X, Y\right) = \prod_{j : \operatorname{Fin}\left(n\right)} (\operatorname{ite}\left(((k : \operatorname{Fin}\left(3\right) \mapsto X\left(k\right)\left(j\right)), (k : \operatorname{Fin}\left(3\right) \mapsto Y\left(k\right)\left(j\right))) \in T, 1, 0\right))$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.R` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The source convention is r(T) = sum over (x;y) in T of |x><y|. Regrouping r(T) tensor n into three n-qudit copies gives the matrix R: each column j contributes the indicator that its pair of three-component vectors belongs to T.

**Definition 1.3 (Three copies of a pure-state density matrix).**

$$\forall d : \mathbb{N}, \forall n : \mathbb{N}, \forall Psi : ((\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)) \to \mathbb{C}, \forall X : (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right), \forall Y : (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right), \operatorname{stateCube}\left(Psi, X, Y\right) = \prod_{k : \operatorname{Fin}\left(3\right)} (Psi\left(X\left(k\right)\right) \cdot \operatorname{star}\left(Psi\left(Y\left(k\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.stateCube` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The matrix of (|Psi><Psi|) tensor three has the displayed product of amplitudes and conjugate amplitudes.

**Definition 1.4 (The trace expectation).**

$$\forall d : \mathbb{N}, \forall n : \mathbb{N}, (d \ne 0) \Rightarrow (\forall Psi : ((\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)) \to \mathbb{C}, \forall T : \operatorname{Submodule}\left(\operatorname{ZMod}\left(d\right), ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)) \times ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right))\right), \operatorname{kappa}\left(d, n, Psi, T\right) = \operatorname{trace}\left(\operatorname{R}\left(d, n, T\right) \cdot \operatorname{stateCube}\left(Psi\right)\right))$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.kappa` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The expectation is the trace of R times stateCube, in the source bra-ket convention. The nonzero dimension hypothesis makes the computational basis finite.

**Definition 1.5 (The pointwise bound of Conjecture 2).**

$$(claim) \Leftrightarrow (\forall d : \mathbb{N}, (\operatorname{Prime}\left(d\right)) \Rightarrow ((d \ne 2) \Rightarrow (\forall n : \mathbb{N}, \forall Psi : ((\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)) \to \mathbb{C}, (\sum_{x : (\operatorname{Fin}\left(n\right)) \to \operatorname{ZMod}\left(d\right)} (\left\lVert Psi\left(x\right) \right\rVert^{2}) = 1) \Rightarrow (\forall T : \operatorname{Submodule}\left(\operatorname{ZMod}\left(d\right), ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right)) \times ((\operatorname{Fin}\left(3\right)) \to \operatorname{ZMod}\left(d\right))\right), (\operatorname{IsStochasticLagrangian}\left(d, T\right)) \Rightarrow ((0 \le \operatorname{kappa}\left(d, n, Psi, T\right)) \land (\operatorname{kappa}\left(d, n, Psi, T\right) \le 1))))))$$

*Formalization.* `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.claim` (`✓ std3`).

*Citation.* H. Zhu, C. Mao, C. Yi (2024). *Third moments of qudit Clifford orbits and 3-designs based on magic orbits*. DOI: [10.48550/arXiv.2410.13575](https://doi.org/10.48550/arXiv.2410.13575). URL: <https://arxiv.org/abs/2410.13575v1>.

*Commentary.*

The assertion ranges over every odd prime dimension, every number of qudits, every normalized complex amplitude vector and every stochastic Lagrangian subspace. The complex order requires a zero imaginary part and bounds the real part between zero and one.

**Theorem 1.6 (A normalized state violates the lower bound).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhu-2024-clifford-third-moment-kappa-negativity` (refuted) by `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhu-2024-clifford-third-moment-kappa-negativity","declaration_gid":"D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Over ZMod 11, let O have diagonal entries 7 and off-diagonal entries 8, and let T be the range of y mapped to (Oy,y). The identities transpose(O) O = I and O 1 = 1 make T stochastic Lagrangian; injectivity gives dimension three. Let v = (-2,0,-2i,1-2i,-1-i,1+2i,-1-2i,-2,-2i,2-i,1-i), whose squared norm is 40, and set Psi(x) = v(x(0))/sqrt(40). The trace reduces to 40^(-3) times the sum, over all y in (ZMod 11)^3, of the product of v(y(k)) conjugate(v((Oy)(k))). This Gaussian-integer sum is exactly -1196, with zero imaginary part. Thus kappa = -1196/64000 < 0.

## References

- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.IsStochasticLagrangian`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.R`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.claim`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.kappa`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.result`
- Truth anchor: `D5/S3/Quantum/Magic/CliffordThirdMomentNegativity.stateCube`
