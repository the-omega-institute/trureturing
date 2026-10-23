# Stationarity of quadratic POVM variations

## Abstract

At an optimum of a finite matrix POVM score, a positive quadratic perturbation of an effect gives an equality between its first-order score and the corresponding weighted total score.

**Theorem 1.1 (A first-order necessary condition).**

$$\forall n \in \mathbb{N},\; \forall dim \in \mathbb{N},\; \forall A \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dim\right), \operatorname{Fin}\left(dim\right), \mathbb{C}\right),\; \forall M \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dim\right), \operatorname{Fin}\left(dim\right), \mathbb{C}\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; (\operatorname{IsPOVM}\left(M\right)) \Rightarrow ((\forall F \in \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dim\right), \operatorname{Fin}\left(dim\right), \mathbb{C}\right),\; (\operatorname{IsPOVM}\left(F\right)) \Rightarrow (\sum_{j : \operatorname{Fin}\left(n\right)} (\operatorname{Matrix.trace}\left(A\left(j\right) \cdot F\left(j\right)\right).re) \le \sum_{j : \operatorname{Fin}\left(n\right)} (\operatorname{Matrix.trace}\left(A\left(j\right) \cdot M\left(j\right)\right).re))) \Rightarrow (\forall D \in \operatorname{Matrix}\left(\operatorname{Fin}\left(dim\right), \operatorname{Fin}\left(dim\right), \mathbb{C}\right),\; \forall E \in \operatorname{Matrix}\left(\operatorname{Fin}\left(dim\right), \operatorname{Fin}\left(dim\right), \mathbb{C}\right),\; \forall d \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \forall e \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; (\sum_{j : \operatorname{Fin}\left(n\right)} (\operatorname{SMul.smul}\left(d\left(j\right), M\left(j\right)\right)) = D) \Rightarrow ((\sum_{j : \operatorname{Fin}\left(n\right)} (\operatorname{SMul.smul}\left(e\left(j\right), M\left(j\right)\right)) = E) \Rightarrow ((\forall t \in \mathbb{R},\; \operatorname{Matrix.PosSemidef}\left(M\left(i\right) + \operatorname{SMul.smul}\left(t, D\right) + \operatorname{SMul.smul}\left(t^{2}, E\right)\right)) \Rightarrow (\operatorname{Matrix.trace}\left(A\left(i\right) \cdot D\right).re = \sum_{j : \operatorname{Fin}\left(n\right)} (d\left(j\right) \cdot \operatorname{Matrix.trace}\left(A\left(j\right) \cdot M\left(j\right)\right).re))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/QuadraticPovmStationarity.quadratic_stationarity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and M be families of complex dim by dim matrices indexed by Fin n. Suppose M is a POVM maximizing the sum of the real traces of A(j) M(j). The matrices D and E have real expansions d and e in the effects M(j), and M(i)+t D+t squared E is positive semidefinite for every real t. These hypotheses imply that the real trace of A(i) D equals the d-weighted sum of the real traces of A(j) M(j). No Hermitian assumption on A is required, and both n and dim range over all natural numbers.

Near t=0, the coefficient of M(i) in the perturbed effect stays positive and exceeds each other coefficient. The other effects can therefore be rescaled by positive coefficients so that, after normalization, the family remains a POVM. Optimality bounds its score. Clearing the positive normalization factor yields a real quadratic polynomial with a local maximum at zero. Its linear coefficient vanishes by the derivative condition for a local maximum. This equality supplies the first-order constraints used for the isolated four-state qubit ensemble.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/QuadraticPovmStationarity.quadratic_stationarity`
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
