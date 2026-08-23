# Future Probability Residual Correlation

## Abstract

Future linear-prediction error is exactly the correlation of state and effect residuals.

**Theorem 1.1 (Future probability error is the exact residual correlation).**

$$\forall d, [\operatorname{Fintype}\left(d\right)] [\operatorname{Nonempty}\left(d\right)] [\operatorname{DecidableEq}\left(d\right)],\\{}\rho: \operatorname{Matrix}\left(d, d, \mathbb{C}\right), H: \operatorname{LinearMap}\left(\mathbb{R}, \operatorname{HermitianTraceZero}\left(d\right), \operatorname{HermitianTraceZero}\left(d\right)\right),\\{}r\in \mathbb{N}, E: \operatorname{Fin}\left(r+1\right) \to \operatorname{HermitianTraceZero}\left(d\right), m, k\in \mathbb{N}, a\in \operatorname{Fin}\left(r+1\right),\\{}\operatorname{Density}\left(\rho\right) \Rightarrow \operatorname{let} S = \operatorname{towerSpace}\left(H, E, m\right), R = S^{{\perp}},\\{}X_{\rho} = \operatorname{densityCoordinate}\left(\rho\right), A_{a,k} = H^{{k}}(E(a)),\\{}\rho_{m} = \operatorname{linearPredictionRepresentative}\left(S, X_{\rho}\right), \Delta p_{a,k}^{(m)} = \operatorname{ReTr}\left((\rho-\rho_{m})A_{a,k}\right)\;\\{}\Delta p_{a,k}^{(m)} = \operatorname{innerHS}\left(\operatorname{P}\left(R, X_{\rho}\right), \operatorname{P}\left(R, A_{a,k}\right)\right) \land \\{}\operatorname{abs}\left(\Delta p_{a,k}^{(m)}\right) \leq \sqrt{\operatorname{residualMass}\left(S, X_{\rho}\right)} \operatorname{normHS}\left(\operatorname{P}\left(R, A_{a,k}\right)\right) \land \\{}\neg\operatorname{PosSemidef}\left(\operatorname{linearPredictionRepresentative}\left(\operatorname{span}\left(\mathbb{R}, \operatorname{diag}\left(1, 0, -1\right)\right), \operatorname{densityCoordinate}\left(\operatorname{diag}\left(1, 0, 0\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/FutureProbabilityResidualCorrelation.future_probability_residual_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a positive semidefinite trace-one matrix on a finite nonempty carrier. Its centered coordinate lies in the canonical real trace-zero Hermitian space. A real-linear Heisenberg map and a finite centered-effect family construct the visible tower S, its orthogonal residual R, and every future effect A_a,k.

The linear representative retains the visible projection of the centered state and restores the trace-one identity component. The real trace error against every iterated future effect equals the Hilbert--Schmidt inner product of the state and effect residual projections.

Cauchy--Schwarz bounds the absolute error by the square root of the canonical residual mass times the future effect residual norm. The final public conjunct uses the valid density diag(1,0,0) and the visible real line spanned by diag(1,0,-1); its projected representative has diagonal entries 5/6, 1/3, and -1/6, so it is not positive semidefinite.

The proof applies the exact orthogonal-projection self-adjointness and Cauchy--Schwarz bounds from the pinned library. Repository carrier, tower, residual-space, residual-mass, and centered-state definitions are imported rather than redeclared.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/FutureProbabilityResidualCorrelation.future_probability_residual_correlation`
- Dependency: [D5/S3/Quantum/Fibers/CenteredEffectTowerStability](../Fibers/CenteredEffectTowerStability.md)
- Dependency: [D5/S3/Quantum/Tomography/ResidualControlsNaturality](ResidualControlsNaturality.md)
