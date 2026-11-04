# Continuant obstruction and coordinate dimensions

## Abstract

Continuant obstruction and coordinate dimensions.

**Theorem 1.1 (Endpoint of a bounded recurrence).**

$$\forall N: \operatorname{Nat}, (1 \le N) \Rightarrow (\forall t: \operatorname{Real}, \forall y: \operatorname{Nat} \to \operatorname{Real}, (\forall j: \operatorname{Nat}, (j + 2 \le N) \Rightarrow (y\left(j + 2\right) = t \cdot y\left(j + 1\right) - y\left(j\right))) \Rightarrow (y\left(N\right) = \operatorname{Polynomial}.\operatorname{eval}\left(t, \operatorname{Polynomial}.\operatorname{Chebyshev}.\operatorname{S}\left(\operatorname{Real}, (\operatorname{Nat}.\operatorname{cast}\left(N\right): \operatorname{Int}) - 1\right)\right) \cdot y\left(1\right) - \operatorname{Polynomial}.\operatorname{eval}\left(t, \operatorname{Polynomial}.\operatorname{Chebyshev}.\operatorname{S}\left(\operatorname{Real}, (\operatorname{Nat}.\operatorname{cast}\left(N\right): \operatorname{Int}) - 2\right)\right) \cdot y\left(0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.bounded_continuant_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

A real sequence satisfying the second-order recurrence through N is determined at N by its first two values and the rescaled Chebyshev polynomials.

**Definition 1.2 (Theta coordinate structure).**

$$\forall E: \operatorname{Type}, [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\operatorname{Real}, E\right)] \forall k: \operatorname{Nat}, \forall t: \operatorname{Real}, \forall e: \operatorname{Real}, \operatorname{ThetaCoordinates} E k t e: \operatorname{structure} (A: E \to_{l[\operatorname{Real}]} \operatorname{Real}; D: E \to_{l[\operatorname{Real}]} \operatorname{Real}; B: E \to_{l[\operatorname{Real}]} \operatorname{Real}; C: E \to_{l[\operatorname{Real}]} \operatorname{Real}; B': E \to_{l[\operatorname{Real}]} \operatorname{Real}; C': E \to_{l[\operatorname{Real}]} \operatorname{Real}; Y: \operatorname{Nat} \to E \to_{l[\operatorname{Real}]} \operatorname{Real}; (Y\left(0\right) = A) \land ((Y\left(6 \cdot k + 4\right) = D) \land ((\forall x: E, t \cdot B\left(x\right) = A\left(x\right) + C\left(x\right)) \land ((\forall x: E, t \cdot C\left(x\right) = B\left(x\right) + D\left(x\right)) \land ((\forall x: E, t \cdot B'\left(x\right) = A\left(x\right) + C'\left(x\right)) \land ((\forall x: E, t \cdot C'\left(x\right) = B'\left(x\right) + D\left(x\right)) \land ((\forall x: E, Y\left(1, x\right) = \left(t + e\right) \cdot A\left(x\right) - B\left(x\right) - B'\left(x\right)) \land ((\forall x: E, Y\left(6 \cdot k + 3, x\right) = \left(t + e\right) \cdot D\left(x\right) - C\left(x\right) - C'\left(x\right)) \land ((\forall j: \operatorname{Nat}, (j + 2 \le 6 \cdot k + 4) \Rightarrow (\forall x: E, Y\left(j + 2, x\right) = t \cdot Y\left(j + 1, x\right) - Y\left(j, x\right))) \land (\forall x: E, (A\left(x\right) = 0) \Rightarrow ((D\left(x\right) = 0) \Rightarrow ((B\left(x\right) = 0) \Rightarrow ((C\left(x\right) = 0) \Rightarrow ((B'\left(x\right) = 0) \Rightarrow ((C'\left(x\right) = 0) \Rightarrow ((\forall j: \operatorname{Nat}, (j \le 6 \cdot k + 4) \Rightarrow (Y\left(j, x\right) = 0)) \Rightarrow (x = 0)))))))))))))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.ThetaCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

The fields A,D,B,C,B',C' are real linear maps, and Y is a sequence of real linear maps. The first and last fields identify the long-path endpoints; the four short-path equations, the two terminal equations and the bounded recurrence describe the operator. The separates field says that these coordinates determine a vector.

**Theorem 1.3 (Singular coordinate dimension bound).**

$$\forall E: \operatorname{Type}, [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\operatorname{Real}, E\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}, E\right)] \forall k: \operatorname{Nat}, \forall t: \operatorname{Real}, ((t = 1) \lor (t = -(1))) \Rightarrow (\operatorname{ThetaCoordinates}\left(E, k, t, 1\right) \to \left(\operatorname{Module}.\operatorname{finrank}\left(\operatorname{Real}, E\right) \le 2\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.model_laplacian_singular_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

At t=1 and t=−1, the recurrence is periodic. The terminal equations leave at most 2 independent real coordinates.

**Theorem 1.4 (Singular coordinate dimension bound).**

$$\forall E: \operatorname{Type}, [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\operatorname{Real}, E\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}, E\right)] \forall k: \operatorname{Nat}, \forall t: \operatorname{Real}, ((t = 1) \lor (t = -(1))) \Rightarrow (\operatorname{ThetaCoordinates}\left(E, k, t, -(1)\right) \to \left(\operatorname{Module}.\operatorname{finrank}\left(\operatorname{Real}, E\right) \le 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.model_signless_singular_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

At t=1 and t=−1, the recurrence is periodic. The terminal equations leave at most 1 independent real coordinates.

**Theorem 1.5 (Nonsingular coordinate dimension bound).**

$$\forall E: \operatorname{Type}, [\operatorname{AddCommGroup}\left(E\right)] [\operatorname{Module}\left(\operatorname{Real}, E\right)] [\operatorname{FiniteDimensional}\left(\operatorname{Real}, E\right)] \forall k: \operatorname{Nat}, \forall eQ: \operatorname{Rat}, \forall t: \operatorname{Real}, ((eQ = 1) \lor (eQ = -(1))) \Rightarrow ((t \ne 1) \Rightarrow ((t \ne -(1)) \Rightarrow (\operatorname{ThetaCoordinates}\left(E, k, t, (eQ: \operatorname{Real})\right) \to \left(\operatorname{Module}.\operatorname{finrank}\left(\operatorname{Real}, E\right) \le 1\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.model_nonsingular_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Monther Rashed Alfuraidan, Suliman Khan, Lorenzo Sauras-Altuzarra (2026). *Metric dimension and maximum eigenvalue multiplicity of graph Laplacians*. DOI: [10.48550/arXiv.2610.26875](https://doi.org/10.48550/arXiv.2610.26875). URL: <https://arxiv.org/abs/2610.26875v1>.

*Commentary.*

Away from t=±1, endpoints determine every coordinate. If two endpoint coordinates were independent, two consecutive continuant values would be forced. Their determinant identity and quadratic conjugation exclude that collision.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.ThetaCoordinates`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.bounded_continuant_endpoint`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.model_laplacian_singular_finrank`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.model_nonsingular_finrank`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TwinFreeThetaRecurrence.model_signless_singular_finrank`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace](CyclicTridiagonalTransferTrace.md)
