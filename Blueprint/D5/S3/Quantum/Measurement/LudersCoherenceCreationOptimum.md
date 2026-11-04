# The optimal coherence created by qubit measurements

## Abstract

Every qubit density matrix has an attained maximum of output coherence under finite nonselective measurements, with exact zero and maximal gain criteria.

**Definition 1.1 (The nonselective Luders action).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(e: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum.luders}\left(e, \rho\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right) = \operatorname{D5.S3.Observer.Conditioning.unreadState}\left(\lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(\operatorname{CFC.sqrt}\left(e\left(i\right)\right)\right), \rho\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.luders` (`✓ std3`).

*Citation.* Sanuja D. Mohanty; Gautam Sharma; Sk Sazim; Biswajit Pradhan; Arun K. Pati (2022). *Creation of quantum coherence with general measurement processes*. DOI: [10.1007/s11128-021-03394-5](https://doi.org/10.1007/s11128-021-03394-5). URL: <https://arxiv.org/abs/2004.10875v2>.

*Commentary.*

For a family e of n complex two by two matrices, apply the square-root functional calculus to each member and sum its sandwiches with the input matrix. The function unreadState denotes precisely this sum. For positive semidefinite effects these are their positive square roots, giving the nonselective measurement rule in Section 2, coh-measure.tex, lines 127–130. The displayed definition itself accepts every family and every input matrix; positivity and completeness are imposed when discussing measurements.

**Definition 1.2 (The Bloch length).**

$$\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum.blochNorm}\left(\rho\right): \mathbb{R}\right) = \operatorname{Real.sqrt}\left(\left(\operatorname{Complex.re}\left(\rho\left(\left(0: \operatorname{Fin}\left(2\right)\right), \left(0: \operatorname{Fin}\left(2\right)\right)\right) - \rho\left(\left(1: \operatorname{Fin}\left(2\right)\right), \left(1: \operatorname{Fin}\left(2\right)\right)\right)\right)\right)^{\left(2: \mathbb{N}\right)} + \left(\left(4: \mathbb{R}\right)\right) \cdot \left(\left(\left\lVert \rho\left(\left(0: \operatorname{Fin}\left(2\right)\right), \left(1: \operatorname{Fin}\left(2\right)\right)\right) \right\rVert\right)^{\left(2: \mathbb{N}\right)}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.blochNorm` (`✓ std3`).

*Citation.* Sanuja D. Mohanty; Gautam Sharma; Sk Sazim; Biswajit Pradhan; Arun K. Pati (2022). *Creation of quantum coherence with general measurement processes*. DOI: [10.1007/s11128-021-03394-5](https://doi.org/10.1007/s11128-021-03394-5). URL: <https://arxiv.org/abs/2004.10875v2>.

*Commentary.*

For a Hermitian qubit matrix, the squared Bloch length is the squared real diagonal difference plus four times the squared modulus of the upper off-diagonal entry. Taking its nonnegative square root gives the length used in the source's Bloch representation and coherence maximum, coh-measure.tex, lines 212 and 228–235. The same expression defines a real number for every complex two by two matrix, without a density hypothesis.

**Theorem 1.3 (The attained maximum and both extremal gain criteria).**

$$\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)\right) \Rightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\left(\left(2: \mathbb{N}\right) \le n\right) \Rightarrow \left(\left(\operatorname{IsGreatest}\left(\{c: \mathbb{R} \mid \exists \left(e: \operatorname{Fin}\left(n\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM}\left(e\right)\right) \land \left(c = \operatorname{D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence}\left(\operatorname{D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum.luders}\left(e, \rho\right)\right)\right)\right)\}, \frac{\operatorname{D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence}\left(\rho\right) + \operatorname{D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum.blochNorm}\left(\rho\right)}{\left(2: \mathbb{R}\right)}\right)\right) \land \left(\left(\left(\frac{\operatorname{D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence}\left(\rho\right) + \operatorname{D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum.blochNorm}\left(\rho\right)}{\left(2: \mathbb{R}\right)} - \operatorname{D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence}\left(\rho\right) = \left(0: \mathbb{R}\right)\right) \Leftrightarrow \left(\rho\left(\left(0: \operatorname{Fin}\left(2\right)\right), \left(0: \operatorname{Fin}\left(2\right)\right)\right) = \rho\left(\left(1: \operatorname{Fin}\left(2\right)\right), \left(1: \operatorname{Fin}\left(2\right)\right)\right)\right)\right) \land \left(\left(\frac{\operatorname{D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence}\left(\rho\right) + \operatorname{D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum.blochNorm}\left(\rho\right)}{\left(2: \mathbb{R}\right)} - \operatorname{D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence}\left(\rho\right) \le \frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)}\right) \land \left(\left(\frac{\operatorname{D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence}\left(\rho\right) + \operatorname{D5.S3.Quantum.Measurement.LudersCoherenceCreationOptimum.blochNorm}\left(\rho\right)}{\left(2: \mathbb{R}\right)} - \operatorname{D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence}\left(\rho\right) = \frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)}\right) \Leftrightarrow \left(\left(\rho = \operatorname{Matrix.diagonal}\left(![\left(1: \mathbb{C}\right), \left(0: \mathbb{C}\right)]\right)\right) \lor \left(\rho = \operatorname{Matrix.diagonal}\left(![\left(0: \mathbb{C}\right), \left(1: \mathbb{C}\right)]\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/mohanty-sharma-sazim-pradhan-pati-2022-luders-coherence-optimum` (proved) by `D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mohanty-sharma-sazim-pradhan-pati-2022-luders-coherence-optimum","declaration_gid":"D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sanuja D. Mohanty; Gautam Sharma; Sk Sazim; Biswajit Pradhan; Arun K. Pati (2022). *Creation of quantum coherence with general measurement processes*. DOI: [10.1007/s11128-021-03394-5](https://doi.org/10.1007/s11128-021-03394-5). URL: <https://arxiv.org/abs/2004.10875v2>.

*Commentary.*

IsDensity means positive semidefinite with trace one; IsPOVM means that every effect is positive semidefinite and their sum is the identity. The coherence l1Coherence is the sum of the moduli of all off-diagonal entries, as in coh-measure.tex, line 109. The maximum ranges over every family indexed by Fin n, including zero effects. The four conclusions give the greatest output coherence, the exact condition for zero optimal gain, the upper bound one half for optimal gain, and its equality cases. The source gives the maximum for a restricted one-parameter family at lines 230–231; the general two-outcome question is stated at line 298 and the finite-outcome question at line 505.

First, Hermitian matrices have real diagonal entries and conjugate off-diagonal entries, so their coherence is twice the modulus of the upper off-diagonal entry. Put c = ρ₀₁, r = Re(ρ₀₀ − ρ₁₁), s = 2|c| and R = √(r² + s²). For an arbitrary measurement, write its positive square roots as mᵢ = ((pᵢ, zᵢ), (conjugate(zᵢ), qᵢ)), with real pᵢ and qᵢ. Define vᵢ = (pᵢ − qᵢ)/2 and kᵢ = pᵢqᵢ − |zᵢ|². Nonnegativity of the determinants gives kᵢ ≥ 0. Completeness gives ∑ᵢ mᵢ² = I; its trace yields ∑ᵢ(kᵢ + 2(|zᵢ|² + vᵢ²)) = 1, and its upper off-diagonal entry gives ∑ᵢ((pᵢ + qᵢ)/2)zᵢ = 0. Expanding the sandwiches and using trace one therefore shows that the output is Hermitian and its upper off-diagonal entry is ∑ᵢ[kᵢc + (2Re(conjugate(zᵢ)c) + vᵢr)zᵢ].

For real s, r, t and v, the larger eigenvalue of the real symmetric matrix with diagonal (s, 0) and off-diagonal |r|/2 is (s + √(r² + s²))/2. Its quadratic-form bound gives st² + |r|tv ≤ ((s + √(r² + s²))/2)(t² + v²). The inequalities |Re(conjugate(z)c)| ≤ |z||c| and the triangle inequality, followed by this bound with t = |z| and v replaced by |v|, imply 2|(2Re(conjugate(z)c) + vr)z| ≤ (|z|² + v²)(2|c| + √(r² + 4|c|²)).

The Bloch length satisfies R² = r² + s², with 0 ≤ s ≤ R. Its equality with the Euclidean norm of the Bloch vector follows by expanding the three real coordinates. Positive semidefiniteness bounds this norm by the real trace, hence R ≤ 1 for a density matrix. Set l = (s + R)/2, so s ≤ l. For each term of the output entry, the triangle inequality, kᵢ ≥ 0 and the preceding quadratic bound give 2|kᵢc + (2Re(conjugate(zᵢ)c) + vᵢr)zᵢ| ≤ (kᵢ + 2(|zᵢ|² + vᵢ²))l. Summing, applying the triangle inequality to the sum, and using that the coefficients sum to one proves that every output coherence is at most l.

To attain this bound, first choose a complex phase a with |a| = 1 and conjugate(a)c = |c|. Seek a complex z and real v with |z|² + v² = 1 and |(2Re(conjugate(z)c) + vr)z| = l. If R = 0, then c = 0 and r = 0, and z = 1, v = 0 suffice. Otherwise R > 0 and l > 0. Put t = √(l/R), v = rt/(2l), and z = ta. The identity 4l(l − s) = r² gives t² = l/R and v² = (l − s)/R, so |z|² + v² = 1. The phase choice gives Re(conjugate(z)c) = t|c|, whence 2Re(conjugate(z)c) + vr = Rt and |(2Re(conjugate(z)c) + vr)z| = Rt² = l.

Form the matrix p with rows ((1 + v)/2, z/2) and (conjugate(z)/2, (1 − v)/2). The unit-length equation makes p self-adjoint and idempotent. Thus p and q = I − p are positive semidefinite complementary projections. For n ≥ 2, write n = m + 2 and take the effects p, q followed by m zero matrices. They form a POVM. The positive square roots of these projections are themselves, and the square root of zero is zero, so the output is pρp + qρq. Expanding its upper off-diagonal entry gives (2Re(conjugate(z)c) + vr)z/2. The output is Hermitian, so its coherence is |(2Re(conjugate(z)c) + vr)z| = l. This supplies an attaining measurement for every allowed n.

The optimal gain is l − s = (R − s)/2. It vanishes exactly when R = s. The squared-radius identity then forces r = 0; conversely r = 0 gives R = s by nonnegativity. Since both diagonal entries of ρ are real, r = 0 is equivalent to ρ₀₀ = ρ₁₁.

Finally, R ≤ 1 and s ≥ 0 give l − s ≤ 1/2. Equality forces s = 0 and R = 1. Thus c = 0, its conjugate lower entry also vanishes, and r² = 1. Together with the real trace equation ρ₀₀ + ρ₁₁ = 1, the alternatives r = 1 and r = −1 give exactly diag(1, 0) and diag(0, 1). Conversely each of these matrices has coherence zero and Bloch length one, so each attains gain one half. The attaining measurement puts l in the set of output coherences, and the bound for every measurement makes it the greatest element of that set.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.blochNorm`
- Truth anchor: `D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.luders`
- Truth anchor: `D5/S3/Quantum/Measurement/LudersCoherenceCreationOptimum.result`
- Dependency: [D5/S3/Divergence/CoherenceL1RelativeEntropyBound](../../Divergence/CoherenceL1RelativeEntropyBound.md)
- Dependency: [D5/S3/Quantum/Information/ActualQubitChordObstruction](../Information/ActualQubitChordObstruction.md)
- Dependency: [D5/S3/Quantum/Measurement/OccupationPartialTransposeSpectral](OccupationPartialTransposeSpectral.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation](../QuantumChannels/ConcealmentKernelNecessityRefutation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction](../QuantumChannels/HiaiRuskaiRiemannianContraction.md)
