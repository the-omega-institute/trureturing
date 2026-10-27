# The quantum coherence fraction can increase under incoherent operations

## Abstract

A four-dimensional density matrix and two diagonal Kraus matrices give a strict increase of the quantum coherence fraction.

**Definition 1.1 (Incoherent operations in Kraus form).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(k: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone.IsIncoherentOperation}\left(k\right)\right) \Leftrightarrow \left(\left(\sum_{i: \operatorname{Fin}\left(m\right)} \left(\left(\operatorname{Matrix.conjTranspose}\left(k\left(i\right)\right)\right) \cdot \left(k\left(i\right)\right)\right) = \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right) \land \left(\forall \left(i: \operatorname{Fin}\left(m\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{Matrix.IsDiag}\left(\rho\right)\right) \Rightarrow \left(\operatorname{Matrix.IsDiag}\left(\left(\left(k\left(i\right)\right) \cdot \left(\rho\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(k\left(i\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.IsIncoherentOperation` (`✓ std3`).

*Citation.* Yao Yao; Dong Li; C. P. Sun (2019). *Quantum coherence fraction*. DOI: [10.1103/PhysRevA.100.032324](https://doi.org/10.1103/PhysRevA.100.032324). URL: <https://arxiv.org/abs/1906.09789v1>.

*Commentary.*

For natural dimensions d and m, a family of m complex d by d Kraus matrices is incoherent when its adjoint products sum to the identity and each individual Kraus sandwich preserves diagonality. The diagonal test ranges over all complex diagonal matrices. This expresses the source's condition on the individual branches without dividing by their traces, and includes branches of trace zero. The source states its normalized condition for diagonal density operators in Section II, CF.tex, lines 122–131.

**Definition 1.2 (The coherence fraction).**

$$\forall \left(d: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone.coherenceFraction}\left(\rho\right): \mathbb{R}\right) = \operatorname{sSup}\left(\{\left(r: \mathbb{R}\right) \mid \exists \left(z: \left(\operatorname{Fin}\left(d\right)\right) \to \left(\mathbb{C}\right)\right), \left(\left(\forall \left(j: \operatorname{Fin}\left(d\right)\right), \left(\left\lVert z\left(j\right) \right\rVert = \left(1: \mathbb{R}\right)\right)\right) \land \left(r = \frac{\operatorname{Complex.re}\left(\operatorname{dotProduct}\left(\operatorname{star}\left(z\right), \operatorname{Matrix.mulVec}\left(\rho, z\right)\right)\right)}{\left(\operatorname{Nat.cast}\left(d\right): \mathbb{R}\right)}\right)\right)\}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.coherenceFraction` (`✓ std3`).

*Citation.* Yao Yao; Dong Li; C. P. Sun (2019). *Quantum coherence fraction*. DOI: [10.1103/PhysRevA.100.032324](https://doi.org/10.1103/PhysRevA.100.032324). URL: <https://arxiv.org/abs/1906.09789v1>.

*Commentary.*

For every vector whose coordinates have norm one, divide the real quadratic form by the dimension and take the supremum of the resulting values. The dimension is explicitly cast from a natural number to a real number. For a density matrix in positive dimension, dividing such a vector by the square root of d gives a maximally coherent unit vector. Thus this is the overlap optimized in equation (QCF), CF.tex, lines 141–151. The real-supremum formula itself is defined for every natural dimension and every complex square matrix.

**Definition 1.3 (Monotonicity under incoherent operations).**

$$\left(\operatorname{D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone.claim}\right) \Leftrightarrow \left(\forall \left(d: \mathbb{N}\right), \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right), \left(\forall \left(k: \left(\operatorname{Fin}\left(m\right)\right) \to \left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone.IsIncoherentOperation}\left(k\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone.coherenceFraction}\left(\sum_{i: \operatorname{Fin}\left(m\right)} \left(\left(\left(k\left(i\right)\right) \cdot \left(\rho\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(k\left(i\right)\right)\right)\right)\right) \le \operatorname{D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone.coherenceFraction}\left(\rho\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yao Yao; Dong Li; C. P. Sun (2019). *Quantum coherence fraction*. DOI: [10.1103/PhysRevA.100.032324](https://doi.org/10.1103/PhysRevA.100.032324). URL: <https://arxiv.org/abs/1906.09789v1>.

*Commentary.*

For every natural dimension d, every natural number m of Kraus matrices, every density matrix and every incoherent Kraus family, the coherence fraction of the sum of all output branches is at most the input coherence fraction. IsDensity means positive semidefinite with trace one. The source conjectures failure of this monotonicity in Section V, CF.tex, lines 422–425; the proposition displayed here is the universal monotonicity assertion whose negation answers that question.

**Theorem 1.4 (A strict increase in dimension four).**

$$\neg \left(\operatorname{D5.S3.Quantum.Measurement.CoherenceFractionIncoherentNonmonotone.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.result` (`✓ std3`). ∎

*Resolves.* `Problems/yao-li-sun-2019-coherence-fraction-incoherent-nonmonotone` (refuted) by `D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yao-li-sun-2019-coherence-fraction-incoherent-nonmonotone","declaration_gid":"D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yao Yao; Dong Li; C. P. Sun (2019). *Quantum coherence fraction*. DOI: [10.1103/PhysRevA.100.032324](https://doi.org/10.1103/PhysRevA.100.032324). URL: <https://arxiv.org/abs/1906.09789v1>.

*Commentary.*

Use coordinates 0, 1, 2, 3 and write i for the imaginary unit. Let P be 1/2163 times the matrix with rows (1425, −300−300i, 615−240i, 615+240i), (−300+300i, 1075, 680+180i, −180−680i), (615+240i, 680−180i, 913, 225−400i), and (615−240i, −180+680i, 225+400i, 913). Entrywise rational arithmetic gives P† = P, P² = P and tr(P) = 2. A self-adjoint idempotent is positive semidefinite. Therefore R = P/2 is positive semidefinite and has trace one, so R is a density matrix.

Choose K₀ = diag(1, 0, 3/5, 3/5) and K₁ = diag(0, 1, 4/5, −4i/5). Their adjoint products sum to the identity: the last two diagonal entries are 9/25 + 16/25 = 1. Each Kⱼ is diagonal, so sandwiching a diagonal matrix by Kⱼ and its adjoint again gives a diagonal matrix. Consequently these two matrices define an incoherent operation Φ(X) = K₀XK₀† + K₁XK₁†.

For every complex four by four matrix A, the set of values in its coherence-fraction supremum is bounded above. Indeed, for a vector z with unit-modulus coordinates, expanding the dot product and applying the triangle inequality gives |z†Az| ≤ ∑ⱼ∑ₗ |Aⱼₗ|. The real part is at most the modulus, and division by four preserves an upper bound by this nonnegative sum.

Write a = (1, 0, 3/5, 3/5), b = (0, 1, 4/5, −4i/5), and Q = Φ(R). Diagonal multiplication gives Qⱼₗ = Pⱼₗ(aⱼ conjugate(aₗ) + bⱼ conjugate(bₗ))/2. Substituting the entries above and summing them gives Re(𝟙†Q𝟙)/4 = 1/2, where 𝟙 has all four coordinates equal to one.

To obtain a uniform bound for the input, first let u and w be complex numbers with |u| ≤ 7/5 and |w| = 1. The reverse triangle inequality gives ||u| − 1| ≤ |w − u|. Since (|u| + 1)² ≤ 144/25, factoring the difference of squares yields (|u|² − 1)² ≤ (144/25)|w − u|².

For complex numbers x, y, w, t of modulus one, set u = (3x + 4y)/5 and v = (3x + 4iy)/5. Both |u| and |v| are at most 7/5. Expanding real and imaginary parts gives |u|² − 1 = (24/25)(Re(x)Re(y) + Im(x)Im(y)) and |v|² − 1 = (24/25)(Im(x)Re(y) − Re(x)Im(y)). The sum of their squares is 576/625 because |x|²|y|² = 1. Applying the preceding estimate to (u,w) and (v,t) therefore gives 4/25 ≤ |w − (3x + 4y)/5|² + |t − (3x + 4iy)/5|².

For arbitrary complex a, b, c, d, the triangle inequality bounds |c − (3a + 4b)/5| by |c| + (3|a| + 4|b|)/5. Cauchy–Schwarz with coefficients (1, 3/5, 4/5), whose squared norm is two, bounds its square by 2(|a|² + |b|² + |c|²). The same argument bounds |d − (3a + 4ib)/5|² by 2(|a|² + |b|² + |d|²). Adding and using nonnegativity gives an upper bound 4(|a|² + |b|² + |c|² + |d|²) for the sum of the two squared residuals.

For any vector z, expand the squared Euclidean norm of z − Pz. The identities P† = P and P² = P imply (Pz)†Pz = z†Pz. Consequently Re(z†Pz) + ∑ⱼ |zⱼ − (Pz)ⱼ|² = ∑ⱼ |zⱼ|². Direct multiplication by the displayed matrix also gives (Pz)₂ = (3(Pz)₀ + 4(Pz)₁)/5 and (Pz)₃ = (3(Pz)₀ + 4i(Pz)₁)/5. Thus the linear functionals F₁(z) = z₂ − (3z₀ + 4z₁)/5 and F₂(z) = z₃ − (3z₀ + 4iz₁)/5 vanish on Pz. By linearity F₁(z) = F₁(z − Pz) and F₂(z) = F₂(z − Pz).

Now assume every coordinate of z has modulus one and put e = z − Pz. The four-scalar lower bound and the residual upper bound give 4/25 ≤ |F₁(z)|² + |F₂(z)|² = |F₁(e)|² + |F₂(e)|² ≤ 4∑ⱼ |eⱼ|². Hence ∑ⱼ |eⱼ|² ≥ 1/25. The projection identity and ∑ⱼ |zⱼ|² = 4 give Re(z†Pz) ≤ 4 − 1/25. Since R = P/2, every value Re(z†Rz)/4 is at most 1/2 − 1/200.

The all-ones vector is admissible in the bounded output supremum, so coherenceFraction(Q) ≥ 1/2. The input set is nonempty, again using the all-ones vector, and every one of its values satisfies the preceding uniform estimate. Taking its supremum gives coherenceFraction(R) ≤ 1/2 − 1/200. Applying universal monotonicity at d = 4, m = 2, the density matrix R and the two incoherent Kraus matrices would give coherenceFraction(Q) ≤ coherenceFraction(R). This contradicts coherenceFraction(R) ≤ 1/2 − 1/200 < 1/2 ≤ coherenceFraction(Q).

## References

- Truth anchor: `D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.IsIncoherentOperation`
- Truth anchor: `D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.coherenceFraction`
- Truth anchor: `D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Information/SLDSpectralEnergy.md)
