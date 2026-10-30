# Partial tightness of the multipartite entangled-measurement bound

## Abstract

Computational and Fourier bases in disjoint sectors attain every multipartite partial bound with a multiple of d separable outcomes.

**Definition 1.1 (Joint coordinates).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right) = \left((\operatorname{Fin}\left(n\right)) \to (\operatorname{ZMod}\left(d\right))\right)))$$

*Formalization.* `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.jointIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli, Alastair A. Abbott, Marc-Olivier Renou, Nicolas Gisin and Nicolas Brunner (2018). *Semi-device-independent characterization of multipartite entanglement of states and measurements*. DOI: [10.1103/PhysRevA.98.052333](https://doi.org/10.1103/PhysRevA.98.052333). URL: <https://arxiv.org/abs/1805.00377v1>.

*Commentary.*

A joint coordinate is a function from the n party indices to the residues modulo d. When n is nonzero, the first party has index zero. This type describes inputs, outcomes and computational basis labels; its definition allows every natural n and d.

**Definition 1.2 (The sum-and-difference winning string).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), ([\operatorname{NeZero}\left(n\right)], (\forall (x: \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)), (\forall (y: \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)), (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.winningOutcome}\left(x, y\right) = \lambda (k: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{ite}\left(k = (0: \operatorname{Fin}\left(n\right)), \sum_{i: \operatorname{Fin}\left(n\right)} (x\left(i\right)), (y\left(k\right)) - (y\left((0: \operatorname{Fin}\left(n\right))\right))\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.winningOutcome` (`✓ std3`).

*Citation.* Armin Tavakoli, Alastair A. Abbott, Marc-Olivier Renou, Nicolas Gisin and Nicolas Brunner (2018). *Semi-device-independent characterization of multipartite entanglement of states and measurements*. DOI: [10.1103/PhysRevA.98.052333](https://doi.org/10.1103/PhysRevA.98.052333). URL: <https://arxiv.org/abs/1805.00377v1>.

*Commentary.*

The coordinate at party zero is the sum of the x inputs; each other coordinate is its y input minus the y input at party zero. All these operations take place in ZMod d. This is the winning condition in SDI_manuscript.tex, lines 150–155, with party indices starting at zero. Only n must be nonzero for this definition.

**Definition 1.3 (The average winning probability).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), ([\operatorname{NeZero}\left(n\right)], [\operatorname{NeZero}\left(d\right)], [\operatorname{Fintype}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)\right)], [\operatorname{DecidableEq}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)\right)], (\forall (\rho: \operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \mathbb{C}\right)), (\forall (u: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{ZMod}\left(d\right)) \to ((\operatorname{ZMod}\left(d\right)) \to (\operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right))))), (\forall (p: (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)) \to (\operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \mathbb{C}\right))), (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.score}\left(\rho, u, p\right) = (\operatorname{Inv.inv}\left((\operatorname{Nat.cast}\left(d\right): \mathbb{R})^{((2: \mathbb{N})) \cdot (n)}\right)) \cdot (\sum_{x: \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)} (\sum_{y: \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)} (\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((((\operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(d\right)\right), \lambda (k: \operatorname{Fin}\left(n\right)) \mapsto (u\left(k, x\left(k\right), y\left(k\right)\right))\right)) \cdot (\rho)) \cdot (\operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap}\left(\operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(d\right)\right), \lambda (k: \operatorname{Fin}\left(n\right)) \mapsto (u\left(k, x\left(k\right), y\left(k\right)\right))\right)\right))) \cdot (p\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.winningOutcome}\left(x, y\right)\right))\right)\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.score` (`✓ std3`).

*Citation.* Armin Tavakoli, Alastair A. Abbott, Marc-Olivier Renou, Nicolas Gisin and Nicolas Brunner (2018). *Semi-device-independent characterization of multipartite entanglement of states and measurements*. DOI: [10.1103/PhysRevA.98.052333](https://doi.org/10.1103/PhysRevA.98.052333). URL: <https://arxiv.org/abs/1805.00377v1>.

*Commentary.*

For each pair of input strings, form the tensor product of the chosen local matrices, conjugate ρ by it, and take the real part of the trace against the winning measurement operator. Averaging uniformly over the d to the power 2n input pairs gives the score. The product map is the matrix tensor product on joint coordinates. This specializes the transformations of SDI_manuscript.tex, lines 143–160, to conjugation by local matrices. The definition itself imposes no positivity, normalization or unitarity conditions; those enter the existence statement.

**Definition 1.4 (Finite sums of positive product operators).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (a: \operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.IsFullySeparable}\left(a\right)) \Leftrightarrow (\exists (k: \mathbb{N}), (\exists (s: (\operatorname{Fin}\left(k\right)) \to ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right)))), ((\forall (j: \operatorname{Fin}\left(k\right)), (\forall (v: \operatorname{Fin}\left(n\right)), (\operatorname{Matrix.PosSemidef}\left(s\left(j, v\right)\right)))) \land (\forall (i: \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)), (\forall (j: \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)), (a\left(i, j\right) = \sum_{q: \operatorname{Fin}\left(k\right)} (\prod_{v: \operatorname{Fin}\left(n\right)} (s\left(q, v, i\left(v\right), j\left(v\right)\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.IsFullySeparable` (`✓ std3`).

*Citation.* Armin Tavakoli, Alastair A. Abbott, Marc-Olivier Renou, Nicolas Gisin and Nicolas Brunner (2018). *Semi-device-independent characterization of multipartite entanglement of states and measurements*. DOI: [10.1103/PhysRevA.98.052333](https://doi.org/10.1103/PhysRevA.98.052333). URL: <https://arxiv.org/abs/1805.00377v1>.

*Commentary.*

An operator is fully separable when its entries are a finite sum of products of entries of positive semidefinite local matrices. The number k of summands is arbitrary and may be zero. With at least one party, nonnegative scalar weights can be absorbed into the local factors. The definition also allows zero parties, in which case each empty product equals one. This is the fully separable decomposition of SDI_manuscript.tex, line 258.

**Definition 1.5 (A complete family of orthogonal projections).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), ([\operatorname{NeZero}\left(n\right)], [\operatorname{NeZero}\left(d\right)], [\operatorname{Fintype}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)\right)], [\operatorname{DecidableEq}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)\right)], (\forall (p: (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)) \to (\operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.IsProjectiveMeasurement}\left(p\right)) \Leftrightarrow ((\forall (b: \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)), (\operatorname{IsStarProjection}\left(p\left(b\right)\right))) \land (\sum_{b: \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)} (p\left(b\right)) = (1: \operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \mathbb{C}\right))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.IsProjectiveMeasurement` (`✓ std3`).

*Citation.* Armin Tavakoli, Alastair A. Abbott, Marc-Olivier Renou, Nicolas Gisin and Nicolas Brunner (2018). *Semi-device-independent characterization of multipartite entanglement of states and measurements*. DOI: [10.1103/PhysRevA.98.052333](https://doi.org/10.1103/PhysRevA.98.052333). URL: <https://arxiv.org/abs/1805.00377v1>.

*Commentary.*

Every outcome operator is a self-adjoint idempotent, and their sum is the identity matrix. The predicate does not require rank one. It expresses the projective measurements used in SDI_manuscript.tex, lines 193–195 and 478–490.

**Definition 1.6 (Multipartite partial tightness).**

$$(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (m: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (((2: \mathbb{N}) \le d) \to ((m \le d^{(n) - ((1: \mathbb{N}))}) \to (\exists (\rho: \operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \mathbb{C}\right)), (\exists (u: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{ZMod}\left(d\right)) \to ((\operatorname{ZMod}\left(d\right)) \to (\operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right))))), (\exists (p: (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)) \to (\operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)) \land ((\forall (k: \operatorname{Fin}\left(n\right)), (\forall (x: \operatorname{ZMod}\left(d\right)), (\forall (y: \operatorname{ZMod}\left(d\right)), (u\left(k, x, y\right) \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{ZMod}\left(d\right), \mathbb{C}\right))))) \land ((\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.IsProjectiveMeasurement}\left(p\right)) \land ((\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (b: \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)) \mapsto (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.IsFullySeparable}\left(p\left(b\right)\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)\right))\right)\right) = (d) \cdot (m)) \land (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.score}\left(\rho, u, p\right) = \frac{(((\operatorname{Nat.cast}\left(d\right): \mathbb{R})^{n}) - (((\operatorname{Nat.cast}\left(d\right): \mathbb{R})) \cdot ((\operatorname{Nat.cast}\left(m\right): \mathbb{R})))) + ((\operatorname{Nat.cast}\left(m\right): \mathbb{R}))}{(\operatorname{Nat.cast}\left(d\right): \mathbb{R})^{n}}))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli, Alastair A. Abbott, Marc-Olivier Renou, Nicolas Gisin and Nicolas Brunner (2018). *Semi-device-independent characterization of multipartite entanglement of states and measurements*. DOI: [10.1103/PhysRevA.98.052333](https://doi.org/10.1103/PhysRevA.98.052333). URL: <https://arxiv.org/abs/1805.00377v1>.

*Commentary.*

For every n and d at least two and every natural m at most d^(n − 1), there are a density matrix, local unitary encodings, and a projective measurement with exactly dm fully separable outcome operators and the displayed score. The lower bounds on n and d provide the nonzero instances in the predicates and score. All casts in the score equality are from natural numbers to real numbers. This is the affirmative reading of the question at SDI_manuscript.tex, line 497, extending the bipartite partial tightness at lines 474–496. At k = dm the score equals the right side of Result 2, lines 265–272. The statement concerns the multiples of d and does not assert attainment at other numbers of separable outcomes.

**Theorem 1.7 (Attainment by a choice of basis in each sector).**

$$\forall (n: \mathbb{N}), (\forall (d: \mathbb{N}), (\forall (m: \mathbb{N}), (((2: \mathbb{N}) \le n) \to (((2: \mathbb{N}) \le d) \to ((m \le d^{(n) - ((1: \mathbb{N}))}) \to (\exists (\rho: \operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \mathbb{C}\right)), (\exists (u: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{ZMod}\left(d\right)) \to ((\operatorname{ZMod}\left(d\right)) \to (\operatorname{Matrix}\left(\operatorname{ZMod}\left(d\right), \operatorname{ZMod}\left(d\right), \mathbb{C}\right))))), (\exists (p: (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)) \to (\operatorname{Matrix}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right), \mathbb{C}\right))), ((\operatorname{D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity}\left(\rho\right)) \land ((\forall (k: \operatorname{Fin}\left(n\right)), (\forall (x: \operatorname{ZMod}\left(d\right)), (\forall (y: \operatorname{ZMod}\left(d\right)), (u\left(k, x, y\right) \in \operatorname{Matrix.unitaryGroup}\left(\operatorname{ZMod}\left(d\right), \mathbb{C}\right))))) \land ((\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.IsProjectiveMeasurement}\left(p\right)) \land ((\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (b: \operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)) \mapsto (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.IsFullySeparable}\left(p\left(b\right)\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.jointIndex}\left(n, d\right)\right))\right)\right) = (d) \cdot (m)) \land (\operatorname{D5.S3.Quantum.Measurement.MultipartiteEntangledMeasurementPartialTightness.score}\left(\rho, u, p\right) = \frac{(((\operatorname{Nat.cast}\left(d\right): \mathbb{R})^{n}) - (((\operatorname{Nat.cast}\left(d\right): \mathbb{R})) \cdot ((\operatorname{Nat.cast}\left(m\right): \mathbb{R})))) + ((\operatorname{Nat.cast}\left(m\right): \mathbb{R}))}{(\operatorname{Nat.cast}\left(d\right): \mathbb{R})^{n}})))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.result` (`✓ std3`). ∎

*Resolves.* `Problems/tavakoli-abbott-renou-gisin-brunner-2018-multipartite-partial-tightness` (proved) by `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"tavakoli-abbott-renou-gisin-brunner-2018-multipartite-partial-tightness","declaration_gid":"D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Armin Tavakoli, Alastair A. Abbott, Marc-Olivier Renou, Nicolas Gisin and Nicolas Brunner (2018). *Semi-device-independent characterization of multipartite entanglement of states and measurements*. DOI: [10.1103/PhysRevA.98.052333](https://doi.org/10.1103/PhysRevA.98.052333). URL: <https://arxiv.org/abs/1805.00377v1>.

*Commentary.*

For a joint label r with r(0) = 0, write e(t,r) for the computational vector at the string whose kth coordinate is t + r(k). Every string i has the unique representation t = i(0), r(k) = i(k) − i(0). Thus the sectors indexed by r are disjoint and exhaust the computational basis. Within a sector let g(a,r) have coefficient d⁻¹ᐟ² χ(at) at e(t,r), and zero elsewhere, where χ is the standard additive character of ZMod d. For an outcome b set a = b(0) and r equal to b with its zeroth coordinate replaced by zero. Given a set R of sectors, choose e(a,r) when r belongs to R and g(a,r) otherwise; the outcome operator is the projector onto that vector.

Each computational projector is the tensor product of its one-coordinate positive projectors, so it is fully separable. For each party use the clock power Z to the input x times the shift power X to the input y, using the natural representatives of the residues as exponents. The clock and shift matrices are unitary; closure under powers and products makes every local encoding unitary.

The Fourier vectors in distinct sectors have disjoint support. Within one sector, their inner product is d⁻¹ times the sum of χ(t(c − a)) over t. Character orthogonality makes this one when a = c and zero otherwise. In particular g(0,0) is normalized, and its outer product is a positive semidefinite density matrix of trace one, the generalized GHZ state. Computational vectors in selected sectors are mutually orthonormal and orthogonal to Fourier vectors in unselected sectors. The selected vectors therefore form an orthonormal family indexed by all joint outcomes. If W has these vectors as columns, W†W = I. Since W is square, WW† = I as well. Each rank-one operator is a self-adjoint idempotent, and their sum is WW†, proving completeness of the measurement.

To identify every separable outcome, consider a normalized vector v whose rank-one projector is a sum of positive product matrices Aⱼ. Positivity of these product matrices follows by successive Hadamard products of pulled-back local positive matrices. Reindex the joint basis by Fintype.equivFin and apply summand_kernel from AbsolutelyEntangledAllPartitions with all weights equal to one: every Aⱼ annihilates the orthogonal complement of v. Choose a coordinate i with v(i) nonzero and a summand with Aⱼ(i,i) nonzero. The same owner's supported_column gives column i as z v; transporting back to the joint basis preserves this identity, and the nonzero diagonal entry forces z to be nonzero. That column is a product of local columns; absorbing z⁻¹ into the factor at party zero expresses v itself as a product vector.

A Fourier vector g(a,r) cannot be a product vector. Let i and j be the sector strings at t = 0 and t = 1, and let q and p be obtained by swapping their zeroth coordinates. Both original amplitudes are nonzero. Because n and d are at least two, q lies outside the sector and has amplitude zero. A product vector would satisfy v(i)v(j) = v(q)v(p), contradicting these amplitudes. The rank-one argument therefore excludes full separability for every unselected Fourier projector. Consequently an outcome is fully separable exactly when its sector belongs to R.

The map sending an outcome b to its zeroth coordinate together with b with that coordinate replaced by zero is a bijection between the selected outcomes and ZMod d times R. There are therefore d times the cardinality of R fully separable operators. The sector labels with zeroth coordinate zero are in bijection with functions from the remaining n − 1 party indices to ZMod d, so there are d^(n − 1) such labels. The bound on m permits a subset R of cardinality m.

The local encoding has entry χ(xi) when j = i − y and zero otherwise. Multiplying these entries across parties and acting on g(0,0) gives a scalar of modulus one times g(a,r), where a is the sum of the x inputs and r(k) = y(k) − y(0). The scalar is χ(∑ₖ x(k)(y(k) − y(0))). The winning outcome has precisely this a and r. Conjugation removes the scalar, and the trace against the winning projector is the squared overlap with its selected vector. Fourier orthonormality gives probability one outside R; the computational amplitude has squared modulus 1/d inside R.

Reindex y by its zeroth coordinate and its sector label. Exactly d times the cardinality of R of the dⁿ strings have sector in R. The sum of winning probabilities over y is d|R|/d + dⁿ − d|R|, independently of x. Summing over the dⁿ choices of x and dividing by d²ⁿ gives (dⁿ − d|R| + |R|)/dⁿ. With |R| = m, the GHZ density matrix, the clock-shift encodings and the selected projectors satisfy all five conclusions.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.IsFullySeparable`
- Truth anchor: `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.IsProjectiveMeasurement`
- Truth anchor: `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.jointIndex`
- Truth anchor: `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.result`
- Truth anchor: `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.score`
- Truth anchor: `D5/S3/Quantum/Measurement/MultipartiteEntangledMeasurementPartialTightness.winningOutcome`
- Dependency: [D5/S3/Observer/MatrixUnitCertificate](../../Observer/MatrixUnitCertificate.md)
- Dependency: [D5/S3/Quantum/Entanglement/Witness/AbsolutelyEntangledAllPartitions](../Entanglement/Witness/AbsolutelyEntangledAllPartitions.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../Information/SLDSpectralEnergy.md)
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](../Information/SeparableStateLocalUnitaryStabilizerObstruction.md)
