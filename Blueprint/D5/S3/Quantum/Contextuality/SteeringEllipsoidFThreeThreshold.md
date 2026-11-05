# The sharp centre threshold for three-setting steering

## Abstract

The three-setting steering value is at most max(sqrt(3(1 - c)), 1), where c is Bob's steering-ellipsoid centre length. Every centre length below two thirds is attained by a state violating the inequality.

**Definition 1.1 (Bob's steering-ellipsoid centre).**

$$\forall (\rho: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{CHSHWitness}.\operatorname{TwoQubitMatrix}), ((\operatorname{centreB}\left(\rho\right): (\operatorname{Fin}\left(3\right)) \to (\mathbb{R})) = \operatorname{ite}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{blochA}\left(\rho\right)\right) = 1, \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{blochB}\left(\rho\right), \lambda (j: \operatorname{Fin}\left(3\right)) \mapsto (\frac{(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{blochB}\left(\rho\right)\left(j\right)) - (\sum_{(i: \operatorname{Fin}\left(3\right))} ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{corr}\left(\rho, i, j\right)) \cdot (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{blochA}\left(\rho\right)\left(i\right))))}{(1) - ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{blochA}\left(\rho\right)\right))^{2})})\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.centreB` (`✓ std3`).

*Citation.* Andrés F. Ducuara, Cristian E. Susa, Paul Skrzypczyk (2024). *Locally inaccessible hidden quantum correlations*. DOI: [10.1103/PhysRevA.110.022435](https://doi.org/10.1103/PhysRevA.110.022435). URL: <https://arxiv.org/abs/2406.03945v1>.

*Commentary.*

Equation (QSEcentre), QC_LI.tex lines 245-261, gives Bob's centre as (b - transpose(T)a)/(1 - |a| squared). Here blochA and blochB are the two Bloch vectors, corr is the real correlation matrix and vlen is Euclidean length. When Alice's Bloch vector has length one, the definition assigns Bob's Bloch vector itself, the centre of the single-point ellipsoid. The definition applies to every complex two-qubit matrix.

**Definition 1.2 (Three-setting steering values).**

$$\forall (\rho: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{CHSHWitness}.\operatorname{TwoQubitMatrix}), ((\operatorname{fThreeValues}\left(\rho\right): \operatorname{Set}\left(\mathbb{R}\right)) = \{(r: \mathbb{R}) \mid (\exists (\alpha: (\operatorname{Fin}\left(3\right)) \to ((\operatorname{Fin}\left(3\right)) \to (\mathbb{R}))), (\exists (\beta: (\operatorname{Fin}\left(3\right)) \to ((\operatorname{Fin}\left(3\right)) \to (\mathbb{R}))), ((\forall (i: \operatorname{Fin}\left(3\right)), (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\alpha\left(i\right)\right) = 1)) \land ((\forall (i: \operatorname{Fin}\left(3\right)), (\forall (j: \operatorname{Fin}\left(3\right)), (\operatorname{dotProduct}\left(\beta\left(i\right), \beta\left(j\right)\right) = \operatorname{ite}\left(i = j, (1: \mathbb{R}), (0: \mathbb{R})\right)))) \land (r = \frac{\left\lVert \sum_{(i: \operatorname{Fin}\left(3\right))} (\operatorname{Matrix}.\operatorname{trace}\left((\rho) \cdot (\operatorname{Matrix}.\operatorname{kronecker}\left(\operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{PauliThreeWeightBayesianInverseUniqueness}.\operatorname{spin}\left(\alpha\left(i\right)\right), \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumChannels}.\operatorname{PauliThreeWeightBayesianInverseUniqueness}.\operatorname{spin}\left(\beta\left(i\right)\right)\right))\right)) \right\rVert}{\operatorname{Real}.\operatorname{sqrt}\left(3\right)})))))\})$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.fThreeValues` (`✓ std3`).

*Citation.* Andrés F. Ducuara, Cristian E. Susa, Paul Skrzypczyk (2024). *Locally inaccessible hidden quantum correlations*. DOI: [10.1103/PhysRevA.110.022435](https://doi.org/10.1103/PhysRevA.110.022435). URL: <https://arxiv.org/abs/2406.03945v1>.

*Commentary.*

The steering expression in QC_LI.tex lines 190-203 uses three unit Alice directions. Bob's directions form a real orthonormal frame; spin maps a real direction to its Pauli observable. The value set contains the complex norm of the sum of the three expectations, divided by sqrt(3). Equation (CAC), lines 209-214, gives the optimum in terms of the three singular values. The orthonormal-frame formulation expresses this optimum while allowing Bob's frame to vary.

**Definition 1.3 (The maximal three-setting value).**

$$\forall (\rho: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{CHSHWitness}.\operatorname{TwoQubitMatrix}), ((\operatorname{fThree}\left(\rho\right): \mathbb{R}) = \operatorname{sSup}\left(\operatorname{fThreeValues}\left(\rho\right)\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.fThree` (`✓ std3`).

*Citation.* Andrés F. Ducuara, Cristian E. Susa, Paul Skrzypczyk (2024). *Locally inaccessible hidden quantum correlations*. DOI: [10.1103/PhysRevA.110.022435](https://doi.org/10.1103/PhysRevA.110.022435). URL: <https://arxiv.org/abs/2406.03945v1>.

*Commentary.*

The maximal steering value is the real supremum of fThreeValues. This is the maximal F3 violation of Equation (CAC), QC_LI.tex lines 209-214, with the value set specified above. For a Hermitian matrix the set is nonempty and bounded above; no maximizer is assumed.

**Definition 1.4 (A centre bound and its exact violation threshold).**

$$(\operatorname{claim}: \operatorname{Prop}) = ((\forall (\rho: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{CHSHWitness}.\operatorname{TwoQubitMatrix}), ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\rho\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(\rho\right) = (1: \mathbb{C})) \Rightarrow (\operatorname{fThree}\left(\rho\right) \le \operatorname{max}\left(\operatorname{Real}.\operatorname{sqrt}\left((3) \cdot ((1) - (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{centreB}\left(\rho\right)\right)))\right), 1\right))))) \land (\forall (t: \mathbb{R}), ((0 \le t) \Rightarrow ((t < \frac{2}{3}) \Rightarrow (\exists (\rho: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{CHSHWitness}.\operatorname{TwoQubitMatrix}), ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\rho\right)) \land ((\operatorname{Matrix}.\operatorname{trace}\left(\rho\right) = (1: \mathbb{C})) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{centreB}\left(\rho\right)\right) = t) \land (1 < \operatorname{fThree}\left(\rho\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés F. Ducuara, Cristian E. Susa, Paul Skrzypczyk (2024). *Locally inaccessible hidden quantum correlations*. DOI: [10.1103/PhysRevA.110.022435](https://doi.org/10.1103/PhysRevA.110.022435). URL: <https://arxiv.org/abs/2406.03945v1>.

*Commentary.*

The QSE conjecture in QC_LI.tex lines 282-288 asks for a bound depending only on Bob's centre length and reports a numerical impossibility threshold of 0.66. The proposition specifies a centre-only upper bound for every positive semidefinite trace-one two-qubit matrix and requires a violating state at every real centre length t with 0 <= t < 2/3. It gives the exact threshold two thirds; it does not assert that the displayed upper bound is the optimal value at each fixed centre length.

**Theorem 1.5 (The bound and the sharp threshold).**

$$(\forall (\rho: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{CHSHWitness}.\operatorname{TwoQubitMatrix}), ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\rho\right)) \Rightarrow ((\operatorname{Matrix}.\operatorname{trace}\left(\rho\right) = (1: \mathbb{C})) \Rightarrow (\operatorname{fThree}\left(\rho\right) \le \operatorname{max}\left(\operatorname{Real}.\operatorname{sqrt}\left((3) \cdot ((1) - (\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{centreB}\left(\rho\right)\right)))\right), 1\right))))) \land (\forall (t: \mathbb{R}), ((0 \le t) \Rightarrow ((t < \frac{2}{3}) \Rightarrow (\exists (\rho: \operatorname{D5}.\operatorname{S3}.\operatorname{QuantumBounds}.\operatorname{CHSHWitness}.\operatorname{TwoQubitMatrix}), ((\operatorname{Matrix}.\operatorname{PosSemidef}\left(\rho\right)) \land ((\operatorname{Matrix}.\operatorname{trace}\left(\rho\right) = (1: \mathbb{C})) \land ((\operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{SteeringEllipsoidFullyEntangledFraction}.\operatorname{vlen}\left(\operatorname{centreB}\left(\rho\right)\right) = t) \land (1 < \operatorname{fThree}\left(\rho\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.result` (`✓ std3`). ∎

*Resolves.* `Problems/ducuara-susa-skrzypczyk-2024-f3-steering-ellipsoid-threshold` (proved) by `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ducuara-susa-skrzypczyk-2024-f3-steering-ellipsoid-threshold","declaration_gid":"D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Andrés F. Ducuara, Cristian E. Susa, Paul Skrzypczyk (2024). *Locally inaccessible hidden quantum correlations*. DOI: [10.1103/PhysRevA.110.022435](https://doi.org/10.1103/PhysRevA.110.022435). URL: <https://arxiv.org/abs/2406.03945v1>.

*Commentary.*

Swapping the two tensor factors preserves traces and positivity, interchanges the two Bloch vectors, transposes the correlation matrix and interchanges the two ellipsoid centres. Write T for corr(rho), E for the sum of its squared real entries, and |x| for vlen(x). For an orthonormal frame beta, its row matrix O satisfies O times transpose(O) = I and hence transpose(O) times O = I. Applying this identity to each row of T gives sum_i |T beta_i| squared = E.

For a Hermitian rho, bell_trace_real_expansion with the second Alice and Bob directions zero identifies tr(rho (spin(a) tensor spin(b))) with the real number a dot T b embedded in the complex numbers. The triangle inequality and unit_dot_le bound the absolute sum of the three correlations by sum_i |T beta_i|. Cauchy-Schwarz bounds the latter by sqrt(3) sqrt(E). The value set is nonempty, using a constant Alice direction and the coordinate frame, and this estimate bounds it above. Taking its supremum gives F3(rho) <= sqrt(E).

For a positive semidefinite trace-one rho, put b = blochB(rho), r = |b| squared, c = |centre(rho)| and Delta = delta(rho). Each flipped state obtained by conjugating the transpose of rho by flipMatrix(n) is positive semidefinite. Consequently Re tr(rho flipped(rho,n)) is nonnegative. Apply flip_purity_identity to each of the three coordinate unit vectors and sum: each squared column length of T occurs once, giving 2E + r <= 3 + 6Delta. The estimate delta_le_centre gives Delta <= (1 - r)(1/2 - c), so E <= 3 - 3c + (3c - 2)r. The estimate bob_radius_le gives 0 <= r <= 1. If 3c - 2 is nonnegative the affine expression is at most 1; otherwise it is at most 3(1 - c). Thus E <= max(3(1 - c), 1). Apply this inequality to the swapped state: its Alice centre is centreB(rho), and transposition preserves E. Monotonicity of the square root and the preceding steering estimate prove the first clause.

To obtain a violation for a diagonal correlation matrix diag(p,-p,q) with 2 p² + q² > 1, put c = sqrt(3)/3 and choose the three Bob directions ((1+c)/2,(c-1)/2,c), ((c-1)/2,(1+c)/2,c), and (-c,-c,c). Since c squared = 1/3 these directions are orthonormal, and their images under T all have length L = sqrt((2 p² + q²)/3) > 0. Choose each Alice direction to be T beta_i divided by its length. Each expectation is L, so the value is 3L/sqrt(3) > 1 and is bounded above by F3(rho).

For 0 <= t < 2/3 put D = 2 - 2t - t squared and s = t(1-t)/D. These inequalities imply D > 0 and 0 <= s < 1. The state tightState(t,s) is positive semidefinite and has trace one; tight_readouts gives its Bloch vectors (0,0,t+(1-t)s), (0,0,s), and correlation matrix diag(p,-p,q), where p = sqrt(1+s) sqrt((1-t)(1-s)) and q = 1-t+ts. The identity (2 p² + q² - 1)D = (2 - 3t)² shows that its correlation energy exceeds one. Swap its two tensor factors. The matrix remains positive semidefinite with trace one, its Bob centre length is t by tight_centre, and its diagonal correlation matrix is unchanged by transposition. The balanced directions just constructed therefore give F3 > 1, proving the second clause.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.centreB`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.fThree`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.fThreeValues`
- Truth anchor: `D5/S3/Quantum/Contextuality/SteeringEllipsoidFThreeThreshold.result`
- Dependency: [D5/S3/Arith/Lattices/Klartag/Walk/ChainEllipsoid](../../Arith/Lattices/Klartag/Walk/ChainEllipsoid.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall](../Entanglement/AbsoluteSeparability/GurvitsBarnumBall.md)
- Dependency: [D5/S3/Quantum/Entanglement/SteeringEllipsoidCHSH](../Entanglement/SteeringEllipsoidCHSH.md)
