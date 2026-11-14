# Quantitative density stability on all effects

## Abstract

Uniform approximate effect additivity yields one density with explicit dimension-dependent error.

In the formulas, Mat(d) is Matrix(Fin(d), Fin(d), C), Id(d) is its identity and Tr is the complex trace. The symbol i in roman type is the complex imaginary unit; italic indices lie in Fin(d). The real and complex embeddings, real and complex, are explicit where needed. Dots mean scalar action or matrix multiplication according to type. The functions fst and snd are the two pair projections, and ite(Q,u,v) is u if Q holds and v otherwise. The matrix single(i,j,z) has entry z only at (i,j); singleVector(i,z) has coordinate z only at i. The matrix vecMulVec(u,v) has entry u(r)v(s), and star conjugates a scalar or each vector coordinate. The function diagonal(v) places v on the diagonal. All sums run over the displayed finite type. The generic sum identities retain arbitrary universes and the anonymous algebraic instance assumptions.

Let d>=1, epsilon>=0 and p be an arbitrary total real function on actual Matrix (Fin d) (Fin d) Complex. An effect E has E.PosSemidef and (1-E).PosSemidef. Assume nonnegativity on every effect, p(identity)=1 and absolute binary defect at most epsilon for all positive semidefinite pairs with effect-valued sum.

Diagonal probes and real and imaginary pair probes give d squared positive matrices. Their total is at most (2*d-1) times the identity and every effect coordinate has absolute value at most 2*d-1. The signed-family estimate therefore gives a Hermitian candidate error eta=(2*d-1)^2*(6*d^2+1)*epsilon. The exact coordinate trace formula identifies the same candidate on every Hermitian matrix.

Nonnegativity and normalization give the two premises of uniform density repair. Its 3*eta correction combines with the candidate error to give 4*(2*d-1)^2*(6*d^2+1)*epsilon for one positive semidefinite rho with complex trace exactly one, simultaneously for every actual effect. This quantitative argument is the finite positive-coordinate construction with bounded interval stability and spectral repair.

Busch supplies the exact all-effect representation background. The quantitative estimate uses the global hypotheses stated here; finite observations alone do not establish them. No optimality, positive-error uniqueness or physical realization is asserted.

**Definition 1.1 (diagonalProbe).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\operatorname{diagonalProbe}(i) = \operatorname{single}(i, i, 1)))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.diagonalProbe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The diagonal probe is the matrix with a single one at the indicated diagonal coordinate.

**Definition 1.2 (realProbe).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\operatorname{realProbe}(i, j) = (\operatorname{complex}(\frac{1}{2}) \cdot \operatorname{vecMulVec}((\operatorname{singleVector}(i, 1)+\operatorname{singleVector}(j, 1)), \operatorname{star}((\operatorname{singleVector}(i, 1)+\operatorname{singleVector}(j, 1))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.realProbe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real pair probe is one half of the outer product of e_i+e_j with its conjugate; effect claims below retain the distinct-index premise.

**Definition 1.3 (imaginaryProbe).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\operatorname{imaginaryProbe}(i, j) = (\operatorname{complex}(\frac{1}{2}) \cdot \operatorname{vecMulVec}((\operatorname{singleVector}(i, 1)+\operatorname{singleVector}(j, \mathrm{i})), \operatorname{star}((\operatorname{singleVector}(i, 1)+\operatorname{singleVector}(j, \mathrm{i}))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.imaginaryProbe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The imaginary pair probe is one half of the outer product of e_i+I*e_j with its conjugate, fixing the negative imaginary sign in its upper entry.

**Definition 1.4 (upperEntry).**

$$\forall (d: \mathbb{N}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\operatorname{upperEntry}(p, i, j) = (\operatorname{complex}((p(\operatorname{realProbe}(i, j))-\frac{(p(\operatorname{diagonalProbe}(i))+p(\operatorname{diagonalProbe}(j)))}{2}))+(\mathrm{i} \cdot \operatorname{complex}((\frac{(p(\operatorname{diagonalProbe}(i))+p(\operatorname{diagonalProbe}(j)))}{2}-p(\operatorname{imaginaryProbe}(i, j))))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.upperEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper candidate entry is formed from actual values on the real and imaginary pair probes and the mean of the two diagonal values.

**Definition 1.5 (candidate).**

$$\forall (d: \mathbb{N}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\operatorname{candidate}(p)(i, j) = \operatorname{ite}(i = j, \operatorname{complex}(p(\operatorname{diagonalProbe}(i))), \operatorname{ite}(i < j, \operatorname{upperEntry}(p, i, j), \operatorname{star}(\operatorname{upperEntry}(p, j, i))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.candidate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every arbitrary real function on actual matrices, the candidate uses its diagonal probe values, the specified upper entries and conjugate lower entries.

**Theorem 1.6 (candidate hermitian).**

$$\forall (d: \mathbb{N}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\operatorname{IsHermitian}(\operatorname{candidate}(p))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.candidate_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete candidate is Hermitian for every real function p and every natural dimension, without any positivity, normalization or additivity hypothesis.

**Definition 1.7 (realMinus).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\operatorname{realMinus}(i, j) = (\operatorname{complex}(\frac{1}{2}) \cdot \operatorname{vecMulVec}((\operatorname{singleVector}(i, 1)-\operatorname{singleVector}(j, 1)), \operatorname{star}((\operatorname{singleVector}(i, 1)-\operatorname{singleVector}(j, 1))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.realMinus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real complementary pair matrix is one half of the outer product of e_i-e_j with its conjugate.

**Definition 1.8 (imaginaryMinus).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\operatorname{imaginaryMinus}(i, j) = (\operatorname{complex}(\frac{1}{2}) \cdot \operatorname{vecMulVec}((\operatorname{singleVector}(i, 1)-\operatorname{singleVector}(j, \mathrm{i})), \operatorname{star}((\operatorname{singleVector}(i, 1)-\operatorname{singleVector}(j, \mathrm{i}))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.imaginaryMinus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The imaginary complementary pair matrix is one half of the outer product of e_i-I*e_j with its conjugate.

**Theorem 1.9 (diagonal eq).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\operatorname{diagonalProbe}(i) = \operatorname{diagonal}(((k: \operatorname{Fin}(d)) \mapsto \operatorname{ite}(k = i, 1, 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each diagonal probe is exactly the diagonal matrix of the corresponding coordinate indicator.

**Theorem 1.10 (diagonal effect).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), ((\operatorname{PosSemidef}(\operatorname{diagonalProbe}(i))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-\operatorname{diagonalProbe}(i))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every diagonal probe is an actual effect in every natural dimension for which its index exists.

**Theorem 1.11 (pair diagonal le).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies ((\operatorname{diagonalProbe}(i)+\operatorname{diagonalProbe}(j)) \leq \operatorname{Id}(d)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.pair_diagonal_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct indices the sum of the two diagonal probes is at most the identity in native matrix order.

**Theorem 1.12 (real complement).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies (((\operatorname{diagonalProbe}(i)+\operatorname{diagonalProbe}(j))-\operatorname{realProbe}(i, j)) = \operatorname{realMinus}(i, j)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.real_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct indices the sum of the diagonal probes minus the real pair probe equals its specified real complementary outer product.

**Theorem 1.13 (imaginary complement).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies (((\operatorname{diagonalProbe}(i)+\operatorname{diagonalProbe}(j))-\operatorname{imaginaryProbe}(i, j)) = \operatorname{imaginaryMinus}(i, j)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct indices the sum of the diagonal probes minus the imaginary pair probe equals its specified imaginary complementary outer product.

**Theorem 1.14 (real le pair).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies (\operatorname{realProbe}(i, j) \leq (\operatorname{diagonalProbe}(i)+\operatorname{diagonalProbe}(j))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.real_le_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct indices the real pair probe is bounded above by the sum of its diagonal probes.

**Theorem 1.15 (imaginary le pair).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies (\operatorname{imaginaryProbe}(i, j) \leq (\operatorname{diagonalProbe}(i)+\operatorname{diagonalProbe}(j))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_le_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct indices the imaginary pair probe is bounded above by the sum of its diagonal probes.

**Theorem 1.16 (real effect).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies ((\operatorname{PosSemidef}(\operatorname{realProbe}(i, j))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-\operatorname{realProbe}(i, j))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.real_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct indices the real pair probe and its identity complement are positive semidefinite.

**Theorem 1.17 (imaginary effect).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies ((\operatorname{PosSemidef}(\operatorname{imaginaryProbe}(i, j))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-\operatorname{imaginaryProbe}(i, j))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct indices the imaginary pair probe and its identity complement are positive semidefinite.

**Theorem 1.18 (entry norm bound).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\operatorname{norm}(E(i, j)) \leq 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.entry_norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every complex entry of every actual effect has complex norm at most one.

**Definition 1.19 (probe).**

$$\forall (d: \mathbb{N}), (\forall (a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)), (\operatorname{probe}(a) = \operatorname{ite}(\operatorname{fst}(a) = \operatorname{snd}(a), \operatorname{diagonalProbe}(\operatorname{fst}(a)), \operatorname{ite}(\operatorname{fst}(a) < \operatorname{snd}(a), \operatorname{realProbe}(\operatorname{fst}(a), \operatorname{snd}(a)), \operatorname{imaginaryProbe}(\operatorname{snd}(a), \operatorname{fst}(a))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.probe` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index pair selects a diagonal probe on the diagonal, a real pair probe above it and an imaginary pair probe below it.

**Theorem 1.20 (probe effect).**

$$\forall (d: \mathbb{N}), (\forall (a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)), ((\operatorname{PosSemidef}(\operatorname{probe}(a))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-\operatorname{probe}(a))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.probe_effect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every member of this concrete indexed probe family is an actual effect.

**Theorem 1.21 (probe card).**

$$\forall (d: \mathbb{N}), (\operatorname{card}(\operatorname{Fin}(d) \times \operatorname{Fin}(d)) = (d)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.probe_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every natural dimension the finite pair-index type has exactly d^2 members.

**Definition 1.22 (majorant).**

$$\forall (d: \mathbb{N}), (\forall (a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)), (\operatorname{majorant}(a) = ((\operatorname{diagonalProbe}(\operatorname{fst}(a))+\operatorname{diagonalProbe}(\operatorname{snd}(a)))-\operatorname{ite}(\operatorname{fst}(a) = \operatorname{snd}(a), \operatorname{diagonalProbe}(\operatorname{fst}(a)), 0))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.majorant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The majorant is the sum of the two indicated diagonal probes, with one duplicate removed on the diagonal.

**Theorem 1.23 (probe le majorant).**

$$\forall (d: \mathbb{N}), (\forall (a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)), (\operatorname{probe}(a) \leq \operatorname{majorant}(a)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.probe_le_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every concrete probe is bounded above by its stated diagonal majorant.

**Theorem 1.24 (diagonal sum).**

$$\forall (d: \mathbb{N}), (\sum_{i: \operatorname{Fin}(d)} (\operatorname{diagonalProbe}(i)) = \operatorname{Id}(d))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of all diagonal probes is the actual identity matrix, including the empty-dimensional identity convention.

**Theorem 1.25 (triangular sum).**

$$\forall (J: \operatorname{Type}()), (\forall (A: \operatorname{Type}()), ([\operatorname{Fintype}(J)] ([\operatorname{LinearOrder}(J)] ([\operatorname{AddCommMonoid}(A)] (\forall (f: J \to J \to A), (\sum_{i: J} (\sum_{j: J} (f(i, j))) = (\sum_{i: J} (f(i, i))+\sum_{i: J} (\sum_{j: J} (\operatorname{ite}(i < j, (f(i, j)+f(j, i)), 0))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.triangular_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite linearly ordered index type and any additive commutative monoid, the double sum splits into its diagonal sum and paired strict-upper sum.

**Theorem 1.26 (incident sum).**

$$\forall (J: \operatorname{Type}()), (\forall (A: \operatorname{Type}()), ([\operatorname{Fintype}(J)] ([\operatorname{AddCommMonoid}(A)] ([\operatorname{Module}(\mathbb{R}, A)] (\forall (q: J \to J \to \mathbb{R}), (\forall (D: J \to A), (\sum_{i: J} ((\sum_{j: J} ((q(i, j)+q(j, i))) \cdot D(i))) = \sum_{i: J} (\sum_{j: J} ((q(i, j) \cdot (D(i)+D(j))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.incident_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite index type and any real module with additive commutative monoid structure, the sum of incident scalar weights on the indexed vectors equals the double sum of pair weights on the corresponding vector sums.

**Definition 1.27 (coordinate).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), (\forall (a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)), (\operatorname{coordinate}(E, a) = \operatorname{ite}(\operatorname{fst}(a) = \operatorname{snd}(a), (\Re (E(\operatorname{fst}(a), \operatorname{fst}(a)))-\sum_{k: \operatorname{Fin}(d)} (\operatorname{ite}(\operatorname{fst}(a) < k, (\Re (E(\operatorname{fst}(a), k))-\operatorname{Im}(E(\operatorname{fst}(a), k))), \operatorname{ite}(k < \operatorname{fst}(a), (\Re (E(k, \operatorname{fst}(a)))-\operatorname{Im}(E(k, \operatorname{fst}(a)))), 0)))), \operatorname{ite}(\operatorname{fst}(a) < \operatorname{snd}(a), (2 \cdot \Re (E(\operatorname{fst}(a), \operatorname{snd}(a)))), (-2 \cdot \operatorname{Im}(E(\operatorname{snd}(a), \operatorname{fst}(a)))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The concrete real Hermitian coordinates use twice the real upper entry, minus twice its imaginary part, and the stated diagonal incident corrections.

**Definition 1.28 (offdiagTerm).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\operatorname{offdiagTerm}(E, i, j) = ((((2 \cdot \Re (E(i, j))) \cdot \operatorname{realProbe}(i, j))+((-2 \cdot \operatorname{Im}(E(i, j))) \cdot \operatorname{imaginaryProbe}(i, j)))-((\Re (E(i, j))-\operatorname{Im}(E(i, j))) \cdot (\operatorname{diagonalProbe}(i)+\operatorname{diagonalProbe}(j))))))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.offdiagTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each upper pair contributes its real and imaginary probe multiples with the diagonal correction subtracted.

**Theorem 1.29 (offdiag identity).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies (\operatorname{offdiagTerm}(E, i, j) = (\operatorname{single}(i, j, E(i, j))+\operatorname{single}(j, i, \operatorname{star}(E(i, j)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.offdiag_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any actual complex matrix and distinct indices the corrected pair contribution is exactly its upper matrix unit plus the conjugate lower matrix unit.

**Definition 1.30 (upperCorrection).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\operatorname{upperCorrection}(E, i, j) = \operatorname{ite}(i < j, (\Re (E(i, j))-\operatorname{Im}(E(i, j))), 0)))))$$

*Formalization.* `D5/S3/Quantum/Foundation/EffectDensityStability.upperCorrection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The correction is the real part minus the imaginary part of an upper entry, and zero elsewhere.

**Theorem 1.31 (coordinate diagonal).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), (\forall (i: \operatorname{Fin}(d)), (\operatorname{coordinate}(E, (i, i)) = (\Re (E(i, i))-\sum_{j: \operatorname{Fin}(d)} ((\operatorname{upperCorrection}(E, i, j)+\operatorname{upperCorrection}(E, j, i)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal coordinate subtracts the sum of both incident upper corrections from the real diagonal entry, for every actual complex matrix.

**Theorem 1.32 (coordinate pair).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\operatorname{ite}(i < j, ((\operatorname{coordinate}(E, (i, j)) \cdot \operatorname{probe}((i, j)))+(\operatorname{coordinate}(E, (j, i)) \cdot \operatorname{probe}((j, i)))), 0) = (\operatorname{ite}(i < j, \operatorname{offdiagTerm}(E, i, j), 0)+(\operatorname{upperCorrection}(E, i, j) \cdot (\operatorname{diagonalProbe}(i)+\operatorname{diagonalProbe}(j))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two coordinates and probes of an upper pair split into the off-diagonal contribution and its diagonal correction, with the displayed conditional retained.

**Theorem 1.33 (coordinate split).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), (\sum_{a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)} ((\operatorname{coordinate}(E, a) \cdot \operatorname{probe}(a))) = (\sum_{i: \operatorname{Fin}(d)} ((\Re (E(i, i)) \cdot \operatorname{diagonalProbe}(i)))+\sum_{i: \operatorname{Fin}(d)} (\sum_{j: \operatorname{Fin}(d)} (\operatorname{ite}(i < j, \operatorname{offdiagTerm}(E, i, j), 0))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual complex matrix the complete probe sum splits into its real diagonal contribution and the sum of corrected upper-pair contributions.

**Theorem 1.34 (coordinate expansion).**

$$\forall (d: \mathbb{N}), (\forall (E: \operatorname{Mat}(d)), ((\operatorname{IsHermitian}(E)) \implies (\sum_{a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)} ((\operatorname{coordinate}(E, a) \cdot \operatorname{probe}(a))) = E)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual Hermitian matrix is exactly the real linear combination of the concrete probes given by its coordinates; all natural dimensions are included.

**Lemma 1.35 (real probe decomp).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies (\operatorname{realProbe}(i, j) = (\operatorname{complex}(\frac{1}{2}) \cdot (((\operatorname{single}(i, i, 1)+\operatorname{single}(i, j, 1))+\operatorname{single}(j, i, 1))+\operatorname{single}(j, j, 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.real_probe_decomp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct indices the real pair probe is one half of the sum of its four specified matrix units.

**Lemma 1.36 (imaginary probe decomp).**

$$\forall (d: \mathbb{N}), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies (\operatorname{imaginaryProbe}(i, j) = (\operatorname{complex}(\frac{1}{2}) \cdot (((\operatorname{single}(i, i, 1)+\operatorname{single}(i, j, -\mathrm{i}))+\operatorname{single}(j, i, \mathrm{i}))+\operatorname{single}(j, j, 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_probe_decomp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct indices the imaginary pair probe is one half of the four specified matrix units, with upper coefficient -I and lower coefficient I.

**Lemma 1.37 (trace single sum).**

$$\forall (d: \mathbb{N}), (\forall (C: \operatorname{Mat}(d)), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), (\forall (a: \mathbb{C}), (\operatorname{Tr}((C \cdot \operatorname{single}(i, j, a))) = (a \cdot C(j, i)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.trace_single_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any actual complex matrix C and complex scalar a, the complex trace of C times the indicated matrix unit is exactly a*C(j,i).

**Lemma 1.38 (trace real formula).**

$$\forall (d: \mathbb{N}), (\forall (C: \operatorname{Mat}(d)), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies (\Re (\operatorname{Tr}((C \cdot \operatorname{realProbe}(i, j)))) = \frac{(((\Re (C(i, i))+\Re (C(j, j)))+\Re (C(i, j)))+\Re (C(j, i)))}{2})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.trace_real_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual complex C and distinct indices, its real trace pairing with the real pair probe is the stated mean of four real entries, without a Hermiticity hypothesis.

**Lemma 1.39 (trace imaginary formula).**

$$\forall (d: \mathbb{N}), (\forall (C: \operatorname{Mat}(d)), (\forall (i: \operatorname{Fin}(d)), (\forall (j: \operatorname{Fin}(d)), ((i \neq j) \implies (\Re (\operatorname{Tr}((C \cdot \operatorname{imaginaryProbe}(i, j)))) = \frac{(((\Re (C(i, i))+\Re (C(j, j)))+\operatorname{Im}(C(j, i)))-\operatorname{Im}(C(i, j)))}{2})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.trace_imaginary_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual complex C and distinct indices, its real trace pairing with the imaginary pair probe is the stated combination of diagonal real parts and off-diagonal imaginary parts, without a Hermiticity hypothesis.

**Theorem 1.40 (probe trace).**

$$\forall (d: \mathbb{N}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\forall (a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)), (\Re (\operatorname{Tr}((\operatorname{candidate}(p) \cdot \operatorname{probe}(a)))) = p(\operatorname{probe}(a)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.probe_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arbitrary real p the concrete Hermitian candidate reproduces p exactly on every probe through the real part of the actual complex trace.

**Theorem 1.41 (coordinate trace).**

$$\forall (d: \mathbb{N}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (\forall (H: \operatorname{Mat}(d)), ((\operatorname{IsHermitian}(H)) \implies (\Re (\operatorname{Tr}((\operatorname{candidate}(p) \cdot H))) = \sum_{a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)} ((\operatorname{coordinate}(H, a) \cdot p(\operatorname{probe}(a))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every arbitrary real p and every actual Hermitian H, the real part of the complex trace of candidate(p)*H equals the complete coordinate-weighted sum of p on the concrete probes. No probability premises on p are assumed.

**Theorem 1.42 (majorant sum).**

$$\forall (d: \mathbb{N}), (\sum_{a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)} (\operatorname{majorant}(a)) = (((2 \cdot \operatorname{real}(d))-1) \cdot \operatorname{Id}(d)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.majorant_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every natural dimension the total diagonal majorant equals (2*d-1) times the actual identity, with d interpreted in the reals.

**Theorem 1.43 (probe sum bound).**

$$\forall (d: \mathbb{N}), (\sum_{a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)} (\operatorname{probe}(a)) \leq (((2 \cdot \operatorname{real}(d))-1) \cdot \operatorname{Id}(d)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.probe_sum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In every natural dimension the total concrete probe family is at most (2*d-1) times the actual identity in native matrix order.

**Theorem 1.44 (coordinate bound).**

$$\forall (d: \mathbb{N}), ((1 \leq d) \implies (\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (\forall (a: \operatorname{Fin}(d) \times \operatorname{Fin}(d)), (\lvert \operatorname{coordinate}(E, a) \rvert  \leq ((2 \cdot \operatorname{real}(d))-1))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=1 and every actual effect, every concrete real coordinate has absolute value at most 2*d-1, including dimension one.

**Theorem 1.45 (candidate error).**

$$\forall (d: \mathbb{N}), ((1 \leq d) \implies (\forall (\varepsilon: \mathbb{R}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (((0 \leq \varepsilon) \land (\forall (X: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(X)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-X)))) \implies (0 \leq p(X)))) \land (p(\operatorname{Id}(d)) = 1) \land (\forall (X: \operatorname{Mat}(d)), (\forall (Y: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(X)) \land (\operatorname{PosSemidef}(Y)) \land ((\operatorname{PosSemidef}((X+Y))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-(X+Y)))))) \implies (\lvert ((p((X+Y))-p(X))-p(Y)) \rvert  \leq \varepsilon))))) \implies (\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (\lvert (p(E)-\Re (\operatorname{Tr}((\operatorname{candidate}(p) \cdot E)))) \rvert  \leq (((((2 \cdot \operatorname{real}(d))-1))^{2} \cdot ((6 \cdot (\operatorname{real}(d))^{2})+1)) \cdot \varepsilon))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.candidate_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every d>=1 and epsilon>=0, global effect nonnegativity, identity normalization and binary defect at most epsilon bound the error from p to the concrete candidate on every actual effect by (2*d-1)^2*(6*d^2+1)*epsilon.

**Theorem 1.46 (approximate effect density).**

$$\forall (d: \mathbb{N}), ((1 \leq d) \implies (\forall (\varepsilon: \mathbb{R}), (\forall (p: \operatorname{Mat}(d) \to \mathbb{R}), (((0 \leq \varepsilon) \land (\forall (X: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(X)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-X)))) \implies (0 \leq p(X)))) \land (p(\operatorname{Id}(d)) = 1) \land (\forall (X: \operatorname{Mat}(d)), (\forall (Y: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(X)) \land (\operatorname{PosSemidef}(Y)) \land ((\operatorname{PosSemidef}((X+Y))) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-(X+Y)))))) \implies (\lvert ((p((X+Y))-p(X))-p(Y)) \rvert  \leq \varepsilon))))) \implies (\exists (\rho: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(\rho)) \land (\operatorname{Tr}(\rho) = 1)) \land (\forall (E: \operatorname{Mat}(d)), (((\operatorname{PosSemidef}(E)) \land (\operatorname{PosSemidef}((\operatorname{Id}(d)-E)))) \implies (\lvert (p(E)-\Re (\operatorname{Tr}((\rho \cdot E)))) \rvert  \leq (4 \cdot (((((2 \cdot \operatorname{real}(d))-1))^{2} \cdot ((6 \cdot (\operatorname{real}(d))^{2})+1)) \cdot \varepsilon)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/EffectDensityStability.approximate_effect_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul Busch (2003). *Quantum States and Generalized Observables — A Simple Proof of Gleason’s Theorem*. DOI: [10.1103/PhysRevLett.91.120403](https://doi.org/10.1103/PhysRevLett.91.120403). URL: <https://arxiv.org/html/quant-ph/9909073v3>.

*Commentary.*

For every natural d>=1, every real epsilon>=0 and every arbitrary real function p on actual complex d by d matrices, assume p is nonnegative on every actual effect, p(identity)=1, and absolute binary additive defect at most epsilon for all positive semidefinite E,F whose sum is an effect. There exists ONE actual positive semidefinite complex matrix rho with COMPLEX trace rho=1, such that for EVERY actual effect E the absolute difference between p(E) and Re(trace(rho*E)) is at most 4*(2*d-1)^2*(6*d^2+1)*epsilon, with d interpreted in the reals. The density is chosen before E. Epsilon zero and dimension one are included. No continuity, measurability, p(0)=0, commutativity, rank, small-error, supplied-coordinate, supplied-density or finite-sample premise is imposed.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.approximate_effect_density`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.candidate`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.candidate_error`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.candidate_hermitian`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_diagonal`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_expansion`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_pair`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_split`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.coordinate_trace`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.diagonalProbe`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_effect`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_eq`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.diagonal_sum`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.entry_norm_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.imaginaryMinus`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.imaginaryProbe`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_complement`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_effect`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_le_pair`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.imaginary_probe_decomp`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.incident_sum`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.majorant`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.majorant_sum`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.offdiagTerm`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.offdiag_identity`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.pair_diagonal_le`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.probe`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.probe_card`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.probe_effect`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.probe_le_majorant`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.probe_sum_bound`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.probe_trace`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.realMinus`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.realProbe`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.real_complement`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.real_effect`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.real_le_pair`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.real_probe_decomp`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.trace_imaginary_formula`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.trace_real_formula`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.trace_single_sum`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.triangular_sum`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.upperCorrection`
- Truth anchor: `D5/S3/Quantum/Foundation/EffectDensityStability.upperEntry`
- Dependency: [D5/S3/Quantum/Foundation/EffectAdditivityStability](EffectAdditivityStability.md)
- Dependency: [D5/S3/Quantum/Foundation/EffectDensityRepair](EffectDensityRepair.md)
