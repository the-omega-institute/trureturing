# Universal coefficients for the peakon transfer expansion

## Abstract

The Camassa–Holm peakon transfer matrices have a partition expansion with explicit universal rational coefficients satisfying the values of Conjecture 5.2.

**Definition 1.1 (The hyperbolic phase).**

$$\forall N \in \mathbb{N},\; \forall q \in (\operatorname{Fin}\left(N\right) \to \mathbb{R}),\; \forall nu \in \mathbb{C},\; \forall i \in \operatorname{Fin}\left(N\right),\; \forall j \in \operatorname{Fin}\left(N\right),\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.phase}\left(q, nu, i, j\right) = \frac{nu \cdot ((q\left(i\right) - q\left(j\right): \mathbb{R}): \mathbb{C})}{2}$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.phase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positions are real and the parameter nu is complex. Their difference is cast to the complex numbers before multiplication by nu and division by two.

**Definition 1.2 (The antisymmetric hyperbolic matrix).**

$$\forall N \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \mathbb{C}),\; \forall q \in (\operatorname{Fin}\left(N\right) \to \mathbb{R}),\; \forall nu \in \mathbb{C},\; \forall i \in \operatorname{Fin}\left(N\right),\; \forall j \in \operatorname{Fin}\left(N\right),\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.A}\left(w, q, nu\right)\left(i, j\right) = w\left(i\right) \cdot w\left(j\right) \cdot \operatorname{Complex.sinh}\left(\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.phase}\left(q, nu, i, j\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.A` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

Equation (2.1) gives these entries with the factorized weights w_i w_j in place of the square root of p_i p_j. The weights may be complex; nonnegative momenta are recovered by taking w_i to be the real square root of p_i. Transposition is ordinary transposition.

**Definition 1.3 (The symmetric hyperbolic matrix).**

$$\forall N \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \mathbb{C}),\; \forall q \in (\operatorname{Fin}\left(N\right) \to \mathbb{R}),\; \forall nu \in \mathbb{C},\; \forall i \in \operatorname{Fin}\left(N\right),\; \forall j \in \operatorname{Fin}\left(N\right),\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.T}\left(w, q, nu\right)\left(i, j\right) = w\left(i\right) \cdot w\left(j\right) \cdot \operatorname{Complex.cosh}\left(\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.phase}\left(q, nu, i, j\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.T` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

Equation (2.2) uses the same weights and phase with the complex hyperbolic cosine. Interchanging the two indices leaves the entry unchanged.

**Definition 1.4 (The position-sign matrix).**

$$\forall N \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \mathbb{C}),\; \forall q \in (\operatorname{Fin}\left(N\right) \to \mathbb{R}),\; \forall nu \in \mathbb{C},\; \forall i \in \operatorname{Fin}\left(N\right),\; \forall j \in \operatorname{Fin}\left(N\right),\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.S}\left(w, q, nu\right)\left(i, j\right) = (\operatorname{SignType.sign}\left((q\left(i\right) - q\left(j\right))\right): \mathbb{C}) \cdot \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.A}\left(w, q, nu\right)\left(i, j\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.S` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

Equation (2.3) multiplies the corresponding entry of A by the sign of the real position difference, cast to the complex numbers. SignType.sign is zero at coincident positions, including the diagonal; no distinctness or ordering of the positions is assumed.

**Definition 1.5 (The first spectral rational function).**

$$\forall gamma \in \mathbb{C},\; \forall z \in \mathbb{C},\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.Lambda}\left(gamma, z\right) = \frac{(z)^{2} - 1}{2 \cdot z + gamma}$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.Lambda` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

This rational function is the coefficient of T in the spectral matrix of §5.3. Its definition uses complex division for every gamma and z; the transfer expansion below excludes a zero denominator.

**Definition 1.6 (The second spectral rational function).**

$$\forall gamma \in \mathbb{C},\; \forall z \in \mathbb{C},\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.xi}\left(gamma, z\right) = \frac{(z)^{2} + gamma \cdot z + 1}{2 \cdot z + gamma}$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.xi` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

This rational function is the coefficient of A in §5.3. When 2z + gamma is nonzero, the two rational functions satisfy the conic relation xi squared = Lambda squared + gamma Lambda + 1 of (5.18).

**Definition 1.7 (The spectral Lax matrix).**

$$\forall N \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \mathbb{C}),\; \forall q \in (\operatorname{Fin}\left(N\right) \to \mathbb{R}),\; \forall nu \in \mathbb{C},\; \forall gamma \in \mathbb{C},\; \forall z \in \mathbb{C},\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.L}\left(w, q, nu, gamma, z\right) = \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.S}\left(w, q, nu\right) + \operatorname{HSMul.hSMul}\left(\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.Lambda}\left(gamma, z\right), \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.T}\left(w, q, nu\right)\right) + \operatorname{HSMul.hSMul}\left(\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.xi}\left(gamma, z\right), \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.A}\left(w, q, nu\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.L` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

The decomposition in §5.3 is S + Lambda T + xi A, with complex scalar multiplication of matrices. The matrices are indexed by Fin N, and N may be zero.

**Definition 1.8 (The transfer traces).**

$$\forall N \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \mathbb{C}),\; \forall q \in (\operatorname{Fin}\left(N\right) \to \mathbb{R}),\; \forall nu \in \mathbb{C},\; \forall gamma \in \mathbb{C},\; \forall z \in \mathbb{C},\; \forall m \in \mathbb{N},\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.tau}\left(w, q, nu, gamma, z\right)\left(m\right) = \operatorname{Matrix.trace}\left((\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.L}\left(w, q, nu, gamma, z\right))^{m}\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.tau` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

The transfer matrix in §5.3 is the trace of the m-th ordinary matrix power. This definition includes m = 0; the partition expansion is stated for positive m.

**Definition 1.9 (The Hamiltonian trace coefficients).**

$$\forall N \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \mathbb{C}),\; \forall q \in (\operatorname{Fin}\left(N\right) \to \mathbb{R}),\; \forall nu \in \mathbb{C},\; \forall gamma \in \mathbb{C},\; \forall k \in \mathbb{N},\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.h}\left(w, q, nu, gamma\right)\left(k\right) = (k: \mathbb{C}) \cdot \operatorname{Matrix.trace}\left((\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.T}\left(w, q, nu\right) + \operatorname{HSMul.hSMul}\left(\frac{gamma}{2}, \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.A}\left(w, q, nu\right)\right)) \cdot (\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.S}\left(w, q, nu\right) + \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.A}\left(w, q, nu\right))^{(k - 1: \mathbb{N})}\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.h` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

Equation (5.17) gives k times the trace of (T + (gamma/2) A)(S + A) to the power k−1. The factor k is cast to the complex numbers. The exponent uses natural subtraction, so it is zero at k = 0 as well as k = 1; the coefficient h at zero is zero because of the leading factor.

**Definition 1.10 (Rational families indexed by partitions).**

$$\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.CoeffFamily} = \left((m: \mathbb{N}) \to \left(\operatorname{Nat.Partition}\left(m\right) \to \mathbb{Q}\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.CoeffFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coefficient family assigns a rational number to every natural m and every Nat.Partition m. It has no dependence on the number of positions, weights or spectral parameters.

**Definition 1.11 (The factorials of repeated-part counts).**

$$\forall m \in \mathbb{N},\; \forall pi \in \operatorname{Nat.Partition}\left(m\right),\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.multiplicityFactor}\left(pi\right) = \prod_{r \in \operatorname{Multiset.toFinset}\left(\operatorname{Nat.Partition.parts}\left(pi\right)\right)} (\operatorname{Nat.factorial}\left(\operatorname{Multiset.count}\left(r, \operatorname{Nat.Partition.parts}\left(pi\right)\right)\right))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.multiplicityFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each distinct part, take the factorial of its multiplicity in the multiset of parts, then multiply these factorials. Passing to Multiset.toFinset ensures that each distinct part contributes exactly once.

**Definition 1.12 (The universal rational coefficient).**

$$\forall m \in \mathbb{N},\; \forall pi \in \operatorname{Nat.Partition}\left(m\right),\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.universalCoeff}\left(m, pi\right) = \frac{(m: \mathbb{Q}) \cdot (\operatorname{Nat.factorial}\left((\operatorname{Multiset.card}\left(\operatorname{Nat.Partition.parts}\left(pi\right)\right) - 1: \mathbb{N})\right): \mathbb{Q})}{(\operatorname{Multiset.prod}\left(\operatorname{Nat.Partition.parts}\left(pi\right)\right): \mathbb{Q}) \cdot (\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.multiplicityFactor}\left(pi\right): \mathbb{Q})}$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.universalCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a partition with j parts, the coefficient is m (j−1)! divided by the product of its parts and the factorials of their multiplicities. All factors are cast from the natural numbers to the rational numbers before division; j−1 is natural subtraction. The definition also includes the empty partition of zero.

**Definition 1.13 (The product associated with a partition).**

$$\forall m \in \mathbb{N},\; \forall f \in (\mathbb{N} \to \mathbb{C}),\; \forall pi \in \operatorname{Nat.Partition}\left(m\right),\; \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.partMonomial}\left(f, pi\right) = \operatorname{Multiset.prod}\left(\operatorname{Multiset.map}\left(f, \operatorname{Nat.Partition.parts}\left(pi\right)\right)\right)$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.partMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map a complex-valued function over the multiset of parts and multiply the resulting multiset. Repeated parts therefore give repeated factors, and the empty multiset gives one.

**Definition 1.14 (The three prescribed coefficient values).**

$$\forall a \in \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.CoeffFamily},\; (\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.prescribedValues}\left(a\right)) \Leftrightarrow ((\forall m \in \mathbb{N},\; \forall pi \in \operatorname{Nat.Partition}\left(m\right),\; (0 < m) \Rightarrow ((\operatorname{Nat.Partition.parts}\left(pi\right) = \left\{m\right\}) \Rightarrow (a\left(m, pi\right) = 1))) \land ((\forall m \in \mathbb{N},\; \forall pi \in \operatorname{Nat.Partition}\left(m\right),\; (0 < m) \Rightarrow ((\operatorname{Nat.Partition.parts}\left(pi\right) = \operatorname{Multiset.replicate}\left(m, 1\right)) \Rightarrow (a\left(m, pi\right) = 1))) \land (\forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall pi \in \operatorname{Nat.Partition}\left(m\right),\; (j < (m - 1: \mathbb{N})) \Rightarrow ((\operatorname{Nat.Partition.parts}\left(pi\right) = \operatorname{Multiset.cons}\left((m - j: \mathbb{N}), \operatorname{Multiset.replicate}\left(j, 1\right)\right)) \Rightarrow (a\left(m, pi\right) = \frac{(m: \mathbb{Q})}{((m - j: \mathbb{N}): \mathbb{Q})})))))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.prescribedValues` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

The single-part coefficient is one for positive m, as in (5.20), and the coefficient of m parts equal to one is one, as in (5.21). For j < m−1, the partition consisting of m−j and j ones has coefficient m/(m−j). Both subtractions are in the natural numbers, and the denominator m−j is cast to the rational numbers after subtraction. The third clause needs no separate positivity hypothesis on m because its inequality already implies positivity.

**Definition 1.15 (The partition expansion of each transfer trace).**

$$\forall a \in \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.CoeffFamily},\; (\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.expansion}\left(a\right)) \Leftrightarrow (\forall N \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall w \in (\operatorname{Fin}\left(N\right) \to \mathbb{C}),\; \forall q \in (\operatorname{Fin}\left(N\right) \to \mathbb{R}),\; \forall nu \in \mathbb{C},\; \forall gamma \in \mathbb{C},\; \forall z \in \mathbb{C},\; (0 < m) \Rightarrow ((2 \cdot z + gamma \ne 0) \Rightarrow (\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.tau}\left(w, q, nu, gamma, z\right)\left(m\right) = \sum_{(pi: \operatorname{Nat.Partition}\left(m\right))} ((\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.Lambda}\left(gamma, z\right))^{\operatorname{Multiset.card}\left(\operatorname{Nat.Partition.parts}\left(pi\right)\right)} \cdot (a\left(m, pi\right): \mathbb{C}) \cdot \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.partMonomial}\left(\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.h}\left(w, q, nu, gamma\right), pi\right)))))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.expansion` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

Equation (5.20) is written as a single sum over Nat.Partition m. The number of parts gives the power of Lambda, and the part monomial is the product of the corresponding Hamiltonian coefficients. For positive m, all parts are positive and their sum is m. The identity holds for every finite N, complex weights and parameters, and real positions, provided 2z + gamma is nonzero; the rational coefficient is cast to the complex numbers.

**Definition 1.16 (The coefficient-existence proposition).**

$$(\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.claim}) \Leftrightarrow (\exists a \in \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.CoeffFamily},\; (a = \operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.universalCoeff}) \land ((\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.prescribedValues}\left(a\right)) \land (\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.expansion}\left(a\right))))$$

*Formalization.* `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.claim` (`✓ std3`).

*Citation.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

Conjecture 5.2 asks for coefficients giving the transfer expansion and the prescribed values. This proposition also specifies the explicit family universalCoeff. The existential precedes every matrix and parameter quantifier in expansion, so a single rational family serves them all. Removing the equality to universalCoeff gives the source's existence assertion; uniqueness of coefficient families is not asserted.

**Theorem 1.17 (The universal family gives the transfer expansion).**

$$\operatorname{D5.S3.FluidDynamics.Solitons.CamassaHolmPeakonTransferExpansion.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.result` (`✓ std3`). ∎

*Resolves.* `Problems/avan-frappat-ragoucy-2026-peakon-transfer-expansion` (proved) by `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"avan-frappat-ragoucy-2026-peakon-transfer-expansion","declaration_gid":"D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jean Avan, Luc Frappat, Eric Ragoucy (2026). *Quadratic Poisson brackets for the Camassa–Holm peakons*. DOI: [10.1088/1751-8121/ae7683](https://doi.org/10.1088/1751-8121/ae7683). URL: <https://arxiv.org/abs/2512.11066v3>.

*Commentary.*

The matrix S + A has zero entries whenever the row position is at most the column position. Triangularity with blocks labelled by positions gives determinant one for its formal resolvent pencil, including coincident positions. The vectors with entries w_i exp(nu q_i/2) and w_i exp(−nu q_i/2) give the rank-two decomposition of T and A. The relation (5.18), together with the determinant identity for a rank-two perturbation and ordinary transposition, yields det(1 − tL) = 1 − Lambda sum over k ≥ 1 of (h_k/k)t^k as an identity of formal power series. Jacobi's formula gives the generating series of the transfer traces as the negative logarithmic derivative. Extracting each positive-degree coefficient and regrouping compositions by their multisets of parts gives m (j−1)! divided by the product of the parts and their multiplicity factorials. This family satisfies each of the three prescribed values and the expansion of Conjecture 5.2.

## References

- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.A`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.CoeffFamily`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.L`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.Lambda`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.S`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.T`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.claim`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.expansion`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.h`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.multiplicityFactor`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.partMonomial`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.phase`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.prescribedValues`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.result`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.tau`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.universalCoeff`
- Truth anchor: `D5/S3/FluidDynamics/Solitons/CamassaHolmPeakonTransferExpansion.xi`
