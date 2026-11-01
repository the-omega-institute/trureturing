# The instability count of a Lennard-Jones chain

## Abstract

For a clamped steady Lennard-Jones chain with positive pre-stretch, positive bond lengths, at least one free particle and k ≥ 1 broken bonds, the positive force-Jacobian eigenvalue count lies between k − 1 and k.

**Definition 1.1 (The Lennard-Jones interaction).**

$$\forall (r: \mathbb{R}), ((\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.ljPotential}\left(r\right): \mathbb{R}) = (r)^{(-12: \mathbb{Z})} - (2: \mathbb{R}) \cdot (r)^{(-6: \mathbb{Z})})$$

*Formalization.* `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.ljPotential` (`✓ std3`).

*Citation.* A. S. Rodrigues; P. G. Kevrekidis; M. Dobson (2019). *N-break states in a chain of nonlinear oscillators*. DOI: [10.1103/PhysRevE.99.022201](https://doi.org/10.1103/PhysRevE.99.022201). URL: <https://arxiv.org/abs/1802.03477v2>.

*Commentary.*

The interaction potential is the difference of the inverse twelfth power and twice the inverse sixth power. This is equation (2) of oscillatorsNN_resubmit.tex, lines 185-189. The exponents are integers and the values are real. Integer powers give a total real function, including at zero; the instability statement below assumes positive bond lengths.

**Definition 1.2 (The inflection length).**

$$(\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.inflectionPoint}: \mathbb{R}) = (\frac{(13: \mathbb{R})}{(7: \mathbb{R})})^{\frac{(1: \mathbb{R})}{(6: \mathbb{R})}}$$

*Formalization.* `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.inflectionPoint` (`✓ std3`).

*Citation.* A. S. Rodrigues; P. G. Kevrekidis; M. Dobson (2019). *N-break states in a chain of nonlinear oscillators*. DOI: [10.1103/PhysRevE.99.022201](https://doi.org/10.1103/PhysRevE.99.022201). URL: <https://arxiv.org/abs/1802.03477v2>.

*Commentary.*

The inflection length is the real sixth root of thirteen sevenths, as in oscillatorsNN_resubmit.tex, lines 197-200. The exponent one sixth is real. A positive bond length is broken precisely when it is strictly greater than this length (lines 280-283); equality is excluded from the broken-bond count.

**Definition 1.3 (Successive particle separations).**

$$\forall (m: \mathbb{N}), (\forall (d: \mathbb{R}), (\forall (u: (\operatorname{Fin}\left(m + (2: \mathbb{N})\right)) \to (\mathbb{R})), (\forall (j: \operatorname{Fin}\left(m + (1: \mathbb{N})\right)), ((\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.bondLength}\left(d, u, j\right): \mathbb{R}) = d + u\left(\operatorname{Fin.succ}\left(j\right)\right) - u\left(\operatorname{Fin.castSucc}\left(j\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.bondLength` (`✓ std3`).

*Citation.* A. S. Rodrigues; P. G. Kevrekidis; M. Dobson (2019). *N-break states in a chain of nonlinear oscillators*. DOI: [10.1103/PhysRevE.99.022201](https://doi.org/10.1103/PhysRevE.99.022201). URL: <https://arxiv.org/abs/1802.03477v2>.

*Commentary.*

The displacement vector u has m plus two coordinates, including both endpoints. The bond indexed by j joins coordinates j.castSucc and j.succ, and its length is the pre-stretch d plus the right displacement minus the left displacement. Thus the m plus one bonds have indices starting at zero. This expresses the separations in the potential energy in oscillatorsNN_resubmit.tex, lines 161-170.

**Definition 1.4 (The force at a free particle).**

$$\forall (m: \mathbb{N}), (\forall (d: \mathbb{R}), (\forall (u: (\operatorname{Fin}\left(m + (2: \mathbb{N})\right)) \to (\mathbb{R})), (\forall (n: \operatorname{Fin}\left(m\right)), ((\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.force}\left(d, u, n\right): \mathbb{R}) = \operatorname{deriv}\left(\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.ljPotential}, \operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.bondLength}\left(d, u, \operatorname{Fin.succ}\left(n\right)\right)\right) - \operatorname{deriv}\left(\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.ljPotential}, \operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.bondLength}\left(d, u, \operatorname{Fin.castSucc}\left(n\right)\right)\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.force` (`✓ std3`).

*Citation.* A. S. Rodrigues; P. G. Kevrekidis; M. Dobson (2019). *N-break states in a chain of nonlinear oscillators*. DOI: [10.1103/PhysRevE.99.022201](https://doi.org/10.1103/PhysRevE.99.022201). URL: <https://arxiv.org/abs/1802.03477v2>.

*Commentary.*

For the free particle indexed by n, the force is the derivative of the potential at the right bond length minus its derivative at the left bond length. The particle has coordinate n plus one in u. This is equation (1) of oscillatorsNN_resubmit.tex, lines 175-181, with the free particles indexed from zero.

**Definition 1.5 (The tridiagonal force Jacobian).**

$$\forall (m: \mathbb{N}), (\forall (d: \mathbb{R}), (\forall (u: (\operatorname{Fin}\left(m + (2: \mathbb{N})\right)) \to (\mathbb{R})), ((\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.jacobian}\left(d, u\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(m\right), \operatorname{Fin}\left(m\right), \mathbb{R}\right)) = (\lambda (n: \operatorname{Fin}\left(m\right)) \mapsto (\lambda (q: \operatorname{Fin}\left(m\right)) \mapsto (\operatorname{let} (c: (\operatorname{Fin}\left(m + (1: \mathbb{N})\right)) \to (\mathbb{R})) = (\lambda (j: \operatorname{Fin}\left(m + (1: \mathbb{N})\right)) \mapsto (\operatorname{deriv}\left(\operatorname{deriv}\left(\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.ljPotential}\right), \operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.bondLength}\left(d, u, j\right)\right))); (\operatorname{ite}\left((n = q), (-c\left(\operatorname{Fin.castSucc}\left(n\right)\right) - c\left(\operatorname{Fin.succ}\left(n\right)\right)), (\operatorname{ite}\left(((\operatorname{Fin.val}\left(n\right): \mathbb{N}) + (1: \mathbb{N}) = (\operatorname{Fin.val}\left(q\right): \mathbb{N})), (c\left(\operatorname{Fin.succ}\left(n\right)\right)), (\operatorname{ite}\left(((\operatorname{Fin.val}\left(q\right): \mathbb{N}) + (1: \mathbb{N}) = (\operatorname{Fin.val}\left(n\right): \mathbb{N})), (c\left(\operatorname{Fin.succ}\left(q\right)\right)), ((0: \mathbb{R}))\right))\right))\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.jacobian` (`✓ std3`).

*Citation.* A. S. Rodrigues; P. G. Kevrekidis; M. Dobson (2019). *N-break states in a chain of nonlinear oscillators*. DOI: [10.1103/PhysRevE.99.022201](https://doi.org/10.1103/PhysRevE.99.022201). URL: <https://arxiv.org/abs/1802.03477v2>.

*Commentary.*

Let c(j) be the second derivative of the potential at bond j. The diagonal entry at n is minus the sum of the two adjacent curvatures. The entry immediately to its right is the right-bond curvature, and the symmetric entry immediately to its left is the corresponding shared-bond curvature; all other entries vanish. Fin.val makes both conversions of the finite indices to natural numbers explicit in each adjacency test. This is the force Jacobian in the linearization of oscillatorsNN_resubmit.tex, lines 230-250.

**Definition 1.6 (The two-sided count for a clamped steady chain).**

$$(\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.claim}) \Leftrightarrow (\forall (m: \mathbb{N}), (((1: \mathbb{N}) \le m) \to (\forall (d: \mathbb{R}), (((0: \mathbb{R}) < d) \to (\forall (u: (\operatorname{Fin}\left(m + (2: \mathbb{N})\right)) \to (\mathbb{R})), ((u\left((0: \operatorname{Fin}\left(m + (2: \mathbb{N})\right))\right) = (0: \mathbb{R})) \to ((u\left(\operatorname{Fin.last}\left(m + (1: \mathbb{N})\right)\right) = (0: \mathbb{R})) \to ((\forall (n: \operatorname{Fin}\left(m\right)), (\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.force}\left(d, u, n\right) = (0: \mathbb{R}))) \to ((\forall (j: \operatorname{Fin}\left(m + (1: \mathbb{N})\right)), ((0: \mathbb{R}) < \operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.bondLength}\left(d, u, j\right))) \to (\forall (k: \mathbb{N}), (((1: \mathbb{N}) \le k) \to (((\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (j: \operatorname{Fin}\left(m + (1: \mathbb{N})\right)) \mapsto (\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.inflectionPoint} < \operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.bondLength}\left(d, u, j\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(m + (1: \mathbb{N})\right)\right))\right)\right): \mathbb{N}) = k) \to (\forall (h: \operatorname{Matrix.IsHermitian}\left(\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.jacobian}\left(d, u\right)\right)), ((k - (1: \mathbb{N}) \le (\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (i: \operatorname{Fin}\left(m\right)) \mapsto ((0: \mathbb{R}) < \operatorname{Matrix.IsHermitian.eigenvalues}\left(h, i\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right))\right)\right): \mathbb{N})) \land ((\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda (i: \operatorname{Fin}\left(m\right)) \mapsto ((0: \mathbb{R}) < \operatorname{Matrix.IsHermitian.eigenvalues}\left(h, i\right)), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(m\right)\right))\right)\right): \mathbb{N}) \le k)))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* A. S. Rodrigues; P. G. Kevrekidis; M. Dobson (2019). *N-break states in a chain of nonlinear oscillators*. DOI: [10.1103/PhysRevE.99.022201](https://doi.org/10.1103/PhysRevE.99.022201). URL: <https://arxiv.org/abs/1802.03477v2>.

*Commentary.*

For every m at least one and every positive pre-stretch d, take a displacement vector u with both endpoints zero, zero force at each free particle, and all bond lengths positive. If exactly k bonds are broken, with k at least one, then for every Hermitian witness h of the force Jacobian, the number of its strictly positive eigenvalues lies between k minus one and k. The subtraction and both finite cardinalities are natural-valued, and eigenvalues are counted with multiplicity by their indices in Fin m. The explicit argument of Fin.last is m plus one, so it selects the last of the m plus two coordinates. This is the positive-Jacobian-eigenvalue reading of the conjecture in oscillatorsNN_resubmit.tex, lines 55-59. Its interpretation as unstable pairs follows the squared spectral parameter in the linearization, lines 230-250.

**Theorem 1.7 (The curvature and dimension argument).**

$$\operatorname{D5.S3.StatisticalMechanics.LennardJonesChainBreakInstabilityCount.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/rodrigues-kevrekidis-dobson-2019-n-break-instability-count` (proved) by `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rodrigues-kevrekidis-dobson-2019-n-break-instability-count","declaration_gid":"D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* A. S. Rodrigues; P. G. Kevrekidis; M. Dobson (2019). *N-break states in a chain of nonlinear oscillators*. DOI: [10.1103/PhysRevE.99.022201](https://doi.org/10.1103/PhysRevE.99.022201). URL: <https://arxiv.org/abs/1802.03477v2>.

*Commentary.*

For r positive, differentiating the interaction twice gives φ″(r) = 12(13 − 7r⁶)/r¹⁴. The first derivative is −12r⁻¹³ + 12r⁻⁷; its expression holds throughout a neighbourhood of r, so it can be differentiated again there. Since the denominator r¹⁴ is positive and taking a positive sixth root preserves strict order, φ″(r) < 0 holds exactly when inflectionPoint < r.

Define the real matrix b with m plus one rows and m columns by b(j,n) = 1 if j = n.castSucc, minus 1 if j = n.succ, and zero otherwise, and put c(j) = φ″(bondLength d u j). Expanding the matrix product entry by entry gives jacobian d u = −bᵀ diag(c)b. The two nonzero entries of each column give the diagonal and neighbouring entries in the displayed Jacobian; the remaining entries are zero.

The map x ↦ bx is injective. For m = 0 this follows from the unique vector in the zero-dimensional domain. For positive m, extend scalars to the algebraic closure of the reals. The two standard face maps insert a zero after or before the m coordinates. Their matrix pencil at identity factors and coefficients 1 and −1 is the scalar extension of b, and its full-rank property gives rank m. Rank-nullity makes its kernel zero. Applying this injectivity to the images of two real vectors and using injectivity of the scalar inclusion proves injectivity over the reals. Consequently the range of b has dimension m in a space of dimension m plus one.

Pulling back the diagonal quadratic form along b and negating it yields hermForm(jacobian d u,x) = −∑ⱼ c(j)(bx)(j)². This follows from the quadratic-form identity for a transpose product and the coordinate formula for a diagonal matrix.

For the lower bound, let e be the coordinate subspace supported on the broken bonds, and let v be its inverse image under b. The broken-bond count gives dim e = k. Injectivity identifies v with range(b) ∩ e. The dimension identity for a sum and intersection of subspaces, together with dim range(b) = m and the ambient dimension m plus one, gives dim v ≥ k − 1. For a nonzero x in v, every unbroken coordinate of bx is zero, and injectivity ensures that some broken coordinate is nonzero. Each broken curvature is strictly negative, so every term c(j)(bx)(j)² is nonpositive and at least one is negative. Thus the Jacobian quadratic form is positive definite on v. The Hermitian positive-index bound then gives k − 1 ≤ dim v ≤ the number of positive eigenvalues.

For the upper bound, choose a subspace w on which the Jacobian quadratic form is positive definite and whose dimension equals the number of positive eigenvalues. Map x in w to the broken coordinates of bx. This linear map is injective: if those coordinates vanish, all remaining curvatures are nonnegative, so −∑ⱼ c(j)(bx)(j)² ≤ 0. Positive definiteness forces x = 0. The target is the real coordinate space on exactly k broken bonds, of dimension k, and therefore dim w ≤ k. Combining the lower and upper bounds proves claim for all its stated parameters. The argument uses positive bond lengths and their broken-bond count; the steady-state, endpoint, and positive-pre-stretch hypotheses are retained in the statement. It asserts no existence of steady states with a specified count.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.bondLength`
- Truth anchor: `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.force`
- Truth anchor: `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.inflectionPoint`
- Truth anchor: `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.jacobian`
- Truth anchor: `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.ljPotential`
- Truth anchor: `D5/S3/StatisticalMechanics/LennardJonesChainBreakInstabilityCount.result`
- Dependency: [D5/S3/Combinatorics/Hypermatrix/PencilParameterFibers](../Combinatorics/Hypermatrix/PencilParameterFibers.md)
