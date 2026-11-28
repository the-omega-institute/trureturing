# Lattice points in the dihedral permutohedron

## Abstract

A prefix recurrence counts the lattice points in every nonnegative integral dilation of the dihedral permutohedron.

**Definition 1.1 (Integer points of the source dilation).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.SourcePoints`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.SourcePoints` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Let Qₙ be the real convex hull of the orbit of (1, …, n) under the two permutation matrices of Equation (2). Residue zero denotes paper label n. Write Xₙ,ₖ for the integer-coordinate vectors whose real images lie in kQₙ. Question 6.1 of Colin Olairez, arXiv:2610.28672v2, §6, printed p. 21, asks for the number of lattice points or the Ehrhart polynomial. Source locator https://arxiv.org/html/2610.28672v2#S6.Thmquestion1 . Both n and k are natural; the counting theorem assumes n ≥ 3 and includes k = 0.

**Definition 1.2 (The integral difference coset).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.Coset`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.Coset` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Set S = n(n + 1)/2 and T = n(n − 1)/2. The existing source-coordinate conjugacy identifies the real signed wrap hull for every n ≥ 3. The forward difference dᵢ = xᵢ₊₁ − xᵢ wraps cyclically. It has sum zero and weighted sum W(d) = ∑ᵢ i dᵢ = nx₀ − ∑ᵢ xᵢ. On the plane ∑ᵢ xᵢ = kS, its image is precisely the sum-zero lattice coset W(d) ≡ −kS modulo n. This residue is n/2 when n is even and k is odd, and zero otherwise.

For the inverse, let pᵢ be the sum of dⱼ over 0 ≤ j < i. The sum-zero condition supplies the last cyclic increment. Recover xᵢ by adding (kS − ∑ⱼ pⱼ)/n to each pᵢ. The residue condition makes this constant integral.

The signed wrap hull is the image of the radius-k cross-polytope under the map u ↦ (∑ᵢ uᵢ)1 − nu. Thus a difference vector is feasible exactly when some translate z = d + t1 has absolute sum at most B = nk. For integral d, the absolute sum is affine between consecutive integers, so feasibility over the reals implies feasibility at an integer endpoint.

**Definition 1.3 (The least feasible integer translate).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.IsFirst`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.IsFirst` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Feasible integer translates form an interval inside −k ≤ t ≤ k. At z = d + t1 let a = ∑ᵢ |zᵢ| and let p count its positive entries. The absolute sum at the predecessor z − 1 is a + n − 2p. The least feasible translate is characterized by a ≤ B and B + 2p < a + n.

**Definition 1.4 (The prefix recurrence).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.D`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

The state (s, r, a, p) records coordinate sum, weighted residue, absolute sum and positive entry count. At length zero the state (0, 0, 0, 0) has count one and every other state has count zero. At length i, for each integer v with |v| ≤ B − a, add the old count to (s + v, r + iv, a + |v|, p + [v > 0]), reducing r modulo n. Distinct prefixes that reach the same state contribute separately.

**Definition 1.5 (The terminal sum).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.terminalSum`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.terminalSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Write E(n, k) for the sum of Dₙ(nt, Tt − kS mod n, a, p) over integers t with |t| ≤ k, natural numbers a ≤ B and p ≤ n, and the strict inequality B + 2p < a + n. Each terminal vector recovers t from its coordinate sum, then d by subtracting t from every coordinate.

**Theorem 1.6 (Finite cardinality in every dilation).**

$$\forall n,k \in \mathbb{N}, n \geq 3 \implies (\operatorname{Finite}\left(X_{n,k}\right) \land \operatorname{card}\left(X_{n,k}\right)=E\left(n, k\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.latticePointCount_terminalSum` (`✓ std3`). ∎

*Resolves.* `Problems/olairez-2026-dihedral-permutohedron-lattice-points` (proved) by `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.latticePointCount_terminalSum`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"olairez-2026-dihedral-permutohedron-lattice-points","declaration_gid":"D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.latticePointCount_terminalSum","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

Every source point corresponds to one terminal prefix of length n, and every such prefix recovers one source point. The sum counts the prefixes with multiplicity across states. Taking k = 1 gives the undilated count, and k = 0 gives the singleton at the origin. This resolves the lattice-point alternative of Question 6.1. An explicit Ehrhart coefficient formula remains open here.

On the named input fourOneInput = (4, 1), kernel evaluation counts 22 occurrences passing the terminal filter. An anonymous application of the cardinality theorem and the recurrence identity gives 22 points in the original source lattice.

**Definition 1.7 (Four coordinates at unit dilation).**

Lean statement: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.fourOneInput`

*Formalization.* `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.fourOneInput` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Olairez (2026). *Triangulation, Volume, and Symmetries of a Dihedral Group Analogue of the Permutohedron*. DOI: [10.48550/arXiv.2610.28672](https://doi.org/10.48550/arXiv.2610.28672). URL: <https://arxiv.org/html/2610.28672v2#S6.Thmquestion2>.

*Commentary.*

The input pair (4, 1) gives the coordinate count and dilation for the anonymous checker application.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.Coset`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.D`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.IsFirst`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.SourcePoints`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.fourOneInput`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.latticePointCount_terminalSum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/Permutohedra/OlairezCount.terminalSum`
- Dependency: [D5/S3/Combinatorics/Geometry/Permutohedra/OlairezWrapHull](OlairezWrapHull.md)
