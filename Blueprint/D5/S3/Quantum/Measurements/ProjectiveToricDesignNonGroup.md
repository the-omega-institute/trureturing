# A projective toric design without additive closure

## Abstract

An identity-containing projective toric two-design in dimension 27 satisfies the MUB overlap condition without being a group.

**Definition 1.1 (The second moment condition).**

$$\forall (d: \mathbb{N}), (\forall (X: \operatorname{Finset}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})\right)), ((\operatorname{D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup.design2}\left(X\right)) \Leftrightarrow (\forall (a_{1}: \operatorname{Fin}\left(d\right)), (\forall (a_{2}: \operatorname{Fin}\left(d\right)), (\forall (b_{1}: \operatorname{Fin}\left(d\right)), (\forall (b_{2}: \operatorname{Fin}\left(d\right)), (((((a_{1} = b_{1}) \land (a_{2} = b_{2})) \lor ((a_{1} = b_{2}) \land (a_{2} = b_{1}))) \to (\sum_{\varphi \in X} ((\operatorname{Subtype.val}\left(\operatorname{Real.Angle.toCircle}\left((((\varphi\left(a_{1}\right)) + (\varphi\left(a_{2}\right))) - (\varphi\left(b_{1}\right))) - (\varphi\left(b_{2}\right))\right)\right): \mathbb{C})) = (\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(X\right)\right): \mathbb{C}))) \land ((\neg (((a_{1} = b_{1}) \land (a_{2} = b_{2})) \lor ((a_{1} = b_{2}) \land (a_{2} = b_{1})))) \to (\sum_{\varphi \in X} ((\operatorname{Subtype.val}\left(\operatorname{Real.Angle.toCircle}\left((((\varphi\left(a_{1}\right)) + (\varphi\left(a_{2}\right))) - (\varphi\left(b_{1}\right))) - (\varphi\left(b_{2}\right))\right)\right): \mathbb{C})) = (0: \mathbb{C}))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.design2` (`✓ std3`).

*Citation.* Joseph T. Iosue, T. C. Mooney, Adam Ehrenberg, Alexey V. Gorshkov (2024). *Projective toric designs, quantum state designs, and mutually unbiased bases*. DOI: [10.22331/q-2024-12-03-1546](https://doi.org/10.22331/q-2024-12-03-1546). URL: <https://arxiv.org/abs/2311.13479v3>.

*Commentary.*

The angles lie in Real.Angle, the additive circle ℝ/(2πℤ). Real.Angle.toCircle sends an angle to its unit complex exponential; Subtype.val includes that circle element in ℂ. For each four coordinate indices, the sum is the complex cast of the cardinality when the two index pairs agree as multisets, and is complex zero otherwise. This is the uniformly weighted second moment equation multiplied by the cardinality, from main.tex lines 198–206, equation eq:repr-proj-toric. The predicate itself allows every natural d and every finite X, including the empty set, and does not impose a zero first coordinate.

**Definition 1.2 (The unnormalized overlap condition).**

$$\forall (d: \mathbb{N}), (\forall (X: \operatorname{Finset}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})\right)), ((\operatorname{D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup.mubOverlap}\left(X\right)) \Leftrightarrow (\forall (\varphi: (\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})), ((\varphi \in X) \to (\forall (\theta: (\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})), ((\theta \in X) \to ((\varphi \ne \theta) \to ((\left\lVert \sum_{(j: \operatorname{Fin}\left(d\right))} ((\operatorname{Subtype.val}\left(\operatorname{Real.Angle.toCircle}\left((\varphi\left(j\right)) - (\theta\left(j\right))\right)\right): \mathbb{C})) \right\rVert^{2} = (0: \mathbb{R})) \lor (\left\lVert \sum_{(j: \operatorname{Fin}\left(d\right))} ((\operatorname{Subtype.val}\left(\operatorname{Real.Angle.toCircle}\left((\varphi\left(j\right)) - (\theta\left(j\right))\right)\right): \mathbb{C})) \right\rVert^{2} = (\operatorname{Nat.cast}\left(d\right): \mathbb{R}))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.mubOverlap` (`✓ std3`).

*Citation.* Joseph T. Iosue, T. C. Mooney, Adam Ehrenberg, Alexey V. Gorshkov (2024). *Projective toric designs, quantum state designs, and mutually unbiased bases*. DOI: [10.22331/q-2024-12-03-1546](https://doi.org/10.22331/q-2024-12-03-1546). URL: <https://arxiv.org/abs/2311.13479v3>.

*Commentary.*

For distinct phase functions φ and θ in X, the squared complex norm of their exponential sum is either real zero or the real cast of d. The sum ranges over all j in Fin d. This is equation eq:toric-angle in main.tex lines 654–657. There is no positivity or cardinality hypothesis in this predicate.

**Definition 1.3 (The subgroup conjecture with the identity included).**

$$(\operatorname{D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup.claim}) \Leftrightarrow (\forall (d: \mathbb{N}), (((0: \mathbb{N}) < d) \to (\forall (X: \operatorname{Finset}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})\right)), ((\forall (\varphi: (\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})), ((\varphi \in X) \to (\varphi\left((0: \operatorname{Fin}\left(d\right))\right) = (0: \operatorname{Real.Angle})))) \to ((\operatorname{Finset.card}\left(X\right) = d^{2}) \to ((\operatorname{D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup.design2}\left(X\right)) \to ((\operatorname{D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup.mubOverlap}\left(X\right)) \to ((\operatorname{Function.const}\left(\operatorname{Fin}\left(d\right), (0: \operatorname{Real.Angle})\right) \in X) \to (\exists (H: \operatorname{AddSubgroup}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})\right)), ((\operatorname{SetLike.coe}\left(H\right): \operatorname{Set}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})\right)) = (\operatorname{SetLike.coe}\left(X\right): \operatorname{Set}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Joseph T. Iosue, T. C. Mooney, Adam Ehrenberg, Alexey V. Gorshkov (2024). *Projective toric designs, quantum state designs, and mutually unbiased bases*. DOI: [10.22331/q-2024-12-03-1546](https://doi.org/10.22331/q-2024-12-03-1546). URL: <https://arxiv.org/abs/2311.13479v3>.

*Commentary.*

The conjecture in main.tex lines 783–788 says that a projective toric two-design of size d² satisfying the overlap condition must be a subgroup. Here d is positive, the representative of every projective point has coordinate zero equal to zero, and the design is additionally required to contain the zero phase function. The representative slice identifies the projective torus with the additive subgroup {0} × T^(d−1) of T^d, so the conclusion asks for an additive subgroup of the full phase-function space with carrier exactly X. The condition that zero belong to X weakens the universal assertion in the source; it excludes a failure caused solely by translating a group away from its identity. Positivity ensures that coordinate zero belongs to Fin d. SetLike.coe explicitly gives both carriers in the concluding equality.

**Theorem 1.4 (A non-group design with 729 points).**

$$\neg (\forall (d: \mathbb{N}), (((0: \mathbb{N}) < d) \to (\forall (X: \operatorname{Finset}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})\right)), ((\forall (\varphi: (\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})), ((\varphi \in X) \to (\varphi\left((0: \operatorname{Fin}\left(d\right))\right) = (0: \operatorname{Real.Angle})))) \to ((\operatorname{Finset.card}\left(X\right) = d^{2}) \to ((\operatorname{D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup.design2}\left(X\right)) \to ((\operatorname{D5.S3.Quantum.Measurements.ProjectiveToricDesignNonGroup.mubOverlap}\left(X\right)) \to ((\operatorname{Function.const}\left(\operatorname{Fin}\left(d\right), (0: \operatorname{Real.Angle})\right) \in X) \to (\exists (H: \operatorname{AddSubgroup}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})\right)), ((\operatorname{SetLike.coe}\left(H\right): \operatorname{Set}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})\right)) = (\operatorname{SetLike.coe}\left(X\right): \operatorname{Set}\left((\operatorname{Fin}\left(d\right) \to \operatorname{Real.Angle})\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.result` (`✓ std3`). ∎

*Resolves.* `Problems/iosue-mooney-ehrenberg-gorshkov-2024-projective-toric-design-subgroup-conjecture` (refuted) by `D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"iosue-mooney-ehrenberg-gorshkov-2024-projective-toric-design-subgroup-conjecture","declaration_gid":"D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Joseph T. Iosue, T. C. Mooney, Adam Ehrenberg, Alexey V. Gorshkov (2024). *Projective toric designs, quantum state designs, and mutually unbiased bases*. DOI: [10.22331/q-2024-12-03-1546](https://doi.org/10.22331/q-2024-12-03-1546). URL: <https://arxiv.org/abs/2311.13479v3>.

*Commentary.*

Index the 27 coordinates by x in (ZMod 3)³, using the base-three equivalence from Fin 27, which sends coordinate zero to the zero vector. Let χ be ZMod.stdAddChar and let an element k of ZMod 3 determine the angle 2π times the real cast of k.val, divided by 3, modulo 2π. This map is additive and injective, and its complex exponential is χ(k). Use 27 symmetric matrices Mᵢ over ZMod 3. In order i = 0,…,26, their upper triangular entries (M₀₀,M₀₁,M₀₂,M₁₁,M₁₂,M₂₂) are (0,0,0,0,0,0), (0,1,2,1,2,0), (0,2,1,2,1,0), (0,0,2,2,1,2), (1,1,1,0,2,2), (1,2,2,0,2,1), (0,0,1,1,2,1), (2,1,1,0,1,2), (2,2,2,0,1,1), (2,0,2,2,0,0), (1,2,0,1,2,2), (1,2,1,2,0,1), (1,1,2,2,2,2), (2,2,0,2,2,0), (0,2,2,1,0,1), (0,1,0,0,0,1), (2,0,1,0,2,0), (1,0,0,2,2,1), (1,0,1,1,0,0), (2,1,2,1,0,2), (2,1,0,2,1,1), (0,2,0,0,0,2), (2,0,0,1,1,2), (1,0,2,0,1,0), (2,2,1,1,1,1), (0,1,1,2,0,2), and (1,1,0,1,1,0). For each i in Fin 27 and b in (ZMod 3)³, define the phase function by the angle of xᵀMᵢx + b·x, and let X be the set of these functions. Finite arithmetic verifies symmetry, det(Mᵢ − Mⱼ) ≠ 0 for i ≠ j, and that no listed matrix equals M₁ + M₃.

Character orthogonality gives Σₓχ(w·x) = 27 for w = 0 and zero otherwise. Indeed, for w ≠ 0, the character x ↦ χ(w·x) is nontrivial: if it were trivial, injectivity of χ would force w·x = 0 for every x and hence w = 0. Writing q(x) = xᵀMx + b·x for a symmetric matrix M, expansion gives q(h + y) − q(y) = q(h) + (2My)·h = q(h) + (2Mh)·y. When det M ≠ 0, the squared norm of Σₓχ(q(x)) is its product with the conjugate sum. Reindex that double sum by x = h + y and use the shift identity. The inner sum becomes Σᵧχ((2Mh)·y). Since M is invertible and 2 is nonzero in ZMod 3, only h = 0 contributes, giving squared norm 27.

For every nonzero g, the map i ↦ Mᵢg is injective: equality for distinct i and j would put g in the kernel of the invertible difference Mᵢ − Mⱼ. Both its domain and codomain have 27 elements, so it is bijective. Also, a symmetric quadratic polynomial xᵀAx + b·x determines A and b uniquely as functions on (ZMod 3)³. Subtracting its values at x and y from its value at x + y determines 2xᵀAy. Since 2 ≠ 0, equality of two such polynomials gives equality of their bilinear forms, hence A = B; the remaining linear terms then give b = c.

For two distinct parameter pairs (i,b) and (k,c), equal matrix indices leave the nonzero linear form (b − c)·x, whose character sum vanishes. Different matrix indices leave the symmetric quadratic form with matrix Mᵢ − Mₖ and linear term b − c. Its matrix is invertible, so the preceding squared-norm calculation gives 27. Thus every two distinct parameter pairs have squared exponential overlap zero or 27.

For the second moment, sum first over the linear parameter c. Set s = a₁ + a₂ − b₁ − b₂ in (ZMod 3)³. If the two index pairs agree as multisets, every exponent is zero and the double sum is 729. Otherwise the double sum factors as the sum of the quadratic phases over i times 27 when s = 0, or times zero when s ≠ 0, by character orthogonality. In the remaining case s = 0, symmetry gives the quadratic phase 2(a₁ − b₁)ᵀMᵢ(a₁ − b₂). Both a₁ − b₁ and a₁ − b₂ are nonzero, since either equality would make the two pairs agree. Reindex the sum over i by the bijection i ↦ Mᵢ(a₁ − b₂). It becomes the character sum of the nonzero linear form 2(a₁ − b₁)·y and is zero. This proves both cases of the required moment identity.

The phase functions belonging to distinct parameter pairs are distinct. If two were equal, injectivity of the angle map would make their exponent polynomials equal at every x. Their overlap sum would then be 27, with squared norm 729, contradicting the values zero and 27 just obtained. Every phase function vanishes at coordinate zero because the corresponding vector x is zero. Consequently X has 27 · 27 = 729 = 27² elements. Reindexing by the coordinate equivalence and using additivity of the angle map transfers the moment identity to design2(X), and transfers the exponential overlap calculation to mubOverlap(X). The zero matrix M₀ with zero linear term gives the zero phase function in X.

Finally, suppose an additive subgroup had carrier X. It would contain the phase functions with parameters (1,0) and (3,0), hence their sum. That sum would be a phase function with some parameters (i,b). Injectivity of the angle map would identify its polynomial with xᵀ(M₁ + M₃)x. Uniqueness of symmetric quadratic and linear coefficients would force Mᵢ = M₁ + M₃, contradicting the finite matrix calculation. Thus X has no such subgroup carrier. Applying the universal assertion to d = 27 and this X contradicts that fact. The conclusion concerns these identity-containing representatives; it makes no assertion about whether a different choice of anchoring of a complete set of mutually unbiased bases yields a group, or about dimension six.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.design2`
- Truth anchor: `D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.mubOverlap`
- Truth anchor: `D5/S3/Quantum/Measurements/ProjectiveToricDesignNonGroup.result`
