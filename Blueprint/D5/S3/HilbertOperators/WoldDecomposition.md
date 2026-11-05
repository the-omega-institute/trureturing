# Finite Wold decomposition and residual equivalence

## Abstract

Finite wandering decompositions and the actual residual isometry for arbitrary real or complex inner product spaces.

**Definition 1.1 (wanderingSub).**

$$\forall (k: Type*), [\operatorname{RCLike}(k)] \forall (H: Type*), [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(k, H)] \forall (V: \operatorname{LinearIsometry}(k, H, H)), \operatorname{W}(V) = \operatorname{Orthogonal}(\operatorname{Range}(V))$$

*Formalization.* `D5/S3/HilbertOperators/WoldDecomposition.wanderingSub` (`✓ std3`).

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Finite Wold decomposition and residual isometry*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/WoldDecomposition.lean>.

*Commentary.*

W(V) is wanderingSub V, the orthogonal complement of the linear range of V. Scalar and space universes are independent. No completeness is needed for this definition.

**Theorem 1.2 (exists_wold_decomposition).**

$$\forall (k: Type*), [\operatorname{RCLike}(k)] \forall (H: Type*), [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(k, H)] [\operatorname{CompleteSpace}(H)] \forall (V: \operatorname{LinearIsometry}(k, H, H)), \forall (x: H), \forall (n: Nat), \exists (w: Nat \to H), \exists (y: H), (\forall (j: Nat), \operatorname{w}(j) \in \operatorname{W}(V)) \land ((\forall (j: Nat), (n \leq j) \Rightarrow (\operatorname{w}(j) = 0)) \land ((x = (\operatorname{SumRange}(n, \operatorname{PowerWanderingFamily}(V, w)))+(\operatorname{PowerApply}(V, n, y))) \land (\operatorname{NormSquare}(x) = (\operatorname{SumRange}(n, \operatorname{NormSquareFamily}(w)))+(\operatorname{NormSquare}(y)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/WoldDecomposition.exists_wold_decomposition` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Finite Wold decomposition and residual isometry*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/WoldDecomposition.lean>.

*Commentary.*

For every x and every natural n, including zero, a single family w and remainder y realize all clauses together. Every w j lies in W(V), w j vanishes for j >= n, and x is the sum over j in Finset.range n of (V^j)(w j), plus (V^n)y. The exact conjunction is coefficient membership AND (tail support AND (reconstruction AND squared norm identity)), inside the same existential w,y. For these SAME witnesses, norm(x)^2 is the sum of norm(w j)^2 over j < n plus norm(y)^2. SumRange(n,f) denotes that finite sum; PowerApply(V,j,z) denotes (V^j)z; PowerWanderingFamily(V,w) denotes j mapped to (V^j)(w j). Completeness gives the orthogonal range splitting. The source induction splits the old remainder and updates its coefficient family at n, then wold_norm_sq supplies the norm equation for that family and remainder. No separability, finite dimension or ambient surjectivity is required.

**Theorem 1.3 (wold_norm_sq).**

$$\forall (k: Type*), [\operatorname{RCLike}(k)] \forall (H: Type*), [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(k, H)] \forall (V: \operatorname{LinearIsometry}(k, H, H)), \forall (n: Nat), \forall (w: Nat \to H), \forall (hw: \forall (j: Nat), \operatorname{w}(j) \in \operatorname{W}(V)), \forall (y: H), \forall (x: H), (x = (\operatorname{SumRange}(n, \operatorname{PowerWanderingFamily}(V, w)))+(\operatorname{PowerApply}(V, n, y))) \Rightarrow (\operatorname{NormSquare}(x) = (\operatorname{SumRange}(n, \operatorname{NormSquareFamily}(w)))+(\operatorname{NormSquare}(y)))$$

*Proof.* Machine-checked in Lean as `D5/S3/HilbertOperators/WoldDecomposition.wold_norm_sq` (`✓ std3`). ∎

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Finite Wold decomposition and residual isometry*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/WoldDecomposition.lean>.

*Commentary.*

For any n, family w with every coefficient in W(V), y and x satisfying exactly the reconstruction equation, norm(x)^2 equals the sum over j in Finset.range n of norm(w j)^2 plus norm(y)^2. NormSquareFamily(w) is j mapped to norm(w j)^2. This theorem needs neither completeness nor the support condition. The proof of exists_wold_decomposition applies it to the SAME w and y constructed there. The source norm induction groups the terminal wandering coefficient with V y and uses orthogonality and isometry.

**Definition 1.4 (residualSub).**

$$\forall (k: Type*), [\operatorname{RCLike}(k)] \forall (H: Type*), [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(k, H)] \forall (V: \operatorname{LinearIsometry}(k, H, H)), \operatorname{R}(V) = \operatorname{InfPowerRanges}(V)$$

*Formalization.* `D5/S3/HilbertOperators/WoldDecomposition.residualSub` (`✓ std3`).

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Finite Wold decomposition and residual isometry*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/WoldDecomposition.lean>.

*Commentary.*

R(V) is residualSub V, the infimum over all natural m of the linear range of V^m. Membership means membership in every actual power range. No closure or completeness assumption is added.

**Definition 1.5 (woldResidualEquiv).**

$$\forall (k: Type*), [\operatorname{RCLike}(k)] \forall (H: Type*), [\operatorname{NormedAddCommGroup}(H)] [\operatorname{InnerProductSpace}(k, H)] \forall (V: \operatorname{LinearIsometry}(k, H, H)), (\operatorname{LinearIsometricEquiv}(\operatorname{U}(V), \operatorname{R}(V), \operatorname{R}(V))) \land (\forall (z: \operatorname{R}(V)), \operatorname{Coe}(\operatorname{U}(V, z)) = \operatorname{V}(\operatorname{Coe}(z)))$$

*Formalization.* `D5/S3/HilbertOperators/WoldDecomposition.woldResidualEquiv` (`✓ std3`).

*Citation.* Meta Platforms, Inc. and affiliates (2026). *Finite Wold decomposition and residual isometry*. URL: <https://github.com/facebookresearch/atlas-lean/blob/a60759060b5616df0d5775b42da4d337719feb32/MathlibExt/Analysis/InnerProductSpace/WoldDecomposition.lean>.

*Commentary.*

U(V) is woldResidualEquiv V, a linear isometric equivalence R(V) to itself over k. Its forward function is literally the linear restriction of V, so after subtype coercion U(V)z = Vz for every z. Invariance shifts the power-range witnesses. For surjectivity take a V-preimage of a residual point; injectivity of V and the next power-range witness put that preimage in every power range. The equivalence packages this bijection and preservation of inner products. Completeness is absent from its full telescope. These finite and residual statements give no infinite direct-sum or coefficientwise uniqueness theorem.

## References

- Truth anchor: `D5/S3/HilbertOperators/WoldDecomposition.exists_wold_decomposition`
- Truth anchor: `D5/S3/HilbertOperators/WoldDecomposition.residualSub`
- Truth anchor: `D5/S3/HilbertOperators/WoldDecomposition.wanderingSub`
- Truth anchor: `D5/S3/HilbertOperators/WoldDecomposition.woldResidualEquiv`
- Truth anchor: `D5/S3/HilbertOperators/WoldDecomposition.wold_norm_sq`
