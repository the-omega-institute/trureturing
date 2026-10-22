# The Original Vacuum Coefficient And Nonexactness

## Abstract

The actual original vacuum is closed, and its tensor coefficient excludes preimages in the entire original State.

D is arbitrary original LatticeData: finite rank, an integral symmetric Gram matrix and even diagonal entries, with no positivity or nondegeneracy premise. H is any complex matrix on Fin(D.rank), not necessarily symmetric or an inverse. State(D) remains the original Carrier(D) tensor over Complex with Fock(Complex). The vector V(D) is exactly Finsupp.single zero-charge constant-polynomial-one tensor the actual BcGhostFockSupport.vacuum. No charge, vacuum or intercept is replaced.

The ghost linear functional extracts the empty finite-subset coefficient. The matter linear functional extracts the zero exponent-vector coefficient of the polynomial at charge zero. Their bilinear product is extended through the original algebraic tensor universal property: epsilon is TensorProduct.map of the two coefficient linear maps followed by TensorProduct.lid on Complex tensor Complex. Consequently epsilon(u tensor g) is the constant coefficient of u(0) times g(empty). This is complex-linear, not a conjugate-linear pairing or a Hilbert-space completion.

**Theorem 1.1 (The actual zero-charge ground vacuum is closed).**

$$\forall D, H, \operatorname{Q}\left(D, H, \operatorname{V}\left(D\right)\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass.vacuum_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The exact original telescope is (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) Complex). The conclusion is Q D H (vacuumVector D)=0, without Gram inverse, rank, positivity, nilpotence, grading or highest-weight assumptions.

For each actual normalSummand(i,j,k,m-k) at m>=-1, the rightmost neutral mode is nonnegative: m-k>=0 when k<0, and k>=0 in the other normal-order branch. Positive modes annihilate constant polynomial one by the original frequency-bound supplier; the zero mode annihilates charge zero by the actual integral bilinear form. Thus every normal summand kills the matter ground vector, including m=-1 and m=0. The exact state-dependent sugawaraMode_interval_sum preserves the matrix H(i,j) and the original inverse-two factor.

When n>=-1, the matter ground calculation and the existing BcGhostVacuum.L_vacuum_annihilation give A_n V=0. The ghost stress supplier includes its weighted n=-1 boundary: the unweighted term b(-2)c(1)Omega need not vanish, but its coefficient n-k is zero. When n<-1, c(-n) is an actual annihilator and kills Omega. The negative N branch is G(n) composed with C(-n), so it also kills V. The order is never swapped. Finally A_finite at V licenses the finite sum of these original A terms.

**Theorem 1.2 (The vacuum coefficient annihilates every original charge image).**

$$\forall D, H, state, \operatorname{epsilon}\left(D, \operatorname{Q}\left(D, H, state\right)\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass.epsilon_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The original telescope adds (state : State D) to arbitrary D and H. The conclusion epsilon D (Q D H state)=0 covers every original algebraic tensor superposition, every charge sector and all finite-subset ghost states. It is not restricted by ghost number, energy or a fixed mode bound.

On a ghost basis single(S,a), signed insertion either gives zero or a scalar multiple of single(insert i S,1); insert i S is never empty. Finite Finsupp induction therefore gives epsilon_g create_i=0 on every ghost input over arbitrary CommRing K. For m<=-2, both actual normalPair branches have a creator on the left: b(m+k) when m+k<=-2, and otherwise c(-k), since k>=1. The swapped branch retains its minus sign. The real L_interval_sum at the specific input g makes epsilon_g(L_m g)=0; no operator-valued global finite-support assertion is used.

For negative matter mode m, every actual normal summand has a negative oscillator on the left. Its exact multiplication variable is X(i,(-k-1).toNat) when k<0; otherwise m-k<0 and the leftmost variable is X(j,(-(m-k)-1).toNat). The constant coefficient of X times any polynomial vanishes. Original neutralMode_single preserves charge, so nonzero charges cannot contribute and Finsupp induction extends the calculation to arbitrary matter input. The positive derivative index remains (j,(k-1).toNat); no index shift is introduced. The actual finite interval and both original scalar factors are retained.

In A_n=C(-n) composed with M(n)+(1/2)N_n, n>=-1 has a leftmost c creator in the ghost coefficient of both terms. For n<-1, the matter coefficient of M(n) vanishes, while N_n has the negative ghost stress L_n on the left and is killed on every input. The tensor map formulas give epsilon A_n=0 on pure tensors; tensor induction extends it to the entire State. A_finite at that exact state licenses transporting epsilon through the single original Q finsum. Q is not split into separately unlicensed matter and ghost infinite sums.

**Theorem 1.3 (The actual vacuum coefficient is normalized to one).**

$$\forall D, \operatorname{epsilon}\left(D, \operatorname{V}\left(D\right)\right)=1$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass.epsilon_vacuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

This is the direct coefficient calculation for the actual zero-charge constant-one ground vector and single(empty,1) ghost vacuum. Its exact telescope contains only D. It is a consumed bind-only normalization helper for vacuum_not_mem_range, not a separate new mathematical construction or a finite certified instance.

**Theorem 1.4 (No original algebraic state is a vacuum preimage).**

$$\forall D, H, \neg(\operatorname{V}\left(D\right) \in \operatorname{range}\left(\operatorname{Q}\left(D, H\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass.vacuum_not_mem_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

For every original D and arbitrary H, vacuumVector D does not belong to LinearMap.range(Q D H). A purported preimage state would give epsilon(Q state)=0 and epsilon(V)=1. The contradiction excludes preimages in the entire original State, not merely within a chosen graded sector or finite truncation.

For the cohomology interpretation only, additionally assume H times gramComplex(D)=identity, gramComplex(D) times H=identity, and rank(D)=26. Reuse the existing original all-state theorem LatticeBcGhostBrstNilpotence.nilpotent with BOTH inverses and rank26. Its Q squared equals zero puts range Q in ker Q. The closed vector V then represents a nonzero element in ker Q modulo range Q; equivalently the restriction of epsilon descends and takes this class to one. This passage uses mathlib LinearMap.range_le_ker_iff and the Submodule.Quotient.mk_eq_zero criterion. No renamed nilpotence, range-kernel or quotient theorem is retained as a new D5 result.

This class interpretation is ungraded. A ghost-number commutator alone does not compute cohomology or identify all degree components; the independent ghost-number line is not a premise here. The full BRST cohomology, no-ghost theorem, physical spectrum, string theory and AdS/CFT goal remain open. No positivity, physical realization, literature novelty or holographic correspondence is asserted.

The derivation is assessed as repo-derived. The existing Eholzer-Feher-Honecker ghost note supplies convention provenance, and the existing Bakalov-Kac lattice note supplies carrier and conformal background. Neither note is cited as already proving nonexactness of this repository's original Q. No additional literature identity or unverified source locator is introduced.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass.epsilon_Q`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass.epsilon_vacuum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass.vacuum_closed`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostBrstVacuumClass.vacuum_not_mem_range`
- Dependency: [D5/S3/VertexAlgebra/BcGhostVacuum](BcGhostVacuum.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstCharge](LatticeBcGhostBrstCharge.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraVirasoro](LatticeSugawaraVirasoro.md)
