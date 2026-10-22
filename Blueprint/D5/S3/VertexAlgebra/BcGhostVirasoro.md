# The Original All-State Integral Ghost Virasoro Relation

## Abstract

Every pair of original ghost stress operators satisfies the full Virasoro bracket with an integer-quotient central scalar over every commutative ring.

At any universe u let K : Type u have [CommRing K]. All operators in the statement are the original BcGhostFockSupport.L acting in Module.End K (Fock K), where Fock K is the signed finite-subset algebraic carrier with no global mode cutoff. Products are endomorphism composition, rightmost first. id denotes LinearMap.id on exactly this carrier. The notation ite(test,x,y) denotes if test then x else y. The theorem assumes no Virasoro representation, central-charge relation, field, nontriviality, characteristic or inverse of six.

**Theorem 1.1 (The full original stress bracket has the exact integral central term).**

$$\forall K:Type^{u}, [\operatorname{CommRing}\left(K\right)],\ \forall m:\mathbb{Z}, \forall n:\mathbb{Z},\ \operatorname{L}\left(K, m\right)*\operatorname{L}\left(K, n\right)-\operatorname{L}\left(K, n\right)*\operatorname{L}\left(K, m\right)=(m-n:K)\cdot\operatorname{L}\left(K, m+n\right)+\operatorname{ite}\left(m+n=0, ((-13*(m^{3}-m)/6:\mathbb{Z}):K), 0\right)\cdot id$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostVirasoro.L_virasoro` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* W. Eholzer, L. Feher, A. Honecker (1997). *Ghost Systems: A Vertex Algebra Point of View*. DOI: [10.1016/S0550-3213(98)00061-3](https://doi.org/10.1016/S0550-3213(98)00061-3). URL: <https://arxiv.org/abs/hep-th/9708160>.

*Commentary.*

The complete original telescope is {K : Type u} [CommRing K] (m n : Int). Its exact conclusion is L (K := K) m * L n - L n * L m = (m-n : K) smul L(m+n) + (if m+n=0 then ((-13*(m^3-m)/6 : Int) : K) else 0) smul LinearMap.id. Division is carried out in Int before casting into K, including at negative m. The conditional is the delta(m+n=0) central term. This is the unscaled equality of full operators for every pair of integers, not a vacuum-only identity or a field-only rational-six version.

The live proof forms the defect D=L_m L_n-L_n L_m-(m-n) smul L_(m+n). Its private defect_commutes calculation uses the associative Lie bracket and the original stress-current covariance. For a family X with [L_a,X_t]=(weight*a-t) smul X_(a+t), the Jacobi expansion leaves a scalar polynomial that is zero. Using X=b with weight=1 and X=c with weight=-2 proves the actual defect commutes with every b and c mode. These weights are the covariance coefficients in this calculation. The original mode_commutant_scalar then makes D the scalar given by the empty-subset coefficient of D vacuum.

That scalar is computed, not assumed. Insertion cannot produce the empty subset, so every L_t vacuum has zero empty coordinate. Deleting a one-creator vacuum vector reaches that coordinate only at matching mode indices. Stress-current covariance and the original finite support interval therefore give (L_m(L_n vacuum)) emptyset=0 whenever m+n is nonzero. Both orders of the off-diagonal commutator have zero empty coordinate.

When n=-m and m>0, L_vacuum_annihilation kills L_m vacuum and L_vacuum_contraction computes L_m(L_(-m) vacuum) with the integer quotient -13(m^3-m)/6. At m=0 the commutator and cubic both vanish. At m<0 the reverse product is evaluated using the positive index -m. The proof first establishes 6 divides -13(m^3-m) by the six integer residue classes; Int.neg_ediv_of_dvd then justifies negating that exact integer quotient. Hence the same central scalar is obtained for negative m without an invalid sign rule for arbitrary integer division. Substituting this scalar into the ghost-End commutant equality gives the full operator bracket on every original state.

The existing eholzer1997ghost library note compares the weight-(2,-1) conventions with the conventional label central charge -26. It is acknowledged as background, not as proof of this exact ring-parametric implementation theorem. The operator construction and derivation are repository-derived. No tensor-End factorization, literature novelty, BRST cohomology, no-ghost theorem, complete physical/string result or AdS completion is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostVirasoro.L_virasoro`
- Dependency: [D5/S3/VertexAlgebra/BcGhostFockCommutant](BcGhostFockCommutant.md)
- Dependency: [D5/S3/VertexAlgebra/BcGhostVacuum](BcGhostVacuum.md)
