# Generic Matrix Irreducibility

## Abstract

Full generic determinant and fraction-field characteristic polynomial irreducibility in every positive size.

For every natural n with 0<n, R is exactly MvPolynomial (Fin n x Fin n) Complex, Y is exactly Matrix.mvPolynomialX (Fin n) (Fin n) Complex, and K is FractionRing R. There are n squared independent coefficient variables. Both theorems include n=1. The determinant conclusion lives in R; the characteristic-polynomial conclusion lives in Polynomial K after mapping coefficients by algebraMap R K. No matrix normality, covariance, diagonalizability, chosen normal form or extra target premise is imposed.

**Theorem 1.1 (The full generic determinant).**

$$\forall n: Nat, 0 < n \implies \operatorname{Irreducible}(\operatorname{det}(\operatorname{mvPolynomialX}(\operatorname{Fin}(n), \operatorname{Fin}(n), Complex)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.det_generic_irreducible` (`✓ std3`). ∎

*Citation.* mathlib-initiative (2026). *Auxiliary matrix determinant irreducibility, clean Lean release*. URL: <https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1/blob/c6d86a8bd52065aafb8251fa1cdcd55b609743ef/clean-code/release/RepresentationTheory/AuxiliaryMatrixDeterminantIrreducibility.lean>.

*Commentary.*

The clean Apache-2.0 release theorem det_auxiliaryMatrix_irreducible_of_pos is transplanted faithfully. Its private generic matrix is definitionally Matrix.mvPolynomialX. The exact immutable revision, source digest, full license and NOTICE chain are specified in the library note. Only imports, namespace, source attribute and the public name/signature are adapted; the unused reflexive equality is omitted. Retire this proof when this repository's own pinned Mathlib supplies an equivalent exact theorem, then replace its live uses directly. There is no source novelty claim.

The proof inducts on positive size. The singleton determinant is one variable. For the induction step, expansion along the first row is linear in the upper left variable. The coefficient is the lower right minor, irreducible by the induction hypothesis and injective renaming. Neither that minor nor the remaining row sum contains the upper left variable. If the minor divided that sum, evaluation of the first row at a single nonzero second entry would force divisibility of a different irreducible minor and hence association. The first minor actually depends on the second diagonal variable: identity evaluation gives one, and setting that entry to zero gives zero. The other minor omits that variable. Association would preserve this variable dependence, a contradiction. The resulting relative primality is the live input of irreducible_mul_X_add.

The substantive intermediate is minor00_isRelPrime, whose two-minor specialization and variable-dependence contradiction are not supplied by coefficient normalization. The determinant theorem is consumed by charpoly_generic_irreducible_fractionRing in this same module. The source proof contributes mathematical content under the transplantation rule, without claiming research novelty.

**Theorem 1.2 (The characteristic polynomial over the exact fraction field).**

$$\forall n: Nat, 0 < n \implies \operatorname{Irreducible}(\operatorname{map}(\operatorname{algebraMap}(\operatorname{MvPolynomial}(\operatorname{Fin}(n)\times\operatorname{Fin}(n), Complex), \operatorname{FractionRing}(\operatorname{MvPolynomial}(\operatorname{Fin}(n)\times\operatorname{Fin}(n), Complex))), \operatorname{charpoly}(\operatorname{mvPolynomialX}(\operatorname{Fin}(n), \operatorname{Fin}(n), Complex))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.charpoly_generic_irreducible_fractionRing` (`✓ std3`). ∎

*Citation.* Matej Brešar and Špela Špenko (2013). *Functional identities of one variable*. URL: <https://arxiv.org/html/1307.2260v1#S2>.

*Commentary.*

This is the irreducibility assertion of closed Lemma 2.1, specialized to Complex with the full coefficient ring retained. No unused quotient-domain companion is introduced. The local formal bridge first extends the determinant prime to Polynomial R by Polynomial.prime_C_iff. It defines a coefficient evaluation sending each y(i,j) to delta(i,j) times t minus y(i,j), and extends it to a ring homomorphism fixing t. Equality on constants and every generator proves that applying it twice is the identity. The resulting ring equivalence sends the constant determinant to det(tI-Y), which is Matrix.charpoly Y. Irreducibility transports through that equivalence. Matrix.charpoly_monic and Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map then give the exact fraction-field result. The coefficient ring is a unique factorization domain and hence integrally closed.

After same-delivery dependency inlining, the transplanted determinant induction and its relative-primality intermediate remain on the live proof path. The substitution identities and Gauss transfer are supporting normalization and direct upstream reuse, not separate novelty or escape claims. No new standalone bind-only theorem or unused convenience declaration is retained.

Private support is consumed on the live determinant path. genMatrix and genMatrix_apply provide entry access. submatrix_eq_rename feeds minor00_eq_rename, submatrix_vars_fst_ne_zero and both minor irreducibility arguments. minor00_eq_rename feeds minor00_ne_zero, the relative-primality proof and the final step. minor00_vars and rest_vars feed irreducible_mul_X_add. vars_subset_vars_mul_left is used by rename_irreducible and the association contradiction; rename_irreducible is used twice by minor00_isRelPrime. No private helper is retained only for a promised future consumer.

The source-volume route is 389.1 and 389.2 in AURIC_C128_ORTHOGONAL_TRACE_AND_CORNER_RELATIONS_CONTINUATION. These are prerequisites for the closed Lemma 2.1 to Lemma 3.2 route used at equation 320.6 inside that volume's theorem 320.1. They do not close the full commuting quadratic trace normal form. The generic centralizer, global quadratic reconstruction for all complex bilinear B, Hermitian complexification, real descent, 273/274, direct sums, classical sources and complete 320/343/359/361/388 consumers remain unproved here. Utility is none: this is uniform ring theory, not a finite checker, numeric reduction or certified instance.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.charpoly_generic_irreducible_fractionRing`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.det_generic_irreducible`
