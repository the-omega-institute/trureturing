# Generic Matrix Irreducibility

## Abstract

Full generic determinant and fraction-field characteristic polynomial irreducibility in every positive size.

For every natural n with 0<n, R is exactly MvPolynomial (Fin n x Fin n) Complex, Y is exactly Matrix.mvPolynomialX (Fin n) (Fin n) Complex, and K is FractionRing R. There are n squared independent coefficient variables. Both theorems include n=1. The determinant conclusion lives in R; the characteristic-polynomial conclusion lives in Polynomial K after mapping coefficients by algebraMap R K. No matrix normality, covariance, diagonalizability, chosen normal form or extra target premise is imposed.

**Theorem 1.1 (The full generic determinant).**

$$\forall n: Nat, 0 < n \implies \operatorname{Irreducible}(\operatorname{det}(\operatorname{mvPolynomialX}(\operatorname{Fin}(n), \operatorname{Fin}(n), Complex)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.det_generic_irreducible` (`✓ std3`). ∎

*Citation.* mathlib-initiative (2026). *Auxiliary matrix determinant irreducibility, clean Lean release*. URL: <https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1/blob/c6d86a8bd52065aafb8251fa1cdcd55b609743ef/clean-code/release/RepresentationTheory/AuxiliaryMatrixDeterminantIrreducibility.lean>.

*Commentary.*

For positive n, the determinant of the generic matrix is irreducible in R. The induction starts with the one-by-one determinant. In the induction step, expansion along the first row is linear in the upper-left variable, and its coefficient is the lower-right minor. The minor is irreducible by the induction hypothesis after injective renaming.

The proof inducts on positive size. The singleton determinant is one variable. For the induction step, expansion along the first row is linear in the upper left variable. The coefficient is the lower right minor, irreducible by the induction hypothesis and injective renaming. Neither that minor nor the remaining row sum contains the upper left variable. If the minor divided that sum, evaluation of the first row at a single nonzero second entry would force divisibility of a different irreducible minor and hence association. The first minor actually depends on the second diagonal variable: identity evaluation gives one, and setting that entry to zero gives zero. The other minor omits that variable. Association would preserve this variable dependence, a contradiction. The resulting relative primality is the input of irreducible_mul_X_add.

The key intermediate is minor00_isRelPrime. Its two-minor specialization and the variable-dependence contradiction establish the relative primality needed for the determinant induction, and that irreducibility supplies the starting point for the characteristic-polynomial argument below.

**Theorem 1.2 (The characteristic polynomial over the exact fraction field).**

$$\forall n: Nat, 0 < n \implies \operatorname{Irreducible}(\operatorname{map}(\operatorname{algebraMap}(\operatorname{MvPolynomial}(\operatorname{Fin}(n)\times\operatorname{Fin}(n), Complex), \operatorname{FractionRing}(\operatorname{MvPolynomial}(\operatorname{Fin}(n)\times\operatorname{Fin}(n), Complex))), \operatorname{charpoly}(\operatorname{mvPolynomialX}(\operatorname{Fin}(n), \operatorname{Fin}(n), Complex))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.charpoly_generic_irreducible_fractionRing` (`✓ std3`). ∎

*Citation.* Matej Brešar and Špela Špenko (2013). *Functional identities of one variable*. URL: <https://arxiv.org/html/1307.2260v1#S2>.

*Commentary.*

For the complex coefficient ring, first extend the determinant prime to Polynomial R by Polynomial.prime_C_iff. Define a coefficient evaluation sending each y(i,j) to delta(i,j) times t minus y(i,j), and extend it to a ring homomorphism fixing t. Equality on constants and every generator proves that applying it twice is the identity. The resulting ring equivalence sends the constant determinant to det(tI-Y), which is Matrix.charpoly Y. Irreducibility transports through that equivalence. Matrix.charpoly_monic and Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map then give the exact fraction-field result. The coefficient ring is a unique factorization domain and hence integrally closed.

The determinant prime in R becomes prime in Polynomial R. The coefficient substitution sending y(i,j) to delta(i,j) times t minus y(i,j) extends to a ring homomorphism fixing t. Its application twice fixes every coefficient and t, so it is an involution. The resulting ring equivalence carries the constant determinant to det(tI-Y), which is Matrix.charpoly Y, and therefore transports irreducibility. Gauss's lemma then transfers irreducibility from Polynomial R to Polynomial K; monicity identifies the mapped polynomial with the stated fraction-field characteristic polynomial.

For every positive n, the determinant over R and the mapped characteristic polynomial over K are therefore irreducible. These conclusions provide the generic irreducibility input for the sections 2–3 argument toward Lemma 3.2 at equation (320.6) inside theorem 320.1 of AURIC_C128_ORTHOGONAL_TRACE_AND_CORNER_RELATIONS_CONTINUATION. They do not by themselves establish the commuting quadratic trace normal form: the generic centralizer, the global quadratic reconstruction for every complex-bilinear B, Hermitian complexification, real descent, 273/274, direct sums, classical sources, and the complete downstream statements at 320/343/359/361/388 remain separate mathematical obligations.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.charpoly_generic_irreducible_fractionRing`
- Truth anchor: `D5/S3/Quantum/Algebra/GenericMatrixIrreducibility.det_generic_irreducible`
