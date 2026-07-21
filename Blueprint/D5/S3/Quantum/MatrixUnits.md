# Finite Weyl Pairs and Matrix Units

## Abstract

Construct exact finite Weyl pairs and the matrix-unit structure of full complex matrix algebras.

The six theorems below are internal statements about explicitly constructed finite complex matrices. They do not identify an arbitrary observer window with a full matrix algebra; prime-power tensor factorization remains residual, and the general Robertson variance inequality remains residual. The no-character theorem is not upgraded to Kochen-Specker, CHSH, hidden-address locality, or a probability interpretation.

**Theorem 1.1 (The constructed finite shift and phase matrices obey the Weyl relation).**

$$\forall n>0,\quad V_nU_n=\omega_n U_nV_n,\qquad \omega_n=\exp(2\pi i/n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixUnits.qudit_weyl_relation` (`✓ std3`). ∎

*Citation.* Julian Schwinger (1960). *Unitary Operator Bases*. DOI: [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).

*Commentary.*

For every positive dimension n, omega is defined as exp(2 pi i/n), V is the permutation matrix of the canonical rotation of Fin n, and U is diagonal with entries omega^r. Lean proves VU = omega UV from these definitions. No desired commutation relation is carried as an assumption, and no observer-window generation claim is inferred.

**Theorem 1.2 (The constructed phase matrix has finite order).**

$$\forall n>0,\quad U_n^n=I_n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixUnits.qudit_phase_order` (`✓ std3`). ∎

*Citation.* Julian Schwinger (1960). *Unitary Operator Bases*. DOI: [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).

*Commentary.*

The canonical root is primitive of order n, so the explicit diagonal phase matrix satisfies U_n^n = I. This is exact finite-register algebra and does not establish prime-power tensor factorization.

**Theorem 1.3 (The constructed cyclic shift has finite order).**

$$\forall n>0,\quad V_n^n=I_n$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixUnits.qudit_shift_order` (`✓ std3`). ∎

*Citation.* Julian Schwinger (1960). *Unitary Operator Bases*. DOI: [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).

*Commentary.*

The canonical rotation of Fin n returns after n steps, and its permutation matrix therefore satisfies V_n^n = I. The proof derives the matrix power from the permutation power rather than assuming cyclicity.

**Theorem 1.4 (Matrix-unit multiplication and adjoint certificates have zero error).**

$$E_{ij}E_{kl}-\delta_{jk}E_{il}=0\quad\land\quad E_{ij}^{*}-E_{ji}=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixUnits.matrix_unit_certificate_error_zero` (`✓ std3`). ∎

*Citation.* Julian Schwinger (1960). *Unitary Operator Bases*. DOI: [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).

*Commentary.*

For every finite decidable index type, the multiplication residual E_ij E_kl - delta_jk E_il and the adjoint residual E_ij^* - E_ji are literally the zero matrix. There is no floating-point tolerance or numerical proxy.

**Theorem 1.5 (Matrix units generate the full finite matrix algebra).**

$$\operatorname{adjoin}_{\mathbb{C}}\{E_{ij}:i,j\in I\}=M_I(\mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixUnits.matrix_units_generate_full_algebra` (`✓ std3`). ∎

*Citation.* Julian Schwinger (1960). *Unitary Operator Bases*. DOI: [10.1073/pnas.46.4.570](https://doi.org/10.1073/pnas.46.4.570).

*Commentary.*

Every finite complex square matrix is a finite linear combination of standard matrix units, so their complex algebraic adjoin is the top subalgebra. The ambient type is already a full matrix algebra; this theorem does not identify an arbitrary observer window with it.

**Theorem 1.6 (Every nontrivial full complex matrix algebra has no character).**

$$|I|\geq 2\quad\Rightarrow\quad \operatorname{IsEmpty}\!\left(M_I(\mathbb{C})\to_{\mathbb{C}\text{-alg}}\mathbb{C}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixUnits.matrix_algebra_has_no_character` (`✓ std3`). ∎

*Citation.* Gerard J. Murphy (1990). *C*-Algebras and Operator Theory*. DOI: [10.1016/C2009-0-22289-6](https://doi.org/10.1016/C2009-0-22289-6).

*Commentary.*

For every finite index type with at least two elements, no unital complex-algebra homomorphism from the full square matrix algebra to the complex numbers exists. This proves the all-matrix-sizes character obstruction without weakening it to a partial value table. Kochen-Specker projection valuations, CHSH bounds, hidden-address locality, and probability conclusions remain separate residuals.
