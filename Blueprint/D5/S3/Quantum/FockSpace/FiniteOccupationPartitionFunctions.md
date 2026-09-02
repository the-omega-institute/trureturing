# Finite Occupation Partition Functions

## Abstract

Finite diagonal spectra admit exact fermionic and truncated bosonic occupation sums.

**Theorem 1.1 (The fermionic determinant is the binary occupation sum).**

$$\forall K, d, x, e,\ \operatorname{det}(I + x \operatorname{diag}(e)) = \sum_{n: \operatorname{Fin}(d) \to \operatorname{Fin}(2)} \prod_{i \in \operatorname{Fin}(d)} {xe_{i}}^{n_{i}}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions.fermionic_determinant_eq_occupation_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite diagonal spectrum e, the determinant of I plus x times diag(e) expands over functions from the mode set to Fin 2. Each spectral mode therefore occurs with exponent zero or one.

**Theorem 1.2 (The bosonic cutoff has an exact inverse-determinant remainder).**

$$\forall K, d, N, x, e,\ (\forall i \in \operatorname{Fin}(d), 1 - xe_{i} \ne 0) \Rightarrow Z_{B,N}(x) = \frac{\prod_{i \in \operatorname{Fin}(d)} (1-{xe_{i}}^{N+1})}{\operatorname{det}(I-x\operatorname{diag}(e))}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions.bosonic_trunc_eq_inverse_determinant_mul_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Occupations through N form a finite product of geometric sums. Multiplication by det(I-x diag(e)) leaves exactly the product of the finite geometric remainders.

The inverse-determinant form explicitly assumes every factor 1-x e_i is nonzero. This excludes totalized division at zero.

The source atom states an infinite Fredholm determinant and power series without a trace-class operator model or convergence hypotheses. The formal statement is the exact finite-spectrum, finite-cutoff specialization instead.

**Theorem 1.3 (One mode separates the two occupation rules).**

$$Z_{F}^{(1)}(1) = 2 \land Z_{B,2}^{(1)}(1) = 3.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions.one_mode_fermionic_bosonic_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At x=1 with one spectral value e=1, binary occupation contributes two states, while bosonic occupation zero, one, or two contributes three states. This is a concrete two-sided witness for the stated difference in state rules.

## References

- Truth anchor: `D5/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions.bosonic_trunc_eq_inverse_determinant_mul_remainder`
- Truth anchor: `D5/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions.fermionic_determinant_eq_occupation_sum`
- Truth anchor: `D5/S3/Quantum/FockSpace/FiniteOccupationPartitionFunctions.one_mode_fermionic_bosonic_witness`
