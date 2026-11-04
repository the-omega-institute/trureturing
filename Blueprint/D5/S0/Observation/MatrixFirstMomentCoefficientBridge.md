# First moment and characteristic coefficient comparison

## Abstract

The first unequal Hermitian matrix power trace determines the first unequal descending characteristic coefficient.

**Theorem 1.1 (The first coefficient defect is the negative moment defect divided by its index).**

Lean statement: `D5/S0/Observation/MatrixFirstMomentCoefficientBridge.matrix_first_moment_coefficient_bridge`

*Proof.* Machine-checked in Lean as `D5/S0/Observation/MatrixFirstMomentCoefficientBridge.matrix_first_moment_coefficient_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A and B be complex Hermitian matrices indexed by the same finite decidable type of cardinality N. Let 0 < n <= N, and assume trace(A^k) = trace(B^k) for every positive k<n. Write cA(j) and cB(j) for the coefficients of degree N-j of their actual characteristic polynomials. Then cA(j) = cB(j) for all j<n, including the leading index j=0, and n(cB(n)-cA(n)) = -(trace(B^n)-trace(A^n)). Thus a nonzero first moment difference gives a nonzero first descending coefficient difference, with a negative sign independent of the parity of n.

Mathlib's Matrix.IsHermitian.spectral_theorem gives actual unitary diagonalization. Powers commute with the conjugating algebra automorphism, cyclic invariance of trace cancels the two unitary factors, and the diagonal trace is the sum of the powers of the eigenvalues. Matrix.IsHermitian.roots_charpoly_eq_eigenvalues and splits_charpoly identify the full root multiset, including multiplicity. Polynomial.coeff_eq_esymm_roots_of_splits then gives cA(j) = (-1)^j eA(j), where eA(j) is the evaluated elementary symmetric polynomial in those eigenvalues. No trace-to-spectrum identity, factorization, or recurrence is an extra premise.

Evaluating MvPolynomial.mul_esymm_eq_sum and inserting the Vieta signs yields k cA(k) + sum_{a+b=k, a<k} cA(a) trace(A^b) = 0. Strong induction proves prefix coefficient equality: every summand uses a coefficient at an earlier descending index and a positive moment no larger than k, and the nonzero complex scalar k can be cancelled. At k=n, subtract the two actual recurrences. Terms with 0<a<n cancel because then 0<b<n. The sole remaining summand is a=0,b=n, and the monic leading coefficient is one. This gives the displayed negative sign.

The nearby NewtonPowerSumCharacteristicPolynomial.power_sums_determine_split_characteristic_polynomial recovers an entire split polynomial from dimension-many power sums. RegularCHS.Newton.sum_eigenvalues_pow_eq_closedWalks uses the same unitary trace calculation, while its hsymm_newton concerns complete homogeneous symmetric values. The present comparison uses the elementary-symmetric Newton primitive for a first differing characteristic coefficient. Its concrete consumer is BajnokBeattyFirstCharacteristicDefect.first_characteristic_defect, where the actual Cayley graph theorem discharges every trace premise. The spectral theorem, Newton identity, and Vieta formula are standard reused inputs; no novelty claim is made.

## References

- Truth anchor: `D5/S0/Observation/MatrixFirstMomentCoefficientBridge.matrix_first_moment_coefficient_bridge`
