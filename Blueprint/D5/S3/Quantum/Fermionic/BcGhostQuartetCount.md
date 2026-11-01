# Actual ghost quartet count on the original Fock carrier

## Abstract

The actual original bc mode sum has a natural occupation count, a spectral inverse, a two-dimensional full ground and a one-dimensional literal relative ground.

The carrier is CountableOccupationFock.Fock: complex finitely supported functions on finite subsets of the natural sites. Ket S is the original Finsupp.single S 1; vacuum is ket of the empty set. Creators and annihilators use the original Jordan-Wigner sign, minus one to the number of occupied sites strictly below the operated site. The b and c modes are exactly BcGhostFock.b and BcGhostFock.c, with annihilation cuts b at m at least minus one and c at n at least two. No tensor decomposition, dimension bound, spectral identity, positivity premise or additional state-finiteness premise is introduced. All operator products compose right to left; natural count scalars are cast into Complex.

**Definition 1.1 (U).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For positive k this is c at minus k composed with b at k plus b at minus k composed with c at k. The artificial natural-index zero term is zero. Products act from right to left. Original Lean signature: def U (k : ℕ) : Module.End ℂ Fock

**Theorem 1.2 (Uzero).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem U_zero : U 0 = 0

**Theorem 1.3 (Upos).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem U_pos (k : ℕ) (hk : 0 < k) : U k = c (-(k : ℤ)) * b (k : ℤ) + b (-(k : ℤ)) * c (k : ℤ)

**Theorem 1.4 (phaseinsertself).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_insert_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_insert_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem phase_insert_self (j : ℕ) (S : Finset ℕ) : phase j (insert j S) = phase j S

**Theorem 1.5 (phaseeraseself).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_erase_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_erase_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem phase_erase_self (j : ℕ) (S : Finset ℕ) : phase j (S.erase j) = phase j S

**Theorem 1.6 (phasesquare).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem phase_square (j : ℕ) (S : Finset ℕ) : phase j S * phase j S = 1

**Theorem 1.7 (createannihilateket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.create_annihilate_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.create_annihilate_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem create_annihilate_ket (j : ℕ) (S : Finset ℕ) : (create j * annihilate j) (ket S) = if j ∈ S then ket S else 0

**Theorem 1.8 (annihilatecreateket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.annihilate_create_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.annihilate_create_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem annihilate_create_ket (j : ℕ) (S : Finset ℕ) : (annihilate j * create j) (ket S) = if j ∈ S then 0 else ket S

**Theorem 1.9 (bpositive).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem b_positive (k : ℕ) : b (k : ℤ) = annihilate (2 * k + 3)

**Theorem 1.10 (cnegative).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem c_negative (k : ℕ) : c (-(k : ℤ)) = create (2 * k + 3)

**Theorem 1.11 (bnegativeone).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem b_negative_one : b (-1) = annihilate 1

**Theorem 1.12 (cpositiveone).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_positive_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_positive_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem c_positive_one : c 1 = create 1

**Theorem 1.13 (bzero).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem b_zero : b 0 = annihilate 3

**Theorem 1.14 (bnegativegetwo).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_ge_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_ge_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem b_negative_ge_two (k : ℕ) (hk : 2 ≤ k) : b (-(k : ℤ)) = create (2 * (k - 2))

**Theorem 1.15 (cpositivegetwo).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_positive_ge_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_positive_ge_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem c_positive_ge_two (k : ℕ) (hk : 2 ≤ k) : c (k : ℤ) = annihilate (2 * (k - 2))

**Theorem 1.16 (cnegativebpositiveket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_negative_b_positive_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_negative_b_positive_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem c_negative_b_positive_ket (k : ℕ) (S : Finset ℕ) : (c (-(k : ℤ)) * b (k : ℤ)) (ket S) = if 2 * k + 3 ∈ S then ket S else 0

**Theorem 1.17 (bnegativecpositiveket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_c_positive_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_c_positive_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem b_negative_c_positive_ket (k : ℕ) (hk : 0 < k) (S : Finset ℕ) : (b (-(k : ℤ)) * c (k : ℤ)) (ket S) = if k = 1 then (if 1 ∈ S then 0 else ket S) else (if 2 * (k - 2) ∈ S then ket S else 0)

**Definition 1.18 (localCount).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.localCount`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.localCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The odd occupied site is 2k+3 for positive k. At k=1 the second branch counts the hole at site 1. For k at least 2 it counts the occupied even site 2(k-2). Original Lean signature: def localCount (k : ℕ) (S : Finset ℕ) : ℕ

**Theorem 1.19 (Uket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem U_ket (k : ℕ) (S : Finset ℕ) : U k (ket S) = (localCount k S : ℂ) • ket S

**Definition 1.20 (count).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the cardinality of S with sites 1 and 3 erased, plus one precisely when site 1 is absent. Site 3 is uncounted; occupying site 1 removes a hole. Original Lean signature: def count (S : Finset ℕ) : ℕ

**Theorem 1.21 (countinsertregular).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_insert_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_insert_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem count_insert_regular (j : ℕ) (S : Finset ℕ) (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj : j ∉ S) : count (insert j S) = count S + 1

**Theorem 1.22 (counteraseregular).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_erase_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_erase_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem count_erase_regular (j : ℕ) (S : Finset ℕ) (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj : j ∈ S) : count S = count (S.erase j) + 1

**Theorem 1.23 (countinsertone).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_insert_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_insert_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem count_insert_one (S : Finset ℕ) (h1 : 1 ∉ S) : count (insert 1 S) + 1 = count S

**Theorem 1.24 (counteraseone).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_erase_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_erase_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem count_erase_one (S : Finset ℕ) (h1 : 1 ∈ S) : count (S.erase 1) = count S + 1

**Theorem 1.25 (countnonnegative).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem count_nonnegative (S : Finset ℕ) : 0 ≤ count S

**Theorem 1.26 (sumlocalCount).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.sum_localCount`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.sum_localCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Explicit bijections enumerate the odd sites other than 1 and 3 and the even sites in S. Their parity partition and the exceptional hole give the count for every finite capture satisfying the displayed bounds. Original Lean signature: theorem sum_localCount (S : Finset ℕ) (N : ℕ) (hN : 3 ≤ N) (hS : ∀ j ∈ S, j + 3 ≤ N) : (∑ k ∈ Finset.range N, localCount k S) = count S

**Theorem 1.27 (localCountzeroofcapture).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.localCount_zero_of_capture`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.localCount_zero_of_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem localCount_zero_of_capture (S : Finset ℕ) (k : ℕ) (hk : 3 ≤ k) (hS : ∀ j ∈ S, j + 3 ≤ k) : localCount k S = 0

**Definition 1.28 (occupied).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.occupied`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.occupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the finite union of the actual occupied site sets in the finitely supported input. Original Lean signature: def occupied (v : Fock) : Finset ℕ

**Definition 1.29 (capture).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.capture`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.capture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum occupied site plus three bounds every potentially nonzero positive summand for this actual input. Original Lean signature: def capture (v : Fock) : ℕ

**Theorem 1.30 (sitecapture).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.site_capture`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.site_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem site_capture (v : Fock) (S : Finset ℕ) (hS : S ∈ v.support) (j : ℕ) (hj : j ∈ S) : j + 3 ≤ capture v

**Theorem 1.31 (ketexpansion).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.ket_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.ket_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem ket_expansion (v : Fock) : (∑ S ∈ v.support, v S • ket S) = v

**Theorem 1.32 (Uzeroabovecapture).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero_above_capture`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero_above_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem U_zero_above_capture (v : Fock) (k : ℕ) (hk : capture v ≤ k) : U k v = 0

**Theorem 1.33 (modesupportsubset).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.mode_support_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.mode_support_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem mode_support_subset (v : Fock) : Function.support (fun k => U k v) ⊆ (Finset.range (capture v) : Set ℕ)

**Theorem 1.34 (modesupportfinite).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.mode_support_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.mode_support_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original finite-excitation state has a finite evaluated mode support. No finite support of the endomorphism family is asserted or assumed. Original Lean signature: theorem mode_support_finite (v : Fock) : (Function.support (fun k => U k v)).Finite

**Definition 1.35 (modeSum).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the locally finite finsum of the original paired modes evaluated on the input. Its finiteness is proved before linearity. Original Lean signature: def modeSum (v : Fock) : Fock

**Theorem 1.36 (modeSumeqsum).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem modeSum_eq_sum (v : Fock) (N : ℕ) (hN : capture v ≤ N) : modeSum v = ∑ k ∈ Finset.range N, U k v

**Theorem 1.37 (modeSumadd).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_add`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One finite range contains the captures of v, w and v+w. Linearity of each original summand proves additivity on that common range. Original Lean signature: theorem modeSum_add (v w : Fock) : modeSum (v + w) = modeSum v + modeSum w

**Theorem 1.38 (modeSumsmul).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One finite range contains the captures of v and its scalar multiple. Scalar compatibility follows on this common range. Original Lean signature: theorem modeSum_smul (a : ℂ) (v : Fock) : modeSum (a • v) = a • modeSum v

**Definition 1.39 (M).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual mode sum is packaged as a complex linear endomorphism only after its linearity has been proved. Original Lean signature: def M : Module.End ℂ Fock

**Theorem 1.40 (MeqmodeSum).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_modeSum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_modeSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem M_eq_modeSum (v : Fock) : M v = ∑ᶠ k : ℕ, U k v

**Theorem 1.41 (Meqsum).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem M_eq_sum (v : Fock) (N : ℕ) (hN : capture v ≤ N) : M v = ∑ k ∈ Finset.range N, U k v

**Theorem 1.42 (Mket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The spectrum on each original occupation ket is derived from the original b and c actions and finite enumeration, rather than supplied as a hypothesis. Original Lean signature: theorem M_ket (S : Finset ℕ) : M (ket S) = (count S : ℂ) • ket S

**Definition 1.43 (diagonal).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coefficient multiplier on the same original Finsupp carrier is used after deriving the actual mode count. It is not a replacement Fock representation. Original Lean signature: def diagonal (f : Finset ℕ → ℂ) : Module.End ℂ Fock

**Theorem 1.44 (diagonalket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem diagonal_ket (f : Finset ℕ → ℂ) (S : Finset ℕ) : diagonal f (ket S) = f S • ket S

**Theorem 1.45 (diagonalcoefficient).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem diagonal_coefficient (f : Finset ℕ → ℂ) (v : Fock) (S : Finset ℕ) : diagonal f v S = f S * v S

**Theorem 1.46 (Meqdiagonal).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem M_eq_diagonal : M = diagonal (fun S => (count S : ℂ))

**Theorem 1.47 (Mcoefficient).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state and every finite occupation, the output coefficient is its input coefficient multiplied by the natural occupation count cast to Complex. Original Lean signature: theorem M_coefficient (v : Fock) (S : Finset ℕ) : M v S = (count S : ℂ) * v S

**Theorem 1.48 (Msupportsubset).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_support_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_support_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem M_support_subset (v : Fock) : (M v).support ⊆ v.support

**Theorem 1.49 (eigenvectoriff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.eigenvector_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.eigenvector_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An eigenvector may have several nonzero coefficients; every occupation in its support must carry exactly the displayed eigenvalue. Original Lean signature: theorem eigenvector_iff (v : Fock) (z : ℂ) : M v = z • v ↔ ∀ S ∈ v.support, (count S : ℂ) = z

**Theorem 1.50 (nonzeroeigenvalueisnatural).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.nonzero_eigenvalue_is_natural`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.nonzero_eigenvalue_is_natural` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero coefficient witnesses that the eigenvalue is a natural count. Nonnegativity is algebraic here; no positive ghost inner product is claimed. Original Lean signature: theorem nonzero_eigenvalue_is_natural (v : Fock) (z : ℂ) (hv : v ≠ 0) (he : M v = z • v) : ∃ q : ℕ, z = (q : ℂ)

**Theorem 1.51 (countsurjectiverelative).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_surjective_relative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_surjective_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every natural number is attained by an occupation omitting site 3. The construction starts at the occupied site-1 ground and inserts a fresh regular site at each successor. Original Lean signature: theorem count_surjective_relative (q : ℕ) : ∃ S : Finset ℕ, 3 ∉ S ∧ count S = q

**Definition 1.52 (P).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Projection onto all zero-count states of the full original carrier, including the site-3 partner. Original Lean signature: def P : Module.End ℂ Fock

**Definition 1.53 (invM).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a nonzero natural count use its complex reciprocal, and set the zero-count coefficient to zero. Original Lean signature: def invM : Module.End ℂ Fock

**Theorem 1.54 (Pket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem P_ket (S : Finset ℕ) : P (ket S) = (if count S = 0 then (1 : ℂ) else 0) • ket S

**Theorem 1.55 (invMket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem invM_ket (S : Finset ℕ) : invM (ket S) = (if count S = 0 then (0 : ℂ) else (count S : ℂ)⁻¹) • ket S

**Theorem 1.56 (Pcoefficient).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem P_coefficient (v : Fock) (S : Finset ℕ) : P v S = if count S = 0 then v S else 0

**Theorem 1.57 (invMcoefficient).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem invM_coefficient (v : Fock) (S : Finset ℕ) : invM v S = if count S = 0 then 0 else (count S : ℂ)⁻¹ * v S

**Theorem 1.58 (MmulinvM).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_invM`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_invM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original count followed by its spectral inverse is identity minus the full zero-count projection. Original Lean signature: theorem M_mul_invM : M * invM = 1 - P

**Theorem 1.59 (invMmulM).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_mul_M`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_mul_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse product gives the same identity minus the full zero-count projection. Original Lean signature: theorem invM_mul_M : invM * M = 1 - P

**Theorem 1.60 (Pidempotent).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_idempotent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_idempotent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem P_idempotent : P * P = P

**Theorem 1.61 (Psq).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem P_sq : P ^ 2 = P

**Theorem 1.62 (MmulP).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_P`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_P` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem M_mul_P : M * P = 0

**Theorem 1.63 (PmulM).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_mul_M`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_mul_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem P_mul_M : P * M = 0

**Theorem 1.64 (invMmulP).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_mul_P`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_mul_P` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem invM_mul_P : invM * P = 0

**Theorem 1.65 (PmulinvM).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_mul_invM`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_mul_invM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem P_mul_invM : P * invM = 0

**Theorem 1.66 (countzeroiff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete zero-count occupation sets are precisely {1} and {1,3}. In particular the full kernel is not a single vacuum line. Original Lean signature: theorem count_zero_iff (S : Finset ℕ) : count S = 0 ↔ S = {1} ∨ S = {1, 3}

**Theorem 1.67 (Papply).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full projection retains exactly the two original coefficients at {1} and {1,3}. Original Lean signature: theorem P_apply (v : Fock) : P v = v {1} • ket {1} + v {1, 3} • ket {1, 3}

**Theorem 1.68 (MeqzeroiffPeqself).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_zero_iff_P_eq_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_zero_iff_P_eq_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem M_eq_zero_iff_P_eq_self (v : Fock) : M v = 0 ↔ P v = v

**Theorem 1.69 (fullkerneliff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.full_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.full_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem full_kernel_iff (v : Fock) : M v = 0 ↔ ∃ a d : ℂ, v = a • ket {1} + d • ket {1, 3}

**Theorem 1.70 (fullkernel).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.full_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.full_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full zero eigenspace is exactly the complex span of the two displayed original kets. Original Lean signature: theorem full_kernel : LinearMap.ker M = Submodule.span ℂ ({ket {1}, ket {1, 3}} : Set Fock)

**Theorem 1.71 (b0down).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_down`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_down` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem b0_down : b 0 (ket {1}) = 0

**Theorem 1.72 (b0otherground).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_other_ground`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_other_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: @[simp] theorem b0_other_ground : b 0 (ket {1, 3}) = -ket {1}

**Theorem 1.73 (b0eqzeroiffcoefficients).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_eq_zero_iff_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_eq_zero_iff_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal original zero mode b at zero is annihilation at site 3. Its kernel is characterized by vanishing of every coefficient whose occupation contains site 3. Original Lean signature: theorem b0_eq_zero_iff_coefficients (v : Fock) : b 0 v = 0 ↔ ∀ S : Finset ℕ, 3 ∈ S → v S = 0

**Theorem 1.74 (relativekerneliff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem relative_kernel_iff (v : Fock) : (M v = 0 ∧ b 0 v = 0) ↔ ∃ a : ℂ, v = a • ket {1}

**Theorem 1.75 (relativekernel).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Intersect the full count kernel with the literal original b-zero kernel. The result is exactly the line of ket {1}. Original Lean signature: theorem relative_kernel : LinearMap.ker M ⊓ LinearMap.ker (b 0) = Submodule.span ℂ ({ket {1}} : Set Fock)

**Definition 1.76 (c1vac).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c1vac`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c1vac` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named relative ground is the original c at one applied to the original empty vacuum. Original Lean signature: def c1vac : Fock

**Theorem 1.77 (c1vaceq).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c1vac_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c1vac_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original mode-vacuum formula identifies this state with ket {1}; it is not the empty occupation vacuum. Original Lean signature: theorem c1vac_eq : c1vac = ket {1}

**Theorem 1.78 (relativekernelc1vac).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel_c1vac`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel_c1vac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal joint kernel is exactly the complex multiples of the named original c-one vacuum. Original Lean signature: theorem relative_kernel_c1vac (v : Fock) : (M v = 0 ∧ b 0 v = 0) ↔ ∃ a : ℂ, v = a • c1vac

**Theorem 1.79 (relativeeigenvalueiff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_eigenvalue_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_eigenvalue_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The algebraic point spectrum is exactly the natural numbers, even when the nonzero witnessing state must satisfy the literal relative b-zero condition. Original Lean signature: theorem relative_eigenvalue_iff (z : ℂ) : (∃ v : Fock, v ≠ 0 ∧ b 0 v = 0 ∧ M v = z • v) ↔ ∃ q : ℕ, z = (q : ℂ)

**Theorem 1.80 (eigenvalueiff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.eigenvalue_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.eigenvalue_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full algebraic point spectrum is exactly the natural numbers. This is not a topological spectral theorem for a Hilbert completion. Original Lean signature: theorem eigenvalue_iff (z : ℂ) : (∃ v : Fock, v ≠ 0 ∧ M v = z • v) ↔ ∃ q : ℕ, z = (q : ℂ)

**Theorem 1.81 (Mcreateregular).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_create_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_create_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem M_create_regular (j : ℕ) (hj1 : j ≠ 1) (hj3 : j ≠ 3) : M * create j - create j * M = create j

**Theorem 1.82 (Mannihilateregular).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_annihilate_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_annihilate_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem M_annihilate_regular (j : ℕ) (hj1 : j ≠ 1) (hj3 : j ≠ 3) : M * annihilate j - annihilate j * M = -annihilate j

**Theorem 1.83 (Mannihilateone).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_annihilate_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_annihilate_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem M_annihilate_one : M * annihilate 1 - annihilate 1 * M = annihilate 1

**Theorem 1.84 (Mcreateone).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_create_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_create_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This original-carrier identity is used in the finite occupation, coefficient, projection or mode calculation; its original telescope and conclusion are recorded below and bound to the native declaration in the evidence bundle. Original Lean signature: theorem M_create_one : M * create 1 - create 1 * M = -create 1

**Theorem 1.85 (Mbnegative).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_b_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_b_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every strictly negative original b mode raises the count by one, including the exceptional site-1 annihilation mode. Original Lean signature: theorem M_b_negative (k : ℕ) (hk : 0 < k) : M * b (-(k : ℤ)) - b (-(k : ℤ)) * M = b (-(k : ℤ))

**Theorem 1.86 (Mcnegative).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_c_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_c_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every strictly negative original c mode raises the count by one. Original Lean signature: theorem M_c_negative (k : ℕ) (hk : 0 < k) : M * c (-(k : ℤ)) - c (-(k : ℤ)) * M = c (-(k : ℤ))

**Theorem 1.87 (Mbpositive).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_b_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_b_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every strictly positive original b mode lowers the count by one. Original Lean signature: theorem M_b_positive (k : ℕ) (hk : 0 < k) : M * b (k : ℤ) - b (k : ℤ) * M = -b (k : ℤ)

**Theorem 1.88 (Mcpositive).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_c_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_c_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every strictly positive original c mode lowers the count by one, including filling the exceptional site-1 hole. Original Lean signature: theorem M_c_positive (k : ℕ) (hk : 0 < k) : M * c (k : ℤ) - c (k : ℤ) * M = -c (k : ℤ)

These are algebraic finite-excitation statements on the original carrier. The full zero-count kernel keeps the uncounted site 3; only intersection with the actual kernel of b at zero removes its partner. The positive and negative commutators require a strictly positive natural mode index. The inverse is zero on the full ground and inverts M only after subtracting that full projection. This supplier does not construct a quartet contraction, the matter tensor, the BRST charge or its nilpotence, homological perturbation, a no-ghost theorem, a Hilbert-space positivity theorem, Monster moonshine, a complete VOA/CFT, string theory or AdS/CFT. Those goals require their own constructions and proofs. No literature novelty is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_annihilate_one`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_annihilate_regular`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_b_negative`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_b_positive`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_c_negative`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_c_positive`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_coefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_create_one`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_create_regular`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_diagonal`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_modeSum`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_sum`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_zero_iff_P_eq_self`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_P`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_invM`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_support_subset`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_apply`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_coefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_idempotent`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_mul_M`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_mul_invM`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_sq`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_pos`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero_above_capture`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.annihilate_create_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_down`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_eq_zero_iff_coefficients`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_other_ground`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_c_positive_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_ge_two`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_one`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_positive`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_zero`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c1vac`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c1vac_eq`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_negative`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_negative_b_positive_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_positive_ge_two`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_positive_one`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.capture`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_erase_one`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_erase_regular`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_insert_one`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_insert_regular`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_nonnegative`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_surjective_relative`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_zero_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.create_annihilate_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal_coefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.eigenvalue_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.eigenvector_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.full_kernel`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.full_kernel_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_coefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_mul_M`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_mul_P`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.ket_expansion`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.localCount`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.localCount_zero_of_capture`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_add`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_eq_sum`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_smul`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.mode_support_finite`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.mode_support_subset`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.nonzero_eigenvalue_is_natural`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.occupied`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_erase_self`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_insert_self`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_square`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_eigenvalue_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel_c1vac`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.site_capture`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.sum_localCount`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostFock](BcGhostFock.md)
