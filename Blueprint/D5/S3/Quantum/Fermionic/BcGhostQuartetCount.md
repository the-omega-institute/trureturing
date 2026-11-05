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

**Theorem 1.2 (U zero).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero branch in U_ket uses this simp identity to discard the artificial index zero. Original Lean signature: @[simp] theorem U_zero : U 0 = 0

**Theorem 1.3 (U pos).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U_ket uses this expansion for every strictly positive index before evaluating the two paired modes. Original Lean signature: theorem U_pos (k : ℕ) (hk : 0 < k) : U k = c (-(k : ℤ)) * b (k : ℤ) + b (-(k : ℤ)) * c (k : ℤ)

**Theorem 1.4 (phase insert self).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_insert_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_insert_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

annihilate_create_ket uses this simp identity to cancel the two original signs after insertion. Original Lean signature: @[simp] theorem phase_insert_self (j : ℕ) (S : Finset ℕ) : phase j (insert j S) = phase j S

**Theorem 1.5 (phase erase self).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_erase_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_erase_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

create_annihilate_ket uses this simp identity to cancel the two original signs after erasure. Original Lean signature: @[simp] theorem phase_erase_self (j : ℕ) (S : Finset ℕ) : phase j (S.erase j) = phase j S

**Theorem 1.6 (phase square).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_square`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.phase_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both same-site ket product proofs use this simp identity to cancel their two phase factors. Original Lean signature: @[simp] theorem phase_square (j : ℕ) (S : Finset ℕ) : phase j S * phase j S = 1

**Theorem 1.7 (create annihilate ket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.create_annihilate_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.create_annihilate_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupied odd and even branches in c_negative_b_positive_ket and b_negative_c_positive_ket use this original ket calculation; b0_eq_zero_iff_coefficients also uses it. Original Lean signature: theorem create_annihilate_ket (j : ℕ) (S : Finset ℕ) : (create j * annihilate j) (ket S) = if j ∈ S then ket S else 0

**Theorem 1.8 (annihilate create ket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.annihilate_create_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.annihilate_create_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exceptional k=1 branch of b_negative_c_positive_ket uses this hole calculation at site 1. Original Lean signature: theorem annihilate_create_ket (j : ℕ) (S : Finset ℕ) : (annihilate j * create j) (ket S) = if j ∈ S then 0 else ket S

**Theorem 1.9 (b positive).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

c_negative_b_positive_ket and M_b_positive use this original-mode correspondence at odd sites. Original Lean signature: theorem b_positive (k : ℕ) : b (k : ℤ) = annihilate (2 * k + 3)

**Theorem 1.10 (c negative).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

c_negative_b_positive_ket and M_c_negative use this original-mode correspondence at odd sites. Original Lean signature: theorem c_negative (k : ℕ) : c (-(k : ℤ)) = create (2 * k + 3)

**Theorem 1.11 (b negative one).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The k=1 ket and negative-b commutator branches use this simp correspondence with annihilation at site 1. Original Lean signature: @[simp] theorem b_negative_one : b (-1) = annihilate 1

**Theorem 1.12 (c positive one).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_positive_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_positive_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The k=1 ket and positive-c commutator branches use this simp correspondence with creation at site 1. Original Lean signature: @[simp] theorem c_positive_one : c 1 = create 1

**Theorem 1.13 (b zero).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

b0_down and b0_eq_zero_iff_coefficients use this correspondence with annihilation at the uncounted site 3. Original Lean signature: @[simp] theorem b_zero : b 0 = annihilate 3

**Theorem 1.14 (b negative ge two).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_ge_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_ge_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The even-site ket branch and M_b_negative use this correspondence for indices at least two. Original Lean signature: theorem b_negative_ge_two (k : ℕ) (hk : 2 ≤ k) : b (-(k : ℤ)) = create (2 * (k - 2))

**Theorem 1.15 (c positive ge two).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_positive_ge_two`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_positive_ge_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The even-site ket branch and M_c_positive use this correspondence for indices at least two. Original Lean signature: theorem c_positive_ge_two (k : ℕ) (hk : 2 ≤ k) : c (k : ℤ) = annihilate (2 * (k - 2))

**Theorem 1.16 (c negative b positive ket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_negative_b_positive_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c_negative_b_positive_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U_ket uses this occupied odd-site branch of the actual paired mode. Original Lean signature: theorem c_negative_b_positive_ket (k : ℕ) (S : Finset ℕ) : (c (-(k : ℤ)) * b (k : ℤ)) (ket S) = if 2 * k + 3 ∈ S then ket S else 0

**Theorem 1.17 (b negative c positive ket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_c_positive_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b_negative_c_positive_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U_ket uses this branch, including its separate site-1 hole case at k=1. Original Lean signature: theorem b_negative_c_positive_ket (k : ℕ) (hk : 0 < k) (S : Finset ℕ) : (b (-(k : ℤ)) * c (k : ℤ)) (ket S) = if k = 1 then (if 1 ∈ S then 0 else ket S) else (if 2 * (k - 2) ∈ S then ket S else 0)

**Definition 1.18 (localCount).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.localCount`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.localCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The odd occupied site is 2k+3 for positive k. At k=1 the second branch counts the hole at site 1. For k at least 2 it counts the occupied even site 2(k-2). Original Lean signature: def localCount (k : ℕ) (S : Finset ℕ) : ℕ

**Theorem 1.19 (U ket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The capture proof and M_ket use this actual-mode local diagonal action. Original Lean signature: theorem U_ket (k : ℕ) (S : Finset ℕ) : U k (ket S) = (localCount k S : ℂ) • ket S

**Definition 1.20 (count).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the cardinality of S with sites 1 and 3 erased, plus one precisely when site 1 is absent. Site 3 is uncounted; occupying site 1 removes a hole. Original Lean signature: def count (S : Finset ℕ) : ℕ

**Theorem 1.21 (count insert regular).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_insert_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_insert_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

count_erase_regular, count_surjective_relative and M_create_regular use the increase under insertion of a regular site. Original Lean signature: theorem count_insert_regular (j : ℕ) (S : Finset ℕ) (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj : j ∉ S) : count (insert j S) = count S + 1

**Theorem 1.22 (count erase regular).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_erase_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_erase_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_annihilate_regular uses this exact count change on occupied regular sites. Original Lean signature: theorem count_erase_regular (j : ℕ) (S : Finset ℕ) (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj : j ∈ S) : count S = count (S.erase j) + 1

**Theorem 1.23 (count insert one).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_insert_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_insert_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

count_erase_one and M_create_one use the reversed count change when the site-1 hole is filled. Original Lean signature: theorem count_insert_one (S : Finset ℕ) (h1 : 1 ∉ S) : count (insert 1 S) + 1 = count S

**Theorem 1.24 (count erase one).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_erase_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_erase_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_annihilate_one uses this increase when deleting site 1 creates a hole. Original Lean signature: theorem count_erase_one (S : Finset ℕ) (h1 : 1 ∈ S) : count (S.erase 1) = count S + 1

**Theorem 1.25 (sum localCount).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.sum_localCount`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.sum_localCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_ket uses the parity bijections and exceptional hole term to identify the actual finite mode sum with count S. Explicit bijections enumerate the odd sites other than 1 and 3 and the even sites in S. Their parity partition and the exceptional hole give the count for every finite capture satisfying the displayed bounds. Original Lean signature: theorem sum_localCount (S : Finset ℕ) (N : ℕ) (hN : 3 ≤ N) (hS : ∀ j ∈ S, j + 3 ≤ N) : (∑ k ∈ Finset.range N, localCount k S) = count S

**Theorem 1.26 (localCount zero of capture).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.localCount_zero_of_capture`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.localCount_zero_of_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U_zero_above_capture uses this vanishing for every occupied basis state in the support of an actual Fock vector. Original Lean signature: theorem localCount_zero_of_capture (S : Finset ℕ) (k : ℕ) (hk : 3 ≤ k) (hS : ∀ j ∈ S, j + 3 ≤ k) : localCount k S = 0

**Definition 1.27 (occupied).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.occupied`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.occupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the finite union of the actual occupied site sets in the finitely supported input. Original Lean signature: def occupied (v : Fock) : Finset ℕ

**Definition 1.28 (capture).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.capture`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.capture` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The maximum occupied site plus three bounds every potentially nonzero positive summand for this actual input. Original Lean signature: def capture (v : Fock) : ℕ

**Theorem 1.29 (site capture).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.site_capture`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.site_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U_zero_above_capture uses this bound for each site of each supported basis state. Original Lean signature: theorem site_capture (v : Fock) (S : Finset ℕ) (hS : S ∈ v.support) (j : ℕ) (hj : j ∈ S) : j + 3 ≤ capture v

**Theorem 1.30 (ket expansion).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.ket_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.ket_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U_zero_above_capture and b0_eq_zero_iff_coefficients use this finite expansion of the original Fock vector. Original Lean signature: theorem ket_expansion (v : Fock) : (∑ S ∈ v.support, v S • ket S) = v

**Theorem 1.31 (U zero above capture).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero_above_capture`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero_above_capture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

mode_support_subset uses the vanishing beyond the state-dependent capture. Original Lean signature: theorem U_zero_above_capture (v : Fock) (k : ℕ) (hk : capture v ≤ k) : U k v = 0

**Theorem 1.32 (mode support subset).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.mode_support_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.mode_support_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

mode_support_finite and modeSum_eq_sum use this explicit finite support bound. Original Lean signature: theorem mode_support_subset (v : Fock) : Function.support (fun k => U k v) ⊆ (Finset.range (capture v) : Set ℕ)

**Theorem 1.33 (mode support finite).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.mode_support_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.mode_support_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the all-state local-finiteness endpoint for the original positive paired modes. Every original finite-excitation state has a finite evaluated mode support. No finite support of the endomorphism family is asserted or assumed. Original Lean signature: theorem mode_support_finite (v : Fock) : (Function.support (fun k => U k v)).Finite

**Definition 1.34 (modeSum).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the locally finite finsum of the original paired modes evaluated on the input. Its finiteness is proved before linearity. Original Lean signature: def modeSum (v : Fock) : Fock

**Theorem 1.35 (modeSum eq sum).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

modeSum_add, modeSum_smul and M_eq_sum use finite captures to handle the original finsum. Original Lean signature: theorem modeSum_eq_sum (v : Fock) (N : ℕ) (hN : capture v ≤ N) : modeSum v = ∑ k ∈ Finset.range N, U k v

**Theorem 1.36 (modeSum add).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_add`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map_add field of the actual operator M uses this common-capture argument. One finite range contains the captures of v, w and v+w. Linearity of each original summand proves additivity on that common range. Original Lean signature: theorem modeSum_add (v w : Fock) : modeSum (v + w) = modeSum v + modeSum w

**Theorem 1.37 (modeSum smul).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.modeSum_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map_smul field of the actual operator M uses this common-capture argument. One finite range contains the captures of v and its scalar multiple. Scalar compatibility follows on this common range. Original Lean signature: theorem modeSum_smul (a : ℂ) (v : Fock) : modeSum (a • v) = a • modeSum v

**Definition 1.38 (M).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual mode sum is packaged as a complex linear endomorphism only after its linearity has been proved. Original Lean signature: def M : Module.End ℂ Fock

**Theorem 1.39 (M eq sum).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_ket uses this statewise finite sum of the original operators to derive its count eigenvalue. Original Lean signature: theorem M_eq_sum (v : Fock) (N : ℕ) (hN : capture v ≤ N) : M v = ∑ k ∈ Finset.range N, U k v

**Theorem 1.40 (M ket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient formula, inverse identities, kernel reconstruction, eigenvalue witnesses and signed commutators use the actual-mode count action. The spectrum on each original occupation ket is derived from the original b and c actions and finite enumeration, rather than supplied as a hypothesis. Original Lean signature: theorem M_ket (S : Finset ℕ) : M (ket S) = (count S : ℂ) • ket S

**Definition 1.41 (diagonal).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A coefficient multiplier on the same original Finsupp carrier is used after deriving the actual mode count. It is not a replacement Fock representation. Original Lean signature: def diagonal (f : Finset ℕ → ℂ) : Module.End ℂ Fock

**Theorem 1.42 (diagonal ket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_eq_diagonal, the projection and inverse ket actions, and the coefficient proof use this generic multiplier action. Original Lean signature: @[simp] theorem diagonal_ket (f : Finset ℕ → ℂ) (S : Finset ℕ) : diagonal f (ket S) = f S • ket S

**Theorem 1.43 (diagonal coefficient).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.diagonal_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_coefficient, P_coefficient and the site-3 coefficient test use this generic coefficient calculation. Original Lean signature: theorem diagonal_coefficient (f : Finset ℕ → ℂ) (v : Fock) (S : Finset ℕ) : diagonal f v S = f S * v S

**Theorem 1.44 (M eq diagonal).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_coefficient uses this equality, proved from the actual-mode M_ket rather than assumed as a spectrum. Original Lean signature: theorem M_eq_diagonal : M = diagonal (fun S => (count S : ℂ))

**Theorem 1.45 (M coefficient).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_support_subset and eigenvector_iff use this all-state formula; the retained Reg attempt also refers to its exact original telescope. For every original state and every finite occupation, the output coefficient is its input coefficient multiplied by the natural occupation count cast to Complex. Original Lean signature: theorem M_coefficient (v : Fock) (S : Finset ℕ) : M v S = (count S : ℂ) * v S

**Theorem 1.46 (M support subset).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_support_subset`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_support_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the support-preservation consequence of the actual M coefficient formula. Original Lean signature: theorem M_support_subset (v : Fock) : (M v).support ⊆ v.support

**Theorem 1.47 (eigenvector iff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.eigenvector_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.eigenvector_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

nonzero_eigenvalue_is_natural uses a nonzero supported coefficient to identify its count. An eigenvector may have several nonzero coefficients; every occupation in its support must carry exactly the displayed eigenvalue. Original Lean signature: theorem eigenvector_iff (v : Fock) (z : ℂ) : M v = z • v ↔ ∀ S ∈ v.support, (count S : ℂ) = z

**Theorem 1.48 (nonzero eigenvalue is natural).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.nonzero_eigenvalue_is_natural`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.nonzero_eigenvalue_is_natural` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward directions of the full and literal-relative eigenvalue characterizations use this conclusion. A nonzero coefficient witnesses that the eigenvalue is a natural count. Nonnegativity is algebraic here; no positive ghost inner product is claimed. Original Lean signature: theorem nonzero_eigenvalue_is_natural (v : Fock) (z : ℂ) (hv : v ≠ 0) (he : M v = z • v) : ∃ q : ℕ, z = (q : ℂ)

**Theorem 1.49 (count surjective relative).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_surjective_relative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_surjective_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

relative_eigenvalue_iff uses the constructed site-3-free finite set to witness every natural eigenvalue. Every natural number is attained by an occupation omitting site 3. The construction starts at the occupied site-1 ground and inserts a fresh regular site at each successor. Original Lean signature: theorem count_surjective_relative (q : ℕ) : ∃ S : Finset ℕ, 3 ∉ S ∧ count S = q

**Definition 1.50 (P).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Projection onto all zero-count states of the full original carrier, including the site-3 partner. Original Lean signature: def P : Module.End ℂ Fock

**Definition 1.51 (invM).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a nonzero natural count use its complex reciprocal, and set the zero-count coefficient to zero. Original Lean signature: def invM : Module.End ℂ Fock

**Theorem 1.52 (P ket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both actual inverse identities and the M-projection annihilation proofs use this zero-count indicator action. Original Lean signature: @[simp] theorem P_ket (S : Finset ℕ) : P (ket S) = (if count S = 0 then (1 : ℂ) else 0) • ket S

**Theorem 1.53 (invM ket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both actual inverse identities use this reciprocal action away from zero and its zero action at the ground. Original Lean signature: @[simp] theorem invM_ket (S : Finset ℕ) : invM (ket S) = (if count S = 0 then (0 : ℂ) else (count S : ℂ)⁻¹) • ket S

**Theorem 1.54 (P coefficient).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P_apply uses this indicator coefficient formula to recover exactly the two full-ground coefficients. Original Lean signature: theorem P_coefficient (v : Fock) (S : Finset ℕ) : P v S = if count S = 0 then v S else 0

**Theorem 1.55 (M mul invM).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_invM`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_invM` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the right inverse identity for the original-mode M after subtracting its full zero-count projection. The original count followed by its spectral inverse is identity minus the full zero-count projection. Original Lean signature: theorem M_mul_invM : M * invM = 1 - P

**Theorem 1.56 (invM mul M).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_mul_M`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_mul_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_eq_zero_iff_P_eq_self uses this left inverse identity to reconstruct every vector killed by the original-mode M. The reverse product gives the same identity minus the full zero-count projection. Original Lean signature: theorem invM_mul_M : invM * M = 1 - P

**Theorem 1.57 (M mul P).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_P`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_P` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reverse direction of M_eq_zero_iff_P_eq_self uses this original-mode annihilation of the projected ground. Original Lean signature: theorem M_mul_P : M * P = 0

**Theorem 1.58 (P mul M).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_mul_M`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_mul_M` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the reverse-order annihilation consequence for the actual-mode M and its full ground projection. Original Lean signature: theorem P_mul_M : P * M = 0

**Theorem 1.59 (count zero iff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.count_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P_apply uses the exhaustive original-site zero-count classification to eliminate all other coefficients. The complete zero-count occupation sets are precisely {1} and {1,3}. In particular the full kernel is not a single vacuum line. Original Lean signature: theorem count_zero_iff (S : Finset ℕ) : count S = 0 ↔ S = {1} ∨ S = {1, 3}

**Theorem 1.60 (P apply).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

full_kernel_iff uses this two-coefficient ground reconstruction after the inverse argument. The full projection retains exactly the two original coefficients at {1} and {1,3}. Original Lean signature: theorem P_apply (v : Fock) : P v = v {1} • ket {1} + v {1, 3} • ket {1, 3}

**Theorem 1.61 (M eq zero iff P eq self).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_zero_iff_P_eq_self`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_zero_iff_P_eq_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

full_kernel_iff uses the inverse and M_mul_P to characterize precisely the fixed vectors of P. Original Lean signature: theorem M_eq_zero_iff_P_eq_self (v : Fock) : M v = 0 ↔ P v = v

**Theorem 1.62 (full kernel iff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.full_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.full_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

full_kernel and relative_kernel_iff use this exact reconstruction by the two original ground kets. Original Lean signature: theorem full_kernel_iff (v : Fock) : M v = 0 ↔ ∃ a d : ℂ, v = a • ket {1} + d • ket {1, 3}

**Theorem 1.63 (full kernel).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.full_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.full_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the full-Fock kernel endpoint, retaining both the site-3-free and site-3-occupied ground. The full zero eigenspace is exactly the complex span of the two displayed original kets. Original Lean signature: theorem full_kernel : LinearMap.ker M = Submodule.span ℂ ({ket {1}, ket {1, 3}} : Set Fock)

**Theorem 1.64 (b0 down).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_down`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_down` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

relative_kernel_iff uses this simp calculation for the reverse implication on the site-3-free ground. Original Lean signature: @[simp] theorem b0_down : b 0 (ket {1}) = 0

**Theorem 1.65 (b0 eq zero iff coefficients).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_eq_zero_iff_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_eq_zero_iff_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

relative_kernel_iff uses its coefficient test at {1,3} to eliminate the second ground coefficient. The literal original zero mode b at zero is annihilation at site 3. Its kernel is characterized by vanishing of every coefficient whose occupation contains site 3. Original Lean signature: theorem b0_eq_zero_iff_coefficients (v : Fock) : b 0 v = 0 ↔ ∀ S : Finset ℕ, 3 ∈ S → v S = 0

**Theorem 1.66 (relative kernel iff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

relative_kernel and relative_kernel_c1vac use this exact conjunction of the M and b-zero equations. Original Lean signature: theorem relative_kernel_iff (v : Fock) : (M v = 0 ∧ b 0 v = 0) ↔ ∃ a : ℂ, v = a • ket {1}

**Theorem 1.67 (relative kernel).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the literal relative submodule endpoint: the intersection of the two actual operator kernels. Intersect the full count kernel with the literal original b-zero kernel. The result is exactly the line of ket {1}. Original Lean signature: theorem relative_kernel : LinearMap.ker M ⊓ LinearMap.ker (b 0) = Submodule.span ℂ ({ket {1}} : Set Fock)

**Definition 1.68 (c1vac).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c1vac`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c1vac` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named relative ground is the original c at one applied to the original empty vacuum. Original Lean signature: def c1vac : Fock

**Theorem 1.69 (c1vac eq).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c1vac_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.c1vac_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

relative_kernel_c1vac uses this identification with the original c at one acting on the empty vacuum. The original mode-vacuum formula identifies this state with ket {1}; it is not the empty occupation vacuum. Original Lean signature: theorem c1vac_eq : c1vac = ket {1}

**Theorem 1.70 (relative kernel c1vac).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel_c1vac`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_kernel_c1vac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the named original-ground endpoint for the literal relative kernel. The literal joint kernel is exactly the complex multiples of the named original c-one vacuum. Original Lean signature: theorem relative_kernel_c1vac (v : Fock) : (M v = 0 ∧ b 0 v = 0) ↔ ∃ a : ℂ, v = a • c1vac

**Theorem 1.71 (relative eigenvalue iff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_eigenvalue_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.relative_eigenvalue_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

eigenvalue_iff uses its site-3-free witnesses; it also gives the exact natural eigenvalue set under the literal relative condition. The algebraic point spectrum is exactly the natural numbers, even when the nonzero witnessing state must satisfy the literal relative b-zero condition. Original Lean signature: theorem relative_eigenvalue_iff (z : ℂ) : (∃ v : Fock, v ≠ 0 ∧ b 0 v = 0 ∧ M v = z • v) ↔ ∃ q : ℕ, z = (q : ℂ)

**Theorem 1.72 (eigenvalue iff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.eigenvalue_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.eigenvalue_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the exact full algebraic eigenvalue-set endpoint; it concerns nonzero eigenvectors on the original finite-excitation carrier. The full algebraic point spectrum is exactly the natural numbers. This is not a topological spectral theorem for a Hilbert completion. Original Lean signature: theorem eigenvalue_iff (z : ℂ) : (∃ v : Fock, v ≠ 0 ∧ M v = z • v) ↔ ∃ q : ℕ, z = (q : ℂ)

**Theorem 1.73 (M create regular).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_create_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_create_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_b_negative and M_c_negative use this regular-site count increase. Original Lean signature: theorem M_create_regular (j : ℕ) (hj1 : j ≠ 1) (hj3 : j ≠ 3) : M * create j - create j * M = create j

**Theorem 1.74 (M annihilate regular).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_annihilate_regular`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_annihilate_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

M_b_positive and M_c_positive use this regular-site count decrease. Original Lean signature: theorem M_annihilate_regular (j : ℕ) (hj1 : j ≠ 1) (hj3 : j ≠ 3) : M * annihilate j - annihilate j * M = -annihilate j

**Theorem 1.75 (M annihilate one).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_annihilate_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_annihilate_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exceptional k=1 branch of M_b_negative uses the hole-creation sign at site 1. Original Lean signature: theorem M_annihilate_one : M * annihilate 1 - annihilate 1 * M = annihilate 1

**Theorem 1.76 (M create one).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_create_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_create_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exceptional k=1 branch of M_c_positive uses the hole-filling sign at site 1. Original Lean signature: theorem M_create_one : M * create 1 - create 1 * M = -create 1

**Theorem 1.77 (M b negative).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_b_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_b_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the original negative-b commutator endpoint for every strictly positive natural index, including k=1. Every strictly negative original b mode raises the count by one, including the exceptional site-1 annihilation mode. Original Lean signature: theorem M_b_negative (k : ℕ) (hk : 0 < k) : M * b (-(k : ℤ)) - b (-(k : ℤ)) * M = b (-(k : ℤ))

**Theorem 1.78 (M c negative).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_c_negative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_c_negative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the original negative-c commutator endpoint for every strictly positive natural index. Every strictly negative original c mode raises the count by one. Original Lean signature: theorem M_c_negative (k : ℕ) (hk : 0 < k) : M * c (-(k : ℤ)) - c (-(k : ℤ)) * M = c (-(k : ℤ))

**Theorem 1.79 (M b positive).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_b_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_b_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the original positive-b commutator endpoint, with the negative sign, for every strictly positive natural index. Every strictly positive original b mode lowers the count by one. Original Lean signature: theorem M_b_positive (k : ℕ) (hk : 0 < k) : M * b (k : ℤ) - b (k : ℤ) * M = -b (k : ℤ)

**Theorem 1.80 (M c positive).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_c_positive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_c_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the original positive-c commutator endpoint, with the negative sign and a separate k=1 proof. Every strictly positive original c mode lowers the count by one, including filling the exceptional site-1 hole. Original Lean signature: theorem M_c_positive (k : ℕ) (hk : 0 < k) : M * c (k : ℤ) - c (k : ℤ) * M = -c (k : ℤ)

The projection consequences follow directly from its zero-count indicator on each original ket. If count S is zero, P fixes ket S and invM kills it; otherwise P kills ket S and invM multiplies it by the reciprocal of count S. Thus P composed with itself equals P, equivalently P squared equals P, and both invM composed with P and P composed with invM vanish. The proved M ket action additionally gives M composed with P and P composed with M equal to zero. These exact consequences are checked by anonymous applications during verification; the generic projection-only identities have no retained named declarations. Likewise the inverse coefficient action is zero at count zero and otherwise the reciprocal count times the original coefficient. For the second full ground, b at zero acts on ket {1,3} as minus ket {1}: exactly one occupied site lies below 3 and erasing 3 leaves {1}. The relative-kernel proof instead uses b0_eq_zero_iff_coefficients at {1,3}; it does not consume a named special-ground sign lemma. Natural nonnegativity is inherent in count, and M is defined by modeSum; neither fact requires a separate theorem alias.

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
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_sum`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_eq_zero_iff_P_eq_self`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_P`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_mul_invM`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.M_support_subset`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_apply`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_coefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.P_mul_M`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_pos`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.U_zero_above_capture`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.annihilate_create_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_down`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.b0_eq_zero_iff_coefficients`
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
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostQuartetCount.invM_mul_M`
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
