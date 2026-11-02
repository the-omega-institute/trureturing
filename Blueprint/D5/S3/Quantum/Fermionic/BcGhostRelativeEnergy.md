# Original bc relative energy

## Abstract

Original bc relative energy

The carrier is exactly CountableOccupationFock.Fock = Finset Nat ->_0 Complex, and ket S = Finsupp.single S 1. The operators b,c and L are the original BcGhostFock and BcGhostVirasoro operators. L(0)v is the statewise locally finite finsum over ALL q:Int of summand 0 q v. The proof reduces this actual sum to active modes; it never replaces it by a bounded-mode operator.

For each j:Nat put e(j)=-siteMode(j)*siteSign(j):Int, E(S)=sum(j in S)e(j), R(S)=E(S)+1 and level(S)=R(S).toNat. Explicitly e(2k)=k+2, e(2k+1)=k-1, so e(1)=-1 and e(3)=0. b(0) is the original annihilation operator at site 3. The down vector is literally c(1) vacuum = ket {1}. R is nonnegative even outside the relative kernel; it is not the unshifted L(0) eigenvalue.

All variables and premises of each declaration are included in its exact Lean telescope below. For every ell:Nat, RelativeLevel ell v means b(0)v=0 AND (L(0)+id)v=ell*v. Its finite ket basis uses occupations excluding site 3 of exact relative energy ell, contained in range(2*ell+4). The proof supplies the support bound and the basis rather than assuming either.

These are algebraic statements on finite-excitation vectors. Nonnegative relative energy is not positivity of a Hermitian form. No quartet contraction, no-ghost theorem, full BRST/string theory, Monster moonshine, complete VOA/CFT, anomaly/fusion completion or AdS/CFT completion follows here. These precise original-carrier statements are repo-derived; no literature novelty is claimed.

Registration audit is unfinished for all 43 retained public theorems: https://github.com/the-omega-institute/trureturing/issues/25750. Completed registrations: 0; no declared_validated registration is claimed. The three excluded unconsumed research companions retain their exact statements and proofs in the pinned pre-repair native evidence linked by that issue.

**Definition 1.1 (siteEnergy).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed original site mode gives the integer contribution -siteMode(j)*siteSign(j).

Exact Lean telescope: def siteEnergy (j : ℕ) : ℤ

**Definition 1.2 (energy).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.energy`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.energy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unshifted ghost energy is the sum of siteEnergy over the actual finite occupation S.

Exact Lean telescope: def energy (S : Finset ℕ) : ℤ

**Definition 1.3 (relativeEnergy).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeEnergy`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The relative energy is energy(S)+1; the shift is fixed by the actual down state, not a replacement for L(0).

Exact Lean telescope: def relativeEnergy (S : Finset ℕ) : ℤ

**Theorem 1.4 (L_zero_ket).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_ket`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_ket` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof evaluates the original locally finite sum over every integer mode q, reduces its support to activeModes(ket S), reindexes by siteMode and obtains the diagonal eigenvalue energy(S). No bounded-mode operator is substituted.

Exact Lean telescope: theorem L_zero_ket (S : Finset ℕ) : L 0 (ket S) = (energy S : ℂ) • ket S

**Theorem 1.5 (L_zero_coefficient).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finsupp induction extends the ket calculation to every original Fock vector, including mixed energies.

Exact Lean telescope: theorem L_zero_coefficient (v : Fock) (S : Finset ℕ) : (L 0 v) S = (energy S : ℂ) * v S

**Theorem 1.6 (siteEnergy_even).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_even`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every even site 2*k has energy k+2, for all k in Nat.

Exact Lean telescope: theorem siteEnergy_even (k : ℕ) : siteEnergy (2*k) = (k : ℤ) + 2

**Theorem 1.7 (siteEnergy_odd).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_odd`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every odd site 2*k+1 has energy k-1 in Int, including k=0 and k=1.

Exact Lean telescope: theorem siteEnergy_odd (k : ℕ) : siteEnergy (2*k+1) = (k : ℤ) - 1

**Theorem 1.8 (siteEnergy_one).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupied site 1 has energy -1; the convention retains the exceptional negative-energy site.

Exact Lean telescope: theorem siteEnergy_one : siteEnergy 1 = -1

**Theorem 1.9 (siteEnergy_three).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupied site 3 has energy zero; its exclusion comes from ker b(0), not an energy inequality.

Exact Lean telescope: theorem siteEnergy_three : siteEnergy 3 = 0

**Theorem 1.10 (siteEnergy_pos_of_ne_one_three).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_pos_of_ne_one_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_pos_of_ne_one_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All other sites have strictly positive integer site energy.

Exact Lean telescope: theorem siteEnergy_pos_of_ne_one_three {j : ℕ} (h1 : j ≠ 1) (h3 : j ≠ 3) : 0 < siteEnergy j

**Theorem 1.11 (L_zero_down).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_down`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_down` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal c(1) vacuum, equal to ket {1}, is a -1 eigenvector of the original L(0).

Exact Lean telescope: theorem L_zero_down : L 0 (c 1 vacuum) = -(c 1 vacuum)

**Theorem 1.12 (b_zero_down).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.b_zero_down`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.b_zero_down` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original b(0) annihilates ket {1}; the coefficient characterization of its kernel supplies the proof.

Exact Lean telescope: theorem b_zero_down : b 0 (ket {1}) = 0

**Theorem 1.13 (relativeEnergy_split).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeEnergy_split`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeEnergy_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Separating sites 1 and 3 gives the missing-site-1 indicator plus the positive contributions of the remaining sites. This includes every finite occupation, whether or not it lies in ker b(0).

Exact Lean telescope: theorem relativeEnergy_split (S : Finset ℕ) : relativeEnergy S = (if 1 ∉ S then 1 else 0) + ∑ j ∈ (S.erase 1).erase 3, siteEnergy j

**Theorem 1.14 (relativeEnergy_nonneg).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeEnergy_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeEnergy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The split proves nonnegativity of the shifted ghost energy for every occupation. It asserts nothing about the lattice Gram form or an inner product.

Exact Lean telescope: theorem relativeEnergy_nonneg (S : Finset ℕ) : 0 ≤ relativeEnergy S

**Definition 1.15 (level).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.level`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.level` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural relative level is relativeEnergy(S).toNat.

Exact Lean telescope: def level (S : Finset ℕ) : ℕ

**Theorem 1.16 (level_cast).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.level_cast`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.level_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegativity proves that casting the natural level back to Int recovers relativeEnergy exactly.

Exact Lean telescope: theorem level_cast (S : Finset ℕ) : (level S : ℤ) = relativeEnergy S

**Definition 1.17 (relativeOperator).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeOperator`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeOperator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This endomorphism is the original L(0) plus the identity on the original Fock carrier.

Exact Lean telescope: def relativeOperator : Module.End ℂ Fock

**Theorem 1.18 (relativeOperator_coefficient).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeOperator_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeOperator_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shifted original operator multiplies each original coefficient by relativeEnergy(S).

Exact Lean telescope: theorem relativeOperator_coefficient (v : Fock) (S : Finset ℕ) : (relativeOperator v) S = (relativeEnergy S : ℂ) * v S

**Definition 1.19 (RelativeKernel).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.RelativeKernel`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.RelativeKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This predicate means literally b(0)(v)=0.

Exact Lean telescope: def RelativeKernel (v : Fock) : Prop

**Definition 1.20 (RelativeLevel).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.RelativeLevel`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.RelativeLevel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This predicate is the conjunction of the literal b(0) kernel and the ell eigen-equation for L(0)+id; ell ranges over every natural number.

Exact Lean telescope: def RelativeLevel (ell : ℕ) (v : Fock) : Prop

**Theorem 1.21 (relative_level_coeff_iff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_coeff_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_coeff_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions hold for any Fock vector: coefficients on occupations containing site 3 vanish, and every nonzero coefficient has relativeEnergy ell. No support or eigenvector premise is suppressed.

Exact Lean telescope: theorem relative_level_coeff_iff (ell : ℕ) (v : Fock) : RelativeLevel ell v ↔ (∀ S : Finset ℕ, 3 ∈ S → v S = 0) ∧ (∀ S : Finset ℕ, v S ≠ 0 → relativeEnergy S = (ell : ℤ))

**Theorem 1.22 (relative_ground_line).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_ground_line`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_ground_line` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint kernel of b(0) and L(0)+id is exactly the complex line through the actual ket {1}. The zero coefficient is allowed.

Exact Lean telescope: theorem relative_ground_line (v : Fock) : (RelativeKernel v ∧ relativeOperator v = 0) ↔ ∃ α : ℂ, v = α • ket {1}

**Theorem 1.23 (relative_level_support).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_support`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a vector in RelativeLevel ell, each occupation with nonzero original coefficient is contained in range(2*ell+4). The proof uses both the level equation and exclusion of site 3.

Exact Lean telescope: theorem relative_level_support (ell : ℕ) (v : Fock) (hv : RelativeLevel ell v) : ∀ S : Finset ℕ, v S ≠ 0 → S ⊆ Finset.range (2*ell+4)

**Definition 1.24 (levelOccupationSets).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.levelOccupationSets`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.levelOccupationSets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This finite set filters the powerset of range(2*ell+4) by exclusion of site 3 and the exact integer energy equation.

Exact Lean telescope: def levelOccupationSets (ell : ℕ) : Finset (Finset ℕ)

**Theorem 1.25 (mem_levelOccupationSets_iff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.mem_levelOccupationSets_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.mem_levelOccupationSets_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the complete membership criterion, including the finite range bound, site-3 exclusion and exact integer relative energy.

Exact Lean telescope: theorem mem_levelOccupationSets_iff (ell : ℕ) (S : Finset ℕ) : S ∈ levelOccupationSets ell ↔ S ⊆ Finset.range (2*ell+4) ∧ 3 ∉ S ∧ relativeEnergy S = (ell : ℤ)

**Theorem 1.26 (relative_level_expansion).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual relative-level vector is the finite sum of its original coefficients times the original kets over levelOccupationSets ell.

Exact Lean telescope: theorem relative_level_expansion (ell : ℕ) (v : Fock) (hv : RelativeLevel ell v) : v = ∑ S ∈ levelOccupationSets ell, v S • ket S

**Definition 1.27 (levelKets).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.levelKets`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.levelKets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spanning set is the image of the finite allowed occupation set under the original ket map.

Exact Lean telescope: def levelKets (ell : ℕ) : Set Fock

**Theorem 1.28 (level_ket_linearIndependent).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.level_ket_linearIndependent`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.level_ket_linearIndependent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independence is inherited from the full original Finsupp unit basis after restriction to the finite allowed occupations.

Exact Lean telescope: theorem level_ket_linearIndependent (ell : ℕ) : LinearIndependent ℂ (fun S : {S : Finset ℕ // S ∈ levelOccupationSets ell} => ket S)

**Theorem 1.29 (relative_level_mem_span).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_mem_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_mem_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite coefficient expansion places every actual relative-level vector in the span of the original allowed kets.

Exact Lean telescope: theorem relative_level_mem_span (ell : ℕ) (v : Fock) (hv : RelativeLevel ell v) : v ∈ Submodule.span ℂ (levelKets ell)

**Definition 1.30 (relativeLevelSpace).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeLevelSpace`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeLevelSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual simultaneous kernel/eigenspace is a complex submodule, closed under zero, sums and scalar multiplication.

Exact Lean telescope: def relativeLevelSpace (ell : ℕ) : Submodule ℂ Fock where carrier

**Theorem 1.31 (mem_relativeLevelSpace_iff).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.mem_relativeLevelSpace_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.mem_relativeLevelSpace_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership unfolds to the full RelativeLevel predicate; this bridge is used to prove the basis vectors belong to the actual submodule.

Exact Lean telescope: theorem mem_relativeLevelSpace_iff (ell : ℕ) (v : Fock) : v ∈ relativeLevelSpace ell ↔ RelativeLevel ell v

**Theorem 1.32 (relative_level_space_eq_span).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_space_eq_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_space_eq_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both submodule inclusions are proved: the actual relative-level space equals the span of the original allowed kets.

Exact Lean telescope: theorem relative_level_space_eq_span (ell : ℕ) : relativeLevelSpace ell = Submodule.span ℂ (levelKets ell)

**Definition 1.33 (relativeLevelBasis).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeLevelBasis`

*Formalization.* `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeLevelBasis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A genuine basis of the actual submodule is constructed by transporting the basis of the span of the independent allowed kets.

Exact Lean telescope: def relativeLevelBasis (ell : ℕ) : Module.Basis {S : Finset ℕ // S ∈ levelOccupationSets ell} ℂ (relativeLevelSpace ell)

**Theorem 1.34 (relative_level_finite_dimensional).**

Lean statement: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_finite_dimensional`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_finite_dimensional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite index set of that actual basis proves finite dimensionality of every relative-level space.

Exact Lean telescope: theorem relative_level_finite_dimensional (ell : ℕ) : FiniteDimensional ℂ (relativeLevelSpace ell)

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_coefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_down`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.L_zero_ket`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.RelativeKernel`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.RelativeLevel`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.b_zero_down`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.energy`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.level`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.levelKets`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.levelOccupationSets`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.level_cast`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.level_ket_linearIndependent`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.mem_levelOccupationSets_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.mem_relativeLevelSpace_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeEnergy`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeEnergy_nonneg`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeEnergy_split`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeLevelBasis`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeLevelSpace`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeOperator`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relativeOperator_coefficient`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_ground_line`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_coeff_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_expansion`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_finite_dimensional`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_mem_span`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_space_eq_span`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.relative_level_support`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_even`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_odd`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_one`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_pos_of_ne_one_three`
- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostRelativeEnergy.siteEnergy_three`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostCharge](BcGhostCharge.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostQuartetCount](BcGhostQuartetCount.md)
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostVirasoro](BcGhostVirasoro.md)
