/- GID: D5/S3/VertexAlgebra/BcGhostLZeroSpectrum
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostLZeroSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original ghost zero stress has integral weighted occupation on all finite subsets. -/

/-
proof_shape: L_zero_single: content
escape_witness: Signed insertion and erasure of arbitrary finite subsets change
  the actual variable site-weight sum by the weight of that site. These all-state
  identities give the diagonal comparison operator the original integer b/c
  mode brackets, including negative c-creator energy. The supplied ghost-only
  commutant and vacuum annihilation then identify it with the original L zero.
admission_basis: escape-witness
utility: none; this is a uniform symbolic operator theorem over every finite
  subset and every commutative coefficient ring, not a bounded instance.
-/

import D5.S3.VertexAlgebra.BcGhostFockCommutant
import D5.S3.VertexAlgebra.BcGhostVacuum

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostLZeroSpectrum

open BcGhostFockSupport BcGhostStressCurrent BcGhostFockCommutant BcGhostVacuum
open scoped BigOperators

noncomputable section

variable {K : Type*} [CommRing K]

def siteWeight (site : ℕ) : ℤ :=
  if site % 2 = 0 then ((site / 2 : ℕ) : ℤ) + 2 else ((site / 2 : ℕ) : ℤ) - 1

def energy (subset : Finset ℕ) : ℤ := ∑ site ∈ subset, siteWeight site

private def diagonal : Module.End K (Fock K) :=
  Finsupp.linearCombination K (fun subset =>
    (energy subset : K) • Finsupp.single subset 1)

private theorem siteWeight_even (index : ℕ) : siteWeight (2 * index) = (index : ℤ) + 2 := by
  simp [siteWeight]

private theorem siteWeight_odd (index : ℕ) :
    siteWeight (2 * index + 1) = (index : ℤ) - 1 := by
  have parity : (2 * index + 1) % 2 ≠ 0 := by omega
  have quotient : (2 * index + 1) / 2 = index := by omega
  simp only [siteWeight, if_neg parity, quotient]

private theorem energy_insert (site : ℕ) (subset : Finset ℕ) (absent : site ∉ subset) :
    energy (insert site subset) = energy subset + siteWeight site := by
  simp [energy, absent, add_comm]

private theorem energy_erase (site : ℕ) (subset : Finset ℕ) (present : site ∈ subset) :
    energy (subset.erase site) = energy subset - siteWeight site := by
  have inserted := energy_insert site (subset.erase site) (by simp)
  rw [Finset.insert_erase present] at inserted
  omega

private theorem diagonal_single (subset : Finset ℕ) (scalar : K) :
    diagonal (Finsupp.single subset scalar) =
      (energy subset : K) • Finsupp.single subset scalar := by
  simp [diagonal, Finsupp.smul_single, mul_comm]

private theorem diagonal_create_apply (site : ℕ) (state : Fock K) :
    diagonal (create site state) - create site (diagonal state) =
      (siteWeight site : K) • create site state := by
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
      simp only [map_add, smul_add]
      calc
        _ = (diagonal (create site first) - create site (diagonal first)) +
            (diagonal (create site second) - create site (diagonal second)) := by abel
        _ = _ := by rw [firstProof, secondProof]
  | single subset scalar =>
      simp only [create, Finsupp.linearCombination_single, diagonal_single, map_smul]
      by_cases present : site ∈ subset
      · simp [createBasis, present]
      · simp only [createBasis, if_neg present, diagonal_single]
        rw [energy_insert site subset present]
        simp only [Int.cast_add, add_smul, smul_smul]
        module

private theorem diagonal_annihilate_apply (site : ℕ) (state : Fock K) :
    diagonal (annihilate site state) - annihilate site (diagonal state) =
      -(siteWeight site : K) • annihilate site state := by
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
      simp only [map_add, smul_add]
      calc
        _ = (diagonal (annihilate site first) - annihilate site (diagonal first)) +
            (diagonal (annihilate site second) - annihilate site (diagonal second)) := by abel
        _ = _ := by rw [firstProof, secondProof]
  | single subset scalar =>
      simp only [annihilate, Finsupp.linearCombination_single, diagonal_single, map_smul]
      by_cases present : site ∈ subset
      · simp only [annihilateBasis, if_pos present, diagonal_single]
        rw [energy_erase site subset present]
        simp only [Int.cast_sub, sub_smul, smul_smul]
        module
      · simp [annihilateBasis, present]

private theorem diagonal_b_commutator (mode : ℤ) :
    diagonal (K := K) * b mode - b mode * diagonal = -(mode : K) • b mode := by
  apply LinearMap.ext
  intro state
  change diagonal (b mode state) - b mode (diagonal state) = -(mode : K) • b mode state
  by_cases creator : mode ≤ -2
  · have weight : siteWeight (2 * (-mode - 2).toNat) = -mode := by
      rw [siteWeight_even]
      have cast := Int.toNat_of_nonneg (show 0 ≤ -mode - 2 by omega)
      omega
    simpa only [b, if_pos creator, weight, Int.cast_neg] using
      diagonal_create_apply (K := K) (2 * (-mode - 2).toNat) state
  · have weight : siteWeight (2 * (mode + 1).toNat + 1) = mode := by
      rw [siteWeight_odd]
      have cast := Int.toNat_of_nonneg (show 0 ≤ mode + 1 by omega)
      omega
    simpa only [b, if_neg creator, weight] using
      diagonal_annihilate_apply (K := K) (2 * (mode + 1).toNat + 1) state

private theorem diagonal_c_commutator (mode : ℤ) :
    diagonal (K := K) * c mode - c mode * diagonal = -(mode : K) • c mode := by
  apply LinearMap.ext
  intro state
  change diagonal (c mode state) - c mode (diagonal state) = -(mode : K) • c mode state
  by_cases creator : mode ≤ 1
  · have weight : siteWeight (2 * (1 - mode).toNat + 1) = -mode := by
      rw [siteWeight_odd]
      have cast := Int.toNat_of_nonneg (show 0 ≤ 1 - mode by omega)
      omega
    simpa only [c, if_pos creator, weight, Int.cast_neg] using
      diagonal_create_apply (K := K) (2 * (1 - mode).toNat + 1) state
  · have weight : siteWeight (2 * (mode - 2).toNat) = mode := by
      rw [siteWeight_even]
      have cast := Int.toNat_of_nonneg (show 0 ≤ mode - 2 by omega)
      omega
    simpa only [c, if_neg creator, weight] using
      diagonal_annihilate_apply (K := K) (2 * (mode - 2).toNat) state

private theorem diagonal_eq_L_zero : diagonal (K := K) = L 0 := by
  let difference : Module.End K (Fock K) := diagonal - L 0
  have bCommutation (mode : ℤ) :
      difference.comp (b mode) = (b mode).comp difference := by
    apply sub_eq_zero.mp
    simp only [← Module.End.mul_eq_comp]
    dsimp only [difference]
    have stress : L (K := K) 0 * b mode - b mode * L 0 = -(mode : K) • b mode := by
      simpa using L_b_commutator (K := K) 0 mode
    calc
      _ = (diagonal (K := K) * b mode - b mode * diagonal) -
          (L 0 * b mode - b mode * L 0) := by noncomm_ring
      _ = 0 := by rw [diagonal_b_commutator, stress, sub_self]
  have cCommutation (mode : ℤ) :
      difference.comp (c mode) = (c mode).comp difference := by
    apply sub_eq_zero.mp
    simp only [← Module.End.mul_eq_comp]
    dsimp only [difference]
    have stress : L (K := K) 0 * c mode - c mode * L 0 = -(mode : K) • c mode := by
      simpa using L_c_commutator (K := K) 0 mode
    calc
      _ = (diagonal (K := K) * c mode - c mode * diagonal) -
          (L 0 * c mode - c mode * L 0) := by noncomm_ring
      _ = 0 := by rw [diagonal_c_commutator, stress, sub_self]
  have scalar := mode_commutant_scalar difference bCommutation cCommutation
  have emptyAction : diagonal (vacuum : Fock K) = 0 := by
    simp [vacuum, diagonal_single, energy]
  have emptyCoefficient : (difference vacuum) ∅ = 0 := by
    dsimp only [difference]
    rw [LinearMap.sub_apply, emptyAction, L_vacuum_annihilation 0 (by omega), sub_self]
    rfl
  rw [emptyCoefficient, zero_smul] at scalar
  exact sub_eq_zero.mp scalar

theorem L_zero_single (subset : Finset ℕ) (scalar : K) :
    L (K := K) 0 (Finsupp.single subset scalar) =
      (energy subset : K) • Finsupp.single subset scalar := by
  rw [← diagonal_eq_L_zero, diagonal_single]

#print axioms diagonal_create_apply
#print axioms diagonal_annihilate_apply
#print axioms diagonal_eq_L_zero
#print axioms L_zero_single

end

end D5.S3.VertexAlgebra.BcGhostLZeroSpectrum
