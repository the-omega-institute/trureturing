/- GID: D5/S3/VertexAlgebra/BcGhostEnergyRotation
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/BcGhostEnergyRotation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual integer ghost conformal-energy half-turn is a real involution on the full finite-support bc Fock carrier.
-/

import D5.S3.VertexAlgebra.BcGhostLZeroSpectrum
import D5.S3.VertexAlgebra.BcGhostStressCurrent
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.BcGhostEnergyRotation

open D5.S3.VertexAlgebra.BcGhostFockSupport
open D5.S3.VertexAlgebra.BcGhostLZeroSpectrum
open scoped BigOperators

noncomputable section

abbrev GhostFock := Fock ℂ

def phase (subset : Finset ℕ) : ℂ := (-1 : ℂ) ^ energy subset

noncomputable def rotation : Module.End ℂ GhostFock :=
  Finsupp.linearCombination ℂ (fun subset => phase subset • Finsupp.single subset 1)

theorem energy_insert (site : ℕ) (subset : Finset ℕ) (absent : site ∉ subset) :
    energy (insert site subset) = energy subset + siteWeight site := by
  simp [energy, absent, add_comm]

theorem energy_erase (site : ℕ) (subset : Finset ℕ) (present : site ∈ subset) :
    energy (subset.erase site) = energy subset - siteWeight site := by
  have inserted := energy_insert site (subset.erase site) (by simp)
  rw [Finset.insert_erase present] at inserted
  omega

theorem phase_add (left right : ℤ) :
    (-1 : ℂ) ^ (left + right) = (-1 : ℂ) ^ left * (-1 : ℂ) ^ right := by
  rw [zpow_add₀]
  norm_num

theorem phase_square (integer : ℤ) :
    (-1 : ℂ) ^ integer * (-1 : ℂ) ^ integer = 1 := by
  rw [← phase_add integer integer]
  rw [show integer + integer = 2 * integer by ring, zpow_mul]
  norm_num

theorem phase_neg (integer : ℤ) :
    (-1 : ℂ) ^ (-integer) = (-1 : ℂ) ^ integer := by
  rw [zpow_neg]
  exact (mul_eq_one_iff_inv_eq₀
    (zpow_ne_zero integer (by norm_num : (-1 : ℂ) ≠ 0))).mp
    (phase_square integer)

theorem phase_insert (site : ℕ) (subset : Finset ℕ) (absent : site ∉ subset) :
    phase (insert site subset) =
      (-1 : ℂ) ^ siteWeight site * phase subset := by
  change (-1 : ℂ) ^ energy (insert site subset) =
    (-1 : ℂ) ^ siteWeight site * (-1 : ℂ) ^ energy subset
  rw [energy_insert site subset absent, phase_add]
  ring

theorem phase_erase (site : ℕ) (subset : Finset ℕ) (present : site ∈ subset) :
    phase (subset.erase site) =
      (-1 : ℂ) ^ siteWeight site * phase subset := by
  have henergy : energy (subset.erase site) + siteWeight site = energy subset := by
    rw [energy_erase site subset present]
    ring
  have hphase : phase subset =
      (-1 : ℂ) ^ siteWeight site * phase (subset.erase site) := by
    change (-1 : ℂ) ^ energy subset =
      (-1 : ℂ) ^ siteWeight site * (-1 : ℂ) ^ energy (subset.erase site)
    rw [← henergy, phase_add]
    ring
  have hsquare :
      (-1 : ℂ) ^ siteWeight site * (-1 : ℂ) ^ siteWeight site = 1 :=
    phase_square (siteWeight site)
  calc
    phase (subset.erase site) = 1 * phase (subset.erase site) := by simp
    _ = ((-1 : ℂ) ^ siteWeight site * (-1 : ℂ) ^ siteWeight site) *
        phase (subset.erase site) := by rw [hsquare]
    _ = (-1 : ℂ) ^ siteWeight site *
        ((-1 : ℂ) ^ siteWeight site * phase (subset.erase site)) := by ring
    _ = (-1 : ℂ) ^ siteWeight site * phase subset := by rw [← hphase]

theorem siteWeight_even (index : ℕ) :
    siteWeight (2 * index) = (index : ℤ) + 2 := by
  simp [siteWeight]

theorem siteWeight_odd (index : ℕ) :
    siteWeight (2 * index + 1) = (index : ℤ) - 1 := by
  have parity : (2 * index + 1) % 2 ≠ 0 := by omega
  have quotient : (2 * index + 1) / 2 = index := by omega
  simp only [siteWeight, if_neg parity, quotient]

theorem phase_conj (subset : Finset ℕ) :
    star (phase subset) = phase subset := by
  simp [phase]

theorem rotation_single (subset : Finset ℕ) (scalar : ℂ) :
    rotation (Finsupp.single subset scalar) = phase subset • Finsupp.single subset scalar := by
  classical
  apply Finsupp.ext
  intro target
  by_cases equality : subset = target
  · subst target
    simp [rotation, phase, Finsupp.linearCombination_single]
    ring
  · simp [rotation, phase, Finsupp.linearCombination_single, equality]

theorem rotation_create (site : ℕ) (state : GhostFock) :
    rotation (create site state) =
      ((-1 : ℂ) ^ siteWeight site) • create site (rotation state) := by
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
      simp only [map_add, firstProof, secondProof, smul_add]
  | single subset scalar =>
      simp only [create, Finsupp.linearCombination_single, map_smul]
      by_cases present : site ∈ subset
      · rw [rotation_single, map_smul, Finsupp.linearCombination_single]
        simp [createBasis, present, mul_assoc, mul_left_comm, mul_comm]
      · rw [rotation_single, map_smul, Finsupp.linearCombination_single]
        simp only [createBasis, if_neg present]
        rw [rotation_single]
        simp [phase_insert site subset present, mul_assoc, mul_left_comm, mul_comm]

theorem rotation_annihilate (site : ℕ) (state : GhostFock) :
    rotation (annihilate site state) =
      ((-1 : ℂ) ^ siteWeight site) • annihilate site (rotation state) := by
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
      simp only [map_add, firstProof, secondProof, smul_add]
  | single subset scalar =>
      simp only [annihilate, Finsupp.linearCombination_single, map_smul]
      by_cases present : site ∈ subset
      · rw [rotation_single, map_smul, Finsupp.linearCombination_single]
        simp only [annihilateBasis, if_pos present]
        rw [rotation_single]
        simp [phase_erase site subset present, mul_assoc, mul_left_comm, mul_comm]
      · rw [rotation_single, map_smul, Finsupp.linearCombination_single]
        simp [annihilateBasis, present, mul_assoc, mul_left_comm, mul_comm]

theorem rotation_b (mode : ℤ) :
    rotation * b mode = (-1 : ℂ) ^ mode • (b mode * rotation) := by
  apply LinearMap.ext
  intro state
  change rotation (b mode state) = (-1 : ℂ) ^ mode • b mode (rotation state)
  by_cases creator : mode ≤ -2
  · have weight : siteWeight (2 * (-mode - 2).toNat) = -mode := by
      rw [siteWeight_even]
      omega
    have h := rotation_create (2 * (-mode - 2).toNat) state
    rw [weight, phase_neg] at h
    simpa [b, creator] using h
  · have weight : siteWeight (2 * (mode + 1).toNat + 1) = mode := by
      rw [siteWeight_odd]
      omega
    simpa [b, creator, weight] using
      rotation_annihilate (2 * (mode + 1).toNat + 1) state

theorem rotation_c (mode : ℤ) :
    rotation * c mode = (-1 : ℂ) ^ mode • (c mode * rotation) := by
  apply LinearMap.ext
  intro state
  change rotation (c mode state) = (-1 : ℂ) ^ mode • c mode (rotation state)
  by_cases creator : mode ≤ 1
  · have weight : siteWeight (2 * (1 - mode).toNat + 1) = -mode := by
      rw [siteWeight_odd]
      omega
    have h := rotation_create (2 * (1 - mode).toNat + 1) state
    rw [weight, phase_neg] at h
    simpa [c, creator] using h
  · have weight : siteWeight (2 * (mode - 2).toNat) = mode := by
      rw [siteWeight_even]
      omega
    simpa [c, creator, weight] using
      rotation_annihilate (2 * (mode - 2).toNat) state

theorem rotation_coefficient (state : GhostFock) (subset : Finset ℕ) :
    rotation state subset = phase subset * state subset := by
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
      simp only [map_add, Finsupp.add_apply, firstProof, secondProof]
      rw [mul_add]
  | single label scalar =>
      by_cases equality : label = subset
      · subst subset
        simp [rotation, phase, Finsupp.linearCombination_single]
        ring
      · simp [rotation, phase, Finsupp.linearCombination_single, equality]

theorem rotation_involutive :
    rotation.comp rotation = (LinearMap.id : Module.End ℂ GhostFock) := by
  apply LinearMap.ext
  intro state
  apply Finsupp.ext
  intro subset
  rw [LinearMap.comp_apply, rotation_coefficient, rotation_coefficient]
  have square : phase subset * phase subset = 1 := by
    exact phase_square (energy subset)
  calc
    phase subset * (phase subset * state subset) =
        (phase subset * phase subset) * state subset := by ring
    _ = state subset := by rw [square, one_mul]
    _ = (LinearMap.id state) subset := by rfl

theorem rotation_star_coefficient (state : GhostFock) (subset : Finset ℕ) :
    star (rotation state subset) = phase subset * star (state subset) := by
  rw [rotation_coefficient]
  simp [phase_conj]

theorem rotation_commutes_zero :
    rotation * L 0 = L 0 * rotation := by
  apply LinearMap.ext
  intro state
  change rotation (L 0 state) = L 0 (rotation state)
  induction state using Finsupp.induction_linear with
  | zero => simp
  | add first second firstProof secondProof =>
      simp only [map_add, firstProof, secondProof]
  | single label scalar =>
      simp only [L_zero_single, map_smul, rotation_single]
      simp [phase, mul_assoc, mul_left_comm, mul_comm]

end
end D5.S3.VertexAlgebra.BcGhostEnergyRotation
