/- GID: D5/S3/Quantum/Fermionic/BcGhostChargeTensor
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostChargeTensor
   mirror-E: none(waiver:algebraic-tensor-charge)
   anchors: []
   utility: none
   digest: Finite normal capture annihilates charged tensor ghost commutants. -/

import D5.S3.Quantum.Fermionic.BcGhostCharge
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! No restriction on the dimension or representation of the matter module is imposed. -/

open scoped BigOperators TensorProduct
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostCharge

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostChargeTensor

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The identity on arbitrary matter, tensored with an actual ghost endomorphism. -/
def liftGhost (T : Module.End ℂ Fock) : Module.End ℂ (M ⊗[ℂ] Fock) :=
  TensorProduct.map LinearMap.id T

abbrev number : Module.End ℂ (M ⊗[ℂ] Fock) := liftGhost ghostNumber
abbrev B (m : ℤ) : Module.End ℂ (M ⊗[ℂ] Fock) := liftGhost (b m)
abbrev C (m : ℤ) : Module.End ℂ (M ⊗[ℂ] Fock) := liftGhost (c m)

def partialNumber (K : Finset ℤ) : Module.End ℂ (M ⊗[ℂ] Fock) :=
  ∑ n ∈ K, liftGhost (normalTerm n)

private theorem lift_mul (T U : Module.End ℂ Fock) :
    liftGhost (M := M) (T * U) = liftGhost T * liftGhost U := by
  ext m v
  simp [liftGhost, Module.End.mul_apply]

private theorem lift_neg (T : Module.End ℂ Fock) :
    liftGhost (M := M) (-T) = -liftGhost T := by
  apply TensorProduct.ext'
  intro m v
  simp only [liftGhost, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.neg_apply]
  exact TensorProduct.tmul_neg m (T v)

private theorem partial_tmul (K : Finset ℤ) (m : M) (v : Fock) :
    partialNumber K (m ⊗ₜ[ℂ] v) = m ⊗ₜ[ℂ] ((∑ n ∈ K, normalTerm n) v) := by
  simp [partialNumber, liftGhost, TensorProduct.tmul_sum, LinearMap.sum_apply]

/-- A tensor has one finite ghost capture, valid for every larger finite set. -/
theorem tensor_finite_capture (x : M ⊗[ℂ] Fock) :
    ∃ K : Finset ℤ, ∀ L : Finset ℤ, K ⊆ L → partialNumber L x = number x := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun L hL => by simp⟩
  | tmul m v =>
    refine ⟨activeModes v, fun L hL => ?_⟩
    rw [partial_tmul, finite_normal_capture v L hL]
    rfl
  | add x y hx hy =>
    obtain ⟨K, hK⟩ := hx
    obtain ⟨J, hJ⟩ := hy
    refine ⟨K ∪ J, fun L hL => ?_⟩
    rw [map_add, map_add, hK L (Finset.Subset.trans Finset.subset_union_left hL),
      hJ L (Finset.Subset.trans Finset.subset_union_right hL)]

private theorem bilinear_commutes (E : Module.End ℂ (M ⊗[ℂ] Fock)) (ε : ℂ)
    (hε : ε * ε = 1)
    (hb : ∀ m : ℤ, E * B m = ε • (B m * E))
    (hc : ∀ m : ℤ, E * C m = ε • (C m * E)) (n : ℤ) :
    E * liftGhost (normalTerm n) = liftGhost (normalTerm n) * E := by
  have pair (U V : Module.End ℂ (M ⊗[ℂ] Fock))
      (hU : E * U = ε • (U * E)) (hV : E * V = ε • (V * E)) :
      E * (U * V) = (U * V) * E := by
    calc
      E * (U * V) = (E * U) * V := (mul_assoc _ _ _).symm
      _ = ε • (U * (E * V)) := by rw [hU, smul_mul_assoc, mul_assoc]
      _ = (ε * ε) • ((U * V) * E) := by
        rw [hV, mul_smul_comm, smul_smul, mul_assoc]
      _ = (U * V) * E := by rw [hε, one_smul]
  unfold normalTerm
  split_ifs
  · rw [lift_mul]
    exact pair (C n) (B (-n)) (hc n) (hb (-n))
  · rw [lift_neg, lift_mul, mul_neg, neg_mul, pair (B (-n)) (C n) (hb (-n)) (hc n)]

/-- Commutation or anticommutation with both odd mode families implies charge neutrality.
The finite set used at a vector captures both that vector and its image under E. -/
theorem number_commutes_of_signed_modes
    (E : Module.End ℂ (M ⊗[ℂ] Fock)) (ε : ℂ) (hε : ε * ε = 1)
    (hb : ∀ m : ℤ, E * B m = ε • (B m * E))
    (hc : ∀ m : ℤ, E * C m = ε • (C m * E)) :
    number * E - E * number = 0 := by
  classical
  apply LinearMap.ext
  intro x
  obtain ⟨K, hK⟩ := tensor_finite_capture x
  obtain ⟨J, hJ⟩ := tensor_finite_capture (E x)
  let L := K ∪ J
  have hcomm : E * partialNumber L = partialNumber L * E := by
    simp only [partialNumber, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun n hn => bilinear_commutes E ε hε hb hc n)
  have hLx := hK L Finset.subset_union_left
  have hLEx := hJ L Finset.subset_union_right
  have he := LinearMap.congr_fun hcomm x
  change number (E x) - E (number x) = 0
  rw [← hLx, ← hLEx]
  exact sub_eq_zero.mpr he.symm

/-- Commuting with every tensor b and c is incompatible with nonzero charge degree. -/
theorem charged_commutant_vanishes
    (E : Module.End ℂ (M ⊗[ℂ] Fock))
    (hb : ∀ m : ℤ, E * B m = B m * E)
    (hc : ∀ m : ℤ, E * C m = C m * E)
    (d : ℂ) (hd : d ≠ 0) (hdegree : number * E - E * number = d • E) : E = 0 := by
  have hz : d • E = 0 := by
    rw [← hdegree]
    exact number_commutes_of_signed_modes E 1 (by simp)
      (by simpa using hb) (by simpa using hc)
  exact (smul_eq_zero.mp hz).resolve_left hd

end D5.S3.Quantum.Fermionic.BcGhostChargeTensor
