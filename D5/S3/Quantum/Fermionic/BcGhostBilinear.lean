/- GID: D5/S3/Quantum/Fermionic/BcGhostBilinear
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostBilinear
   mirror-E: none(waiver:algebraic-bc-bilinear)
   anchors: []
   utility: none
   digest: Bilinear occupation pairing, mode transposes and relative c₀ coefficients. -/

import D5.S3.Quantum.Fermionic.BcGhostHermitian
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-! The complex-bilinear ghost form in the original occupation basis. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Fermionic.BcGhostBilinear

open CountableOccupationFock (Fock ket create annihilate phase lowerCount)
open BcGhostFock (b c)
open BcGhostCharge (charge ghostNumber)
open BcGhostHermitian

/-- Coefficient conjugation in the original occupation basis. -/
def kappa (x : Fock) : Fock :=
  Finsupp.mapRange (star : ℂ → ℂ) (star_zero ℂ) x

@[simp] theorem kappa_apply (x : Fock) (S : Finset ℕ) : kappa x S = star (x S) :=
  Finsupp.mapRange_apply

private theorem kappa_add (x y : Fock) : kappa (x + y) = kappa x + kappa y := by
  ext S
  simp [star_add]

private theorem kappa_smul (a : ℂ) (x : Fock) :
    kappa (a • x) = star a • kappa x := by
  ext S
  simp [smul_eq_mul, star_mul, mul_comm]

@[simp] theorem kappa_ket (S : Finset ℕ) : kappa (ket S) = ket S := by
  ext T
  by_cases h : S = T <;> simp [ket, h]

private theorem kappa_support (x : Fock) : (kappa x).support = x.support :=
  Finsupp.support_mapRange_of_injective (star_zero ℂ) x star_injective

private theorem kappa_create (j : ℕ) (x : Fock) :
    kappa (create j x) = create j (kappa x) := by
  ext S
  by_cases h : j ∈ S <;> simp [create_coefficient, h, star_mul, phase_real, mul_comm]

private theorem kappa_annihilate (j : ℕ) (x : Fock) :
    kappa (annihilate j x) = annihilate j (kappa x) := by
  ext S
  by_cases h : j ∈ S <;> simp [annihilate_coefficient, h, star_mul, phase_real, mul_comm]

theorem kappa_b (n : ℤ) (x : Fock) : kappa (b n x) = b n (kappa x) := by
  by_cases h : n ≤ -2 <;> simp [b, h, kappa_create, kappa_annihilate]

theorem kappa_c (n : ℤ) (x : Fock) : kappa (c n x) = c n (kappa x) := by
  by_cases h : n ≤ 1 <;> simp [c, h, kappa_create, kappa_annihilate]

/-- The signed occupation form with two complex-linear slots. -/
def Bg : LinearMap.BilinForm ℂ Fock where
  toFun x :=
    { toFun := Hg (kappa x)
      map_add' := Hg_add_right (kappa x)
      map_smul' := fun a y => by
        simpa only [RingHom.id_apply, smul_eq_mul] using Hg_smul_right a (kappa x) y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change Hg (kappa (x + y)) z = Hg (kappa x) z + Hg (kappa y) z
    rw [kappa_add, Hg_add_left]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change Hg (kappa (a • x)) y = a * Hg (kappa x) y
    rw [kappa_smul, Hg_smul_left, star_star]

theorem Bg_signed_coefficient (x y : Fock) :
    Bg x y = ∑ S ∈ x.support, x S * eps S * y (partner S) := by
  change Hg (kappa x) y = _
  rw [Hg_signed_coefficient, kappa_support]
  simp only [kappa_apply, star_star]

theorem Bg_ket_coefficient (S : Finset ℕ) (y : Fock) :
    Bg (ket S) y = eps S * y (partner S) := by
  change Hg (kappa (ket S)) y = _
  rw [kappa_ket, Hg_ket_coefficient]

theorem Bg_right_ket (x : Fock) (S : Finset ℕ) :
    Bg x (ket S) = x (partner S) * eps (partner S) := by
  change Hg (kappa x) (ket S) = _
  rw [Hg_right_ket, kappa_apply, star_star]

theorem Bg_symmetric (x y : Fock) : Bg x y = Bg y x := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  | single S a =>
    have h : Finsupp.single S a = a • ket S := by simp [ket]
    simp only [h, map_smul, LinearMap.smul_apply, Bg_ket_coefficient, Bg_right_ket,
      eps_partner, mul_comm (eps S) (y (partner S))]

theorem Bg_b (n : ℤ) (x y : Fock) : Bg (b n x) y = Bg x (b (-n) y) := by
  change Hg (kappa (b n x)) y = Hg (kappa x) (b (-n) y)
  rw [kappa_b, Hg_b]

theorem Bg_c (n : ℤ) (x y : Fock) : Bg (c n x) y = Bg x (c (-n) y) := by
  change Hg (kappa (c n x)) y = Hg (kappa x) (c (-n) y)
  rw [kappa_c, Hg_c]

/-- The coefficient of the zero-mode insertion against one relative ket. -/
theorem Bg_c0_ket_coefficient (S : Finset ℕ) (hS : 3 ∉ S) (y : Fock) :
    Bg (ket S) (c 0 y) = relativeEps S * y (relativePartner S) := by
  rw [Bg_ket_coefficient, c_zero, create_coefficient, ite_eq_left (three_mem_partner S hS)]
  simp only [relativeEps, relativePartner, mul_assoc]

/-- The full relative sum on the original b₀ kernel, with literal CAR signs. -/
theorem Bg_c0_signed_coefficient (x y : Fock) (hx : b 0 x = 0) :
    Bg x (c 0 y) = ∑ S ∈ x.support, x S * relativeEps S * y (relativePartner S) := by
  classical
  rw [Bg_signed_coefficient]
  apply Finset.sum_congr rfl
  intro S hS
  have hthree : 3 ∉ S := by
    intro h
    exact (Finsupp.mem_support_iff.mp hS) ((mem_relative_iff x).mp hx S h)
  rw [c_zero, create_coefficient, ite_eq_left (three_mem_partner S hthree)]
  simp only [relativeEps, relativePartner, mul_assoc]

theorem Bg_c0_charge_selection (g h : ℤ) (x y : Fock) (hb : b 0 x = 0)
    (hx : Homogeneous g x) (hy : Homogeneous h y) (hgh : g + h ≠ 2) :
    Bg x (c 0 y) = 0 := by
  classical
  rw [Bg_c0_signed_coefficient x y hb]
  apply Finset.sum_eq_zero
  intro S hS
  have hs : x S ≠ 0 := Finsupp.mem_support_iff.mp hS
  have hthree : 3 ∉ S := fun h => hs ((mem_relative_iff x).mp hb S h)
  have hz : y (relativePartner S) = 0 := by
    by_contra hyS
    have hc := charge_relativePartner S hthree
    rw [hx S hs, hy _ hyS] at hc
    exact hgh hc
  simp [hz]

/-- The two occupation signs are both negative at the ghost-one root ket. -/
theorem Bg_c0_ket_one : Bg (ket {1}) (c 0 (ket {1})) = 1 := by
  have hp : partner ({1} : Finset ℕ) = {1, 3} := by decide
  have hr : relativePartner ({1} : Finset ℕ) = {1} := by decide
  have hs : ({1} : Finset ℕ).sort (· ≤ ·) = [1] := Finset.sort_singleton _ _
  have h5 : lowerCount 5 E = 2 := by decide
  have h3 : lowerCount 3 ({1, 3} : Finset ℕ) = 1 := by decide
  have he : eps ({1} : Finset ℕ) = -1 := by
    simp only [eps, hs, epsList, List.toFinset_nil, partner_empty]
    have ht : tau 1 = 5 := by decide
    norm_num [ht, phase, h5]
  rw [Bg_c0_ket_coefficient ({1} : Finset ℕ) (by decide), relativeEps, hr, he, hp]
  norm_num [phase, h3, ket]

end D5.S3.Quantum.Fermionic.BcGhostBilinear
