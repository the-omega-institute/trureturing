/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTGhostBilinear
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTGhostBilinear
   mirror-E: none(waiver:algebraic-original-orbifold-brst-ghost-bilinear)
   anchors: []
   utility: none
   digest: Absolute and relative bilinear forms and the zero-mode Ward identity for bc ghosts. -/

import D5.S3.Quantum.Fermionic.BcGhostBRST
import D5.S3.Quantum.Fermionic.BcGhostBRSTHermitian

/-! Coefficient conjugation transports the signed Hermitian pairing to a complex
bilinear pairing with its original vacuum normalization. The relative pairing
inserts the actual c zero mode on the kernel of the actual b zero mode. -/

set_option autoImplicit false

open scoped BigOperators

noncomputable section
namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTGhostBilinear

open D5.S3.Quantum.Fermionic
open CountableOccupationFock BcGhostFock BcGhostHermitian
open BcGhostBRST (cubic cubicTerm cubicTerm_finite Qg Hg_Qg R)

/-- Pointwise complex conjugation of the finite occupation coefficients. -/
def kappa : Fock →+ Fock :=
  Finsupp.mapRange.addMonoidHom (starRingEnd ℂ).toAddMonoidHom

@[simp] theorem kappa_apply (x : Fock) (S : Finset ℕ) :
    kappa x S = star (x S) := rfl

@[simp] theorem kappa_kappa (x : Fock) : kappa (kappa x) = x := by
  exact Finsupp.ext fun S => by simp

theorem kappa_smul (a : ℂ) (x : Fock) : kappa (a • x) = star a • kappa x := by
  apply Finsupp.ext
  intro S
  simp only [kappa_apply, Finsupp.smul_apply, smul_eq_mul, star_mul, mul_comm]

@[simp] theorem kappa_ket (S : Finset ℕ) : kappa (ket S) = ket S := by
  apply Finsupp.ext
  intro T
  by_cases h : S = T <;> simp [ket, h]

private theorem kappa_support (x : Fock) : (kappa x).support = x.support :=
  Finsupp.support_mapRange_of_injective (star_zero ℂ) x star_injective

private theorem kappa_create (j : ℕ) (x : Fock) :
    kappa (create j x) = create j (kappa x) := by
  apply Finsupp.ext
  intro S
  simp only [kappa_apply, create_coefficient]
  split_ifs <;> simp only [star_mul, phase_real, star_zero, mul_comm]

private theorem kappa_annihilate (j : ℕ) (x : Fock) :
    kappa (annihilate j x) = annihilate j (kappa x) := by
  apply Finsupp.ext
  intro S
  simp only [kappa_apply, annihilate_coefficient]
  split_ifs <;> simp only [star_mul, phase_real, star_zero, mul_comm]

theorem kappa_b (m : ℤ) (x : Fock) : kappa (b m x) = b m (kappa x) := by
  unfold b
  split_ifs <;> simp only [kappa_create, kappa_annihilate]

theorem kappa_c (m : ℤ) (x : Fock) : kappa (c m x) = c m (kappa x) := by
  unfold c
  split_ifs <;> simp only [kappa_create, kappa_annihilate]

private theorem kappa_cubic (p q : ℤ) (x : Fock) :
    kappa (cubic p q x) = cubic p q (kappa x) := by
  unfold cubic
  split_ifs <;> simp only [Module.End.mul_apply, LinearMap.neg_apply,
    map_neg, kappa_b, kappa_c]

private theorem kappa_cubicTerm (pq : ℤ × ℤ) (x : Fock) :
    kappa (cubicTerm pq x) = cubicTerm pq (kappa x) := by
  simp only [cubicTerm, LinearMap.smul_apply, kappa_smul, kappa_cubic,
    star_mul, star_div₀, star_one, star_ofNat, star_intCast, mul_comm]

theorem kappa_Qg (x : Fock) : kappa (Qg x) = Qg (kappa x) := by
  change kappa (∑ᶠ pq : ℤ × ℤ, cubicTerm pq x) =
    ∑ᶠ pq : ℤ × ℤ, cubicTerm pq (kappa x)
  rw [map_finsum kappa (cubicTerm_finite x)]
  exact finsum_congr fun pq => kappa_cubicTerm pq x

/-- The absolute bilinear pairing obtained from the native signed rows. -/
def Bg : Fock →ₗ[ℂ] Fock →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := Hg (kappa x)
      map_add' := Hg_add_right (kappa x)
      map_smul' := fun a y => Hg_smul_right a (kappa x) y }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change Hg (kappa (x + z)) y = Hg (kappa x) y + Hg (kappa z) y
    rw [map_add, Hg_add_left]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change Hg (kappa (a • x)) y = a * Hg (kappa x) y
    rw [kappa_smul, Hg_smul_left, star_star]

theorem Bg_apply (x y : Fock) : Bg x y = Hg (kappa x) y := rfl

theorem Bg_vacuum_left (y : Fock) : Bg vacuum y = -y E := by
  rw [Bg_apply, show kappa vacuum = vacuum from kappa_ket ∅, Hg_vacuum_left]

private theorem Hg_kappa_right (x y : Fock) :
    Hg x (kappa y) = star (Hg (kappa x) y) := by
  simp only [Hg_signed_coefficient, kappa_support, kappa_apply, star_star,
    star_sum, star_mul, eps_real]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem Bg_symm (x y : Fock) : Bg x y = Bg y x := by
  rw [Bg_apply, Bg_apply, Hg_hermitian (kappa x) y, Hg_kappa_right, star_star]

theorem Bg_b (m : ℤ) (x y : Fock) : Bg (b m x) y = Bg x (b (-m) y) := by
  rw [Bg_apply, Bg_apply, kappa_b, Hg_b]

theorem Bg_c (m : ℤ) (x y : Fock) : Bg (c m x) y = Bg x (c (-m) y) := by
  rw [Bg_apply, Bg_apply, kappa_c, Hg_c]

theorem Bg_Qg (x y : Fock) : Bg (Qg x) y = Bg x (Qg y) := by
  rw [Bg_apply, Bg_apply, kappa_Qg, Hg_Qg]

theorem Bg_right_radical (y : Fock) (hy : ∀ x, Bg x y = 0) : y = 0 := by
  apply Hg_right_radical y
  intro x
  simpa only [Bg_apply, kappa_kappa] using hy (kappa x)

theorem Bg_left_radical (x : Fock) (hx : ∀ y, Bg x y = 0) : x = 0 := by
  exact Bg_right_radical x (fun y => (Bg_symm y x).trans (hx y))

private theorem zero_mixed_car :
    b 0 * c 0 + c 0 * b 0 = (1 : Module.End ℂ Fock) := by
  simpa using ghost_mixed_car 0 0

/-- The absolute pairing vanishes on two states in the kernel of b₀. -/
theorem Bg_isotropic {x y : Fock} (hx : b 0 x = 0) (hy : b 0 y = 0) :
    Bg x y = 0 := by
  have hsplit : b 0 (c 0 y) = y := by
    have h := LinearMap.congr_fun zero_mixed_car y
    simpa only [LinearMap.add_apply, Module.End.mul_apply, hy, map_zero,
      add_zero, Module.End.one_apply] using h
  calc
    Bg x y = Bg x (b 0 (c 0 y)) := by rw [hsplit]
    _ = Bg (b 0 x) (c 0 y) := by simpa only [neg_zero] using (Bg_b 0 x (c 0 y)).symm
    _ = 0 := by rw [hx, map_zero, LinearMap.zero_apply]

/-- Conjugation restricts to the original relative ghost space. -/
def kappaRel (x : Relative) : Relative :=
  ⟨kappa (x : Fock), by
    change b 0 (kappa (x : Fock)) = 0
    rw [← kappa_b, show b 0 (x : Fock) = 0 from x.property, map_zero]⟩

@[simp] theorem coe_kappaRel (x : Relative) :
    (kappaRel x : Fock) = kappa (x : Fock) := rfl

@[simp] theorem kappaRel_kappaRel (x : Relative) : kappaRel (kappaRel x) = x := by
  apply Subtype.ext
  simp

/-- The relative bilinear pairing on the native kernel, with c₀ inserted on the right. -/
def Brel : Relative →ₗ[ℂ] Relative →ₗ[ℂ] ℂ where
  toFun x := ((Bg (x : Fock)).comp (c 0)).comp relativeSpace.subtype
  map_add' x z := by
    apply LinearMap.ext
    intro y
    change Bg ((x : Fock) + (z : Fock)) (c 0 (y : Fock)) =
      Bg (x : Fock) (c 0 (y : Fock)) + Bg (z : Fock) (c 0 (y : Fock))
    rw [map_add, LinearMap.add_apply]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change Bg (a • (x : Fock)) (c 0 (y : Fock)) = a • Bg (x : Fock) (c 0 (y : Fock))
    rw [map_smul, LinearMap.smul_apply]

theorem Brel_apply (x y : Relative) : Brel x y = Bg (x : Fock) (c 0 (y : Fock)) := rfl

theorem Brel_eq_Hrel (x y : Relative) : Brel x y = Hrel (kappaRel x) y := rfl

theorem Brel_ket_coefficient (S : Finset ℕ) (hS : 3 ∉ S) (y : Relative) :
    Brel (relativeKet S hS) y = relativeEps S * (y : Fock) (relativePartner S) := by
  have hk : kappaRel (relativeKet S hS) = relativeKet S hS :=
    Subtype.ext (kappa_ket S)
  rw [Brel_eq_Hrel, hk, Hrel_ket_coefficient]

theorem Brel_symm (x y : Relative) : Brel x y = Brel y x := by
  calc
    Brel x y = Bg (c 0 (y : Fock)) (x : Fock) := Bg_symm _ _
    _ = Brel y x := by simpa only [neg_zero, Brel_apply] using Bg_c 0 (y : Fock) (x : Fock)

theorem Brel_right_radical (y : Relative) (hy : ∀ x, Brel x y = 0) : y = 0 := by
  apply Hrel_right_radical y
  intro x
  simpa only [Brel_eq_Hrel, kappaRel_kappaRel] using hy (kappaRel x)

theorem Brel_left_radical (x : Relative) (hx : ∀ y, Brel x y = 0) : x = 0 := by
  exact Brel_right_radical x (fun y => (Brel_symm y x).trans (hx y))

theorem Brel_charge_selection (g h : ℤ) (x y : Relative)
    (hx : Homogeneous g (x : Fock)) (hy : Homogeneous h (y : Fock))
    (hgh : g + h ≠ 2) : Brel x y = 0 := by
  rw [Brel_eq_Hrel]
  apply Hrel_charge_selection g h _ _ ?_ hy hgh
  intro S hS
  exact hx S (by simpa only [coe_kappaRel, kappa_apply, ne_eq, star_eq_zero] using hS)

/-- The pure-c zero-mode obstruction commutes with b₀ by the two Ward identities and CAR. -/
theorem b_zero_commutes_R_zero : b 0 * R 0 = R 0 * b 0 := by
  apply sub_eq_zero.mp
  rw [← BcGhostBRST.ward_c]
  calc
    _ = (Qg * b 0 + b 0 * Qg) * c 0 - c 0 * (Qg * b 0 + b 0 * Qg) +
        (b 0 * c 0 + c 0 * b 0) * Qg - Qg * (b 0 * c 0 + c 0 * b 0) := by
      noncomm_ring
    _ = 0 := by
      rw [BcGhostBRST.ward_b, zero_mixed_car, one_mul, mul_one, add_sub_assoc,
        sub_self, add_zero, BcGhostVirasoro.ward_c]
      simp

theorem R_zero_mem_relative {y : Fock} (hy : b 0 y = 0) : b 0 (R 0 y) = 0 := by
  have h := LinearMap.congr_fun b_zero_commutes_R_zero y
  simpa only [Module.End.mul_apply, hy, map_zero] using h

theorem Bg_R_zero_vanishes {x y : Fock} (hx : b 0 x = 0) (hy : b 0 y = 0) :
    Bg x (R 0 y) = 0 :=
  Bg_isotropic hx (R_zero_mem_relative hy)

/-- The zero-mode insertion gives skew transposition of the ghost charge between relative
inputs, with the two expressions evaluated on the ambient Fock space. -/
theorem Bg_Qg_relative_ward {x y : Fock} (hx : b 0 x = 0) (hy : b 0 y = 0) :
    Bg (Qg x) (c 0 y) + Bg x (c 0 (Qg y)) = 0 := by
  have h := LinearMap.congr_fun (BcGhostBRST.ward_c 0) y
  rw [Bg_Qg, ← map_add, show Qg (c 0 y) + c 0 (Qg y) = R 0 y from h]
  exact Bg_R_zero_vanishes hx hy

#print axioms kappa
#print axioms kappa_apply
#print axioms kappa_kappa
#print axioms kappa_smul
#print axioms kappa_ket
#print axioms kappa_b
#print axioms kappa_c
#print axioms kappa_Qg
#print axioms Bg
#print axioms Bg_apply
#print axioms Bg_vacuum_left
#print axioms Bg_symm
#print axioms Bg_b
#print axioms Bg_c
#print axioms Bg_Qg
#print axioms Bg_left_radical
#print axioms Bg_right_radical
#print axioms Bg_isotropic
#print axioms kappaRel
#print axioms coe_kappaRel
#print axioms kappaRel_kappaRel
#print axioms Brel
#print axioms Brel_apply
#print axioms Brel_eq_Hrel
#print axioms Brel_ket_coefficient
#print axioms Brel_symm
#print axioms Brel_left_radical
#print axioms Brel_right_radical
#print axioms Brel_charge_selection
#print axioms b_zero_commutes_R_zero
#print axioms R_zero_mem_relative
#print axioms Bg_R_zero_vanishes
#print axioms Bg_Qg_relative_ward

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTGhostBilinear
