/- GID: D5/S3/VertexAlgebra/Characters/OriginalOrbifoldVerlinde
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/OriginalOrbifoldVerlinde
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Leech sign-orbifold character matrices give the binary pair addition law. -/

import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldProjectedCharacters
import D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

/-! The numerical Verlinde formula for the four actual Leech sign-orbifold traces. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate

namespace D5.S3.VertexAlgebra.OriginalOrbifoldVerlinde

open LatticeDiscriminantTheta (QmodZ phase phase_mk)
open OriginalOrbifoldProjectedCharacters (projectedS projectedT)

/-- The additive group of sector labels. -/
abbrev Sector := ZMod 2 × ZMod 2

/-- Fixed lattice, anti-fixed lattice, integral twisted, and half-integral twisted
are labelled by `(0,0), (0,1), (1,0), (1,1)` in that order. -/
def sectorEquiv : Fin 4 ≃ Sector :=
  (finProdFinEquiv (m := 2) (n := 2)).symm

theorem sector_labels :
    sectorEquiv 0 = (0, 0) ∧ sectorEquiv 1 = (0, 1) ∧
    sectorEquiv 2 = (1, 0) ∧ sectorEquiv 3 = (1, 1) :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem bit_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have hlt := ZMod.val_lt x
  rcases show x.val = 0 ∨ x.val = 1 by omega with h | h
  · exact Or.inl ((ZMod.natCast_zmod_val x).symm.trans (by simp [h]))
  · exact Or.inr ((ZMod.natCast_zmod_val x).symm.trans (by simp [h]))

private theorem bit_one_val : (1 : ZMod 2).val = 1 :=
  ZMod.val_one'' (by decide)

private def half : QmodZ := ((1 / 2 : ℚ) : QmodZ)

private def halfFromInt : ℤ →+ QmodZ where
  toFun n := n • half
  map_zero' := zero_zsmul _
  map_add' _ _ := by simp only [add_zsmul]

/-- Embed a bit as its half-integer class in `ℚ/ℤ`. -/
private def halfClass : ZMod 2 →+ QmodZ :=
  ZMod.lift 2 ⟨halfFromInt, by
    change (2 : ℤ) • half = 0
    rw [show (2 : ℤ) = 1 + 1 by decide, add_zsmul, one_zsmul, half, ← AddCircle.coe_add,
      show (1 / 2 : ℚ) + 1 / 2 = 1 by norm_num, AddCircle.coe_period]⟩

private theorem halfClass_apply (x : ZMod 2) :
    halfClass x = (((x.val : ℚ) / 2 : ℚ) : QmodZ) := by
  rcases bit_cases x with rfl | rfl
  · rw [map_zero, ZMod.val_zero, Nat.cast_zero, zero_div, AddCircle.coe_zero]
  · have hone : halfClass (1 : ZMod 2) = halfFromInt (1 : ℤ) := ZMod.lift_coe 2 _ 1
    rw [hone, bit_one_val, Nat.cast_one]
    change (1 : ℤ) • half = ((1 / 2 : ℚ) : QmodZ)
    rw [one_zsmul, half]

/-- The quadratic class of a binary pair is the product of its bits divided by two. -/
def quadratic (a : Sector) : QmodZ := halfClass (a.1 * a.2)

theorem quadratic_eq (a : Sector) :
    quadratic a = (((a.1.val : ℚ) * (a.2.val : ℚ) / 2 : ℚ) : QmodZ) := by
  have hprod : a.1.val * a.2.val < 2 := by
    have h₁ := ZMod.val_lt a.1
    have h₂ := ZMod.val_lt a.2
    exact (Nat.mul_le_mul (show a.1.val ≤ 1 by omega)
      (show a.2.val ≤ 1 by omega)).trans_lt (by decide)
  rw [quadratic, halfClass_apply, ZMod.val_mul_of_lt hprod, Nat.cast_mul]

theorem quadratic_nsmul (n : ℕ) (a : Sector) :
    quadratic (n • a) = (n * n) • quadratic a := by
  change halfClass ((n • a.1) * (n • a.2)) = (n * n) • halfClass (a.1 * a.2)
  rw [← map_nsmul]
  simp only [nsmul_eq_mul, Nat.cast_mul]
  congr 1
  ring

/-- The cross-pairing on the sector group, with values in `ℚ/ℤ`. -/
def pairing (a b : Sector) : QmodZ := halfClass (a.1 * b.2 + a.2 * b.1)

theorem pairing_polarization (a b : Sector) :
    pairing a b = quadratic (a + b) - quadratic a - quadratic b := by
  simp only [pairing, quadratic, Prod.fst_add, Prod.snd_add, ← map_sub]
  congr 1
  ring

theorem pairing_symm (a b : Sector) : pairing a b = pairing b a := by
  unfold pairing
  congr 1
  ring

theorem pairing_add_right (a b c : Sector) :
    pairing a (b + c) = pairing a b + pairing a c := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, ← map_add]
  congr 1
  ring

private theorem pairing_neg (a b : Sector) : -pairing a b = pairing a b := by
  rw [pairing, ← map_neg, ZMod.neg_eq_self_mod_two]

/-- The complex bicharacter obtained by exponentiating the cross-pairing. -/
def pairingCharacter (a : Sector) : AddChar Sector ℂ where
  toFun b := phase (pairing a b)
  map_zero_eq_one' := by
    simp [pairing, phase.map_zero_eq_one]
  map_add_eq_mul' b c := by
    rw [pairing_add_right, phase.map_add_eq_mul]

private theorem phase_halfClass (x : ZMod 2) :
    phase (halfClass x) = if x = 0 then 1 else -1 := by
  rcases bit_cases x with rfl | rfl
  · rw [map_zero, phase.map_zero_eq_one, ite_eq_left rfl]
  · rw [ite_eq_right one_ne_zero, halfClass_apply, bit_one_val, Nat.cast_one]
    rw [phase_mk, show 2 * ↑Real.pi * Complex.I * ((1 / 2 : ℚ) : ℂ) =
      ↑Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]

/-- The (S) matrix uses the negative Fourier convention and normalization `1/2`.
All pairing classes have order dividing two. -/
theorem projectedS_eq (a b : Fin 4) :
    projectedS a b = (2 : ℂ)⁻¹ * phase (-pairing (sectorEquiv a) (sectorEquiv b)) := by
  rw [pairing_neg, pairing, phase_halfClass]
  fin_cases a <;> fin_cases b <;>
    simp (config := { decide := true }) [projectedS, Matrix.smul_apply,
      sector_labels.1, sector_labels.2.1, sector_labels.2.2.1, sector_labels.2.2.2]

/-- The (T) matrix uses the positive quadratic phase. The shift by `c/24 = 1`
in the graded traces contributes the unit phase. -/
theorem projectedT_eq (a b : Fin 4) :
    projectedT a b = if a = b then phase (quadratic (sectorEquiv a)) else 0 := by
  simp only [quadratic, phase_halfClass]
  fin_cases a <;> fin_cases b <;>
    simp (config := { decide := true }) [projectedT,
      sector_labels.1, sector_labels.2.1, sector_labels.2.2.1, sector_labels.2.2.2]

private theorem pairingCharacter_trivial_iff (a : Sector) :
    pairingCharacter a = 0 ↔ a = 0 := by
  have detect (x : ZMod 2) (h : phase (halfClass x) = 1) : x = 0 := by
    by_contra hn
    rw [phase_halfClass, ite_eq_right hn] at h
    norm_num at h
  constructor
  · intro h
    have eval (b : Sector) : phase (pairing a b) = 1 := by
      change pairingCharacter a b = 1
      rw [h, AddChar.zero_apply]
    exact Prod.ext
      (detect a.1 (by simpa [pairing] using eval (0, 1)))
      (detect a.2 (by simpa [pairing] using eval (1, 0)))
  · rintro rfl
    ext b
    simp [pairingCharacter, pairing, phase.map_zero_eq_one]

/-- The sum of a row character is four for the trivial label and zero otherwise. -/
theorem pairingCharacter_sum (a : Sector) :
    (∑ x : Sector, pairingCharacter a x) = if a = 0 then 4 else 0 := by
  classical
  rw [AddChar.sum_eq_ite]
  norm_num [pairingCharacter_trivial_iff, Fintype.card_prod, ZMod.card]

private theorem pairingCharacter_add_left (a b x : Sector) :
    pairingCharacter (a + b) x = pairingCharacter a x * pairingCharacter b x := by
  change phase (pairing (a + b) x) = phase (pairing a x) * phase (pairing b x)
  rw [pairing_symm (a + b) x, pairing_add_right, phase.map_add_eq_mul,
    pairing_symm x a, pairing_symm x b]

private theorem pairingCharacter_conj (a b : Sector) :
    conj (pairingCharacter a b) = pairingCharacter a b := by
  change conj (phase (pairing a b)) = phase (pairing a b)
  rw [pairing, phase_halfClass]
  split_ifs <;> simp

private theorem sector_neg (a : Sector) : -a = a :=
  Prod.ext (ZMod.neg_eq_self_mod_two a.1) (ZMod.neg_eq_self_mod_two a.2)

private theorem projectedS_vacuum (x : Fin 4) : projectedS 0 x = (2 : ℂ)⁻¹ := by
  rw [projectedS_eq, pairing_neg, sector_labels.1]
  simp [pairing, phase.map_zero_eq_one]

/-- The numerical Verlinde coefficient of the actual projected trace matrices.
The third entry is conjugated and the denominator is the vacuum row. -/
def verlindeCoefficient (a b c : Fin 4) : ℂ :=
  ∑ x : Fin 4, projectedS a x * projectedS b x * conj (projectedS c x) / projectedS 0 x

/-- The finite modular character data give exactly addition of the binary pairs. -/
theorem verlindeCoefficient_eq_indicator (a b c : Fin 4) :
    verlindeCoefficient a b c =
      if sectorEquiv a + sectorEquiv b = sectorEquiv c then 1 else 0 := by
  let d := sectorEquiv a + sectorEquiv b - sectorEquiv c
  have hs : ∀ i x : Fin 4,
      projectedS i x = (2 : ℂ)⁻¹ * pairingCharacter (sectorEquiv i) (sectorEquiv x) := by
    intro i x
    change projectedS i x = (2 : ℂ)⁻¹ * phase (pairing (sectorEquiv i) (sectorEquiv x))
    rw [projectedS_eq, pairing_neg]
  have hsum := Fintype.sum_equiv sectorEquiv
    (fun x => pairingCharacter d (sectorEquiv x)) (fun x => pairingCharacter d x) (fun _ => rfl)
  calc
    verlindeCoefficient a b c = ∑ x : Fin 4, (4 : ℂ)⁻¹ * pairingCharacter d (sectorEquiv x) := by
      unfold verlindeCoefficient
      apply Finset.sum_congr rfl
      intro x _
      rw [projectedS_vacuum, hs a, hs b, hs c, map_mul, map_inv₀,
        map_ofNat (conj : ℂ →+* ℂ) 2, pairingCharacter_conj]
      dsimp only [d]
      rw [sub_eq_add_neg, sector_neg, pairingCharacter_add_left, pairingCharacter_add_left]
      ring
    _ = (4 : ℂ)⁻¹ * (if d = 0 then 4 else 0) := by
      rw [← Finset.mul_sum, hsum, pairingCharacter_sum]
    _ = _ := by
      simp only [d, sub_eq_zero]
      split_ifs <;> norm_num

#print axioms sector_labels
#print axioms quadratic_eq
#print axioms quadratic_nsmul
#print axioms pairing_polarization
#print axioms pairing_symm
#print axioms pairing_add_right
#print axioms projectedS_eq
#print axioms projectedT_eq
#print axioms pairingCharacter_sum
#print axioms verlindeCoefficient_eq_indicator
#print axioms OriginalOrbifoldProjectedCharacters.projected_characters_covariant

end D5.S3.VertexAlgebra.OriginalOrbifoldVerlinde
