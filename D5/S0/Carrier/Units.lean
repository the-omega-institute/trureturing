/- GID: D5/S0/Carrier/Units
   generality: I
   mirror-B: D5/B/S0/Carrier/Units
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Golden units have norm plus or minus one and signed powers of phi are units. -/

import D5.S0.Carrier.Norm

namespace D5.S0.Carrier

/-- An element is invertible exactly when its integer norm is invertible. -/
theorem isUnit_iff_norm_isUnit (x : GoldenInt) : IsUnit x ↔ IsUnit (norm x) := by
  constructor
  · intro hx
    exact hx.map normMonoidHom
  · intro hn
    rcases Int.isUnit_iff.mp hn with hnorm | hnorm
    · refine isUnit_iff_exists_inv.mpr ⟨conj x, ?_⟩
      rw [← norm_eq_mul_conj, hnorm]
      rfl
    · refine isUnit_iff_exists_inv.mpr ⟨-conj x, ?_⟩
      calc
        x * -conj x = -(x * conj x) := by rw [mul_neg]
        _ = -(norm x : GoldenInt) := by rw [← norm_eq_mul_conj]
        _ = 1 := by rw [hnorm]; norm_num

/-- Coordinate-level unit criterion for the golden integer ring. -/
theorem isUnit_iff_norm_eq_one_or_neg_one (x : GoldenInt) :
    IsUnit x ↔ norm x = 1 ∨ norm x = -1 :=
  (isUnit_iff_norm_isUnit x).trans Int.isUnit_iff

theorem isUnit_iff_norm_natAbs_eq_one (x : GoldenInt) :
    IsUnit x ↔ (norm x).natAbs = 1 :=
  (isUnit_iff_norm_isUnit x).trans Int.isUnit_iff_natAbs_eq

private theorem phi_mul_inv : phi * -conj phi = 1 := by
  calc
    phi * -conj phi = -(phi * conj phi) := by rw [mul_neg]
    _ = -(norm phi : GoldenInt) := by rw [← norm_eq_mul_conj]
    _ = 1 := by rw [norm_phi]; norm_num

/-- The distinguished fundamental unit, with inverse `phi - 1`. -/
def phiUnit : GoldenIntˣ where
  val := phi
  inv := -conj phi
  val_inv := phi_mul_inv
  inv_val := by simpa [mul_comm] using phi_mul_inv

@[simp] theorem coe_phiUnit : (phiUnit : GoldenInt) = phi := rfl
theorem phi_isUnit : IsUnit phi := phiUnit.isUnit

/-- Every natural power has the norm predicted by `N(phi) = -1`. -/
theorem norm_phi_pow (n : ℕ) : norm (phi ^ n) = (-1 : ℤ) ^ n := by
  exact normMonoidHom.map_pow phi n

/-- The explicit family `± phi^n`, for arbitrary integral exponents. -/
def signedPhiPower (negative : Bool) (n : ℤ) : GoldenInt :=
  if negative then -((phiUnit ^ n : GoldenIntˣ) : GoldenInt)
  else ((phiUnit ^ n : GoldenIntˣ) : GoldenInt)

theorem signedPhiPower_isUnit (negative : Bool) (n : ℤ) :
    IsUnit (signedPhiPower negative n) := by
  cases negative <;> simp [signedPhiPower]

end D5.S0.Carrier
