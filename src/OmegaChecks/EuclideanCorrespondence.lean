module

public import D5.S3.Arith.Euclidean.GCD
public import OmegaChecks.NatCorrespondence

/-! Interpretation of the natural Euclidean algorithm and its divisibility witnesses. -/

namespace OmegaChecks.NatCorrespondence

private theorem toStd_mul (a b : Omega.Nat) : toStd (a.mul b) = toStd a * toStd b := by
  induction b with
  | zero => exact (congrArg toStd (fromOmegaEq (Omega.Nat.mul_zero a))).trans (Nat.mul_zero _).symm
  | succ b ih =>
    exact (congrArg toStd (fromOmegaEq (Omega.Nat.mul_succ a b))).trans
      ((toStd_add _ _).trans ((congrArg (· + toStd a) ih).trans (Nat.mul_succ _ _).symm))

/-- Multiplication witnesses for the original relation correspond in both directions. -/
public theorem dvd_iff (a b : Omega.Nat) : Omega.Arithmetic.Dvd a b ↔ toStd a ∣ toStd b := by
  constructor
  · intro h
    exact Omega.Exists.elim h fun k hk => ⟨toStd k, (congrArg toStd (fromOmegaEq hk)).trans (toStd_mul a k)⟩
  · rintro ⟨k, hk⟩
    refine Omega.Exists.intro (fromStd k) ?_
    have eq : toStd b = toStd (a.mul (fromStd k)) := by rw [hk, toStd_mul, toStd_fromStd]
    have eq' := congrArg fromStd eq
    rw [fromStd_toStd, fromStd_toStd] at eq'
    exact eq' ▸ Omega.rfl

/-- The divisor returned with Bézout coefficients is the pinned natural-number gcd. -/
public theorem gcd_eq (a b : Omega.Nat) :
    toStd (Omega.Arithmetic.gcd a b) = Nat.gcd (toStd a) (toStd b) := by
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd ((dvd_iff ..).mp (Omega.Arithmetic.gcd_dvd_left a b))
      ((dvd_iff ..).mp (Omega.Arithmetic.gcd_dvd_right a b))
  · let d := Nat.gcd (toStd a) (toStd b)
    have ha : toStd (fromStd d) ∣ toStd a := (toStd_fromStd d).symm ▸ Nat.gcd_dvd_left _ _
    have hb : toStd (fromStd d) ∣ toStd b := (toStd_fromStd d).symm ▸ Nat.gcd_dvd_right _ _
    have h := Omega.Arithmetic.dvd_gcd ((dvd_iff ..).mpr ha) ((dvd_iff ..).mpr hb)
    have hg := (dvd_iff ..).mp h
    rw [toStd_fromStd] at hg
    exact hg

end OmegaChecks.NatCorrespondence
