/- GID: D5/S0/Carrier/Norm
   generality: G
   mirror-B: D5/B/S0/Carrier/Norm
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The explicit golden norm is conjugate multiplication and is multiplicative. -/

import D5.S0.Carrier.Conj

namespace D5.S0.Carrier

/-- The field norm of `a + b*phi`. -/
def norm (x : GoldenInt) : ℤ := x.a * x.a + x.a * x.b - x.b * x.b

theorem norm_def (x : GoldenInt) : norm x = x.a * x.a + x.a * x.b - x.b * x.b := rfl

@[simp] theorem norm_zero : norm 0 = 0 := rfl
@[simp] theorem norm_one : norm 1 = 1 := rfl
@[simp] theorem norm_phi : norm phi = -1 := rfl

/-- Conjugate multiplication has no `phi` coordinate and equals the integer norm. -/
theorem norm_eq_mul_conj (x : GoldenInt) : (norm x : GoldenInt) = x * conj x := by
  apply GoldenInt.ext
  · change norm x = x.a * (x.a + x.b) + x.b * -x.b
    simp [norm]
    ring
  · change 0 = x.a * -x.b + x.b * (x.a + x.b) + x.b * -x.b
    ring

@[simp] theorem norm_conj (x : GoldenInt) : norm (conj x) = norm x := by
  simp [norm, conj]
  ring

/-- The coordinate formula for the golden integer norm. -/
@[simp] theorem norm_mul (x y : GoldenInt) : norm (x * y) = norm x * norm y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp [norm]
  ring

/-- The norm as a monoid homomorphism. -/
def normMonoidHom : GoldenInt →* ℤ where
  toFun := norm
  map_one' := norm_one
  map_mul' := norm_mul

/-- The doubled `Zsqrtd` embedding scales the quadratic norm by four. -/
theorem zsqrtd_norm_toZsqrtd (x : GoldenInt) :
    Zsqrtd.norm (toZsqrtd x) = 4 * norm x := by
  simp [Zsqrtd.norm, toZsqrtd, norm]
  ring

end D5.S0.Carrier
