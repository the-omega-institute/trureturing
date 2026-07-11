/- GID: D5/S0/Carrier/Conj
   generality: G
   mirror-B: D5/B/S0/Carrier/Conj
   mirror-E: none(waiver:pure-definition)
   anchors: [GICT-v3.6-I.1-theorem-1.3-i]
   digest: The golden Galois conjugation is an involutive ring automorphism. -/

import D5.S0.Carrier.Ring

namespace D5.S0.Carrier

/-- Galois conjugation, determined by `phi` mapping to `1 - phi`. -/
def conj (x : GoldenInt) : GoldenInt := ⟨x.a + x.b, -x.b⟩

@[simp] theorem conj_a (x : GoldenInt) : (conj x).a = x.a + x.b := rfl
@[simp] theorem conj_b (x : GoldenInt) : (conj x).b = -x.b := rfl
@[simp] theorem conj_zero : conj 0 = 0 := rfl
@[simp] theorem conj_one : conj 1 = 1 := rfl

@[simp] theorem conj_add (x y : GoldenInt) : conj (x + y) = conj x + conj y := by
  ext <;> simp [conj] <;> ring

@[simp] theorem conj_mul (x y : GoldenInt) : conj (x * y) = conj x * conj y := by
  ext <;> simp [conj] <;> ring

@[simp] theorem conj_involutive (x : GoldenInt) : conj (conj x) = x := by
  ext <;> simp [conj]

/-- Conjugation packaged as the ring automorphism from GICT Theorem 1.3(i). -/
def conjEquiv : GoldenInt ≃+* GoldenInt where
  toFun := conj
  invFun := conj
  map_mul' := conj_mul
  map_add' := conj_add
  left_inv := conj_involutive
  right_inv := conj_involutive

@[simp] theorem conj_phi : conj phi = 1 - phi := by
  ext <;> norm_num [conj, phi, sub_eq_add_neg]

/-- The algebraic trace in integral coordinates. -/
def trace (x : GoldenInt) : ℤ := 2 * x.a + x.b

theorem add_conj_eq_trace (x : GoldenInt) : x + conj x = (trace x : GoldenInt) := by
  apply GoldenInt.ext
  · change x.a + (x.a + x.b) = 2 * x.a + x.b
    ring
  · change x.b + -x.b = 0
    ring

/-- The doubled `Zsqrtd` coordinates intertwine both conjugations exactly. -/
theorem toZsqrtd_conj (x : GoldenInt) : toZsqrtd (conj x) = star (toZsqrtd x) := by
  apply Zsqrtd.ext
  · simp [toZsqrtd, conj]
    ring
  · simp [toZsqrtd, conj]

end D5.S0.Carrier
