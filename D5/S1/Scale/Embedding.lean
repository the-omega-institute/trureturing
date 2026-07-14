/- GID: D5/S1/Scale/Embedding
   generality: I
   mirror-B: D5/B/S1/Scale/Embedding
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The real embedding of golden integers is an injective ring homomorphism. -/

import D5.S0.Carrier.Norm
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Scale

open D5.S0.Carrier

/-- The distinguished real embedding `a + b*phi ↦ a + b*goldenRatio`. -/
noncomputable def embedding : GoldenInt →+* ℝ where
  toFun x := x.a + x.b * Real.goldenRatio
  map_one' := by simp
  map_mul' x y := by
    simp only [a_mul, b_mul]
    push_cast
    let g : ℝ := Real.goldenRatio
    change x.a * y.a + x.b * y.b +
        (x.a * y.b + x.b * y.a + x.b * y.b) * g =
      (x.a + x.b * g) * (y.a + y.b * g)
    have hg : g ^ 2 = g + 1 := Real.goldenRatio_sq
    calc
      _ = x.a * y.a + x.b * y.b * (g + 1) +
          (x.a * y.b + x.b * y.a) * g := by ring
      _ = (x.a + x.b * g) * (y.a + y.b * g) := by rw [← hg]; ring
  map_zero' := by simp
  map_add' x y := by simp; ring

@[simp] theorem embedding_apply (x : GoldenInt) :
    embedding x = x.a + x.b * Real.goldenRatio := rfl

@[simp] theorem embedding_phi : embedding phi = Real.goldenRatio := by simp [embedding, phi]

theorem embedding_injective : Function.Injective embedding := by
  intro x y hxy
  have h : embedding (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  by_cases hb : (x - y).b = 0
  · have ha : (x - y).a = 0 := by
      simpa [embedding, hb] using h
    exact sub_eq_zero.mp (GoldenInt.ext ha hb)
  · exfalso
    have hratio : Real.goldenRatio = (-(x - y).a : ℤ) / (x - y).b := by
      apply (eq_div_iff (Int.cast_ne_zero.mpr hb)).2
      rw [mul_comm, Int.cast_neg]
      change (x - y).a + (x - y).b * Real.goldenRatio = 0 at h
      linarith
    exact Real.goldenRatio_irrational.ne_rational (-(x - y).a) (x - y).b hratio

@[simp] theorem embedding_eq_zero_iff (x : GoldenInt) : embedding x = 0 ↔ x = 0 :=
  embedding_injective.eq_iff' (map_zero embedding)

/-- The real embedding times its conjugate is the integer norm. -/
theorem embedding_mul_conj (x : GoldenInt) :
    embedding x * embedding (D5.S0.Carrier.conj x) = (D5.S0.Carrier.norm x : ℝ) := by
  rw [← map_mul, ← D5.S0.Carrier.norm_eq_mul_conj]
  simp

theorem abs_embedding_mul_abs_conj (x : GoldenInt) :
    |embedding x| * |embedding (D5.S0.Carrier.conj x)| =
      |(D5.S0.Carrier.norm x : ℝ)| := by
  rw [← abs_mul, embedding_mul_conj]

end D5.S1.Scale
