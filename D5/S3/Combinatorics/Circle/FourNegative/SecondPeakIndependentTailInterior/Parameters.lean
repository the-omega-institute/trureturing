/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakIndependentTailInterior/Parameters
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Independent dyadic coordinates for the low-bit UXWV construction. -/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
private structure Parameters where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  hc : 2 ≤ c
  hd : c + 2 ≤ d
  ha : c + d ≤ a
  hb : a + 1 ≤ b
private def r (p : Parameters) : ℕ := p.a - p.c - p.d
private def s (p : Parameters) : ℕ := p.b - p.a - 1
private def v (p : Parameters) : ℕ := p.d - p.c - 2
private theorem parameter_eqs (p : Parameters) :
    p.a = p.c + p.d + r p ∧ p.b = p.a + 1 + s p ∧
    p.d = p.c + 2 + v p := by
  have := p.ha; have := p.hb; have := p.hd
  dsimp [r, s, v]; omega
private theorem dyadic_eqs (p : Parameters) :
    (2 : ℚ)^p.d = 4 * 2^p.c * 2^(v p) ∧
    (2 : ℚ)^p.a = 2^(r p) * 2^p.c * 2^p.d ∧
    (2 : ℚ)^p.b = 2 * 2^(r p) * 2^p.c * 2^p.d * 2^(s p) ∧
    (2 : ℚ)^(p.d-p.c-1) = 2 * 2^(v p) := by
  obtain ⟨ha,hb,hd⟩ := parameter_eqs p
  have he : p.d-p.c-1 = v p + 1 := by have := p.hd; dsimp [v]; omega
  constructor
  · rw [hd]; simp only [pow_add]; norm_num; ring
  constructor
  · rw [ha]; simp only [pow_add]; norm_num; ring
  constructor
  · calc
      (2 : ℚ)^p.b = 2 * 2^p.a * 2^(s p) := by
        rw [hb]; simp only [pow_add]; norm_num; ring
      _ = _ := by rw [ha]; simp only [pow_add]; norm_num; ring
  · rw [he]; simp only [pow_add]; norm_num; ring
end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakIndependentTailInterior
