/- GID: D5/S3/Factorization/Mordell/UnramifiedQuadraticNorm
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/UnramifiedQuadraticNorm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The p-adic size of an unramified quadratic norm and its tangent consumer. -/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Norms of quadratic extensions with nonsquare residue coefficient. -/

set_option autoImplicit false
namespace D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm
variable {p : ℕ} [Fact p.Prime]
local notation "red" => (PadicInt.toZMod : ℤ_[p] →+* ZMod p)

private theorem integral_norm_one (q x y : ℤ_[p])
    (hq : ¬ IsSquare (red q)) (hxy : ‖x‖ = 1 ∨ ‖y‖ = 1) :
    ‖x ^ 2 - q * y ^ 2‖ = 1 := by
  letI : Fact (¬ IsSquare (red q)) := ⟨hq⟩
  have unit_iff (v : ℤ_[p]) : IsUnit v ↔ red v ≠ 0 := by
    rw [← not_iff_not]
    simp only [not_not]
    change (v ∈ nonunits ℤ_[p]) ↔ red v = 0
    rw [← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker]
  have hn : red (x ^ 2 - q * y ^ 2) ≠ 0 := by
    intro hz
    let z : QuadraticAlgebra (ZMod p) (red q) 0 := ⟨red x, red y⟩
    have hz' : z.norm = 0 := by
      simpa [z, QuadraticAlgebra.norm_def, pow_two, mul_assoc] using hz
    have hzero := QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp hz'
    have hx : red x = 0 := congrArg QuadraticAlgebra.re hzero
    have hy : red y = 0 := congrArg QuadraticAlgebra.im hzero
    rcases hxy with hx1 | hy1
    · exact (unit_iff x).mp (PadicInt.isUnit_iff.mpr hx1) hx
    · exact (unit_iff y).mp (PadicInt.isUnit_iff.mpr hy1) hy
  exact PadicInt.isUnit_iff.mp ((unit_iff _).mpr hn)

/-- Nonsquare reduction prevents cancellation even for arbitrary denominators. -/
theorem norm_size (q : ℤ_[p]) (hq : ¬ IsSquare (red q)) (x y : ℚ_[p]) :
    ‖x ^ 2 - (q : ℚ_[p]) * y ^ 2‖ = (max ‖x‖ ‖y‖) ^ 2 := by
  by_cases hz : x = 0 ∧ y = 0
  · simp [hz.1, hz.2]
  let s := if ‖x‖ ≤ ‖y‖ then y else x
  have hs : s ≠ 0 := by
    dsimp [s]
    split_ifs with h
    · intro hy; apply hz; exact ⟨norm_eq_zero.mp (le_antisymm (by simpa [hy] using h) (norm_nonneg _)), hy⟩
    · intro hx; apply h; simp [hx]
  have hsm : ‖s‖ = max ‖x‖ ‖y‖ := by
    dsimp [s]; split_ifs with h
    · exact (max_eq_right h).symm
    · exact (max_eq_left (le_of_not_ge h)).symm
  have hx : ‖x / s‖ ≤ 1 := by
    rw [norm_div]; exact (div_le_one (norm_pos_iff.mpr hs)).mpr (hsm.symm ▸ le_max_left _ _)
  have hy : ‖y / s‖ ≤ 1 := by
    rw [norm_div]; exact (div_le_one (norm_pos_iff.mpr hs)).mpr (hsm.symm ▸ le_max_right _ _)
  let X : ℤ_[p] := ⟨x / s, hx⟩
  let Y : ℤ_[p] := ⟨y / s, hy⟩
  have hunit : ‖X‖ = 1 ∨ ‖Y‖ = 1 := by
    change ‖x / s‖ = 1 ∨ ‖y / s‖ = 1
    by_cases h : ‖x‖ ≤ ‖y‖
    · right
      have hy0 : y ≠ 0 := by simpa [s, h] using hs
      simp [s, h, hy0]
    · left
      have hx0 : x ≠ 0 := by simpa [s, h] using hs
      simp [s, h, hx0]
  have hu := integral_norm_one q X Y hq hunit
  have he : (x ^ 2 - (q : ℚ_[p]) * y ^ 2) =
      ((X ^ 2 - q * Y ^ 2 : ℤ_[p]) : ℚ_[p]) * s ^ 2 := by
    simp only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow]
    dsimp [X, Y]; field_simp [hs]
  rw [he, norm_mul, norm_pow, PadicInt.norm_coe, hu, one_mul, hsm]

/-- The quadratic norm identity controls a conic tangent on the same pair of points. -/
theorem tangent_norm_size (q : ℤ_[p]) (hq : ¬ IsSquare (red q))
    (a b x y c : ℚ_[p]) (hab : a ^ 2 - (q : ℚ_[p]) * b ^ 2 = c)
    (hxy : x ^ 2 - (q : ℚ_[p]) * y ^ 2 = c) (hc : ‖(2 : ℚ_[p]) * c‖ = 1) :
    let ell := a * x - (q : ℚ_[p]) * b * y - c
    ‖ell‖ = (max ‖ell‖ ‖a * y - b * x‖) ^ 2 := by
  dsimp
  have he : (a*x-(q:ℚ_[p])*b*y-c)^2 - (q:ℚ_[p])*(a*y-b*x)^2 =
      -(2*c)*(a*x-(q:ℚ_[p])*b*y-c) := by
    linear_combination (x^2-(q:ℚ_[p])*y^2)*hab + c*hxy
  have H := norm_size q hq (a*x-(q:ℚ_[p])*b*y-c) (a*y-b*x)
  rw [he, norm_mul, norm_neg, hc, one_mul] at H
  exact H

private theorem valuation_eq_of_norm (x y : ℚ_[p]) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ‖x‖ = ‖y‖) : x.valuation = y.valuation := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℝ) ≠ 1 := by exact_mod_cast (Fact.out : p.Prime).ne_one
  rw [Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy,
    zpow_right_inj₀ hp0 hp1, neg_inj] at h
  exact h

private theorem even_of_norm_square (x y : ℚ_[p]) (hx : x ≠ 0)
    (h : ‖x‖ = ‖y‖ ^ 2) : Even x.valuation := by
  have hy : y ≠ 0 := by intro hy; simp [hy] at h; exact hx h
  have hv := valuation_eq_of_norm x (y^2) hx (pow_ne_zero _ hy) (by simpa using h)
  rw [Padic.valuation_pow] at hv
  exact ⟨y.valuation, by omega⟩

private theorem norm_unit_valuation (x : ℚ_[p]) (h : ‖x‖ = 1) : x.valuation = 0 := by
  have hx : x ≠ 0 := by intro hx; simp [hx] at h
  simpa using valuation_eq_of_norm x 1 hx one_ne_zero (by simpa using h)

private theorem norm_coordinates (q : ℤ_[p]) (hq : ¬ IsSquare (red q))
    (x y d : ℚ_[p]) (h : x^2-(q:ℚ_[p])*y^2=d) (hd : ‖d‖ = 1) :
    ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 := by
  have hh := norm_size q hq x y
  rw [h, hd] at hh
  have hm : max ‖x‖ ‖y‖ ≤ 1 := by nlinarith [le_max_left ‖x‖ ‖y‖, norm_nonneg x]
  exact ⟨(le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩

private theorem sub_integral (x y : ℚ_[p]) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x-y‖ ≤ 1 := by
  have h := Padic.nonarchimedean x (-y)
  simpa only [sub_eq_add_neg, norm_neg] using h.trans (max_le hx (by simpa using hy))

private theorem add_integral (x y : ℚ_[p]) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x+y‖ ≤ 1 := (Padic.nonarchimedean x y).trans (max_le hx hy)

/-- A nonzero quadratic tangent has even finite valuation, without integral-input assumptions. -/
private theorem tangent_even (q : ℤ_[p]) (hq : ¬ IsSquare (red q))
    (a b x y c : ℚ_[p]) (hab : a^2-(q:ℚ_[p])*b^2=c)
    (hxy : x^2-(q:ℚ_[p])*y^2=c) (hc : ‖2*c‖ = 1)
    (he : a*x-(q:ℚ_[p])*b*y-c ≠ 0) :
    Even (a*x-(q:ℚ_[p])*b*y-c).valuation := by
  have h := tangent_norm_size q hq a b x y c hab hxy hc
  dsimp at h
  rcases le_total ‖a*x-(q:ℚ_[p])*b*y-c‖ ‖a*y-b*x‖ with hle | hle
  · rw [max_eq_right hle] at h
    exact even_of_norm_square _ _ he h
  · rw [max_eq_left hle] at h
    exact even_of_norm_square _ _ he h

/-- Normalize one homogeneous common covering; the same scale controls every coordinate. -/
private theorem common_normalization (q : ℤ_[p]) (hq : ¬ IsSquare (red q))
    (c d t x y z : ℚ_[p]) (hc : ‖c‖ ≤ 1) (hd : ‖d‖ = 1)
    (hn : t ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (h₃ : x^2-(q:ℚ_[p])*y^2=d*t^2) (h₂ : y^2-z^2=c*t^2) :
    t ≠ 0 ∧ ‖x/t‖ ≤ 1 ∧ ‖y/t‖ ≤ 1 ∧ ‖z/t‖ ≤ 1 := by
  have ht : t ≠ 0 := by
    intro ht
    have hh := norm_size q hq x y
    rw [h₃, ht] at hh
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, norm_zero] at hh
    have hx : x = 0 := norm_eq_zero.mp (by nlinarith [le_max_left ‖x‖ ‖y‖, norm_nonneg x, norm_nonneg y])
    have hy : y = 0 := norm_eq_zero.mp (by nlinarith [le_max_right ‖x‖ ‖y‖, norm_nonneg x, norm_nonneg y])
    have hz : z = 0 := by simpa [ht, hy, sq_eq_zero_iff] using h₂
    rcases hn with hn | hn | hn | hn <;> contradiction
  have h₃' : (x/t)^2-(q:ℚ_[p])*(y/t)^2=d := by field_simp; simpa [mul_comm] using h₃
  have h₂' : (y/t)^2-(z/t)^2=c := by field_simp; simpa [mul_comm] using h₂
  obtain ⟨hx,hy⟩ := norm_coordinates q hq (x/t) (y/t) d h₃' hd
  have hz : ‖z/t‖ ≤ 1 := by
    have he : (z/t)^2=(y/t)^2-c := by linear_combination -h₂'
    have hh := sub_integral ((y/t)^2) c (by rw [norm_pow]; nlinarith [norm_nonneg (y/t)]) hc
    rw [← he, norm_pow] at hh
    nlinarith [norm_nonneg (z/t)]
  exact ⟨ht,hx,hy,hz⟩

/-- The split-conic tangent is a square times a unit on its integral affine conic. -/
private theorem split_tangent_even (c x y : ℚ_[p]) (hc : ‖c‖ = 1) (h2 : ‖(2:ℚ_[p])‖ = 1)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hxy : x^2-y^2=c)
    (he : ((c+1)/2)*x-((1-c)/2)*y-c ≠ 0) :
    Even (((c+1)/2)*x-((1-c)/2)*y-c).valuation := by
  have hu := add_integral x y hx hy
  have hv := sub_integral x y hx hy
  have huv : (x+y)*(x-y)=c := by linear_combination hxy
  have hprod : ‖x+y‖*‖x-y‖=1 := by rw [← norm_mul, huv, hc]
  have hu1 : ‖x+y‖=1 := by nlinarith [norm_nonneg (x+y), norm_nonneg (x-y)]
  have hu0 : x+y ≠ 0 := by intro h; simp [h] at hu1
  have hid : (((c+1)/2)*x-((1-c)/2)*y-c) * (2*(x+y)) = c*(x+y-1)^2 := by
    field_simp
    linear_combination hxy
  have hnorm : ‖((c+1)/2)*x-((1-c)/2)*y-c‖ = ‖x+y-1‖^2 := by
    have hh := congrArg norm hid
    simpa only [norm_mul, norm_pow, h2, hu1, hc, one_mul, mul_one] using hh
  exact even_of_norm_square _ _ he hnorm

/-- Primitivity is transferred through the single common normalization scale. -/
private theorem primitive_scale_unit (q : ℤ_[p]) (hq : ¬ IsSquare (red q))
    (c d t x y z : ℚ_[p]) (hc : ‖c‖ ≤ 1) (hd : ‖d‖=1)
    (ht : ‖t‖ ≤ 1) (hprim : ‖t‖=1 ∨ ‖x‖=1 ∨ ‖y‖=1 ∨ ‖z‖=1)
    (h₃ : x^2-(q:ℚ_[p])*y^2=d*t^2) (h₂ : y^2-z^2=c*t^2) : ‖t‖=1 := by
  have hn : t ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := by
    rcases hprim with h | h | h | h
    · left; intro hz; simp [hz] at h
    · right; left; intro hz; simp [hz] at h
    · right; right; left; intro hz; simp [hz] at h
    · right; right; right; intro hz; simp [hz] at h
  obtain ⟨ht0,hx,hy,hz⟩ := common_normalization q hq c d t x y z hc hd hn h₃ h₂
  rw [norm_div, div_le_one (norm_pos_iff.mpr ht0)] at hx hy hz
  rcases hprim with h | h | h | h
  · exact h
  · exact le_antisymm ht (h ▸ hx)
  · exact le_antisymm ht (h ▸ hy)
  · exact le_antisymm ht (h ▸ hz)


private theorem mul_integral (x y : ℚ_[p]) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x*y‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

private theorem unit_scale_even (t e : ℚ_[p]) (ht : ‖t‖=1) (he : t*e ≠ 0)
    (h : e ≠ 0 → Even e.valuation) : Even (t*e).valuation := by
  obtain ⟨ht0,he0⟩ := mul_ne_zero_iff.mp he
  rw [Padic.valuation_mul ht0 he0, norm_unit_valuation t ht, zero_add]
  exact h he0

/-- Both tangent parities on an arbitrary nonzero common tuple, including primitive transfer. -/
theorem common_tangent_parity (q : ℤ_[p]) (hq : ¬ IsSquare (red q))
    (c d a b t x y z : ℚ_[p]) (hc : ‖c‖=1) (hd : ‖d‖=1) (h2 : ‖(2:ℚ_[p])‖=1)
    (hab : a^2-(q:ℚ_[p])*b^2=d)
    (hn : t ≠ 0 ∨ x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (h₃ : x^2-(q:ℚ_[p])*y^2=d*t^2) (h₂ : y^2-z^2=c*t^2) :
    let X := x/t; let Y := y/t; let Z := z/t
    let e₂ := ((c+1)/2)*Y-((1-c)/2)*Z-c
    let e₃ := a*X-(q:ℚ_[p])*b*Y-d
    t ≠ 0 ∧ ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖X‖ ≤ 1 ∧ ‖Y‖ ≤ 1 ∧ ‖Z‖ ≤ 1 ∧
    ‖e₂‖ ≤ 1 ∧ ‖e₃‖ ≤ 1 ∧ (e₂ ≠ 0 → Even e₂.valuation) ∧
    (e₃ ≠ 0 → Even e₃.valuation) ∧
    (‖t‖ ≤ 1 → (‖t‖=1 ∨ ‖x‖=1 ∨ ‖y‖=1 ∨ ‖z‖=1) →
      ‖t‖=1 ∧ (t*e₂ ≠ 0 → Even (t*e₂).valuation) ∧
      (t*e₃ ≠ 0 → Even (t*e₃).valuation)) := by
  dsimp
  obtain ⟨ht,hx,hy,hz⟩ := common_normalization q hq c d t x y z (le_of_eq hc) hd hn h₃ h₂
  obtain ⟨ha,hb⟩ := norm_coordinates q hq a b d hab hd
  have hn₃ : (x/t)^2-(q:ℚ_[p])*(y/t)^2=d := by field_simp; simpa [mul_comm] using h₃
  have hn₂ : (y/t)^2-(z/t)^2=c := by field_simp; simpa [mul_comm] using h₂
  have e₂ := split_tangent_even c (y/t) (z/t) hc h2 hy hz hn₂
  have e₃ := tangent_even q hq a b (x/t) (y/t) d hab hn₃ (by rw [norm_mul,h2,hd,one_mul])
  have hhalf₁ : ‖(c+1)/2‖ ≤ 1 := by
    rw [norm_div,h2,div_one]; exact add_integral c 1 (le_of_eq hc) (by simp)
  have hhalf₂ : ‖(1-c)/2‖ ≤ 1 := by
    rw [norm_div,h2,div_one]; exact sub_integral 1 c (by simp) (le_of_eq hc)
  have hi₂ := sub_integral _ c
    (sub_integral _ _ (mul_integral _ _ hhalf₁ hy) (mul_integral _ _ hhalf₂ hz)) (le_of_eq hc)
  have hq1 : ‖(q:ℚ_[p])‖ ≤ 1 := q.property
  have hi₃ := sub_integral _ d
    (sub_integral _ _ (mul_integral _ _ ha hx)
      (mul_integral _ _ (mul_integral _ _ hq1 hb) hy)) (le_of_eq hd)
  refine ⟨ht,ha,hb,hx,hy,hz,hi₂,hi₃,e₂,e₃,?_⟩
  intro hti hprim
  have htu := primitive_scale_unit q hq c d t x y z (le_of_eq hc) hd hti hprim h₃ h₂
  exact ⟨htu, fun he => unit_scale_even _ _ htu he e₂,
    fun he => unit_scale_even _ _ htu he e₃⟩

end D5.S3.Factorization.Mordell.UnramifiedQuadraticNorm
