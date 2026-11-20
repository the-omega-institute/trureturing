/- GID: D5/S3/TotalVariation/FourPointAffineProjection
   generality: G
   mirror-B: D5/B/S3/TotalVariation/FourPointAffineProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every four-point probability law has an explicit nearest affine independent-bit law. -/

import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import D5.S3.TotalVariation.Pinsker
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.TotalVariation.FourPointAffineProjection

open D5.S3.TotalVariation.Pinsker (totalVariation)

universe u

/-- The two-bit output space of an affine parity law. -/
abbrev Point := ZMod 2 × ZMod 2
/-- Finite signed masses on the output space, with multiplication given by convolution. -/
abbrev Mass := AddMonoidAlgebra ℝ Point

private def bit_sign (z : ZMod 2) : ℝ := if z = 0 then 1 else -1

private theorem bit_sign_add (a b : ZMod 2) :
    bit_sign (a + b) = bit_sign a * bit_sign b := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hcases a with rfl | rfl <;>
    rcases hcases b with rfl | rfl <;> norm_num [bit_sign, h11]
  decide

private def real_character (f : Point →+ ZMod 2) : Multiplicative Point →* ℝ where
  toFun x := bit_sign (f x.toAdd)
  map_one' := by simp [bit_sign]
  map_mul' x y := by
    change bit_sign (f (x.toAdd + y.toAdd)) = bit_sign (f x.toAdd) * bit_sign (f y.toAdd)
    rw [map_add, bit_sign_add]

private def coord₁ : Point →+ ZMod 2 := AddMonoidHom.fst (ZMod 2) (ZMod 2)
private def coord₂ : Point →+ ZMod 2 := AddMonoidHom.snd (ZMod 2) (ZMod 2)

private def moment_eval (f : Point →+ ZMod 2) : Mass →ₐ[ℝ] ℝ :=
  AddMonoidAlgebra.lift ℝ ℝ Point (real_character f)

private theorem expand_eval (f : Point →+ ZMod 2) (p : Mass) :
    moment_eval f p = ∑ x, p.coeff x * bit_sign (f x) := by
  rw [moment_eval, AddMonoidAlgebra.lift_apply', Finsupp.sum_fintype]
  · rfl
  · intro x
    simp

private theorem point_univ :
    (Finset.univ : Finset Point) = {(0, 0), (1, 0), (0, 1), (1, 1)} := by decide

private theorem mode₁_of_coeff (p : Mass) :
    moment_eval coord₁ p = p.coeff (0, 0) - p.coeff (1, 0) + p.coeff (0, 1) - p.coeff (1, 1) := by
  rw [expand_eval, point_univ]
  simp [coord₁, bit_sign]
  ring

private theorem mode₂_of_coeff (p : Mass) :
    moment_eval coord₂ p = p.coeff (0, 0) + p.coeff (1, 0) - p.coeff (0, 1) - p.coeff (1, 1) := by
  rw [expand_eval, point_univ]
  simp [coord₂, bit_sign]
  ring

private theorem mode₃_of_coeff (p : Mass) :
    moment_eval (coord₁ + coord₂) p = p.coeff (0, 0) - p.coeff (1, 0) - p.coeff (0, 1) + p.coeff (1, 1) := by
  rw [expand_eval, point_univ]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  simp [coord₁, coord₂, bit_sign, h11]
  ring

private def moment_constraint (p : Mass) : Prop :=
  |moment_eval coord₁ p| * |moment_eval (coord₁ + coord₂) p| ≤ |moment_eval coord₂ p|

private theorem moment_constraint_mul {p q : Mass}
    (hp : moment_constraint p) (hq : moment_constraint q) : moment_constraint (p * q) := by
  unfold moment_constraint at *
  rw [map_mul, map_mul, map_mul, abs_mul, abs_mul, abs_mul, mul_mul_mul_comm]
  exact mul_le_mul hp hq (by positivity) (by positivity)

private theorem moment_constraint_offset (s : Point) :
    moment_constraint (AddMonoidAlgebra.single s 1) := by
  have h (u : ZMod 2) : |bit_sign u| = 1 := by
    unfold bit_sign
    split_ifs <;> norm_num
  simp [moment_constraint, moment_eval, real_character, h]

private def bit_atom (c : Point) (t : ℝ) : Mass :=
  AddMonoidAlgebra.single 0 (1 - t) + AddMonoidAlgebra.single c t

private theorem moment_constraint_bit (c : Point) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    moment_constraint (bit_atom c t) := by
  have hzero : (1 : ZMod 2) + 1 = 0 := by decide
  have hsum : 1 - t + t = 1 := by ring
  have hbound : |1 - t - t| ≤ 1 := abs_le.mpr (by constructor <;> linarith)
  have hx : c ∈ (Finset.univ : Finset Point) := Finset.mem_univ c
  rw [point_univ] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    norm_num [moment_constraint, bit_atom, moment_eval, coord₁, coord₂,
      real_character, bit_sign, hzero, hsum, smul_eq_mul]
  nlinarith [abs_nonneg (1 - t - t)]

/-- The convolution law of an affine sum of independent bits with success rates `t`. -/
def affineBitLaw {I : Type*} [Fintype I] (s : Point)
    (c : I → Point) (t : I → ℝ) : Mass :=
  AddMonoidAlgebra.single s 1 * ∏ i, bit_atom (c i) (t i)

private def moment_sign_constraint (p : Mass) : Prop :=
  0 ≤ moment_eval coord₁ p * moment_eval (coord₁ + coord₂) p * moment_eval coord₂ p

private theorem moment_sign_constraint_mul {p q : Mass}
    (hp : moment_sign_constraint p) (hq : moment_sign_constraint q) :
    moment_sign_constraint (p * q) := by
  unfold moment_sign_constraint at *
  simp only [map_mul]
  convert mul_nonneg hp hq using 1
  ring

private theorem moment_sign_constraint_offset (s : Point) :
    moment_sign_constraint (AddMonoidAlgebra.single s 1) := by
  have hzero : (1 : ZMod 2) + 1 = 0 := by decide
  have hx : s ∈ (Finset.univ : Finset Point) := Finset.mem_univ s
  rw [point_univ] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    norm_num [moment_sign_constraint, moment_eval, coord₁, coord₂, real_character,
      bit_sign, hzero, smul_eq_mul]

private theorem moment_sign_constraint_bit (c : Point) (t : ℝ) :
    moment_sign_constraint (bit_atom c t) := by
  have hzero : (1 : ZMod 2) + 1 = 0 := by decide
  have hsum : 1 - t + t = 1 := by ring
  have hsquare : 0 ≤ (1 - t + -t) * (1 - t + -t) := mul_self_nonneg _
  have hx : c ∈ (Finset.univ : Finset Point) := Finset.mem_univ c
  rw [point_univ] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    norm_num [moment_sign_constraint, bit_atom, moment_eval, coord₁, coord₂,
      real_character, bit_sign, hzero, hsum, smul_eq_mul, hsquare]

private theorem affineBitLaw_moment_sign_nonnegative {I : Type*} [Fintype I] (s : Point)
    (c : I → Point) (t : I → ℝ) : moment_sign_constraint (affineBitLaw s c t) := by
  classical
  have hprod (J : Finset I) : moment_sign_constraint (∏ j ∈ J, bit_atom (c j) (t j)) := by
    induction J using Finset.induction_on with
    | empty => simp [moment_sign_constraint]
    | @insert j J hj ih =>
      rw [Finset.prod_insert hj]
      exact moment_sign_constraint_mul (moment_sign_constraint_bit (c j) (t j)) ih
  exact moment_sign_constraint_mul (moment_sign_constraint_offset s) (hprod Finset.univ)

private def momentA (p : Fin 4 → ℝ) : ℝ := p 0 - p 1 + p 2 - p 3
private def momentC (p : Fin 4 → ℝ) : ℝ := p 0 - p 1 - p 2 + p 3
private def momentB (p : Fin 4 → ℝ) : ℝ := p 0 + p 1 - p 2 - p 3

private theorem abs_delta_le_tv (p q : Fin 4 → ℝ) (h : ∑ i, p i = ∑ i, q i)
    (j : Fin 4) : |p j - q j| ≤ totalVariation p q := by
  classical
  let d (i : Fin 4) := p i - q i
  have hz : ∑ i, d i = 0 := by simpa [d, Finset.sum_sub_distrib] using sub_eq_zero.mpr h
  have hsum := Finset.sum_erase_add Finset.univ d (Finset.mem_univ j)
  have habs := Finset.sum_erase_add Finset.univ (fun i => |d i|) (Finset.mem_univ j)
  have hneg : ∑ i ∈ Finset.univ.erase j, d i = -d j := by linarith
  have hrest := Finset.abs_sum_le_sum_abs (fun i => d i) (Finset.univ.erase j)
  rw [hneg, abs_neg] at hrest
  change |d j| ≤ (1 / 2 : ℝ) * ∑ i, |d i|
  linarith

private theorem moment_deltas (p q : Fin 4 → ℝ)
    (m : (Fin 4 → ℝ) → ℝ) (hm : ∀ r, m r = ∑ i, r i * m (Pi.single i 1))
    (hcoef : ∀ i, |m (Pi.single i 1)| ≤ 1) :
    |m p - m q| ≤ 2 * totalVariation p q := by
  rw [hm p, hm q, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (p i * m (Pi.single i 1) - q i * m (Pi.single i 1))| ≤
        ∑ i, |p i * m (Pi.single i 1) - q i * m (Pi.single i 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |p i - q i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sub_mul, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hcoef i)
    _ = 2 * totalVariation p q := by unfold totalVariation; ring

private theorem four_point_signed_projection_lower_bound (p q : Fin 4 → ℝ)
    (h : ∑ i, p i = ∑ i, q i)
    (ha : 0 ≤ momentA p) (hac : momentA p ≤ momentC p) (hc : momentC p ≤ 1)
    (hb : -momentA p ≤ momentB p)
    (hq : |momentA q| * |momentC q| ≤ |momentB q|)
    (hsign : 0 ≤ momentA q * momentC q * momentB q) :
    momentA p * momentC p - momentB p ≤ 2 * (1 + momentC p) * totalVariation p q := by
  let a := momentA p
  let c := momentC p
  let b := momentB p
  let a' := momentA q
  let c' := momentC q
  let b' := momentB q
  let δ := totalVariation p q
  let x := max 0 (a - a')
  let y := max 0 (c - c')
  let z := b' - b
  have hδ : 0 ≤ δ := by unfold δ totalVariation; positivity
  have hsum : p 0 + p 1 + p 2 + p 3 = q 0 + q 1 + q 2 + q 3 := by
    simpa only [Fin.sum_univ_four, add_assoc] using h
  have hcoords : ∀ (i : Fin 4), |p i - q i| ≤ δ := fun i => abs_delta_le_tv p q h i
  have hdiffA : |a - a'| ≤ 2 * δ := by
    change |momentA p - momentA q| ≤ 2 * δ
    apply moment_deltas p q momentA
    · intro r
      simp [Fin.sum_univ_four, momentA, Pi.single_apply]
      ring
    · intro i
      fin_cases i <;> norm_num [momentA, Pi.single_apply]
  have hdiffC : |c - c'| ≤ 2 * δ := by
    change |momentC p - momentC q| ≤ 2 * δ
    apply moment_deltas p q momentC
    · intro r
      simp [Fin.sum_univ_four, momentC, Pi.single_apply]
      ring
    · intro i
      fin_cases i <;> norm_num [momentC, Pi.single_apply]
  have hdiffB : |b - b'| ≤ 2 * δ := by
    change |momentB p - momentB q| ≤ 2 * δ
    apply moment_deltas p q momentB
    · intro r
      simp [Fin.sum_univ_four, momentB, Pi.single_apply]
      ring
    · intro i
      fin_cases i <;> norm_num [momentB, Pi.single_apply]
  have hx : x ≤ 2 * δ := max_le (by linarith) ((abs_le.mp hdiffA).2)
  have hy : y ≤ 2 * δ := max_le (by linarith) ((abs_le.mp hdiffC).2)
  by_cases hneg : b' < 0
  · have hsmall : a ≤ 2 * δ := by
      by_cases ha' : a' ≤ 0
      · linarith [(abs_le.mp hdiffA).2]
      · have hc' : c' ≤ 0 := by
          by_contra! hc'
          exact (not_lt_of_ge hsign) (mul_neg_of_pos_of_neg
            (mul_pos (lt_of_not_ge ha') hc') hneg)
        linarith [(abs_le.mp hdiffC).2]
    have hc₀ : 0 ≤ c := ha.trans hac
    have hfactor := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ 1 + c by positivity)
    change a * c - b ≤ 2 * (1 + c) * δ
    linarith [show a * (1 + c) = a + a * c by ring,
      show (2 * δ) * (1 + c) = 2 * (1 + c) * δ by ring]
  have hz : z ≤ 2 * δ := by
    dsimp only [z]
    linarith [(abs_le.mp hdiffB).1]
  have hxy : x + y + z ≤ 4 * δ := by
    by_cases hxa : a - a' ≤ 0
    · dsimp only [x]
      rw [max_eq_left hxa]
      linarith
    by_cases hyc : c - c' ≤ 0
    · dsimp only [y]
      rw [max_eq_left hyc]
      linarith
    dsimp only [x, y, z]
    rw [max_eq_right (le_of_not_ge hxa), max_eq_right (le_of_not_ge hyc)]
    have hid : a - a' + (c - c') + (b' - b) = 4 * (q 1 - p 1) := by
      dsimp [a, a', b, b', c, c', momentA, momentB, momentC]
      linarith
    rw [hid]
    linarith [(abs_le.mp (hcoords 1)).1]
  have hax : a - x ≤ |a'| := by
    have hxa : a - a' ≤ x := le_max_right _ _
    linarith [le_abs_self a']
  have hcy : c - y ≤ |c'| := by
    have hyc : c - c' ≤ y := le_max_right _ _
    linarith [le_abs_self c']
  have hprod : a * c - c * x - a * y ≤ |a'| * |c'| := by
    have haxc : 0 ≤ x := le_max_left _ _
    have hycc : 0 ≤ y := le_max_left _ _
    by_cases hax0 : 0 ≤ a - x
    · by_cases hcy0 : 0 ≤ c - y
      · have hmul := mul_le_mul hax hcy hcy0 (abs_nonneg a')
        nlinarith [mul_nonneg haxc hycc]
      · have h1 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hcy0)
        have h2 := mul_nonneg (ha.trans hac) haxc
        nlinarith [mul_nonneg (abs_nonneg a') (abs_nonneg c')]
    · have h1 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hax0) (ha.trans hac)
      have h2 := mul_nonneg ha hycc
      nlinarith [mul_nonneg (abs_nonneg a') (abs_nonneg c')]
  change a * c - b ≤ 2 * (1 + c) * δ
  have hbound : a * c - b ≤ c * (x + y) + z := by
    have hadj := mul_le_mul_of_nonneg_right hac (show 0 ≤ y from le_max_left _ _)
    have hq' : |a'| * |c'| ≤ b' := by
      rw [← abs_of_nonneg (le_of_not_gt hneg)]
      exact hq
    change a * c - b ≤ c * (x + y) + (b' - b)
    linarith [show c * (x + y) = c * x + c * y by ring]
  have hnext := mul_le_mul_of_nonneg_left hxy (ha.trans hac)
  have hlast := mul_le_mul_of_nonneg_left hz (show 0 ≤ 1 - c by linarith)
  linarith [show c * (x + y + z) = c * (x + y) + c * z by ring,
    show (1 - c) * z = z - c * z by ring,
    show (1 - c) * (2 * δ) = 2 * δ - 2 * c * δ by ring,
    show c * (4 * δ) = 4 * c * δ by ring,
    show 2 * (1 + c) * δ = 2 * δ + 2 * c * δ by ring]

private theorem four_point_signed_projection_attained (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (ha : 0 ≤ momentA p) (hac : momentA p ≤ momentC p) (hc : momentC p ≤ 1)
    (hb : -momentA p ≤ momentB p) (hgap : momentB p ≤ momentA p * momentC p) :
    ∃ q : Fin 4 → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      momentB q = momentA q * momentC q ∧
      totalVariation p q = (momentA p * momentC p - momentB p) / (2 * (1 + momentC p)) := by
  let a := momentA p
  let c := momentC p
  let b := momentB p
  let δ := (a * c - b) / (2 * (1 + c))
  have hc₀ : 0 ≤ c := ha.trans hac
  have hdenom : 0 < 2 * (1 + c) := by positivity
  have hδ : 0 ≤ δ := div_nonneg (sub_nonneg.mpr hgap) hdenom.le
  have hδeq : δ * (2 * (1 + c)) = a * c - b :=
    (div_mul_cancel₀ _ hdenom.ne')
  have hmass : 4 * p 2 = 1 + a - c - b := by
    rw [Fin.sum_univ_four] at hs
    dsimp [a, b, c, momentA, momentB, momentC]
    linarith
  have hp₂ : δ ≤ p 2 := by
    have hfactor : 0 ≤ (1 - c) * (1 + c + a + b) := by
      apply mul_nonneg (sub_nonneg.mpr hc)
      linarith
    have hcalc :
        2 * (p 2 * (2 * (1 + c))) - 2 * (a * c - b) =
          (1 - c) * (1 + c + a + b) := by
      linear_combination (1 + c) * hmass
    apply (div_le_iff₀ hdenom).mpr
    linarith
  let q : Fin 4 → ℝ := ![p 0, p 1 + δ, p 2 - δ, p 3]
  have hq0 : q 0 = p 0 := rfl
  have hq1 : q 1 = p 1 + δ := rfl
  have hq2 : q 2 = p 2 - δ := rfl
  have hq3 : q 3 = p 3 := rfl
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hp 0
    · exact add_nonneg (hp 1) hδ
    · exact sub_nonneg.mpr hp₂
    · exact hp 3
  · rw [Fin.sum_univ_four, hq0, hq1, hq2, hq3]
    rw [Fin.sum_univ_four] at hs
    linarith
  · have hA : momentA q = a - 2 * δ := by
      unfold momentA
      rw [hq0, hq1, hq2, hq3]
      dsimp [a, momentA]
      ring
    have hC : momentC q = c := by
      unfold momentC
      rw [hq0, hq1, hq2, hq3]
      dsimp [c, momentC]
      ring
    have hB : momentB q = b + 2 * δ := by
      unfold momentB
      rw [hq0, hq1, hq2, hq3]
      dsimp [b, momentB]
      ring
    rw [hA, hB, hC]
    linear_combination hδeq
  · unfold totalVariation
    rw [Fin.sum_univ_four, hq0, hq1, hq2, hq3]
    change _ = δ
    rw [show p 1 - (p 1 + δ) = -δ by ring, show p 2 - (p 2 - δ) = δ by ring]
    simp [abs_of_nonneg hδ]
    ring

private theorem biases_of_ordered_moments (a b c : ℝ)
    (ha : 0 ≤ a) (hab : b ≤ a) (hac : a ≤ c) (hc : c ≤ 1) (hprod : a * c ≤ b) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, ∃ z ∈ Set.Icc (0 : ℝ) 1,
      x * y = a ∧ x * z = c ∧ y * z = b := by
  have hc₀ := ha.trans hac
  have hb := (mul_nonneg ha hc₀).trans hprod
  rcases eq_or_lt_of_le hb with rfl | hb₀
  · have haz : a = 0 := by
      by_contra h
      exact (not_lt_of_ge hprod) (mul_pos (lt_of_le_of_ne ha (Ne.symm h))
        ((lt_of_le_of_ne ha (Ne.symm h)).trans_le hac))
    refine ⟨c, ⟨hc₀, hc⟩, 0, by simp, 1, by simp, ?_⟩
    simp [haz]
  have ha₀ := hb₀.trans_le hab
  have hc₀' := ha₀.trans_le hac
  have habc : a * b ≤ c := by
    calc
      a * b ≤ a * 1 := mul_le_mul_of_nonneg_left ((hab.trans hac).trans hc) ha
      _ ≤ c := by simpa using hac
  have hbca : b * c ≤ a := by
    calc
      b * c ≤ b * 1 := mul_le_mul_of_nonneg_left hc hb
      _ ≤ a := by simpa using hab
  let x := Real.sqrt (a * c / b)
  let y := Real.sqrt (a * b / c)
  let z := Real.sqrt (b * c / a)
  have hIcc {u v : ℝ} (hu : 0 ≤ u) (hv : 0 < v) (h : u ≤ v) :
      Real.sqrt (u / v) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    rw [Real.sqrt_le_one]
    exact (div_le_iff₀ hv).mpr (by simpa using h)
  refine ⟨x, hIcc (mul_nonneg ha hc₀) hb₀ hprod,
    y, hIcc (mul_nonneg ha hb) hc₀' habc,
    z, hIcc (mul_nonneg hb hc₀) ha₀ hbca, ?_, ?_, ?_⟩
  · dsimp only [x, y]
    rw [← Real.sqrt_mul (by positivity), show a * c / b * (a * b / c) = a ^ 2 by
      field_simp, Real.sqrt_sq ha]
  · dsimp only [x, z]
    rw [← Real.sqrt_mul (by positivity), show a * c / b * (b * c / a) = c ^ 2 by
      field_simp, Real.sqrt_sq hc₀]
  · dsimp only [y, z]
    rw [← Real.sqrt_mul (by positivity), show a * b / c * (b * c / a) = b ^ 2 by
      field_simp, Real.sqrt_sq hb]

/-- Read the four masses in the order `00, 10, 01, 11`. -/
def tabulate (p : Mass) : Fin 4 → ℝ :=
  ![p.coeff (0, 0), p.coeff (1, 0), p.coeff (0, 1), p.coeff (1, 1)]

private theorem tabulate_momentA (p : Mass) :
    momentA (tabulate p) = moment_eval coord₁ p :=
  (mode₁_of_coeff p).symm

private theorem tabulate_momentC (p : Mass) :
    momentC (tabulate p) = moment_eval (coord₁ + coord₂) p :=
  (mode₃_of_coeff p).symm

private theorem tabulate_momentB (p : Mass) :
    momentB (tabulate p) = moment_eval coord₂ p :=
  (mode₂_of_coeff p).symm

private theorem affine_tabulate_sum {I : Type*} [Fintype I]
    (s : Point) (c : I → Point) (t : I → ℝ) : ∑ i, tabulate (affineBitLaw s c t) i = 1 := by
  have hsum (p : Mass) : ∑ i, tabulate p i = moment_eval 0 p := by
    rw [expand_eval, point_univ, Fin.sum_univ_four]
    simp [tabulate, bit_sign, add_left_comm, add_comm]
  have hbit (j : I) : moment_eval 0 (bit_atom (c j) (t j)) = 1 := by
    simp [bit_atom, moment_eval, real_character, bit_sign, smul_eq_mul]
  rw [hsum, affineBitLaw, map_mul, map_prod]
  simp only [hbit, Finset.prod_const_one, mul_one]
  simp [moment_eval, real_character, bit_sign]

private theorem affine_tabulate_constraints {I : Type*} [Fintype I]
    (s : Point) (c : I → Point) (t : I → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) :
    let q := tabulate (affineBitLaw s c t)
    (|momentA q| * |momentC q| ≤ |momentB q|) ∧
      0 ≤ momentA q * momentC q * momentB q := by
  classical
  have hproducts (J : Finset I) : moment_constraint (∏ j ∈ J, bit_atom (c j) (t j)) := by
    induction J using Finset.induction_on with
    | empty => simp [moment_constraint]
    | @insert j J hj ih =>
      rw [Finset.prod_insert hj]
      exact moment_constraint_mul (moment_constraint_bit (c j) (t j) (ht j).1 (ht j).2) ih
  dsimp only
  rw [tabulate_momentA, tabulate_momentC, tabulate_momentB]
  exact ⟨moment_constraint_mul (moment_constraint_offset s) (hproducts Finset.univ),
    affineBitLaw_moment_sign_nonnegative s c t⟩

private def threeColumn (i : Fin 3) : Point := ![(1, 0), (1, 1), (0, 1)] i

private def threeProbability (x y z : ℝ) (i : Fin 3) : ℝ :=
  ![(1 - x) / 2, (1 - y) / 2, (1 - z) / 2] i

private theorem threeProbability_mem {x y z : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ i, threeProbability x y z i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  rcases hx with ⟨hx₀, hx₁⟩
  rcases hy with ⟨hy₀, hy₁⟩
  rcases hz with ⟨hz₀, hz₁⟩
  fin_cases i
  · exact ⟨show 0 ≤ (1 - x) / 2 by linarith, show (1 - x) / 2 ≤ 1 by linarith⟩
  · exact ⟨show 0 ≤ (1 - y) / 2 by linarith, show (1 - y) / 2 ≤ 1 by linarith⟩
  · exact ⟨show 0 ≤ (1 - z) / 2 by linarith, show (1 - z) / 2 ≤ 1 by linarith⟩

private def threeLaw (x y z : ℝ) : Fin 4 → ℝ :=
  tabulate (affineBitLaw 0 threeColumn (threeProbability x y z))

private theorem threeLaw_moments (x y z : ℝ) :
    momentA (threeLaw x y z) = x * y ∧ momentC (threeLaw x y z) = x * z ∧
      momentB (threeLaw x y z) = y * z := by
  have hzero : (1 : ZMod 2) + 1 = 0 := by decide
  unfold threeLaw
  rw [tabulate_momentA, tabulate_momentC, tabulate_momentB]
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [Fin.prod_univ_three, affineBitLaw, threeColumn, threeProbability, bit_atom,
      moment_eval, coord₁, coord₂, real_character, bit_sign, hzero, smul_eq_mul] <;> ring

private theorem eq_of_moments {p q : Fin 4 → ℝ}
    (hpq : ∑ i, p i = ∑ i, q i)
    (ha : momentA p = momentA q) (hb : momentB p = momentB q)
    (hc : momentC p = momentC q) : p = q := by
  rw [Fin.sum_univ_four, Fin.sum_univ_four] at hpq
  unfold momentA momentB momentC at *
  funext i
  fin_cases i
  · change p 0 = q 0
    linarith
  · change p 1 = q 1
    linarith
  · change p 2 = q 2
    linarith
  · change p 3 = q 3
    linarith

private theorem moment_range {p : Fin 4 → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    momentA p ∈ Set.Icc (-1 : ℝ) 1 ∧ momentC p ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [Fin.sum_univ_four] at hs
  unfold momentA momentC
  exact ⟨⟨by linarith [hp 0, hp 2], by linarith [hp 1, hp 3]⟩,
    ⟨by linarith [hp 0, hp 3], by linarith [hp 1, hp 2]⟩⟩

private theorem four_point_affine_projection (p : Fin 4 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (ha : 0 ≤ momentA p) (hac : momentA p ≤ momentC p)
    (hblo : -momentA p ≤ momentB p) (hbhi : momentB p ≤ momentA p) :
    let d := max 0 (momentA p * momentC p - momentB p) / (2 * (1 + momentC p))
    (∀ {I : Type u} [Fintype I] (s : Point) (c : I → Point) (t : I → ℝ),
      (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) → d ≤ totalVariation p (tabulate (affineBitLaw s c t))) ∧
    ∃ x ∈ Set.Icc (-1 : ℝ) 1, ∃ y ∈ Set.Icc (-1 : ℝ) 1, ∃ z ∈ Set.Icc (-1 : ℝ) 1,
      totalVariation p (threeLaw x y z) = d := by
  have hc := (moment_range hp hs).2.2
  have hc₀ := ha.trans hac
  have hdenom : 0 < 2 * (1 + momentC p) := by positivity
  dsimp only
  constructor
  · intro I _ s c t ht
    have hm := affine_tabulate_sum s c t
    have hcond := affine_tabulate_constraints s c t ht
    apply (div_le_iff₀ hdenom).mpr
    rw [mul_comm (totalVariation p (tabulate (affineBitLaw s c t)))]
    apply max_le
    · unfold totalVariation
      positivity
    · exact four_point_signed_projection_lower_bound _ _ (hs.trans hm.symm) ha hac hc
        hblo hcond.1 hcond.2
  by_cases hgood : momentA p * momentC p ≤ momentB p
  · rw [max_eq_left (sub_nonpos.mpr hgood), zero_div]
    obtain ⟨x, hx, y, hy, z, hz, hA, hC, hB⟩ :=
      biases_of_ordered_moments _ _ _ ha hbhi hac hc hgood
    have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have hy' : y ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
    have hz' : z ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
    refine ⟨x, hx', y, hy', z, hz', ?_⟩
    obtain ⟨ha', hc', hb'⟩ := threeLaw_moments x y z
    have eq : p = threeLaw x y z := eq_of_moments (hs.trans (affine_tabulate_sum 0 threeColumn
      (threeProbability x y z)).symm) ((ha'.trans hA).symm)
      ((hb'.trans hB).symm) ((hc'.trans hC).symm)
    rw [eq]
    simp [totalVariation]
  · have hbad := (le_of_not_ge hgood)
    rw [max_eq_right (sub_nonneg.mpr hbad)]
    obtain ⟨q, hq, hm, hfactor, htv⟩ :=
      four_point_signed_projection_attained p hp hs ha hac hc hblo hbad
    obtain ⟨hqA, hqC⟩ := moment_range hq hm
    have hOne : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
    refine ⟨1, hOne, momentA q, hqA, momentC q, hqC, ?_⟩
    obtain ⟨ha', hc', hb'⟩ := threeLaw_moments 1 (momentA q) (momentC q)
    have eq : q = threeLaw 1 (momentA q) (momentC q) := eq_of_moments (hm.trans (affine_tabulate_sum 0 threeColumn
      (threeProbability 1 (momentA q) (momentC q))).symm)
      (by simpa only [one_mul] using ha'.symm)
      (hfactor.trans hb'.symm)
      (by simpa only [one_mul] using hc'.symm)
    rwa [← eq]

private def normalizingPermutation (p : Fin 4 → ℝ) : Equiv.Perm (Fin 4) :=
  let place : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective (![3, 0, 1, 2] : Fin 4 → Fin 4) (by decide)
  place.trans (Tuple.sort p)

/-- Relabel the four atoms in the order largest, smallest,
second-smallest, second-largest. This makes the first two chosen moments
nonnegative, with the product character having the smallest absolute moment. -/
def normalizedMass (p : Fin 4 → ℝ) : Fin 4 → ℝ := p ∘ normalizingPermutation p

private theorem order_normalizes_moments (p : Fin 4 → ℝ) :
    let r := normalizedMass p
    0 ≤ momentA r ∧ momentA r ≤ momentC r ∧
      -momentA r ≤ momentB r ∧ momentB r ≤ momentA r := by
  let r := normalizedMass p
  have hsort := Tuple.monotone_sort p
  have h01 : r 1 ≤ r 2 := hsort (show (0 : Fin 4) ≤ 1 by decide)
  have h23 : r 2 ≤ r 3 := hsort (show (1 : Fin 4) ≤ 2 by decide)
  have h30 : r 3 ≤ r 0 := hsort (show (2 : Fin 4) ≤ 3 by decide)
  exact ⟨by dsimp only [momentA]; linarith,
    by dsimp only [momentA, momentC]; linarith,
    by dsimp only [momentA, momentB]; linarith,
    by dsimp only [momentA, momentB]; linarith⟩

private abbrev pointLabel : Fin 4 ≃ Point :=
  Equiv.ofBijective (![ (0, 0), (1, 0), (0, 1), (1, 1)] : Fin 4 → Point) (by decide)

private theorem tabulate_eq (p : Mass) (x : Fin 4) :
    tabulate p x = p.coeff (pointLabel x) := by
  fin_cases x <;> rfl

private theorem every_permutation_affine (σ : Equiv.Perm Point) (x y : Point) :
    σ (x + y) = σ x + σ y - σ 0 := by
  have h : ∀ (σ : Equiv.Perm Point) (x y : Point), σ (x + y) = σ x + σ y - σ 0 := by
    decide +kernel
  exact h σ x y

private def linear_part (σ : Equiv.Perm Point) : Point ≃+ Point where
  toEquiv := σ.trans (Equiv.addRight (-σ 0))
  map_add' x y := by
    change σ (x + y) + -σ 0 = (σ x + -σ 0) + (σ y + -σ 0)
    rw [every_permutation_affine]
    abel

private def transport (σ : Equiv.Perm Point) (p : Mass) : Mass :=
  AddMonoidAlgebra.single (σ 0) 1 * AddMonoidAlgebra.domCongr ℝ ℝ (linear_part σ) p

private theorem transport_relabels (σ : Equiv.Perm Point) (p : Mass) (x : Point) :
    (transport σ p).coeff (σ x) = p.coeff x := by
  have h : σ 0 + linear_part σ x = σ x := by
    change σ 0 + (σ x + -σ 0) = σ x
    abel
  unfold transport
  rw [← h, AddMonoidAlgebra.coeff_single_mul_add, one_mul, AddMonoidAlgebra.coeff_domCongr,
    AddEquiv.symm_apply_apply]

private theorem transport_affineBitLaw {I : Type*} [Fintype I]
    (σ : Equiv.Perm Point) (s : Point) (c : I → Point) (t : I → ℝ) :
    transport σ (affineBitLaw s c t) =
      affineBitLaw (σ s) (fun i => linear_part σ (c i)) t := by
  classical
  have h : σ 0 + linear_part σ s = σ s := by
    change σ 0 + (σ s + -σ 0) = σ s
    abel
  unfold transport affineBitLaw
  rw [map_mul, AddMonoidAlgebra.domCongr_single, ← mul_assoc, AddMonoidAlgebra.single_mul_single,
    one_mul, h, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [bit_atom]

private def pointPermutation (σ : Equiv.Perm (Fin 4)) : Equiv.Perm Point :=
  pointLabel.symm.trans (σ.trans pointLabel)

private theorem tabulate_transport (σ : Equiv.Perm (Fin 4)) (q : Mass) :
    tabulate (transport (pointPermutation σ).symm q) = tabulate q ∘ σ := by
  funext i
  simp only [Function.comp_apply, tabulate_eq]
  have h := transport_relabels (pointPermutation σ).symm q (pointLabel (σ i))
  have he : (pointPermutation σ).symm (pointLabel (σ i)) = pointLabel i := by
    apply (pointPermutation σ).injective
    simp [pointPermutation]
  rwa [he] at h

private theorem transport_back (σ : Equiv.Perm Point) (q : Mass) :
    transport σ.symm (transport σ q) = q := by
  ext x
  rw [← σ.symm_apply_apply x, transport_relabels σ.symm, transport_relabels σ]

private theorem totalVariation_comp (σ : Equiv.Perm (Fin 4)) (p q : Fin 4 → ℝ) :
    totalVariation (p ∘ σ) (q ∘ σ) = totalVariation p q := by
  unfold totalVariation
  congr 1
  exact σ.sum_comp (fun i => |p i - q i|)

/-- The candidate distance from the three nontrivial sign moments. The first
and second selected moment correspond to the first coordinate and the sum of
the two coordinates in the model's atom ordering. -/
def projectionDistance (p : Fin 4 → ℝ) : ℝ :=
  let r := normalizedMass p
  max 0 (momentA r * momentC r - momentB r) / (2 * (1 + momentC r))

/-- Every probability mass on the four-point space is at least
`projectionDistance p` from any affine independent-bit law. Some law with
three input bits attains the bound. A deterministic bit may be unused. -/
theorem affine_projection_exact (p : Fin 4 → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) :
    (∀ {I : Type u} [Fintype I] (s : Point) (c : I → Point) (t : I → ℝ),
      (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) →
      projectionDistance p ≤ totalVariation p (tabulate (affineBitLaw s c t))) ∧
    ∃ (s : Point) (c : Fin 3 → Point) (t : Fin 3 → ℝ),
      (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧
      totalVariation p (tabulate (affineBitLaw s c t)) = projectionDistance p := by
  let σ := normalizingPermutation p
  let r := normalizedMass p
  let τ := pointPermutation σ
  obtain ⟨ha, hac, hb₀, hb₁⟩ := order_normalizes_moments p
  have hr : ∑ i, r i = 1 := (σ.sum_comp p).trans hs
  obtain ⟨lower, attainable⟩ :=
    four_point_affine_projection r (fun i => hp (σ i)) hr ha hac hb₀ hb₁
  constructor
  · intro I _ s c t ht
    let q := affineBitLaw s c t
    have h := lower (τ.symm s) (fun i => linear_part τ.symm (c i)) t ht
    rw [← transport_affineBitLaw τ.symm s c t] at h
    change projectionDistance p ≤ totalVariation r (tabulate (transport τ.symm q)) at h
    rw [tabulate_transport σ q, totalVariation_comp σ] at h
    exact h
  · obtain ⟨x, hx, y, hy, z, hz, hd⟩ := attainable
    let t := threeProbability x y z
    let q := affineBitLaw 0 threeColumn t
    refine ⟨τ 0, fun i => linear_part τ (threeColumn i), t, threeProbability_mem hx hy hz, ?_⟩
    rw [← transport_affineBitLaw τ 0 threeColumn t, ← totalVariation_comp σ]
    rw [← tabulate_transport σ (transport τ q), transport_back]
    exact hd

end D5.S3.TotalVariation.FourPointAffineProjection
