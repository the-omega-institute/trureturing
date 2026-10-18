/- GID: D5/S3/Factorization/Mordell/GoodPrimeCoverings
   generality: G
   mirror-B: D5/B/S3/Factorization/Mordell/GoodPrimeCoverings
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint finite-field square conditions and good-prime common coverings. -/

import D5.S3.Factorization.Mordell.FieldKummer
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Joint residue solutions and their simultaneous p-adic lifting. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.Mordell.GoodPrimeCoverings

open scoped BigOperators
open Finset

section Finite
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local notation "χ" => quadraticChar F

private theorem shifted_sum (hF : ringChar F ≠ 2) (a : F) :
    ∑ x : F, χ (x - a) = 0 := by
  calc
    (∑ x : F, χ (x - a)) = ∑ x : F, χ x := (Equiv.subRight a).sum_comp _
    _ = 0 := quadraticChar_sum_zero hF

private theorem pair_sum (hF : ringChar F ≠ 2) (a b : F) (hab : a ≠ b) :
    ∑ x : F, χ ((x - a) * (x - b)) = -1 := by
  have reindex : (∑ x ∈ univ.erase b, χ ((x - a) * (x - b))) =
      ∑ y ∈ univ.erase (1 : F), χ y := by
    apply Finset.sum_bij (fun x _ => (x - a)/(x - b))
    · intro x hx
      have hx : x ≠ b := (mem_erase.mp hx).1
      simp only [mem_erase, mem_univ, and_true]
      intro h
      have he := (div_eq_one_iff_eq (sub_ne_zero.mpr hx)).mp h
      exact hab (by linear_combination -he)
    · intro x hx y hy h
      have hx : x ≠ b := (mem_erase.mp hx).1
      have hy : y ≠ b := (mem_erase.mp hy).1
      have he : (x - y) * (a - b) = 0 := by
        field_simp at h
        linear_combination h
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hab))
    · intro y hy
      have hy : y ≠ 1 := (mem_erase.mp hy).1
      let x := (y * b - a)/(y - 1)
      have hx : x ≠ b := by
        intro hx
        have he : y * b - a = b * (y - 1) := (div_eq_iff (sub_ne_zero.mpr hy)).mp hx
        exact hab (by linear_combination -he)
      refine ⟨x, mem_erase.mpr ⟨hx, mem_univ _⟩, ?_⟩
      apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
      dsimp [x]
      field_simp
      ring
    · intro x hx
      have hx : x - b ≠ 0 := sub_ne_zero.mpr (mem_erase.mp hx).1
      have he : (x - a) * (x - b) = ((x - a)/(x - b)) * (x - b) ^ 2 := by field_simp
      rw [he, map_mul, quadraticChar_sq_one' hx, mul_one]
  have hl := sum_erase_add univ (fun x : F => χ ((x - a) * (x - b))) (mem_univ b)
  have hr := sum_erase_add univ (fun x : F => χ x) (mem_univ (1 : F))
  simp only [sub_self, mul_zero, quadraticChar_zero, add_zero] at hl
  rw [← hl, reindex]
  rw [quadraticChar_sum_zero hF, map_one] at hr
  linarith

private theorem char_lower (x : F) : -1 ≤ χ x := by
  by_cases hx : x = 0
  · simp [hx]
  · rcases quadraticChar_dichotomy hx with h | h <;> omega

private theorem joint_squares (hF : ringChar F ≠ 2)
    (a b c u v w : F) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hprod : χ u * χ v * χ w = 1)
    (hsum : χ u * χ v + χ u * χ w + χ v * χ w = -1) :
    ∃ x : F, IsSquare (u * (x - a)) ∧ IsSquare (v * (x - b)) ∧ IsSquare (w * (x - c)) := by
  by_contra h
  have hz (x : F) : (1 + χ (u * (x - a))) * (1 + χ (v * (x - b))) * (1 + χ (w * (x - c))) = 0 := by
    by_cases h₁ : IsSquare (u * (x - a))
    · by_cases h₂ : IsSquare (v * (x - b))
      · have h₃ : ¬IsSquare (w * (x - c)) := fun h₃ => h ⟨x,h₁,h₂,h₃⟩
        rw [quadraticChar_neg_one_iff_not_isSquare.mpr h₃]; ring
      · rw [quadraticChar_neg_one_iff_not_isSquare.mpr h₂]; ring
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr h₁]; ring
  have hexpand (x : F) :
      (1 + χ (u * (x - a))) * (1 + χ (v * (x - b))) * (1 + χ (w * (x - c))) =
      1 + χ u * χ (x - a) + χ v * χ (x - b) + χ w * χ (x - c) + 
      (χ u * χ v) * χ ((x - a) * (x - b)) + (χ u * χ w) * χ ((x - a) * (x - c)) + 
      (χ v * χ w) * χ ((x - b) * (x - c)) + 
      (χ u * χ v * χ w) * χ ((x - a) * (x - b) * (x - c)) := by
    simp only [map_mul]; ring
  have hs := Finset.sum_eq_zero (s := (univ : Finset F)) (fun x _ => hz x)
  simp_rw [hexpand, sum_add_distrib, ← mul_sum] at hs
  rw [shifted_sum hF a, shifted_sum hF b, shifted_sum hF c,
    pair_sum hF a b hab, pair_sum hF a c hac, pair_sum hF b c hbc, hprod] at hs
  have hn : 0 ≤ ∑ x : F, (1 + χ ((x - a) * (x - b) * (x - c))) :=
    sum_nonneg (fun x _ => by have := char_lower ((x - a) * (x - b) * (x - c)); omega)
  rw [sum_add_distrib] at hn
  nlinarith

omit [Fintype F] [DecidableEq F] in
private theorem weighted_square (u y : F) (hu : u ≠ 0) (h : IsSquare (u * y)) :
    ∃ z : F, u * z ^ 2 = y := by
  classical
  rcases h with ⟨z,hz⟩
  refine ⟨z/u, ?_⟩
  field_simp
  linear_combination -hz

private theorem residue_common (hF : ringChar F ≠ 2) (a b u v w : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hprod : χ u * χ v * χ w = 1)
    (hsum : χ u * χ v + χ u * χ w + χ v * χ w = -1) :
    ∃ z₁ z₂ z₃ : F, v * z₂ ^ 2 - u * z₁ ^ 2 = a ∧ u * z₁ ^ 2 - w * z₃ ^ 2 = b := by
  obtain ⟨x,h₁,h₂,h₃⟩ := joint_squares hF 0 (-a) b u v w
    (by simpa using ha) (by simpa using hb.symm)
    (by intro h; apply hab; linear_combination -h) hprod hsum
  obtain ⟨z₁,hz₁⟩ := weighted_square u (x - 0) hu h₁
  obtain ⟨z₂,hz₂⟩ := weighted_square v (x- -a) hv h₂
  obtain ⟨z₃,hz₃⟩ := weighted_square w (x - b) hw h₃
  refine ⟨z₁,z₂,z₃,?_,?_⟩
  · linear_combination hz₂ - hz₁
  · linear_combination hz₁ - hz₃

end Finite

section Lifting
variable {p : ℕ} [Fact p.Prime]
local notation "red" => (PadicInt.toZMod : ℤ_[p] →+* ZMod p)

private theorem residue_norm_lt_one (x : ℤ_[p]) (h : red x = 0) : ‖x‖ < 1 := by
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]; exact h
  simpa only [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] using hm

private theorem residue_norm_one (x : ℤ_[p]) (h : red x ≠ 0) : ‖x‖ = 1 := by
  apply le_antisymm (PadicInt.norm_le_one x)
  by_contra hn
  have hm : x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    simpa only [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] using (lt_of_not_ge hn)
  apply h
  rwa [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm

private theorem lift_weighted (A B : ℤ_[p]) (h₂ : (2 : ZMod p) ≠ 0)
    (hB : red B ≠ 0) (z : ZMod p) (hz : z ≠ 0) (he : red B * z ^ 2 = red A) :
    ∃ Z : ℤ_[p], B * Z ^ 2 = A := by
  let a : ℤ_[p] := (z.val : ℤ_[p])
  have ha : red a = z := by simp [a]
  let f : Polynomial ℤ_[p] := Polynomial.C B * Polynomial.X ^ 2 - Polynomial.C A
  have hf : f.aeval a = B * a ^ 2 - A := by simp [f]
  have hd : f.derivative.aeval a = 2 * B * a := by simp [f, Polynomial.derivative_mul]; ring
  have hn : ‖f.aeval a‖ < 1 := by
    apply residue_norm_lt_one
    rw [hf]
    simp only [map_sub, map_mul, map_pow, ha, he, sub_self]
  have hu : ‖f.derivative.aeval a‖ = 1 := by
    apply residue_norm_one
    rw [hd]
    simpa only [map_mul, map_ofNat, ha] using mul_ne_zero (mul_ne_zero h₂ hB) hz
  have hnorm : ‖f.aeval a‖ < ‖f.derivative.aeval a‖ ^ 2 := by
    rw [hu]; simpa using hn
  obtain ⟨Z,hZ,-⟩ := hensels_lemma hnorm
  refine ⟨Z, ?_⟩
  have : B * Z ^ 2 - A = 0 := by simpa [f] using hZ
  exact sub_eq_zero.mp this

private theorem lift_common (a b u v w : ℤ_[p]) (h₂ : (2 : ZMod p) ≠ 0)
    (ha : red a ≠ 0) (hb : red b ≠ 0) (hab : red (a + b) ≠ 0)
    (hu : red u ≠ 0) (hv : red v ≠ 0) (hw : red w ≠ 0)
    (z₁ z₂ z₃ : ZMod p)
    (e₁ : red v * z₂ ^ 2 - red u * z₁ ^ 2 = red a)
    (e₂ : red u * z₁ ^ 2 - red w * z₃ ^ 2 = red b) :
    ∃ Z₁ Z₂ Z₃ : ℤ_[p], v * Z₂ ^ 2 - u * Z₁ ^ 2 = a ∧ u * Z₁ ^ 2 - w * Z₃ ^ 2 = b := by
  by_cases h₁ : z₁ = 0
  · have h₂' : z₂ ≠ 0 := by intro hz; apply ha; simpa [h₁,hz] using e₁.symm
    have h₃ : z₃ ≠ 0 := by intro hz; apply hb; simpa [h₁,hz] using e₂.symm
    obtain ⟨Z₂,hZ₂⟩ := lift_weighted a v h₂ hv z₂ h₂' (by simpa [h₁] using e₁)
    obtain ⟨Z₃,hZ₃⟩ := lift_weighted (-b) w h₂ hw z₃ h₃ (by
      simp only [map_neg]
      simp only [h₁,zero_pow (by decide : 2 ≠ 0),mul_zero] at e₂
      linear_combination -e₂)
    refine ⟨0,Z₂,Z₃,?_,?_⟩ <;> simp [hZ₂,hZ₃]
  · by_cases h₂' : z₂ = 0
    · have h₃ : z₃ ≠ 0 := by
        intro hz; apply hab
        rw [map_add]
        simp only [h₂',hz,zero_pow (by decide : 2 ≠ 0),mul_zero] at e₁ e₂
        linear_combination -e₁ - e₂
      obtain ⟨Z₁,hZ₁⟩ := lift_weighted (-a) u h₂ hu z₁ h₁ (by
        simp only [map_neg]; simp only [h₂',zero_pow (by decide : 2 ≠ 0),mul_zero] at e₁
        linear_combination -e₁)
      obtain ⟨Z₃,hZ₃⟩ := lift_weighted (-(a + b)) w h₂ hw z₃ h₃ (by
        simp only [map_neg,map_add]
        simp only [h₂',zero_pow (by decide : 2 ≠ 0),mul_zero] at e₁
        linear_combination -e₁ - e₂)
      refine ⟨Z₁,0,Z₃,?_,?_⟩
      · simp only [zero_pow (by decide : 2 ≠ 0),mul_zero]; linear_combination -hZ₁
      · linear_combination hZ₁ - hZ₃
    · let Z₃ : ℤ_[p] := (z₃.val : ℤ_[p])
      have hZ₃ : red Z₃ = z₃ := by simp [Z₃]
      obtain ⟨Z₁,hZ₁⟩ := lift_weighted (w * Z₃ ^ 2 + b) u h₂ hu z₁ h₁ (by
        simp only [map_add,map_mul,map_pow,hZ₃]; linear_combination e₂)
      obtain ⟨Z₂,hZ₂⟩ := lift_weighted (w * Z₃ ^ 2 + b + a) v h₂ hv z₂ h₂' (by
        simp only [map_add,map_mul,map_pow,hZ₃]; linear_combination e₁ + e₂)
      refine ⟨Z₁,Z₂,Z₃,?_,?_⟩
      · linear_combination hZ₂ - hZ₁
      · linear_combination hZ₁

private theorem representative_of_pattern (d u v : ℤ_[p]) (U V : ℚ_[p]ˣ)
    (hU : (U : ℚ_[p]) = (u : ℚ_[p])) (hV : (V : ℚ_[p]) = (v : ℚ_[p]))
    (h₂ : (2 : ZMod p) ≠ 0) (hF : ringChar (ZMod p) ≠ 2)
    (ha : red (5 * d) ≠ 0) (hb : red (15 * d) ≠ 0) (hab : red (20 * d) ≠ 0)
    (hu : red u ≠ 0) (hv : red v ≠ 0)
    (hprod : quadraticChar (ZMod p) (red u) * quadraticChar (ZMod p) (red v) * 
      quadraticChar (ZMod p) (red (u * v)) = 1)
    (hsum : quadraticChar (ZMod p) (red u) * quadraticChar (ZMod p) (red v) + 
      quadraticChar (ZMod p) (red u) * quadraticChar (ZMod p) (red (u * v)) + 
      quadraticChar (ZMod p) (red v) * quadraticChar (ZMod p) (red (u * v)) = -1) :
    Nonempty (FieldKummer.CoveringRep (d : ℚ_[p]) U V) := by
  have huv : red (u * v) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hu hv
  have hab' : red (5 * d) + red (15 * d) ≠ 0 := by
    rw [← map_add, show 5 * d + 15 * d = 20 * d by ring]; exact hab
  obtain ⟨z₁,z₂,z₃,e₁,e₂⟩ := residue_common hF (red (5 * d)) (red (15 * d))
    (red u) (red v) (red (u * v)) ha hb hab' hu hv huv hprod hsum
  obtain ⟨Z₁,Z₂,Z₃,E₁,E₂⟩ := lift_common (5 * d) (15 * d) u v (u * v) h₂ ha hb
    (by rwa [show 5 * d + 15 * d = 20 * d by ring]) hu hv huv z₁ z₂ z₃ e₁ e₂
  let c : FieldKummer.CoveringRep (d : ℚ_[p]) U V := {
    t := 1, z₁ := Z₁, z₂ := Z₂, z₃ := Z₃
    nonzero := Or.inl one_ne_zero
    eq₁₂ := by
      simp only [hU,hV,one_pow,mul_one]
      simpa only [map_sub,map_mul,map_pow,map_ofNat,PadicInt.algebraMap_apply] using
        congrArg (algebraMap ℤ_[p] ℚ_[p]) E₁
    eq₁₃ := by
      simp only [hU,hV,one_pow,mul_one]
      simpa only [map_sub,map_mul,map_pow,map_ofNat,PadicInt.algebraMap_apply] using
        congrArg (algebraMap ℤ_[p] ℚ_[p]) E₂ }
  exact ⟨c⟩

end Lifting

instance primeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩

/-- The two homogeneous quadratic observations for the first ordered class. -/
noncomputable def lambdaQuadrics (p : Nat.Primes) (q : ℕ) (Z : Fin 4 → ℚ_[p]) : ℚ_[p] × ℚ_[p] :=
  (Z 2 ^ 2 - (q : ℚ_[p]) * Z 1 ^ 2,
    (q : ℚ_[p]) * Z 1 ^ 2 - (q : ℚ_[p]) * Z 3 ^ 2)

/-- The two homogeneous quadratic observations for the second ordered class. -/
noncomputable def muQuadrics (p : Nat.Primes) (q : ℕ) (Z : Fin 4 → ℚ_[p]) : ℚ_[p] × ℚ_[p] :=
  ((q : ℚ_[p]) * Z 2 ^ 2 - Z 1 ^ 2,
    Z 1 ^ 2 - (q : ℚ_[p]) * Z 3 ^ 2)

/-- Simultaneous homogeneous quadruples for both original ordered coverings at every good prime. -/
theorem good_prime_common_tuples (p : Nat.Primes) (q r : ℕ)
    (hp : ¬ (p : ℕ) ∣ 30 * q * r) :
    ∃ (L M : Fin 4 → ℚ_[p]),
      (L 0 ≠ 0 ∨ L 1 ≠ 0 ∨ L 2 ≠ 0 ∨ L 3 ≠ 0) ∧
      (M 0 ≠ 0 ∨ M 1 ≠ 0 ∨ M 2 ≠ 0 ∨ M 3 ≠ 0) ∧
      lambdaQuadrics p q L =
        (5 * ((q : ℚ_[p]) * (r : ℚ_[p])) * L 0 ^ 2,
          15 * ((q : ℚ_[p]) * (r : ℚ_[p])) * L 0 ^ 2) ∧
      muQuadrics p q M =
        (5 * ((q : ℚ_[p]) * (r : ℚ_[p])) * M 0 ^ 2,
          15 * ((q : ℚ_[p]) * (r : ℚ_[p])) * M 0 ^ 2) := by
  classical
  have hq₀ : q ≠ 0 := by
    intro h
    apply hp
    simp [h]
  let qK : ℚ_[p]ˣ := Units.mk0 (q : ℚ_[p]) (Nat.cast_ne_zero.mpr hq₀)
  have hqK : (qK : ℚ_[p]) = (q : ℚ_[p]) := rfl
  have H : Nonempty (FieldKummer.CoveringRep ((q : ℚ_[p]) * (r : ℚ_[p])) qK 1) ∧
      Nonempty (FieldKummer.CoveringRep ((q : ℚ_[p]) * (r : ℚ_[p])) 1 qK) := by
    let red := (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
    let d : ℤ_[p] := (q : ℤ_[p]) * (r : ℤ_[p])
    have hg : ((30 * q * r : ℕ) : ZMod p) ≠ 0 := by
      intro h
      exact hp ((CharP.cast_eq_zero_iff (ZMod p) p (30 * q * r)).mp h)
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hg
    obtain ⟨h30q,hr⟩ := mul_ne_zero_iff.mp hg
    obtain ⟨h30,hq⟩ := mul_ne_zero_iff.mp h30q
    have h₂ : (2 : ZMod p) ≠ 0 := by intro h; apply h30; linear_combination 15 * h
    have h₃ : (3 : ZMod p) ≠ 0 := by intro h; apply h30; linear_combination 10 * h
    have h₅ : (5 : ZMod p) ≠ 0 := by intro h; apply h30; linear_combination 6 * h
    have hF : ringChar (ZMod p) ≠ 2 := by
      intro h
      have hp₂ : (p : ℕ) = 2 := by simpa only [ZMod.ringChar_zmod_n] using h
      exact h₂ ((congrArg (fun n : ℕ => (n : ZMod p)) hp₂).symm.trans (ZMod.natCast_self p))
    have hd : red d ≠ 0 := by simpa [red,d] using mul_ne_zero hq hr
    have ha : red (5 * d) ≠ 0 := by simpa only [map_mul,map_ofNat] using mul_ne_zero h₅ hd
    have hb : red (15 * d) ≠ 0 := by
      have h15 : (15 : ZMod p) ≠ 0 := by
        rw [show (15 : ZMod p) = 3 * 5 by norm_num]; exact mul_ne_zero h₃ h₅
      simpa only [map_mul,map_ofNat] using mul_ne_zero h15 hd
    have hab : red (20 * d) ≠ 0 := by
      have h20 : (20 : ZMod p) ≠ 0 := by
        rw [show (20 : ZMod p) = 2 * 2 * 5 by norm_num]
        exact mul_ne_zero (mul_ne_zero h₂ h₂) h₅
      simpa only [map_mul,map_ofNat] using mul_ne_zero h20 hd
    rcases quadraticChar_dichotomy hq with hs | hn
    · obtain ⟨z,hz⟩ := (quadraticChar_one_iff_isSquare hq).mp hs
      have hz₀ : z ≠ 0 := by intro h; apply hq; simpa [h] using hz
      obtain ⟨Z,hZ⟩ := lift_weighted (q : ℤ_[p]) 1 h₂ (by simp) z hz₀ (by
        simp only [map_one,one_mul,map_natCast]; simpa [pow_two] using hz.symm)
      have hZ' : (Z : ℚ_[p]) ^ 2 = (q : ℚ_[p]) := by
        have hh : Z ^ 2 = (q : ℤ_[p]) := by simpa using hZ
        simpa only [map_pow,map_natCast,PadicInt.algebraMap_apply] using
          congrArg (algebraMap ℤ_[p] ℚ_[p]) hh
      constructor
      · let c : FieldKummer.CoveringRep ((q : ℚ_[p]) * (r : ℚ_[p])) qK 1 := {
          t := 0, z₁ := 1, z₂ := Z, z₃ := 1
          nonzero := Or.inr (Or.inl one_ne_zero)
          eq₁₂ := by simp [hqK,hZ']
          eq₁₃ := by simp [hqK] }
        exact ⟨c⟩
      · let c : FieldKummer.CoveringRep ((q : ℚ_[p]) * (r : ℚ_[p])) 1 qK := {
          t := 0, z₁ := Z, z₂ := 1, z₃ := 1
          nonzero := Or.inr (Or.inr (Or.inl one_ne_zero))
          eq₁₂ := by simp [hqK,hZ']
          eq₁₃ := by simp [hqK,hZ'] }
        exact ⟨c⟩
    · have hq' : red (q : ℤ_[p]) ≠ 0 := by simpa [red] using hq
      constructor
      · simpa only [d,PadicInt.coe_mul,PadicInt.coe_natCast] using
          representative_of_pattern d (q : ℤ_[p]) 1 qK 1 hqK (by simp) h₂ hF ha hb hab hq'
            (by simp) (by simp only [mul_one,one_mul,map_one,map_natCast,hn]; norm_num) (by simp only [mul_one,one_mul,map_one,map_natCast,hn]; norm_num)
      · simpa only [d,PadicInt.coe_mul,PadicInt.coe_natCast] using
          representative_of_pattern d 1 (q : ℤ_[p]) 1 qK (by simp) hqK h₂ hF ha hb hab
            (by simp) hq' (by simp only [mul_one,one_mul,map_one,map_natCast,hn]; norm_num) (by simp only [mul_one,one_mul,map_one,map_natCast,hn]; norm_num)
  obtain ⟨⟨l⟩,⟨m⟩⟩ := H
  refine ⟨![l.t,l.z₁,l.z₂,l.z₃],![m.t,m.z₁,m.z₂,m.z₃],l.nonzero,m.nonzero,?_,?_⟩
  · apply Prod.ext
    · simpa [hqK,lambdaQuadrics] using l.eq₁₂
    · simpa [hqK,lambdaQuadrics] using l.eq₁₃
  · apply Prod.ext
    · simpa [hqK,muQuadrics] using m.eq₁₂
    · simpa [hqK,muQuadrics] using m.eq₁₃

end D5.S3.Factorization.Mordell.GoodPrimeCoverings
