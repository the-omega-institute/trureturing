/- GID: D5/S3/Arith/FibonacciAtomic/PrimitiveCoreDepthDeficit
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/PrimitiveCoreDepthDeficit
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Primitive compositions have unique exit cores and logarithmic depth bounds. -/

import D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling
import D5.S0.Carrier.Norm
import D5.S3.Axis.AxisConvergence
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.PrimitiveCoreDepthDeficit

open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity)
local notation "φ" => Real.goldenRatio

private theorem step_injective : Function.Injective (step (A := ℕ)) := by
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [step] at h₁ h₂
  exact Prod.ext (by omega) h₁

private theorem core_exists (x : ℕ × ℕ) (hx : x ≠ (0, 0)) :
    ∃ j : ℕ, ∃ c : ℕ × ℕ, c.2 < c.1 ∧ x = step^[j] c := by
  suffices h : ∀ n : ℕ, ∀ x : ℕ × ℕ, quantity x = n → x ≠ (0, 0) →
      ∃ j : ℕ, ∃ c : ℕ × ℕ, c.2 < c.1 ∧ x = step^[j] c from
    h (quantity x) x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hn hx
    by_cases hc : x.2 < x.1
    · exact ⟨0, x, hc, rfl⟩
    · have hle : x.1 ≤ x.2 := by omega
      let y : ℕ × ℕ := (x.2 - x.1, x.1)
      have hy : y ≠ (0, 0) := by
        intro hz
        have h₁ := congrArg Prod.fst hz
        have h₂ := congrArg Prod.snd hz
        dsimp [y] at h₁ h₂
        apply hx
        exact Prod.ext h₂ (by omega)
      have hdec : quantity y < n := by
        dsimp [quantity, y] at hn ⊢
        have hnonzero : 0 < x.1 + x.2 := by
          by_contra hz
          apply hx
          exact Prod.ext (by omega) (by omega)
        omega
      obtain ⟨j, c, hcore, hrep⟩ := ih (quantity y) hdec y rfl hy
      refine ⟨j + 1, c, hcore, ?_⟩
      rw [Function.iterate_succ_apply', ← hrep]
      dsimp [step, y]
      exact Prod.ext rfl (by omega)

private theorem core_unique (j k : ℕ) (c d : ℕ × ℕ)
    (hc : c.2 < c.1) (hd : d.2 < d.1)
    (heq : step^[j] c = step^[k] d) : j = k ∧ c = d := by
  have ordered (j k : ℕ) (c d : ℕ × ℕ) (hc : c.2 < c.1)
      (hjk : j ≤ k) (heq : step^[j] c = step^[k] d) : j = k ∧ c = d := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
    rw [Function.iterate_add_apply] at heq
    have hcancel := (step_injective.iterate j) heq
    cases m with
    | zero => exact ⟨by omega, by simpa using hcancel⟩
    | succ m =>
      rw [Function.iterate_succ_apply'] at hcancel
      have h₁ := congrArg Prod.fst hcancel
      have h₂ := congrArg Prod.snd hcancel
      simp only [step] at h₁ h₂
      omega
  rcases le_total j k with h | h
  · exact ordered j k c d hc h heq
  · have h' := ordered k j d c hd h heq.symm
    exact ⟨h'.1.symm, h'.2.symm⟩

private theorem gcd_iterate (j : ℕ) (c : ℕ × ℕ) :
    Nat.gcd (step^[j] c).1 (step^[j] c).2 = Nat.gcd c.1 c.2 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simpa only [step, Nat.gcd_add_self_right, Nat.gcd_comm] using ih

private theorem norm_iterate (j : ℕ) (c : ℕ × ℕ) :
    |D5.S0.Carrier.norm ⟨((step^[j] c).1 : ℤ), ((step^[j] c).2 : ℤ)⟩| =
      |D5.S0.Carrier.norm ⟨(c.1 : ℤ), (c.2 : ℤ)⟩| := by
  have one_step (x : ℕ × ℕ) :
      D5.S0.Carrier.norm ⟨((step x).1 : ℤ), ((step x).2 : ℤ)⟩ =
        -D5.S0.Carrier.norm ⟨(x.1 : ℤ), (x.2 : ℤ)⟩ := by
    have h : (⟨((step x).1 : ℤ), ((step x).2 : ℤ)⟩ : D5.S0.Carrier.GoldenInt) =
        D5.S0.Carrier.phi * ⟨(x.1 : ℤ), (x.2 : ℤ)⟩ := by
      ext <;> simp [step, Nat.cast_add]
    rw [h, D5.S0.Carrier.norm_mul, D5.S0.Carrier.norm_phi]
    ring
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', one_step, abs_neg, ih]

private theorem quantity_bounds (j : ℕ) (c : ℕ × ℕ) (hc : c.2 < c.1) :
    (c.1 : ℝ) * φ ^ (j + 1) ≤ ((quantity (step^[j] c) : ℕ) : ℝ) ∧
      ((quantity (step^[j] c) : ℕ) : ℝ) ≤ (c.1 : ℝ) * φ ^ (j + 4) := by
  have fib_bounds (n : ℕ) :
      φ ^ n ≤ (Nat.fib (n + 2) : ℝ) ∧ (Nat.fib (n + 2) : ℝ) ≤ φ ^ (n + 1) := by
    have hrec : (Nat.fib (n + 2) : ℝ) = (Nat.fib n : ℝ) + Nat.fib (n + 1) := by
      exact_mod_cast Nat.fib_add_two (n := n)
    have h₁ := Real.goldenRatio_mul_fib_succ_add_fib n
    constructor
    · have h := D5.S3.Axis.AxisConvergence.goldenRatio_pow_div_le_fib_succ (n + 1)
      simpa only [Nat.add_assoc, pow_succ,
        mul_div_cancel_right₀ _ Real.goldenRatio_pos.ne'] using h
    · nlinarith [Real.one_lt_goldenRatio, Nat.cast_nonneg (α := ℝ) (Nat.fib (n + 1))]
  have hq := D5.S3.Arith.FibonacciAtomic.GlobalGcdSampling.actual_source_value j c
  have hs : (c.2 : ℝ) ≤ c.1 := by exact_mod_cast hc.le
  have hlo := (fib_bounds (j + 1)).1
  have hhi := (fib_bounds (j + 3)).2
  have hsum : (Nat.fib (j + 3) : ℝ) + Nat.fib (j + 4) = Nat.fib (j + 5) := by
    exact_mod_cast (Nat.fib_add_two (n := j + 3)).symm
  have hqR : ((quantity (step^[j] c) : ℕ) : ℝ) =
      (c.1 : ℝ) * Nat.fib (j + 3) + (c.2 : ℝ) * Nat.fib (j + 4) := by
    simpa only [Nat.cast_add, Nat.cast_mul, mul_comm] using
      congrArg (Nat.cast : ℕ → ℝ) hq
  norm_num only [Nat.add_assoc] at hlo hhi
  constructor
  · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) c.2)
      (Nat.cast_nonneg (α := ℝ) (Nat.fib (j + 4))),
      mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (α := ℝ) c.1)]
  · nlinarith [mul_le_mul_of_nonneg_left hhi (Nat.cast_nonneg (α := ℝ) c.1),
      mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α := ℝ) (Nat.fib (j + 4)))]

private theorem logarithmic_bounds (j : ℕ) (r U D : ℝ) (hr : 0 < r)
    (hsize : r ^ 2 ≤ D ∧ D ≤ (5 / 4 : ℝ) * r ^ 2)
    (hqty : r * φ ^ (j + 1) ≤ U ∧ U ≤ r * φ ^ (j + 4)) :
    (Real.log D - Real.log (5 / 4)) / (2 * Real.log φ) + 1 ≤
        Real.log U / Real.log φ - j ∧
      Real.log U / Real.log φ - j ≤ Real.log D / (2 * Real.log φ) + 4 := by
  have hφ : 0 < φ := Real.goldenRatio_pos
  have hp : 0 < Real.log φ := Real.log_pos Real.one_lt_goldenRatio
  have hD : 0 < D := (sq_pos_of_pos hr).trans_le hsize.1
  have hU : 0 < U := (mul_pos hr (pow_pos hφ _)).trans_le hqty.1
  have hlogr₁ := Real.log_le_log (sq_pos_of_pos hr) hsize.1
  rw [Real.log_pow] at hlogr₁
  have hlogr₂ := Real.log_le_log hD hsize.2
  rw [Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) (pow_ne_zero 2 hr.ne'),
    Real.log_pow] at hlogr₂
  have hlogU₁ := Real.log_le_log (mul_pos hr (pow_pos hφ _)) hqty.1
  rw [Real.log_mul hr.ne' (pow_ne_zero _ hφ.ne'), Real.log_pow] at hlogU₁
  have hlogU₂ := Real.log_le_log hU hqty.2
  rw [Real.log_mul hr.ne' (pow_ne_zero _ hφ.ne'), Real.log_pow] at hlogU₂
  push_cast at hlogU₁ hlogU₂
  norm_num only [Nat.cast_ofNat] at hlogr₁ hlogr₂
  have hL : (Real.log U / Real.log φ - (j : ℝ)) * Real.log φ =
      Real.log U - (j : ℝ) * Real.log φ := by
    rw [sub_mul, div_mul_cancel₀ _ hp.ne']
  constructor
  · have h : (Real.log D - Real.log (5 / 4)) / (2 * Real.log φ) ≤
        Real.log U / Real.log φ - j - 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log φ)).mpr
      nlinarith
    linarith
  · have h : Real.log U / Real.log φ - j - 4 ≤
        Real.log D / (2 * Real.log φ) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log φ)).mpr
      nlinarith
    linarith

/-- Every nonzero primitive composition has exactly one exit core and depth.
Its absolute golden norm controls its logarithmic depth deficit. -/
theorem result (x : ℕ × ℕ) (hx : x ≠ (0, 0)) (hprimitive : Nat.gcd x.1 x.2 = 1) :
    let D : ℝ := |(D5.S0.Carrier.norm ⟨(x.1 : ℤ), (x.2 : ℤ)⟩ : ℝ)|
    ∃ j : ℕ, ∃ c : ℕ × ℕ,
      c.2 < c.1 ∧ x = step^[j] c ∧
      (∀ k : ℕ, ∀ d : ℕ × ℕ, d.2 < d.1 → x = step^[k] d → k = j ∧ d = c) ∧
      Nat.gcd c.1 c.2 = 1 ∧
      |D5.S0.Carrier.norm ⟨(x.1 : ℤ), (x.2 : ℤ)⟩| =
        (c.1 : ℤ) ^ 2 + (c.1 : ℤ) * c.2 - (c.2 : ℤ) ^ 2 ∧
      (Real.log D - Real.log (5 / 4)) / (2 * Real.log φ) + 1 ≤
        Real.log ((quantity x : ℕ) : ℝ) / Real.log φ - j ∧
      Real.log ((quantity x : ℕ) : ℝ) / Real.log φ - j ≤
        Real.log D / (2 * Real.log φ) + 4 := by
  dsimp only
  obtain ⟨j, c, hc, hrep⟩ := core_exists x hx
  have hr : 0 < (c.1 : ℝ) := by exact_mod_cast (show 0 < c.1 by omega)
  have hs : (0 : ℝ) ≤ c.2 := Nat.cast_nonneg _
  have hsr : (c.2 : ℝ) ≤ c.1 := by exact_mod_cast hc.le
  have hcoreZ : 0 ≤ D5.S0.Carrier.norm ⟨(c.1 : ℤ), (c.2 : ℤ)⟩ := by
    have hcz : (c.2 : ℤ) ≤ c.1 := by exact_mod_cast hc.le
    dsimp [D5.S0.Carrier.norm]
    nlinarith [Int.natCast_nonneg c.1, Int.natCast_nonneg c.2]
  have hnorm : |D5.S0.Carrier.norm ⟨(x.1 : ℤ), (x.2 : ℤ)⟩| =
      (c.1 : ℤ) ^ 2 + (c.1 : ℤ) * c.2 - (c.2 : ℤ) ^ 2 := by
    rw [hrep, norm_iterate, abs_of_nonneg hcoreZ]
    dsimp [D5.S0.Carrier.norm]
    ring
  have hnormR : |(D5.S0.Carrier.norm ⟨(x.1 : ℤ), (x.2 : ℤ)⟩ : ℝ)| =
      (c.1 : ℝ) ^ 2 + (c.1 : ℝ) * c.2 - (c.2 : ℝ) ^ 2 := by
    exact_mod_cast hnorm
  have hsize : (c.1 : ℝ) ^ 2 ≤
        |(D5.S0.Carrier.norm ⟨(x.1 : ℤ), (x.2 : ℤ)⟩ : ℝ)| ∧
      |(D5.S0.Carrier.norm ⟨(x.1 : ℤ), (x.2 : ℤ)⟩ : ℝ)| ≤
        (5 / 4 : ℝ) * (c.1 : ℝ) ^ 2 := by
    rw [hnormR]
    constructor
    · nlinarith [mul_nonneg hs (sub_nonneg.mpr hsr)]
    · nlinarith [sq_nonneg ((c.1 : ℝ) - 2 * c.2)]
  have hqty := quantity_bounds j c hc
  rw [← hrep] at hqty
  have hlogs := logarithmic_bounds j (c.1 : ℝ) ((quantity x : ℕ) : ℝ)
    |(D5.S0.Carrier.norm ⟨(x.1 : ℤ), (x.2 : ℤ)⟩ : ℝ)| hr hsize hqty
  refine ⟨j, c, hc, hrep, ?_, ?_, hnorm, hlogs⟩
  · intro k d hd hrep'
    exact core_unique k j d c hd hc (hrep'.symm.trans hrep)
  · rw [hrep, gcd_iterate] at hprimitive
    exact hprimitive

end D5.S3.Arith.FibonacciAtomic.PrimitiveCoreDepthDeficit
