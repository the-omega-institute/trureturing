/- GID: D5/S3/Quantum/AURICOmega/ReflectedDisplacementRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/ReflectedDisplacementRefutation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/AURICOmega/ReflectedDisplacementRefutation.claim; result=D5/S3/Quantum/AURICOmega/ReflectedDisplacementRefutation.result; claim=D5/S3/Quantum/AURICOmega/ReflectedDisplacementRefutation.claim
   digest: At sharp reading contrast the reflected displacement can have square fidelity below one. -/

import OmegaBuild.Commands
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open QuadraticAlgebra

namespace D5.S3.Quantum.AURICOmega.ReflectedDisplacementRefutation

/- The two real embeddings of R both send D to positive numbers. The second
   quadratic algebra has generator J with J² = -D. -/
private abbrev R := QuadraticAlgebra ℚ 545 0
private abbrev q (a : ℚ) : R := QuadraticAlgebra.C a
private def D : R := ⟨305 / 578, 1 / 578⟩
private abbrev S := QuadraticAlgebra R (-D) 0
private abbrev G := unitary S

private def a₀ : S := ⟨⟨209 / 674, -1 / 674⟩, ⟨883 / 674, -1 / 674⟩⟩
private def b₀ : S := ⟨⟨-1429 / 1766, -1 / 1766⟩, ⟨5729 / 7064, -17 / 7064⟩⟩

private def a : G := ⟨a₀, by
  rw [Unitary.mem_iff_self_mul_star]
  decide +kernel⟩

private def b : G := ⟨b₀, by
  rw [Unitary.mem_iff_self_mul_star]
  decide +kernel⟩

/- The fourth-power reading is the Chebyshev polynomial T₄ of the first.
   Choose L and C₀ so their weighted sum has a double zero at c. -/
private def c : R := (a₀ * b₀).re
private def T (u : R) : R := 8 * u ^ 4 - 8 * u ^ 2 + 1
private def L : R := -16 * c * (2 * c ^ 2 - 1)
private def C₀ : R := -(L * c + T c)
private def N : ℚ := (C₀ + L + 1).re

private def raw (h : G) : R :=
  C₀ + L * (h : S).re + ((h : S) ^ 4).re

private def k (x y : G) : ℚ := (raw (x⁻¹ * y)).re / N

private theorem norm_pos : 0 < N := by decide +kernel

private noncomputable def e (s : ℝ) (hs : s ^ 2 = 545) : R →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨s, by simpa [pow_two] using hs⟩

private theorem e_apply (s : ℝ) (hs : s ^ 2 = 545) (x : R) :
    e s hs x = (x.re : ℝ) + (x.im : ℝ) * s := by
  simp [e, Algebra.smul_def, mul_comm]

private theorem re_nonneg (x : R)
    (hx : ∀ (s : ℝ) (hs : s ^ 2 = 545), 0 ≤ e s hs x) :
    0 ≤ x.re := by
  let s := Real.sqrt 545
  have hs : s ^ 2 = 545 := Real.sq_sqrt (by norm_num)
  have hn : (-s) ^ 2 = 545 := by simpa using hs
  have hp := hx s hs
  have hm := hx (-s) hn
  rw [e_apply] at hp hm
  exact_mod_cast (show (0 : ℝ) ≤ (x.re : ℝ) by linarith)

private theorem s_bounds {s : ℝ} (hs : s ^ 2 = 545) :
    -24 < s ∧ s < 24 := by
  constructor <;> by_contra! h <;> nlinarith [sq_nonneg (s + 24), sq_nonneg (s - 24)]

private theorem eD (s : ℝ) (hs : s ^ 2 = 545) : 0 < e s hs D := by
  have ⟨hl, _⟩ := s_bounds hs
  rw [e_apply]
  change 0 < ((305 / 578 : ℚ) : ℝ) + ((1 / 578 : ℚ) : ℝ) * s
  norm_num
  linarith

private theorem ec (s : ℝ) (hs : s ^ 2 = 545) : e s hs c < -(3 / 4) := by
  have ⟨_, hu⟩ := s_bounds hs
  rw [e_apply]
  have hc : c = ⟨-240449 / 297571, 441 / 297571⟩ := by decide +kernel
  rw [hc]
  change ((-240449 / 297571 : ℚ) : ℝ) + ((441 / 297571 : ℚ) : ℝ) * s < -(3 / 4 : ℝ)
  norm_num
  linarith

private theorem eL (s : ℝ) (hs : s ^ 2 = 545) : 0 ≤ e s hs L := by
  have hc := ec s hs
  have hc2 : 0 ≤ 2 * (e s hs c) ^ 2 - 1 := by
    nlinarith [sq_nonneg (e s hs c + 3 / 4)]
  simp only [L, map_mul, map_neg, map_ofNat, map_sub, map_pow, map_one]
  exact mul_nonneg (by linarith) hc2

private theorem eC (s : ℝ) (hs : s ^ 2 = 545) : 0 ≤ e s hs C₀ := by
  have hc := ec s hs
  have hc2 : 0 ≤ 2 * (e s hs c) ^ 2 - 1 := by
    nlinarith [sq_nonneg (e s hs c + 3 / 4)]
  simp only [C₀, L, T, map_mul, map_neg, map_ofNat, map_sub, map_pow, map_one, map_add]
  have h : 0 ≤ (2 * (e s hs c) ^ 2 - 1) * (12 * (e s hs c) ^ 2 + 1) :=
    mul_nonneg hc2 (by positivity)
  nlinarith only [h, sq_nonneg (e s hs c)]

private theorem fourth_reading (h : G) : ((h : S) ^ 4).re = T (h : S).re := by
  have hn := congrArg QuadraticAlgebra.re (Unitary.mem_iff_self_mul_star.mp h.property)
  simp only [re_mul, re_star, zero_mul, add_zero, im_star, re_one] at hn
  simp only [pow_succ, pow_zero, one_mul, re_mul, im_mul, zero_mul, add_zero, T]
  linear_combination (-7 * (h : S).re ^ 2 + D * (h : S).im ^ 2 + 1) * hn

private theorem raw_nonneg (h : G) : 0 ≤ (raw h).re := by
  apply re_nonneg
  intro s hs
  have hc := ec s hs
  have hc2 : 0 ≤ 2 * (e s hs c) ^ 2 - 1 := by
    nlinarith [sq_nonneg (e s hs c + 3 / 4)]
  rw [raw, fourth_reading]
  simp only [C₀, L, T, map_mul, map_neg, map_ofNat, map_sub, map_pow, map_one, map_add]
  let u := e s hs (h : S).re
  let v := e s hs c
  change 0 ≤ -(-16 * v * (2 * v ^ 2 - 1) * v + (8 * v ^ 4 - 8 * v ^ 2 + 1)) +
    -16 * v * (2 * v ^ 2 - 1) * u + (8 * u ^ 4 - 8 * u ^ 2 + 1)
  calc
    0 ≤ 8 * (u - v) ^ 2 * ((u + v) ^ 2 + (2 * v ^ 2 - 1)) := by positivity
    _ = _ := by ring

private theorem inv_val (x : G) : (↑x⁻¹ : S) = star (x : S) := rfl

private theorem k_symm (x y : G) : k x y = k y x := by
  have hinv : y⁻¹ * x = (x⁻¹ * y)⁻¹ := by group
  rw [k, k, hinv, raw, raw, fourth_reading, fourth_reading]
  simp only [inv_val, QuadraticAlgebra.re_star, zero_mul, add_zero]

private theorem k_diag (x : G) : k x x = 1 := by
  simpa [k, raw, N] using div_self (ne_of_gt norm_pos)

private theorem k_left (g x y : G) : k (g * x) (g * y) = k x y := by
  unfold k
  congr 2
  group

private theorem k_right (g x y : G) : k (x * g) (y * g) = k x y := by
  simpa [mul_comm] using k_left g x y

private theorem re_inv_mul (x y : G) :
    ((↑(x⁻¹ * y) : S)).re =
      (x : S).re * (y : S).re + D * (x : S).im * (y : S).im := by
  simp [inv_val, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, mul_assoc]

private theorem pair_power (x y : G) :
    (↑(x⁻¹ * y) : S) ^ 4 = (↑((x ^ 4)⁻¹ * (y ^ 4)) : S) := by
  simpa only [SubmonoidClass.coe_pow] using congrArg (fun g : G => (g : S))
    (show (x⁻¹ * y) ^ 4 = (x ^ 4)⁻¹ * (y ^ 4) by rw [mul_pow, inv_pow])

private theorem k_gram (n : ℕ) (x : Fin n → G) (w : Fin n → ℚ) :
    0 ≤ ∑ i, ∑ j, w i * w j * k (x i) (x j) := by
  simp only [k, ← mul_div_assoc, ← Finset.sum_div]
  apply div_nonneg _ norm_pos.le
  let energy : R := ∑ i, ∑ j, q (w i * w j) * raw ((x i)⁻¹ * x j)
  have he : energy.re = ∑ i, ∑ j, w i * w j * (raw ((x i)⁻¹ * x j)).re := by
    simp only [energy, ← reₗ_apply, map_sum]
    congr 1
    funext i
    congr 1
    funext j
    change (q (w i * w j) * raw ((x i)⁻¹ * x j)).re =
      w i * w j * (raw ((x i)⁻¹ * x j)).re
    simp only [re_mul, re_C, im_C, mul_zero, zero_mul, add_zero]
  rw [← he]
  apply re_nonneg
  intro s hs
  let E := e s hs
  let r (g : G) : ℝ := E (g : S).re
  let m (g : G) : ℝ := E (g : S).im
  have hq (v : ℚ) : E (q v) = (v : ℝ) := E.commutes v
  have hE :
      E energy = E C₀ * (∑ i, (w i : ℝ)) ^ 2 +
        E L * ((∑ i, (w i : ℝ) * r (x i)) ^ 2 +
          E D * (∑ i, (w i : ℝ) * m (x i)) ^ 2) +
        (∑ i, (w i : ℝ) * r (x i ^ 4)) ^ 2 +
          E D * (∑ i, (w i : ℝ) * m (x i ^ 4)) ^ 2 := by
    simp only [energy, raw, pair_power, re_inv_mul, map_sum, map_mul, map_add, hq,
      Rat.cast_mul, r, m]
    simp only [pow_two, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change 0 ≤ E energy
  rw [hE]
  have hd : 0 ≤ E D := (eD s hs).le
  have hl : 0 ≤ E L := eL s hs
  have hc : 0 ≤ E C₀ := eC s hs
  positivity

/-- The claim that every interior extremizer has reflected displacement whose
square has unit fidelity. Gram positivity is tested on all finite rational samples. -/
def claim : Prop :=
  ∀ {H : Type} [Group H] (k : H → H → ℚ),
    (∀ x y, k x y = k y x) →
    (∀ x, k x x = 1) →
    (∀ x y, 0 ≤ k x y) →
    (∀ g x y, k (g * x) (g * y) = k x y) →
    (∀ g x y, k (x * g) (y * g) = k x y) →
    (∀ (n : ℕ) (x : Fin n → H) (w : Fin n → ℚ), 0 ≤ ∑ i, ∑ j, w i * w j * k (x i) (x j)) →
    ∀ x y z : H, 0 < k x y → k x y < 1 →
      (k x z - k y z) ^ 2 = 1 - k x y →
      k 1 ((z⁻¹ * (x * z⁻¹ * y)) ^ 2) = 1

/-- A rational kernel on the unitary group of a quadratic algebra refutes the
claim, at overlap 272/441 and signed contrast 13/21. -/
theorem result : ¬ claim := by
  intro h
  have ht : k a b = 272 / 441 := by decide +kernel
  have hd : k a 1 - k b 1 = 13 / 21 := by decide +kernel
  have hsq : k 1 ((a * b) ^ 2) < 1 := by decide +kernel
  have hs := h k k_symm k_diag (fun x y => div_nonneg (raw_nonneg _) norm_pos.le)
    k_left k_right k_gram a b 1 (by rw [ht]; norm_num) (by rw [ht]; norm_num)
    (by rw [ht, hd]; norm_num)
  exact hsq.ne (by simpa using hs)

end D5.S3.Quantum.AURICOmega.ReflectedDisplacementRefutation
