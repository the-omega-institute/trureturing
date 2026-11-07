/- GID: D5/S3/Arith/CharacterSums/PascadiSixWordFiber
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiSixWordFiber
   mirror-E: none(waiver:open-six-letter-return-count)
   anchors: []
   utility: none
   digest: Central six-letter returns have a gcd-periodic fixed-middle interval count. -/

import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

open Matrix
open scoped BigOperators Matrix

namespace D5.S3.Arith.CharacterSums

noncomputable section

variable {c : ℕ} [NeZero c]

/-- The transfer matrix used in the six-letter return-word problem. -/
def returnStep (x : ZMod c) : Matrix (Fin 2) (Fin 2) (ZMod c) :=
  !![x, -1; 1, 0]

/-- The six alternating letters in Pascadi's return-word count. -/
def sixReturnWord (a₁ a₂ h₁ h₂ h₃ h₄ h₅ h₆ : ZMod c) :
    Matrix (Fin 2) (Fin 2) (ZMod c) :=
  returnStep (a₁ * h₁) * returnStep (a₂ * h₂) *
    returnStep (a₁ * h₃) * returnStep (a₂ * h₄) *
    returnStep (a₁ * h₅) * returnStep (a₂ * h₆)

/-- A scalar central return in `SL₂` (the scalar is kept explicit because composite moduli
have central roots of unity beyond `±1`). -/
def scalarReturn (γ : ZMod c) : Matrix (Fin 2) (Fin 2) (ZMod c) :=
  !![γ, 0; 0, γ]

/-- The four-coordinate completion fiber after the two middle coordinates are fixed. -/
def completionFiber (a₁ a₂ γ h₂ h₃ h₅ h₆ : ZMod c) : Set (ZMod c × ZMod c) :=
  {p | (1 - a₁ * a₂ * h₂ * h₃) * p.1 = γ * h₅ - h₃ ∧
    (1 - a₁ * a₂ * h₂ * h₃) * p.2 = γ * h₆ - h₂}

/-- The fixed-middle compatibility equations forced by a central six-letter return.
The proof cancels only the assumed units `a₁` and `a₂`; it does not divide by the
possibly-zero gcd stratum `1-a₁a₂h₂h₃`. -/
theorem completion_equations_of_sixReturnWord
    (a₁ a₂ γ h₁ h₂ h₃ h₄ h₅ h₆ : ZMod c)
    (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂)
    (hγ : sixReturnWord a₁ a₂ h₁ h₂ h₃ h₄ h₅ h₆ = scalarReturn γ)
    (hγsq : γ * γ = 1) :
    let D := 1 - a₁ * a₂ * h₂ * h₃
    D = γ * (a₁ * a₂ * h₅ * h₆ - 1) ∧
      D * h₁ = γ * h₅ - h₃ ∧
      D * h₄ = γ * h₆ - h₂ := by
  dsimp
  let x₁ := a₁ * h₁
  let x₂ := a₂ * h₂
  let x₃ := a₁ * h₃
  let x₄ := a₂ * h₄
  let x₅ := a₁ * h₅
  let x₆ := a₂ * h₆
  let pairInv : Matrix (Fin 2) (Fin 2) (ZMod c) := !![-1, x₅; -x₆, x₅ * x₆ - 1]
  have hpair :
      (returnStep x₅ * returnStep x₆) * pairInv =
        (1 : Matrix (Fin 2) (Fin 2) (ZMod c)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [returnStep, pairInv, Matrix.mul_apply, Fin.sum_univ_two]
      <;> ring
  have hcancel :
      returnStep x₁ * returnStep x₂ * returnStep x₃ * returnStep x₄ =
        scalarReturn γ * pairInv := by
    have h := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) (ZMod c) => M * pairInv) hγ
    rw [show sixReturnWord a₁ a₂ h₁ h₂ h₃ h₄ h₅ h₆ =
        returnStep x₁ * returnStep x₂ * returnStep x₃ * returnStep x₄ *
          returnStep x₅ * returnStep x₆ by rfl] at h
    have h' :
        (returnStep x₁ * returnStep x₂ * returnStep x₃ * returnStep x₄) *
            (returnStep x₅ * returnStep x₆ * pairInv) =
          scalarReturn γ * pairInv := by
      simpa [mul_assoc] using h
    rw [hpair, Matrix.mul_one] at h'
    exact h'
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod c) => M 0 1) hcancel
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod c) => M 1 0) hcancel
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (ZMod c) => M 1 1) hcancel
  have h01' : a₁ * (-(γ * h₅) + h₁ - a₁ * a₂ * h₁ * h₂ * h₃ + h₃) = 0 := by
    have h := sub_eq_zero.mpr h01
    simp [returnStep, pairInv, scalarReturn, x₁, x₂, x₃, x₄, x₅, x₆,
      Matrix.mul_apply, Fin.sum_univ_two] at h
    ring_nf at h ⊢
    exact h
  have h10' : a₂ * (γ * h₆ + a₁ * a₂ * h₂ * h₃ * h₄ - h₂ - h₄) = 0 := by
    have h := sub_eq_zero.mpr h10
    simp [returnStep, pairInv, scalarReturn, x₁, x₂, x₃, x₄, x₅, x₆,
      Matrix.mul_apply, Fin.sum_univ_two] at h
    ring_nf at h ⊢
    exact h
  have h11' : -(γ * (a₁ * a₂ * h₅ * h₆ - 1)) +
      (1 - a₁ * a₂ * h₂ * h₃) = 0 := by
    have h := sub_eq_zero.mpr h11
    simp [returnStep, pairInv, scalarReturn, x₁, x₂, x₃, x₄, x₅, x₆,
      Matrix.mul_apply, Fin.sum_univ_two] at h
    ring_nf at h ⊢
    exact h
  have h01'' := ha₁.mul_left_cancel (show a₁ * _ = a₁ * 0 by simpa using h01')
  have h10'' := ha₂.mul_left_cancel (show a₂ * _ = a₂ * 0 by simpa using h10')
  refine ⟨?_, ?_, ?_⟩
  · apply sub_eq_zero.mp
    convert h11' using 1 <;> ring
  · apply sub_eq_zero.mp
    convert h01'' using 1 <;> ring
  · apply sub_eq_zero.mp
    have h10neg := congrArg (fun z : ZMod c => -z) h10''
    convert h10neg using 1 <;> ring

/-- Every two completions in the same fixed-middle fiber differ by the additive order of
its coefficient.  This is the gcd-periodic stratum behind the finite counting bound. -/
theorem completionFiber_period
    (a₁ a₂ γ h₂ h₃ h₅ h₆ : ZMod c)
    {p q : ZMod c × ZMod c}
    (hp : p ∈ completionFiber a₁ a₂ γ h₂ h₃ h₅ h₆)
    (hq : q ∈ completionFiber a₁ a₂ γ h₂ h₃ h₅ h₆) :
    ((c / Nat.gcd c (1 - a₁ * a₂ * h₂ * h₃).val : ℕ) : ℤ) ∣
        (p.1.val : ℤ) - q.1.val ∧
      ((c / Nat.gcd c (1 - a₁ * a₂ * h₂ * h₃).val : ℕ) : ℤ) ∣
        (p.2.val : ℤ) - q.2.val := by
  have hD : (1 - a₁ * a₂ * h₂ * h₃) =
      ((1 - a₁ * a₂ * h₂ * h₃).val : ZMod c) := by
    symm
    exact ZMod.natCast_zmod_val _
  have hperiod : addOrderOf (1 - a₁ * a₂ * h₂ * h₃) =
      c / Nat.gcd c (1 - a₁ * a₂ * h₂ * h₃).val := by
    rw [hD]
    simpa only [ZMod.natCast_zmod_val] using
      (ZMod.addOrderOf_coe (1 - a₁ * a₂ * h₂ * h₃).val (NeZero.ne c))
  have h₁eq :
      (1 - a₁ * a₂ * h₂ * h₃) * (p.1 - q.1) = 0 := by
    calc
      (1 - a₁ * a₂ * h₂ * h₃) * (p.1 - q.1) =
          (1 - a₁ * a₂ * h₂ * h₃) * p.1 -
            (1 - a₁ * a₂ * h₂ * h₃) * q.1 := by ring
      _ = 0 := sub_eq_zero.mpr (hp.1.trans hq.1.symm)
  have h₂eq :
      (1 - a₁ * a₂ * h₂ * h₃) * (p.2 - q.2) = 0 := by
    calc
      (1 - a₁ * a₂ * h₂ * h₃) * (p.2 - q.2) =
          (1 - a₁ * a₂ * h₂ * h₃) * p.2 -
            (1 - a₁ * a₂ * h₂ * h₃) * q.2 := by ring
      _ = 0 := sub_eq_zero.mpr (hp.2.trans hq.2.symm)
  have hz₁ : ((p.1.val : ℤ) - q.1.val) •
      (1 - a₁ * a₂ * h₂ * h₃) = 0 := by
    rw [zsmul_eq_mul']
    simpa [Int.cast_sub, ZMod.natCast_zmod_val, mul_comm] using h₁eq
  have hz₂ : ((p.2.val : ℤ) - q.2.val) •
      (1 - a₁ * a₂ * h₂ * h₃) = 0 := by
    rw [zsmul_eq_mul']
    simpa [Int.cast_sub, ZMod.natCast_zmod_val, mul_comm] using h₂eq
  have hd₁ := (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hz₁
  have hd₂ := (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hz₂
  exact ⟨by simpa only [hperiod] using hd₁, by simpa only [hperiod] using hd₂⟩

/-- For any natural interval length, actual central returns with four fixed coordinates
occupy at most one pair in each pair of quotient blocks of the gcd period.  No
invertibility of the completion coefficient is required. -/
theorem sixReturnWord_fixed_middle_count
    (a₁ a₂ γ h₂ h₃ h₅ h₆ : ZMod c)
    (ha₁ : IsUnit a₁) (ha₂ : IsUnit a₂) (hγsq : γ * γ = 1) (H : ℕ) :
    (((Finset.range H).product (Finset.range H)).filter fun p : ℕ × ℕ =>
      sixReturnWord a₁ a₂ (p.1 : ZMod c) h₂ h₃ (p.2 : ZMod c) h₅ h₆ =
        scalarReturn γ).card ≤
      (H / (c / Nat.gcd c (1 - a₁ * a₂ * h₂ * h₃).val) + 1) ^ 2 := by
  classical
  let N := c / Nat.gcd c (1 - a₁ * a₂ * h₂ * h₃).val
  let solutions := ((Finset.range H).product (Finset.range H)).filter fun p : ℕ × ℕ =>
    sixReturnWord a₁ a₂ (p.1 : ZMod c) h₂ h₃ (p.2 : ZMod c) h₅ h₆ = scalarReturn γ
  have hNc : N ∣ c := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hNpos : 0 < N := Nat.pos_of_dvd_of_pos hNc (NeZero.pos c)
  have quotient_lt {u : ℕ} (hu : u < H) : u / N < H / N + 1 :=
    (Nat.div_lt_iff_lt_mul hNpos).mpr
      (hu.trans (by simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ H hNpos)))
  have coordinate_eq {u v : ℕ}
      (hd : (N : ℤ) ∣ ((u : ZMod c).val : ℤ) - (v : ZMod c).val)
      (hquot : u / N = v / N) : u = v := by
    have hmod : Nat.ModEq N (u % c) (v % c) :=
      (Nat.modEq_of_dvd (by simpa only [ZMod.val_natCast] using hd)).symm
    exact Nat.ext_div_modEq hquot
      (((Nat.mod_modEq u c).of_dvd hNc).symm.trans
        (hmod.trans ((Nat.mod_modEq v c).of_dvd hNc)))
  have hcard : solutions.card ≤
      ((Finset.range (H / N + 1)).product (Finset.range (H / N + 1))).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.1 / N, p.2 / N))
    · intro p hp
      have hpH := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_product.mpr ⟨
        Finset.mem_range.mpr (quotient_lt (Finset.mem_range.mp hpH.1)),
        Finset.mem_range.mpr (quotient_lt (Finset.mem_range.mp hpH.2))⟩
    · intro p hp q hq hpq
      have hpword := (Finset.mem_filter.mp hp).2
      have hqword := (Finset.mem_filter.mp hq).2
      have hpcomp := completion_equations_of_sixReturnWord
        a₁ a₂ γ (p.1 : ZMod c) h₂ h₃ (p.2 : ZMod c) h₅ h₆ ha₁ ha₂ hpword hγsq
      have hqcomp := completion_equations_of_sixReturnWord
        a₁ a₂ γ (q.1 : ZMod c) h₂ h₃ (q.2 : ZMod c) h₅ h₆ ha₁ ha₂ hqword hγsq
      have hperiod := completionFiber_period a₁ a₂ γ h₂ h₃ h₅ h₆
        (p := ((p.1 : ZMod c), (p.2 : ZMod c)))
        (q := ((q.1 : ZMod c), (q.2 : ZMod c))) hpcomp.2 hqcomp.2
      exact Prod.ext
        (coordinate_eq hperiod.1 (congrArg Prod.fst hpq))
        (coordinate_eq hperiod.2 (congrArg Prod.snd hpq))
  simpa only [solutions, N, Finset.product_eq_sprod, Finset.card_product,
    Finset.card_range, pow_two] using hcard

end

end D5.S3.Arith.CharacterSums
