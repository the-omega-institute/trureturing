/- GID: D5/S3/Combinatorics/SubsetSpectrum/DigitDiagonalCapacity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/DigitDiagonalCapacity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two bounded digits with a rational total weight cover at most one integer per diagonal block. -/


import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A counting bound for integer masses of bounded weighted digit pairs. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.SubsetSpectrum.DigitDiagonalCapacity

/-- The two signed-distance components of the diagonal and the quotient of its position. -/
def code {k : ℕ} (b : ℕ) (d : Fin (k+1) × Fin (k+1)) : ℕ × ℕ × ℕ :=
  (d.1.val - d.2.val, d.2.val - d.1.val, min d.1.val d.2.val / b)

/-- The integral levels covered by two finite digits inject into pairs of a diagonal and a
block of consecutive positions of length b along that diagonal. -/
theorem integral_range_le_diagonal_codes {k n b c : ℕ} (positive : 0 < b)
    (coprime : Nat.Coprime c b) (a z : ℝ) (sum : a + z = (c : ℝ) / b)
    (cover : ∀ t : Fin n, ∃ d : Fin (k+1) × Fin (k+1),
      (d.1.val : ℝ) * a + (d.2.val : ℝ) * z = t.val) :
    n ≤ (Finset.univ.image (code (k := k) b)).card := by
  classical
  choose digits mass using cover
  let tag (t : Fin n) : ↥(Finset.univ.image (code (k := k) b)) :=
    ⟨code b (digits t), Finset.mem_image_of_mem (code b) (Finset.mem_univ _)⟩
  have difference (d : Fin (k+1) × Fin (k+1)) (t : Fin n)
      (eq : (d.1.val : ℝ) * a + (d.2.val : ℝ) * z = t.val) :
      (d.1.val - d.2.val : ℕ) * a + (d.2.val - d.1.val : ℕ) * z +
        (min d.1.val d.2.val : ℕ) * ((c : ℝ) / b) = t.val := by
    have x : d.1.val = d.1.val - d.2.val + min d.1.val d.2.val :=
      (Nat.sub_add_min_cancel d.1.val d.2.val).symm
    have y : d.2.val = d.2.val - d.1.val + min d.1.val d.2.val := by
      simpa only [min_comm] using (Nat.sub_add_min_cancel d.2.val d.1.val).symm
    conv at eq =>
      lhs
      congr
      · lhs
        rw [x]
      · lhs
        rw [y]
    simp only [Nat.cast_add] at eq
    calc
      _ = (_ : ℝ) * a + (_ : ℝ) * z + (min d.1.val d.2.val : ℕ) * (a+z) := by rw [sum]
      _ = (↑(d.1.val - d.2.val) + ↑(min d.1.val d.2.val)) * a +
          (↑(d.2.val - d.1.val) + ↑(min d.1.val d.2.val)) * z := by ring
      _ = _ := eq
  have injective : Function.Injective tag := by
    intro t u equal
    have eq : code b (digits t) = code b (digits u) := congrArg Subtype.val equal
    have nx := congrArg Prod.fst eq
    have ny := congrArg (Prod.fst ∘ Prod.snd) eq
    have nd := congrArg (Prod.snd ∘ Prod.snd) eq
    simp only [code, Function.comp_apply] at nx ny nd
    have d₁ := difference (digits t) t (mass t)
    have d₂ := difference (digits u) u (mass u)
    rw [nx, ny] at d₁
    let x : ℕ := min (digits t).1.val (digits t).2.val
    let y : ℕ := min (digits u).1.val (digits u).2.val
    change x / b = y / b at nd
    have bpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast positive
    have cancellation : (b : ℝ) * ((c : ℝ) / b) = (c : ℝ) := by
      rw [mul_comm, div_mul_cancel₀ _ bpos.ne']
    have e : (x : ℝ) * ((c : ℝ) / b) + (u.val : ℝ) =
        (y : ℝ) * ((c : ℝ) / b) + (t.val : ℝ) := by
      dsimp [x,y]
      linarith only [d₁, d₂]
    have realEq : (c : ℝ) * (x : ℝ) + (b : ℝ) * (u.val : ℝ) =
        (c : ℝ) * (y : ℝ) + (b : ℝ) * (t.val : ℝ) := by
      linear_combination
        (b : ℝ) * e - ((x : ℝ) - (y : ℝ)) * cancellation
    have integerEq : c * x + b * u.val = c * y + b * t.val := by
      exact_mod_cast realEq
    have modEq : x ≡ y [MOD b] := by
      have modMul : c*x ≡ c*y [MOD b] := by
        change c * x % b = c * y % b

        have h := congrArg (· % b) integerEq
        simpa only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod] using h
      exact (Nat.ModEq.cancel_left_of_coprime coprime.symm modMul)
    have same : x = y := Nat.ext_div_modEq nd modEq
    rw [same] at integerEq
    have totals := Nat.add_left_cancel integerEq
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left positive totals).symm
  have card := Fintype.card_le_of_injective tag injective
  simpa only [Fintype.card_fin, Fintype.card_coe] using card

end D5.S3.Combinatorics.SubsetSpectrum.DigitDiagonalCapacity
