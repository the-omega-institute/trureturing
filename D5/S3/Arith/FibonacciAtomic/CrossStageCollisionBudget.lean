/- GID: D5/S3/Arith/FibonacciAtomic/CrossStageCollisionBudget
   generality: I
   mirror-B: none(waiver:stage-A-content)
   mirror-E: none(waiver:stage-A-content)
   anchors: []
   utility: none
   digest: Integer fibres, source exclusion and sharp cross-stage collision budgets. -/

import D5.S1.Scale.Fibonacci
import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum.NatFib

/-! Cross-stage integer collision budgets for the two-stage initial-composition model. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.CrossStageCollisionBudget

/-- Three substitution steps on integral compositions. -/
def S (x : ℤ × ℤ) : ℤ × ℤ := (x.1 + 2 * x.2, 2 * x.1 + 3 * x.2)
def A (ell : ℕ) : ℤ := Nat.fib (3 * ell + 3)
def B (ell : ℕ) : ℤ := Nat.fib (3 * ell + 4)
def v (ell : ℕ) : ℤ := B ell - A ell
def a (j : ℕ) : ℤ := (Nat.fib (3 * j + 1) : ℤ) - Nat.fib (3 * j)
def b (j : ℕ) : ℤ := Nat.fib (3 * j)
def N (j : ℕ) : ℤ := Nat.fib (3 * j + 1)
def advance (j : ℕ) (x : ℤ × ℤ) : ℤ × ℤ :=
  (a j * x.1 + b j * x.2, b j * x.1 + N j * x.2)
def stageRow (ell : ℕ) (x : ℤ × ℤ) : ℤ := A ell * x.1 + B ell * x.2
def sourceSize (x : ℤ × ℤ) : ℤ := x.1 + x.2
def Nonneg (x : ℤ × ℤ) : Prop := 0 ≤ x.1 ∧ 0 ≤ x.2
def Source (x : ℤ × ℤ) : Prop := Nonneg x ∧ 1 ≤ sourceSize x
def Domain (H : ℤ) (x : ℤ × ℤ) : Prop := Source x ∧ sourceSize x ≤ H
def r (k : ℕ) : ℚ := min ((a k : ℚ) / b k) ((b k : ℚ) / N k)
def R (k : ℕ) : ℚ := max ((a k : ℚ) / b k) ((b k : ℚ) / N k)
def Licensed (k : ℕ) (x : ℤ × ℤ) : Prop :=
  0 < x.2 ∧ r k * x.2 ≤ x.1 ∧ (x.1 : ℚ) ≤ R k * x.2
def fibrePoint (ell : ℕ) (c e z : ℤ) : ℤ × ℤ := (c + z * B ell, e - z * A ell)
def affineSum (ell : ℕ) (c e z : ℤ) : ℤ := sourceSize (fibrePoint ell c e z)
def tau (k ell d : ℕ) : ℤ :=
  ⌊((a d : ℚ) - r k * b d) / ((B ell : ℚ) + r k * A ell)⌋
def xMin (k ell d : ℕ) : ℤ × ℤ := fibrePoint ell (a d) (b d) (-tau k ell d)
def Collision (k ell d : ℕ) (x y : ℤ × ℤ) : Prop :=
  Source x ∧ Source y ∧ (Licensed k x ↔ ¬ Licensed k y) ∧
    stageRow ell x = stageRow (ell + d) y
def cost (x y : ℤ × ℤ) : ℤ := max (sourceSize x) (sourceSize y)
def J (k ell d : ℕ) : ℤ := if d ≤ k then N k else N d - tau k ell d * v ell

private theorem row_bounds (ell : ℕ) : 0 < A ell ∧ A ell < B ell ∧ B ell < 2 * A ell := by
  have hp : (0 : ℤ) < Nat.fib (3*ell+3) := by exact_mod_cast Nat.fib_pos.mpr (show 0 < 3*ell+3 by omega)
  have h₁ : (Nat.fib (3*ell+2) : ℤ) < Nat.fib (3*ell+3) := by
    exact_mod_cast Nat.fib_lt_fib_succ (show 2 ≤ 3*ell+2 by omega)
  have h₂ : (Nat.fib (3*ell+3) : ℤ) < Nat.fib (3*ell+4) := by
    exact_mod_cast Nat.fib_lt_fib_succ (show 2 ≤ 3*ell+3 by omega)
  have he : (Nat.fib (3*ell+4) : ℤ) = Nat.fib (3*ell+2) + (Nat.fib (3*ell+3) : ℤ) := by
    exact_mod_cast (@Nat.fib_add_two (3*ell+2))
  dsimp [A,B]
  exact ⟨hp,h₂, by omega⟩

private theorem abN (j : ℕ) : a j + b j = N j := by simp [a, b, N]
private theorem b_pos (j : ℕ) (hj : 1 ≤ j) : 0 < b j := by
  dsimp [b]
  exact_mod_cast Nat.fib_pos.mpr (show 0 < 3 * j by omega)
private theorem a_pos (j : ℕ) : 0 < a j := by
  by_cases hj : j = 0
  · subst j; norm_num [a]
  · have h := Nat.fib_lt_fib_succ (show 2 ≤ 3 * j by omega)
    dsimp [a]
    exact sub_pos.mpr (by exact_mod_cast h)
private theorem a_fib (j : ℕ) (hj : 1 ≤ j) : a j = Nat.fib (3 * j - 1) := by
  have h := @Nat.fib_add_two (3 * j - 1)
  rw [show 3 * j - 1 + 2 = 3 * j + 1 by omega,
    show 3 * j - 1 + 1 = 3 * j by omega] at h
  dsimp [a]
  have hh : (Nat.fib (3*j+1) : ℤ) = Nat.fib (3*j-1) + (Nat.fib (3*j) : ℤ) := by exact_mod_cast h
  linarith

private theorem row_advance (ell j : ℕ) (x : ℤ × ℤ) :
    stageRow ell (advance j x) = stageRow (ell + j) x := by
  have hB := Nat.fib_add (3 * ell + 3) (3 * j)
  have hA := Nat.fib_add (3 * ell + 2) (3 * j)
  have ht := @Nat.fib_add_two (3 * ell + 2)
  have hB' : B (ell + j) = A ell * b j + B ell * N j := by
    dsimp [A, B, b, N]
    convert (congrArg (fun n : ℕ => (n : ℤ)) hB) using 1 <;> push_cast <;> congr 2 <;> omega
  have hA' : A (ell + j) = A ell * a j + B ell * b j := by
    have ht' : B ell = (Nat.fib (3 * ell + 2) : ℤ) + A ell := by
      dsimp [A, B]
      rw [show 3 * ell + 4 = (3 * ell + 2) + 2 by omega, Nat.fib_add_two]
      push_cast
      rfl
    have hh : A (ell + j) = (Nat.fib (3 * ell + 2) : ℤ) * b j + A ell * N j := by
      dsimp [A, b, N]
      convert (congrArg (fun n : ℕ => (n : ℤ)) hA) using 1 <;> push_cast <;> congr 2 <;> omega
    rw [hh, ht']
    dsimp [a, b, N]
    ring
  dsimp [stageRow, advance]
  rw [hA', hB']
  ring

private theorem stage_row_fibre (ell : ℕ) (c e z : ℤ) :
    stageRow ell (fibrePoint ell c e z) = stageRow ell (c, e) := by
  dsimp [stageRow, fibrePoint]
  ring
private theorem affine_sum_formula (ell : ℕ) (c e z : ℤ) :
    affineSum ell c e z = c + e + z * v ell := by
  dsimp [affineSum, sourceSize, fibrePoint, v]
  ring

private theorem source_exclusion (ell d : ℕ) (hd : 1 ≤ d)
    (x y : ℤ × ℤ) (hx : Nonneg x) (hy : Source y) (hye : y ≠ (1, 0))
    (he : stageRow ell x = stageRow (ell + d) y) : N d < sourceSize x := by
  obtain ⟨hA, hAB, hBA⟩ := row_bounds ell
  obtain ⟨hA', hAB', hBA'⟩ := row_bounds (ell + d)
  have hb := b_pos d hd
  have hgap : B ell * N d < B (ell + d) := by
    have h := row_advance ell d (0, 1)
    dsimp [stageRow, advance] at h
    nlinarith
  have hread : B (ell + d) ≤ stageRow (ell + d) y := by
    by_cases hy₂ : y.2 = 0
    · have hy₁ : 2 ≤ y.1 := by
        have hh : y.1 ≠ 1 := fun h => hye (Prod.ext h hy₂)
        dsimp [Source, Nonneg, sourceSize] at hy
        omega
      dsimp [stageRow]
      rw [hy₂]
      nlinarith
    · have hp : 1 ≤ y.2 := by have := hy.1.2; omega
      have hn := hy.1.1
      dsimp [stageRow]
      nlinarith
  have hup : stageRow ell x ≤ B ell * sourceSize x := by
    dsimp [stageRow, sourceSize]
    nlinarith [hx.1]
  have hB : 0 < B ell := by omega
  nlinarith

open D5.S0.Carrier in
private theorem golden_coords (j : ℕ) : (⟨a j, b j⟩ : GoldenInt) = phi ^ (3 * j) := by
  by_cases hj : j = 0
  · subst j; simp [a, b]; rfl
  · rw [show 3 * j = (3 * j - 1) + 1 by omega,
      D5.S1.Scale.golden_phi_pow_eq_fib_pair]
    apply GoldenInt.ext
    · exact a_fib j (by omega)
    · simp only [b]; congr 2; omega

private theorem advance_add (i j : ℕ) (x : ℤ × ℤ) :
    advance (i + j) x = advance i (advance j x) := by
  have hh := congrArg (fun z : D5.S0.Carrier.GoldenInt => (z.a, z.b))
    ((golden_coords (i+j)).trans (by rw [Nat.mul_add, pow_add, ← golden_coords i, ← golden_coords j]))
  have ha : a (i+j) = a i * a j + b i * b j := congrArg Prod.fst hh
  have hb : b (i+j) = a i * b j + b i * a j + b i * b j := congrArg Prod.snd hh
  have hn := abN (i+j)
  dsimp [advance]
  rw [ha, hb, ← abN (i+j), ha, hb, ← abN i, ← abN j]
  ext <;> dsimp <;> ring

private theorem determinant (k : ℕ) : a k * N k - b k ^ 2 = 1 ∨
    a k * N k - b k ^ 2 = -1 := by
  have hh := D5.S0.Carrier.norm_phi_pow (3*k)
  rw [← golden_coords k] at hh
  dsimp [D5.S0.Carrier.norm] at hh
  have hp : ((-1 : ℤ) ^ (3*k)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm (3*k) 2, pow_mul]; norm_num
  have hn := abN k
  have heq : a k*N k-b k^2 = (-1 : ℤ)^(3*k) := by rw [← abN k]; nlinarith [hh]
  have he : (a k * N k - b k ^ 2) ^ 2 = 1 := by rw [heq]; exact hp
  rcases mul_self_eq_one_iff.mp (by nlinarith :
    (a k * N k - b k ^ 2) * (a k * N k - b k ^ 2) = 1) with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem ratio_pos (k : ℕ) (hk : 1 ≤ k) : 0 < r k ∧ 0 < R k := by
  have ha : (0 : ℚ) < a k := by exact_mod_cast a_pos k
  have hb : (0 : ℚ) < b k := by exact_mod_cast b_pos k hk
  have hn : (0 : ℚ) < N k := by
    have he : (a k : ℚ)+b k = N k := by exact_mod_cast abN k
    linarith
  exact ⟨lt_min (div_pos ha hb) (div_pos hb hn),
    (div_pos ha hb).trans_le (le_max_left _ _)⟩

private theorem cone_iff (k : ℕ) (hk : 1 ≤ k) (x : ℤ × ℤ) (hx : Source x) :
    Licensed k x ↔ ∃ u : ℤ × ℤ, Source u ∧ x = advance k u := by
  have ha := a_pos k
  have hb := b_pos k hk
  have hn : 0 < N k := by have := abN k; omega
  have hbq : (0 : ℚ) < b k := by exact_mod_cast hb
  have hnq : (0 : ℚ) < N k := by exact_mod_cast hn
  have hx₁ := hx.1.1
  have hx₂ := hx.1.2
  have hxne := hx.2
  rcases determinant k with hd | hd
  · have ho : (b k : ℚ) / N k ≤ (a k : ℚ) / b k := by
      apply (div_le_div_iff₀ hnq hbq).mpr
      exact_mod_cast (show b k * b k ≤ a k * N k by nlinarith)
    have hr : r k = (b k : ℚ) / N k := min_eq_right ho
    have hR : R k = (a k : ℚ) / b k := max_eq_left ho
    constructor
    · rintro ⟨hpos, hlo, hhi⟩
      rw [hr, div_mul_eq_mul_div, div_le_iff₀ hnq] at hlo
      rw [hR, div_mul_eq_mul_div, le_div_iff₀ hbq] at hhi
      have hlo' : 0 ≤ N k * x.1 - b k * x.2 := by exact_mod_cast (by nlinarith : (0:ℚ) ≤ N k*x.1-b k*x.2)
      have hhi' : 0 ≤ a k * x.2 - b k * x.1 := by exact_mod_cast (by nlinarith : (0:ℚ) ≤ a k*x.2-b k*x.1)
      refine ⟨(N k*x.1-b k*x.2, a k*x.2-b k*x.1), ⟨⟨hlo',hhi'⟩, ?_⟩, ?_⟩
      · by_contra hh
        have hz₁ : N k*x.1-b k*x.2 = 0 := by dsimp [sourceSize] at hh; omega
        have hz₂ : a k*x.2-b k*x.1 = 0 := by dsimp [sourceSize] at hh; omega
        have : x.1 = 0 ∧ x.2 = 0 := by
          constructor
          · linear_combination a k*hz₁ + b k*hz₂ - x.1*hd
          · linear_combination b k*hz₁ + N k*hz₂ - x.2*hd
        dsimp [sourceSize] at hxne
        omega
      · dsimp [advance]; ext <;> dsimp
        · linear_combination -x.1*hd
        · linear_combination -x.2*hd
    · rintro ⟨u, hu, rfl⟩
      have hu₁ := hu.1.1
      have hu₂ := hu.1.2
      have hsum := hu.2
      dsimp [sourceSize] at hsum
      refine ⟨?_, ?_, ?_⟩
      · dsimp [advance]; nlinarith
      · rw [hr, div_mul_eq_mul_div, div_le_iff₀ hnq]
        dsimp [advance]
        exact_mod_cast (show b k*(b k*u.1+N k*u.2) ≤ (a k*u.1+b k*u.2)*N k by nlinarith [congrArg (fun t : ℤ => t*u.1) hd])
      · rw [hR, div_mul_eq_mul_div, le_div_iff₀ hbq]
        dsimp [advance]
        exact_mod_cast (show (a k*u.1+b k*u.2)*b k ≤ a k*(b k*u.1+N k*u.2) by nlinarith [congrArg (fun t : ℤ => t*u.2) hd])
  · have ho : (a k : ℚ) / b k ≤ (b k : ℚ) / N k := by
      apply (div_le_div_iff₀ hbq hnq).mpr
      exact_mod_cast (show a k*N k ≤ b k*b k by nlinarith)
    have hr : r k = (a k : ℚ) / b k := min_eq_left ho
    have hR : R k = (b k : ℚ) / N k := max_eq_right ho
    constructor
    · rintro ⟨hpos, hlo, hhi⟩
      rw [hr, div_mul_eq_mul_div, div_le_iff₀ hbq] at hlo
      rw [hR, div_mul_eq_mul_div, le_div_iff₀ hnq] at hhi
      have hlo' : 0 ≤ b k*x.1-a k*x.2 := by exact_mod_cast (by nlinarith : (0:ℚ) ≤ b k*x.1-a k*x.2)
      have hhi' : 0 ≤ b k*x.2-N k*x.1 := by exact_mod_cast (by nlinarith : (0:ℚ) ≤ b k*x.2-N k*x.1)
      refine ⟨(b k*x.2-N k*x.1, b k*x.1-a k*x.2), ⟨⟨hhi',hlo'⟩, ?_⟩, ?_⟩
      · by_contra hh
        have hz₁ : b k*x.2-N k*x.1 = 0 := by dsimp [sourceSize] at hh; omega
        have hz₂ : b k*x.1-a k*x.2 = 0 := by dsimp [sourceSize] at hh; omega
        have hxz : x.1 = 0 ∧ x.2 = 0 := by
          constructor
          · linear_combination a k*hz₁ + b k*hz₂ + x.1*hd
          · linear_combination b k*hz₁ + N k*hz₂ + x.2*hd
        dsimp [sourceSize] at hxne
        omega
      · dsimp [advance]; ext <;> dsimp
        · linear_combination x.1*hd
        · linear_combination x.2*hd
    · rintro ⟨u, hu, rfl⟩
      have hu₁ := hu.1.1
      have hu₂ := hu.1.2
      have hsum := hu.2
      dsimp [sourceSize] at hsum
      refine ⟨?_, ?_, ?_⟩
      · dsimp [advance]; nlinarith
      · rw [hr, div_mul_eq_mul_div, div_le_iff₀ hbq]
        dsimp [advance]
        exact_mod_cast (show a k*(b k*u.1+N k*u.2) ≤ (a k*u.1+b k*u.2)*b k by nlinarith [congrArg (fun t : ℤ => t*u.1) hd])
      · rw [hR, div_mul_eq_mul_div, le_div_iff₀ hnq]
        dsimp [advance]
        exact_mod_cast (show (a k*u.1+b k*u.2)*N k ≤ b k*(b k*u.1+N k*u.2) by nlinarith [congrArg (fun t : ℤ => t*u.2) hd])

private theorem advance_source (j : ℕ) (x : ℤ × ℤ) (hx : Source x) : Source (advance j x) := by
  have ha := a_pos j
  have hb : 0 ≤ b j := by dsimp [b]; positivity
  have hn : 0 < N j := by have := abN j; omega
  obtain ⟨⟨hx₁,hx₂⟩,hs⟩ := hx
  dsimp [advance, Source, Nonneg, sourceSize] at *
  refine ⟨⟨by positivity, by positivity⟩, ?_⟩
  nlinarith [mul_nonneg (show 0 ≤ a j-1 by omega) hx₁,
    mul_nonneg (show 0 ≤ N j-1 by omega) hx₂]

private theorem e_source : Source (1,0) := by norm_num [Source, Nonneg, sourceSize]
private theorem advance_e (j : ℕ) : advance j (1,0) = (a j,b j) := by simp [advance]
private theorem e_unlicensed (k : ℕ) : ¬ Licensed k (1,0) := by simp [Licensed]
private theorem licensed_min (k : ℕ) (hk : 1 ≤ k) (x : ℤ × ℤ)
    (hx : Source x) (hl : Licensed k x) : N k ≤ sourceSize x := by
  obtain ⟨u,hu,rfl⟩ := (cone_iff k hk x hx).mp hl
  have ha := abN k
  have hb := b_pos k hk
  have hn : 0 < N k := by have := a_pos k; omega
  have hp := mul_nonneg hb.le hu.1.2
  have hq := mul_le_mul_of_nonneg_left hu.2 hn.le
  dsimp [sourceSize,advance] at *
  rw [← abN k] at hq ⊢
  nlinarith

private theorem ab_licensed (k d : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) : Licensed k (a d,b d) := by
  have hs : Source (a d,b d) := by simpa [advance_e] using advance_source d (1,0) e_source
  apply (cone_iff k hk _ hs).mpr
  refine ⟨advance (d-k) (1,0), advance_source _ _ e_source, ?_⟩
  rw [← advance_add, Nat.add_sub_of_le hkd, advance_e]

private theorem row_fibre_iff (ell : ℕ) (x : ℤ × ℤ) (c e : ℤ) :
    stageRow ell x = stageRow ell (c,e) ↔ ∃ z : ℤ, x = fibrePoint ell c e z := by
  constructor
  · intro he
    have hc : IsCoprime (A ell) (B ell) :=
      (Nat.fib_coprime_fib_succ (3*ell+3)).isCoprime
    obtain ⟨u,w,hw⟩ := hc
    have hh : A ell*(x.1-c)+B ell*(x.2-e) = 0 := by dsimp [stageRow] at he; nlinarith
    refine ⟨w*(x.1-c)-u*(x.2-e), ?_⟩
    ext <;> dsimp [fibrePoint]
    · linear_combination u*hh - (x.1-c)*hw
    · linear_combination w*hh - (x.2-e)*hw
  · rintro ⟨z,rfl⟩
    exact stage_row_fibre ell c e z

private theorem cross_stage_fibre (ell d : ℕ) (x y : ℤ × ℤ) :
    stageRow ell x = stageRow (ell+d) y ↔
      ∃ z : ℤ, x = fibrePoint ell (advance d y).1 (advance d y).2 z := by
  rw [← row_advance ell d y]
  exact row_fibre_iff ell x (advance d y).1 (advance d y).2

private theorem fibre_constraints (k ell : ℕ) (hk : 1 ≤ k) (c e H z : ℤ) :
    (Domain H (fibrePoint ell c e z) ↔
      max ⌈((-c : ℤ) : ℚ)/B ell⌉ ⌈((1-c-e : ℤ) : ℚ)/v ell⌉ ≤ z ∧
      z ≤ min ⌊(e : ℚ)/A ell⌋ ⌊((H-c-e : ℤ) : ℚ)/v ell⌋) ∧
    (Source (fibrePoint ell c e z) → (Licensed k (fibrePoint ell c e z) ↔
      ⌈(r k*e-c)/((B ell : ℚ)+r k*A ell)⌉ ≤ z ∧
      z ≤ ⌊(R k*e-c)/((B ell : ℚ)+R k*A ell)⌋)) := by
  obtain ⟨hA,hAB,_⟩ := row_bounds ell
  have hB : 0 < B ell := by omega
  have hv : 0 < v ell := by dsimp [v]; omega
  have ceil_bound (f D w : ℤ) (hD : 0 < D) :
      ⌈(f : ℚ)/D⌉ ≤ w ↔ f ≤ w*D := by
    rw [Int.ceil_le,div_le_iff₀ (by exact_mod_cast hD : (0:ℚ)<D)]
    exact_mod_cast Iff.rfl
  have floor_bound (f D w : ℤ) (hD : 0 < D) :
      w ≤ ⌊(f : ℚ)/D⌋ ↔ w*D ≤ f := by
    rw [Int.le_floor,le_div_iff₀ (by exact_mod_cast hD : (0:ℚ)<D)]
    exact_mod_cast Iff.rfl
  have hAq : (0:ℚ) < A ell := by exact_mod_cast hA
  have hBq : (0:ℚ) < B ell := by exact_mod_cast hB
  have hr := (ratio_pos k hk).1
  have hR := (ratio_pos k hk).2
  have hD : (0:ℚ) < B ell+r k*A ell := by positivity
  have hD' : (0:ℚ) < B ell+R k*A ell := by positivity
  constructor
  · rw [max_le_iff,le_min_iff,ceil_bound _ _ _ hB,ceil_bound _ _ _ hv,
      floor_bound _ _ _ hA,floor_bound _ _ _ hv]
    dsimp [Domain,Source,Nonneg,sourceSize,fibrePoint,v]
    constructor
    · rintro ⟨⟨⟨h₁,h₂⟩,h₃⟩,h₄⟩
      exact ⟨⟨by nlinarith,by nlinarith⟩,by nlinarith,by nlinarith⟩
    · rintro ⟨⟨h₁,h₂⟩,h₃,h₄⟩
      exact ⟨⟨⟨by nlinarith,by nlinarith⟩,by nlinarith⟩,by nlinarith⟩
  · intro hs
    rw [Int.ceil_le,Int.le_floor,div_le_iff₀ hD,le_div_iff₀ hD']
    dsimp [Licensed,fibrePoint]; push_cast
    constructor
    · rintro ⟨h₁,h₂,h₃⟩; exact ⟨by nlinarith,by nlinarith⟩
    · rintro ⟨h₂,h₃⟩; refine ⟨?_,by nlinarith,by nlinarith⟩
      by_contra hh
      have hy : e-z*A ell = 0 := by have := hs.1.2; dsimp [fibrePoint] at this; omega
      have hyq : (e:ℚ)-z*A ell = 0 := by exact_mod_cast hy
      have hxq : (c:ℚ)+z*B ell ≤ 0 := by nlinarith [congrArg (fun q : ℚ => R k*q) hyq]
      have hxi : c+z*B ell ≤ 0 := by exact_mod_cast hxq
      have hsize := hs.2
      dsimp [sourceSize,fibrePoint] at hsize
      omega

/-- Uniform exclusion of every other high-stage source, and the unique
    licensed integer-fibre endpoint; no exclusion or minimization premise is assumed. -/
theorem CrossStageSourceExclusionAndEndpointMinimization
    (k ell d : ℕ) (hk : 1 ≤ k) (hkd : k < d) :
    (∀ x y : ℤ × ℤ, Nonneg x → Source y → y ≠ (1,0) →
      stageRow ell x = stageRow (ell+d) y → N d < sourceSize x) ∧
    (0 ≤ tau k ell d ∧ 0 < (xMin k ell d).1 ∧ 0 < (xMin k ell d).2 ∧
      Licensed k (xMin k ell d)) ∧
    (sourceSize (xMin k ell d) = N d - tau k ell d * v ell ∧
      sourceSize (xMin k ell d) ≤ N d) ∧
    (∀ z : ℤ, Licensed k (fibrePoint ell (a d) (b d) z) →
      -tau k ell d ≤ z ∧
      sourceSize (xMin k ell d) ≤ affineSum ell (a d) (b d) z ∧
      (sourceSize (xMin k ell d) = affineSum ell (a d) (b d) z ↔ z = -tau k ell d)) := by
  have hd : 1 ≤ d := by omega
  have hlic := ab_licensed k d hk hkd.le
  obtain ⟨hA,hAB,hBA⟩ := row_bounds ell
  have hB : 0 < B ell := by omega
  have hv : 0 < v ell := by dsimp [v]; omega
  have hb := b_pos d hd
  have hr := (ratio_pos k hk).1
  have hR := (ratio_pos k hk).2
  have hD : (0 : ℚ) < B ell + r k*A ell := by positivity
  have hnum : (0 : ℚ) ≤ a d-r k*b d := by linarith [hlic.2.1]
  have ht : 0 ≤ tau k ell d := Int.floor_nonneg.mpr (div_nonneg hnum hD.le)
  have htq : (0 : ℚ) ≤ tau k ell d := by exact_mod_cast ht
  have hf : (tau k ell d : ℚ) * (B ell+r k*A ell) ≤ a d-r k*b d :=
    (le_div_iff₀ hD).mp (Int.floor_le _)
  have hlo : r k * ((b d : ℚ)+tau k ell d*A ell) ≤ a d-tau k ell d*B ell := by nlinarith
  have hhi : (a d : ℚ)-tau k ell d*B ell ≤ R k*(b d+tau k ell d*A ell) := by
    nlinarith [hlic.2.2, mul_nonneg htq (show (0:ℚ) ≤ B ell+R k*A ell by positivity)]
  have hypos : 0 < (xMin k ell d).2 := by dsimp [xMin,fibrePoint]; nlinarith
  have hxpos : 0 < (xMin k ell d).1 := by
    have hyq : (0 : ℚ) < b d+tau k ell d*A ell := by
      have hp : (0 : ℚ) < b d := by exact_mod_cast hb
      positivity
    have : (0 : ℚ) < a d-tau k ell d*B ell := lt_of_lt_of_le (mul_pos hr hyq) hlo
    have hh : 0 < a d-tau k ell d*B ell := by exact_mod_cast this
    dsimp [xMin,fibrePoint]
    linarith
  refine ⟨source_exclusion ell d hd, ⟨ht,hxpos,hypos,hypos,?_,?_⟩, ⟨?_,?_⟩, ?_⟩
  · dsimp [xMin,fibrePoint]; push_cast; nlinarith [hlo]
  · dsimp [xMin,fibrePoint]; push_cast; nlinarith [hhi]
  · change affineSum ell (a d) (b d) (-tau k ell d) = _
    rw [affine_sum_formula, abN]
    ring
  · change affineSum ell (a d) (b d) (-tau k ell d) ≤ _
    rw [affine_sum_formula, abN]
    nlinarith
  · intro z hz
    have hxZ : 0 < (fibrePoint ell (a d) (b d) z).1 := by
      exact_mod_cast lt_of_lt_of_le (mul_pos hr (by exact_mod_cast hz.1)) hz.2.1
    have hsZ : Source (fibrePoint ell (a d) (b d) z) :=
      ⟨⟨hxZ.le,hz.1.le⟩,by have := hz.1; dsimp [sourceSize]; omega⟩
    have hi := ((fibre_constraints k ell hk (a d) (b d) (N d) z).2 hsZ).mp hz
    have hz' : -tau k ell d ≤ z := by
      have hc : ⌈-(((a d : ℚ)-r k*b d)/(B ell+r k*A ell))⌉ ≤ z := by
        convert hi.1 using 1
        congr 1
        ring
      simpa only [Int.ceil_neg,tau] using hc
    refine ⟨hz', ?_, ?_⟩
    · change affineSum ell (a d) (b d) (-tau k ell d) ≤ _
      rw [affine_sum_formula,affine_sum_formula]
      nlinarith
    · change affineSum ell (a d) (b d) (-tau k ell d) = _ ↔ _
      rw [affine_sum_formula,affine_sum_formula]
      constructor <;> intro he
      · nlinarith
      · rw [he]

/-- A composition is realized by an actual nonempty ordered binary tree. -/
def Realized (x : ℤ × ℤ) : Prop :=
  ∃ T : GenealogicalFiberTransport.Source,
    ((GenealogicalFiberTransport.composition T).1 : ℤ) = x.1 ∧
    ((GenealogicalFiberTransport.composition T).2 : ℤ) = x.2

def SharpCrossBudget (k ell d : ℕ) (C : ℤ) : Prop :=
  (∀ x y, Collision k ell d x y → C ≤ cost x y) ∧
    ∃ x y, Collision k ell d x y ∧ cost x y = C ∧ Realized x ∧ Realized y

private theorem source_realized (x : ℤ × ℤ) (hx : Source x) : Realized x := by
  have hh : 1 ≤ x.1.toNat+x.2.toNat := by
    have := hx.2
    dsimp [sourceSize] at this
    omega
  obtain ⟨T,hT⟩ := (GenealogicalFiberTransport.result.1 _ _ hh).2.2.1
  exact ⟨T, by rw [hT]; exact Int.toNat_of_nonneg hx.1.1,
    by rw [hT]; exact Int.toNat_of_nonneg hx.1.2⟩

private theorem N_strict : StrictMono N := by
  apply strictMono_nat_of_lt_succ
  intro j
  by_cases hj : j = 0
  · subst j; norm_num [N]
  · have h₁ := Nat.fib_lt_fib_succ (show 2 ≤ 3*j+1 by omega)
    have h₂ := Nat.fib_mono (show 3*j+1+1 ≤ 3*(j+1)+1 by omega)
    dsimp [N]
    exact_mod_cast lt_of_lt_of_le h₁ h₂

private theorem cross_lower (k ell d : ℕ) (hk : 1 ≤ k) (x y : ℤ × ℤ)
    (hc : Collision k ell d x y) : N k ≤ cost x y := by
  classical
  by_cases hl : Licensed k x
  · exact (licensed_min k hk x hc.1 hl).trans (le_max_left _ _)
  · have hy : Licensed k y := by by_contra hy; exact hl (hc.2.2.1.mpr hy)
    exact (licensed_min k hk y hc.2.1 hy).trans (le_max_right _ _)

/-- The all-parameter cross-stage minimum, with a unique ordered composition
    pair in the strict-depth branch and actual finite-tree attainment. -/
theorem cross_stage_first_collision_budget (k ell d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    SharpCrossBudget k ell d (J k ell d) ∧
    (k < d → ∀ x y, Collision k ell d x y →
      (cost x y = J k ell d ↔ x = xMin k ell d ∧ y = (1,0))) := by
  classical
  by_cases hdk : d ≤ k
  · have hj : J k ell d = N k := ite_eq_left hdk
    have hless : N (k-d) < N k := N_strict (by omega)
    have hsx : Source (a k,b k) := by simpa [advance_e] using advance_source k (1,0) e_source
    have hsy : Source (a (k-d),b (k-d)) := by simpa [advance_e] using advance_source (k-d) (1,0) e_source
    have hly : ¬ Licensed k (a (k-d),b (k-d)) := by
      intro hl
      have hh := licensed_min k hk _ hsy hl
      dsimp [sourceSize] at hh
      rw [abN] at hh
      omega
    have hcost : cost (a k,b k) (a (k-d),b (k-d)) = N k := by
      dsimp [cost,sourceSize]
      rw [abN,abN,max_eq_left hless.le]
    refine ⟨⟨?_, (a k,b k), (a (k-d),b (k-d)), ?_, ?_, source_realized _ hsx, source_realized _ hsy⟩, ?_⟩
    · intro x y hc; rw [hj]; exact cross_lower k ell d hk x y hc
    · refine ⟨hsx,hsy,iff_of_true (ab_licensed k k hk le_rfl) hly, ?_⟩
      rw [← advance_e k, ← advance_e (k-d), row_advance, row_advance]
      congr 1
      omega
    · simpa [hj] using hcost
    · intro hh; omega
  · have hkd : k < d := by omega
    have W := CrossStageSourceExclusionAndEndpointMinimization k ell d hk hkd
    have hj : J k ell d = sourceSize (xMin k ell d) := by rw [J,ite_eq_right hdk]; exact W.2.2.1.1.symm
    have hs : Source (xMin k ell d) := ⟨⟨W.2.1.2.1.le,W.2.1.2.2.1.le⟩, by
      have h₁ := W.2.1.2.1; have h₂ := W.2.1.2.2.1; dsimp [sourceSize]; omega⟩
    have hcoll : Collision k ell d (xMin k ell d) (1,0) := by
      refine ⟨hs,e_source,iff_of_true W.2.1.2.2.2 (e_unlicensed k), ?_⟩
      rw [xMin,stage_row_fibre, ← advance_e, row_advance]
    have hcost : cost (xMin k ell d) (1,0) = J k ell d := by
      rw [hj,cost,max_eq_left]
      exact hs.2
    have hlow (x y : ℤ × ℤ) (hc : Collision k ell d x y) : J k ell d ≤ cost x y := by
      by_cases hye : y = (1,0)
      · subst y
        have hl := hc.2.2.1.mpr (e_unlicensed k)
        obtain ⟨z,hz⟩ := (cross_stage_fibre ell d x (1,0)).mp hc.2.2.2
        simp only [advance,mul_one,mul_zero,add_zero] at hz
        subst x
        exact (hj.trans_le (W.2.2.2 z hl).2.1).trans (le_max_left _ _)
      · have hh := W.1 x y hc.1.1 hc.2.1 hye hc.2.2.2
        exact (hj.le.trans W.2.2.1.2).trans (hh.le.trans (le_max_left _ _))
    refine ⟨⟨hlow, _, _, hcoll, hcost, source_realized _ hs, source_realized _ e_source⟩, ?_⟩
    intro _ x y hc
    constructor
    · intro heq
      have hye : y = (1,0) := by
        by_contra hye
        have hh := W.1 x y hc.1.1 hc.2.1 hye hc.2.2.2
        have hu := le_max_left (sourceSize x) (sourceSize y)
        have hjN := W.2.2.1.2
        change sourceSize x ≤ cost x y at hu
        rw [heq,hj] at hu
        omega
      subst y
      obtain ⟨z,hz⟩ := (cross_stage_fibre ell d x (1,0)).mp hc.2.2.2
      simp only [advance,mul_one,mul_zero,add_zero] at hz
      subst x
      have hl := hc.2.2.1.mpr (e_unlicensed k)
      have hz := W.2.2.2 z hl
      have heq' : sourceSize (xMin k ell d) = affineSum ell (a d) (b d) z := by
        have hu := le_max_left (sourceSize (fibrePoint ell (a d) (b d) z)) (sourceSize (1,0))
        change sourceSize (fibrePoint ell (a d) (b d) z) ≤ cost (fibrePoint ell (a d) (b d) z) (1,0) at hu
        rw [heq,hj] at hu
        exact le_antisymm hz.2.1 hu
      exact ⟨by rw [(hz.2.2.mp heq')]; rfl, rfl⟩
    · rintro ⟨rfl,rfl⟩
      exact hcost

def K (k ell : ℕ) : ℤ := if k ≤ ell+1 then B ell + ⌈(A ell : ℚ)*r k⌉ else N k
def SameCollision (k ell : ℕ) (x y : ℤ × ℤ) : Prop :=
  Source x ∧ Source y ∧ (Licensed k x ↔ ¬ Licensed k y) ∧ stageRow ell x = stageRow ell y

private theorem critical_column (ell : ℕ) :
    a (ell+1) = v ell ∧ b (ell+1) = A ell ∧ N (ell+1) = B ell := by
  dsimp [a,b,N,A,B,v]
  rw [show 3*(ell+1) = 3*ell+3 by omega, show 3*ell+3+1 = 3*ell+4 by omega]
  exact ⟨rfl,rfl,rfl⟩

private theorem licensed_nested (k : ℕ) (hk : 1 ≤ k) (x : ℤ × ℤ)
    (hx : Source x) (hl : Licensed k x) : 3*x.1 ≤ 2*x.2 := by
  obtain ⟨u,hu,rfl⟩ := (cone_iff k hk x hx).mp hl
  have he : advance k u = advance 1 (advance (k-1) u) := by rw [← advance_add]; congr 1; omega
  have hh := advance_source (k-1) u hu
  rw [he]
  have h₁ := hh.1.1
  have h₂ := hh.1.2
  have hone (w : ℤ × ℤ) : advance 1 w = S w := by ext <;> norm_num [advance,S,a,b,N]
  rw [hone]
  change 3*((advance (k-1) u).1+2*(advance (k-1) u).2) ≤
    2*(2*(advance (k-1) u).1+3*(advance (k-1) u).2)
  nlinarith

private theorem K_bounds (k ell : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ell+1) :
    0 < ⌈(A ell : ℚ)*r k⌉ ∧ K k ell ≤ B ell+v ell ∧ B ell < K k ell := by
  obtain ⟨hA,hAB,hBA⟩ := row_bounds ell
  have hc := critical_column ell
  have hl : Licensed k (v ell,A ell) := by rw [← hc.1,← hc.2.1]; exact ab_licensed k (ell+1) hk hkl
  have hceil : ⌈(A ell : ℚ)*r k⌉ ≤ v ell := Int.ceil_le.mpr (by nlinarith [hl.2.1])
  have hp : 0 < ⌈(A ell : ℚ)*r k⌉ := Int.ceil_pos.mpr (mul_pos (by exact_mod_cast hA) (ratio_pos k hk).1)
  rw [K,ite_eq_left hkl]
  omega

private theorem same_stage_budget (k ell : ℕ) (hk : 1 ≤ k) :
    (∀ x y, SameCollision k ell x y → K k ell ≤ cost x y) ∧
    ∃ x y, SameCollision k ell x y ∧ cost x y = K k ell := by
  classical
  have lowerN (x y : ℤ × ℤ) (h : SameCollision k ell x y) : N k ≤ cost x y := by
    by_cases hl : Licensed k x
    · exact (licensed_min k hk x h.1 hl).trans (le_max_left _ _)
    · have hy : Licensed k y := by by_contra hy; exact hl (h.2.2.1.mpr hy)
      exact (licensed_min k hk y h.2.1 hy).trans (le_max_right _ _)
  obtain ⟨hA,hAB,hBA⟩ := row_bounds ell
  have hB : 0 < B ell := by omega
  have hv : 0 < v ell := by dsimp [v]; omega
  by_cases hkl : k ≤ ell+1
  · obtain ⟨hp,hK,hBK⟩ := K_bounds k ell hk hkl
    let c : ℤ := ⌈(A ell : ℚ)*r k⌉
    have hc : c ≤ v ell := by simpa [K,ite_eq_left hkl,c] using hK
    have hl : Licensed k (c,A ell) := by
      have hr := Int.le_ceil ((A ell : ℚ)*r k)
      have hcrit := critical_column ell
      have hh := ab_licensed k (ell+1) hk hkl
      rw [hcrit.1,hcrit.2.1] at hh
      exact ⟨hA, by dsimp [c]; nlinarith, le_trans (by exact_mod_cast hc) hh.2.2⟩
    have hs : Source (c,A ell) := ⟨⟨hp.le,hA.le⟩,by dsimp [sourceSize]; omega⟩
    have ht : Source (B ell+c,0) := ⟨⟨by omega,le_rfl⟩,by dsimp [sourceSize]; omega⟩
    have hno : ¬ Licensed k (B ell+c,0) := by simp [Licensed]
    have hb : cost (c,A ell) (B ell+c,0) = K k ell := by
      dsimp [cost,sourceSize,K]
      rw [ite_eq_left hkl,max_eq_right (by omega)]
      simp [c]
    have bound (x y : ℤ × ℤ) (hx : Source x) (hy : Source y)
        (hlx : Licensed k x) (hly : ¬ Licensed k y) (he : stageRow ell y = stageRow ell x) : K k ell ≤ cost x y := by
      obtain ⟨z,hz⟩ := (row_fibre_iff ell y x.1 x.2).mp he
      have hz0 : z ≠ 0 := by intro hh; subst z; simp [fibrePoint] at hz; exact hly (hz ▸ hlx)
      have hyp := hy.1
      rw [hz] at hyp
      dsimp [Nonneg,fibrePoint] at hyp
      by_cases hzpos : 0 < z
      · have hxb : A ell ≤ x.2 := by nlinarith [hyp.2]
        have hxa : c ≤ x.1 := Int.ceil_le.mpr (by
          have hr := (ratio_pos k hk).1
          have hh : (A ell : ℚ) ≤ x.2 := by exact_mod_cast hxb
          nlinarith [hlx.2.1])
        have hycost : B ell+c ≤ sourceSize y := by
          rw [hz]
          dsimp [sourceSize,fibrePoint]
          dsimp [v] at *
          nlinarith
        rw [K,ite_eq_left hkl]
        exact hycost.trans (le_max_right _ _)
      · have hzneg : z ≤ -1 := by omega
        have hxa : B ell ≤ x.1 := by nlinarith [hyp.1]
        have hxcone := licensed_nested k hk x hx hlx
        have hxsize : B ell+v ell ≤ sourceSize x := by dsimp [v,sourceSize]; omega
        exact (hK.trans hxsize).trans (le_max_left _ _)
    refine ⟨?_,_,_,⟨hs,ht,iff_of_true hl hno,?_⟩,hb⟩
    · intro x y h
      by_cases hlx : Licensed k x
      · exact bound x y h.1 h.2.1 hlx (h.2.2.1.mp hlx) h.2.2.2.symm
      · have hly : Licensed k y := by by_contra hh; exact hlx (h.2.2.1.mpr hh)
        simpa [cost,max_comm] using bound y x h.2.1 h.1 hly hlx h.2.2.2
    · dsimp [stageRow]; ring
  · have hdeep : ell+2 ≤ k := by omega
    have ha : B ell ≤ a k := by
      rw [a_fib k hk]
      dsimp [B]
      exact_mod_cast Nat.fib_mono (show 3*ell+4 ≤ 3*k-1 by omega)
    have hb := b_pos k hk
    have hs : Source (a k,b k) := by simpa [advance_e] using advance_source k (1,0) e_source
    let y := fibrePoint ell (a k) (b k) (-1)
    have hy : Source y := by
      dsimp [y,fibrePoint,Source,Nonneg,sourceSize]
      refine ⟨⟨by omega,by omega⟩,by omega⟩
    have hysize : sourceSize y < N k := by dsimp [y,sourceSize,fibrePoint]; have := abN k; omega
    have hly : ¬ Licensed k y := fun h => (not_le_of_gt hysize) (licensed_min k hk y hy h)
    refine ⟨?_,_,_,⟨hs,hy,iff_of_true (ab_licensed k k hk le_rfl) hly,?_⟩,?_⟩
    · intro x y h; rw [K,ite_eq_right hkl]; exact lowerN x y h
    · exact (stage_row_fibre ell (a k) (b k) (-1)).symm
    · rw [K,ite_eq_right hkl,cost,max_eq_left]
      · exact abN k
      · dsimp [sourceSize]; rw [abN]; exact hysize.le

def G (k ell d : ℕ) : ℤ := min (K k ell) (min (K k (ell+d)) (J k ell d))
def selectedStage (ell d : ℕ) (s : Bool) : ℕ := if s then ell+d else ell
def JointCollision (k ell d : ℕ) (s t : Bool) (x y : ℤ × ℤ) : Prop :=
  Source x ∧ Source y ∧ (Licensed k x ↔ ¬ Licensed k y) ∧
    stageRow (selectedStage ell d s) x = stageRow (selectedStage ell d t) y
def Recoverable (k ell d : ℕ) (H : ℤ) (E : ℚ) : Prop :=
  ∃ P : ℚ → Bool, ∀ (s : Bool) (x : ℤ × ℤ), Domain H x →
    ∀ q : ℚ, |q-(stageRow (selectedStage ell d s) x : ℚ)| ≤ E →
      (P q = true ↔ Licensed k x)

private theorem joint_sharp (k ell d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (∀ s t x y, JointCollision k ell d s t x y → G k ell d ≤ cost x y) ∧
    ∃ s t x y, JointCollision k ell d s t x y ∧ cost x y = G k ell d := by
  classical
  have h₁ := same_stage_budget k ell hk
  have h₂ := same_stage_budget k (ell+d) hk
  have h₃ := (cross_stage_first_collision_budget k ell d hk hd).1
  have g₁ : G k ell d ≤ K k ell := min_le_left _ _
  have g₂ : G k ell d ≤ K k (ell+d) := (min_le_right _ _).trans (min_le_left _ _)
  have g₃ : G k ell d ≤ J k ell d := (min_le_right _ _).trans (min_le_right _ _)
  constructor
  · intro s t x y h
    cases s <;> cases t
    · exact g₁.trans (h₁.1 x y h)
    · exact g₃.trans (h₃.1 x y h)
    · have hh : Collision k ell d y x := ⟨h.2.1,h.1,by have := h.2.2.1; tauto,h.2.2.2.symm⟩
      simpa [cost,max_comm] using g₃.trans (h₃.1 y x hh)
    · exact g₂.trans (h₂.1 x y h)
  · have choices : G k ell d = K k ell ∨ G k ell d = K k (ell+d) ∨ G k ell d = J k ell d := by
      rcases min_choice (K k ell) (min (K k (ell+d)) (J k ell d)) with h | h
      · exact Or.inl h
      · rcases min_choice (K k (ell+d)) (J k ell d) with hh | hh
        · exact Or.inr (Or.inl (h.trans hh))
        · exact Or.inr (Or.inr (h.trans hh))
    rcases choices with h | h | h
    · obtain ⟨x,y,hxy,hcost⟩ := h₁.2
      exact ⟨false,false,x,y,hxy,hcost.trans h.symm⟩
    · obtain ⟨x,y,hxy,hcost⟩ := h₂.2
      exact ⟨true,true,x,y,hxy,hcost.trans h.symm⟩
    · obtain ⟨x,y,hxy,hcost,_⟩ := h₃.2
      exact ⟨false,true,x,y,hxy,hcost.trans h.symm⟩

private theorem recoverable_iff (k ell d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) (H : ℤ) :
    Recoverable k ell d H 0 ↔ H < G k ell d := by
  classical
  have hs := joint_sharp k ell d hk hd
  constructor
  · rintro ⟨P,hP⟩
    by_contra hh
    obtain ⟨s,t,x,y,hxy,hcost⟩ := hs.2
    have hHx : Domain H x := ⟨hxy.1, (le_max_left _ _).trans (hcost.le.trans (by omega))⟩
    have hHy : Domain H y := ⟨hxy.2.1, (le_max_right _ _).trans (hcost.le.trans (by omega))⟩
    have hp := hP s x hHx (stageRow (selectedStage ell d s) x) (by simp)
    have hq := hP t y hHy (stageRow (selectedStage ell d s) x) (by rw [hxy.2.2.2]; simp)
    have ha := hxy.2.2.1
    tauto
  · intro hH
    let P : ℚ → Bool := fun q => decide (∃ s x, Domain H x ∧
      q = (stageRow (selectedStage ell d s) x : ℚ) ∧ Licensed k x)
    refine ⟨P,?_⟩
    intro s x hx q hq
    have he : q = (stageRow (selectedStage ell d s) x : ℚ) := by
      exact sub_eq_zero.mp (abs_nonpos_iff.mp hq)
    simp only [P,decide_eq_true_eq]
    constructor
    · rintro ⟨t,y,hy,hyq,hly⟩
      by_contra hlx
      have hh : JointCollision k ell d t s y x :=
        ⟨hy.1,hx.1,iff_of_true hly hlx, by exact_mod_cast (hyq.symm.trans he)⟩
      have hb := hs.1 t s y x hh
      have hu : cost y x ≤ H := max_le hy.2 hx.2
      omega
    · intro hlx; exact ⟨s,x,hx,he,hlx⟩


private theorem K_ge_N (k ell : ℕ) (hk : 1 ≤ k) : N k ≤ K k ell := by
  obtain ⟨x,y,h,hc⟩ := (same_stage_budget k ell hk).2
  have hh : Collision k ell 0 x y := ⟨h.1,h.2.1,h.2.2.1,by simpa using h.2.2.2⟩
  simpa [hc] using cross_lower k ell 0 hk x y hh

private theorem K_stage_mono (k ell d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) : K k ell ≤ K k (ell+d) := by
  by_cases hkl : k ≤ ell+1
  · have hkh : k ≤ ell+d+1 := by omega
    have hK := (K_bounds k ell hk hkl).2.1
    have hg : 2*B ell < B (ell+d) := by
      have hh := row_advance ell 1 (0,1)
      norm_num [stageRow,advance,a,b,N] at hh
      have hm : B (ell+1) ≤ B (ell+d) := by
        dsimp [B]; exact_mod_cast Nat.fib_mono (show 3*(ell+1)+4 ≤ 3*(ell+d)+4 by omega)
      have ha := (row_bounds ell).1
      have hb := (row_bounds ell).2.1
      nlinarith
    have hv : v ell < B ell := by dsimp [v]; have := (row_bounds ell).1; omega
    have hp := (K_bounds k (ell+d) hk hkh).1
    have he : K k (ell+d) = B (ell+d)+⌈(A (ell+d) : ℚ)*r k⌉ := ite_eq_left hkh
    rw [he]
    omega
  · rw [K,ite_eq_right hkl]
    exact K_ge_N k (ell+d) hk

private theorem G_formula (k ell d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    G k ell d = if max k d ≤ ell+1 then N (max k d) else K k ell := by
  have hmon := K_stage_mono k ell d hk hd
  have hcross := (cross_stage_first_collision_budget k ell d hk hd).1
  by_cases hsmall : max k d ≤ ell+1
  · have hkell : k ≤ ell+1 := (le_max_left _ _).trans hsmall
    have hdell : d ≤ ell+1 := (le_max_right _ _).trans hsmall
    have hN : N (max k d) ≤ B ell := by
      rw [← (critical_column ell).2.2]
      exact N_strict.monotone hsmall
    have hJ : J k ell d = N (max k d) := by
      by_cases hdk : d ≤ k
      · rw [J,ite_eq_left hdk,max_eq_left hdk]
      · have hkd : k < d := by omega
        have W := CrossStageSourceExclusionAndEndpointMinimization k ell d hk hkd
        have ht := W.2.1.1
        have had : a d < B ell := by
          have hnd := N_strict.monotone hdell
          rw [(critical_column ell).2.2] at hnd
          have := abN d; have := b_pos d hd; omega
        have hD : (0:ℚ) < B ell+r k*A ell := by
          have hAq : (0:ℚ) < A ell := by exact_mod_cast (row_bounds ell).1
          have hBq : (0:ℚ) < B ell := by exact_mod_cast lt_trans (row_bounds ell).1 (row_bounds ell).2.1
          have hr := (ratio_pos k hk).1
          positivity
        have htlt : tau k ell d < 1 := Int.floor_lt.mpr (by
          apply (div_lt_iff₀ hD).mpr
          have hp := (ratio_pos k hk).1
          have hA := (row_bounds ell).1
          have hb := b_pos d hd
          have ha' : (a d : ℚ) < B ell := by exact_mod_cast had
          have hAq : (0:ℚ) < A ell := by exact_mod_cast hA
          have hbq : (0:ℚ) < b d := by exact_mod_cast hb
          norm_num only [Int.cast_one,one_mul]
          nlinarith [mul_pos hp hAq,mul_pos hp hbq])
        have ht0 : tau k ell d = 0 := by omega
        simp [J,hdk,ht0,max_eq_right hkd.le]
    have hJK : J k ell d ≤ K k ell := by
      rw [hJ]; exact hN.trans (K_bounds k ell hk hkell).2.2.le
    rw [G,min_eq_right (hJK.trans hmon),min_eq_right hJK,ite_eq_left hsmall,hJ]
  · rw [ite_eq_right hsmall]
    have hKJ : K k ell ≤ J k ell d := by
      by_cases hkell : k ≤ ell+1
      · have hddeep : ell+2 ≤ d := by omega
        have hA := (row_bounds ell).1
        have hB : 0 < B ell := lt_trans hA (row_bounds ell).2.1
        have had := a_pos d
        have hbd : A ell+2*B ell ≤ b d := by
          have hh := row_advance ell 1 (1,0)
          norm_num [stageRow,advance,a,b,N] at hh
          have hm : A (ell+1) ≤ b d := by
            dsimp [A,b]; exact_mod_cast Nat.fib_mono (show 3*(ell+1)+3 ≤ 3*d by omega)
          nlinarith
        have hh := row_advance ell d (1,0)
        dsimp [stageRow,advance] at hh
        have hK := (K_bounds k ell hk hkell).2.1
        have hv : v ell < B ell := by dsimp [v]; omega
        have hgap : B ell*K k ell < A (ell+d) := by nlinarith
        obtain ⟨x,y,hxy,hcost,_⟩ := hcross.2
        have hy := hxy.2.1
        have hx := hxy.1
        have hread : A (ell+d) ≤ stageRow (ell+d) y := by
          have hpos := (row_bounds (ell+d)).1
          have hle := (row_bounds (ell+d)).2.1
          dsimp [Source,Nonneg,sourceSize] at hy
          dsimp [stageRow]
          nlinarith
        have hup : stageRow ell x ≤ B ell*cost x y := by
          have hm := le_max_left (sourceSize x) (sourceSize y)
          dsimp [cost] at *
          dsimp [stageRow,sourceSize] at *
          nlinarith [hx.1.1,(row_bounds ell).2.1]
        rw [hcost] at hup
        have he := hxy.2.2.2
        nlinarith
      · rw [K,ite_eq_right hkell]
        obtain ⟨x,y,hxy,hcost,_⟩ := hcross.2
        simpa [hcost] using cross_lower k ell d hk x y hxy
    exact min_eq_left (le_min hmon hKJ)

/-- Both the exact recovery threshold and its full-parameter simplification. -/
theorem joint_first_failure_budget (k ell d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    G k ell d = min (K k ell) (min (K k (ell+d)) (J k ell d)) ∧
    G k ell d = (if max k d ≤ ell+1 then N (max k d) else K k ell) ∧
    (∀ H : ℤ, 1 ≤ H → (Recoverable k ell d H 0 ↔ H < G k ell d)) ∧
    (∀ H : ℤ, G k ell d ≤ H → ∃ s t x y, Domain H x ∧ Domain H y ∧
      JointCollision k ell d s t x y ∧ Realized x ∧ Realized y) ∧
    (∀ (H : ℤ) (E : ℚ), 0 ≤ E → G k ell d ≤ H → ¬ Recoverable k ell d H E) := by
  have hs := joint_sharp k ell d hk hd
  refine ⟨rfl,G_formula k ell d hk hd,fun H _ => recoverable_iff k ell d hk hd H,?_,?_⟩
  · intro H hH
    obtain ⟨s,t,x,y,hxy,hcost⟩ := hs.2
    exact ⟨s,t,x,y,⟨hxy.1,(le_max_left _ _).trans (hcost.le.trans hH)⟩,
      ⟨hxy.2.1,(le_max_right _ _).trans (hcost.le.trans hH)⟩,hxy,
      source_realized _ hxy.1,source_realized _ hxy.2.1⟩
  · intro H E hE hH ⟨P,hP⟩
    obtain ⟨s,t,x,y,hxy,hcost⟩ := hs.2
    have hp := hP s x ⟨hxy.1,(le_max_left _ _).trans (hcost.le.trans hH)⟩
      (stageRow (selectedStage ell d s) x) (by simpa using hE)
    have hq := hP t y ⟨hxy.2.1,(le_max_right _ _).trans (hcost.le.trans hH)⟩
      (stageRow (selectedStage ell d s) x) (by rw [hxy.2.2.2]; simpa using hE)
    have ha := hxy.2.2.1
    tauto

def Nonconstant (k : ℕ) (H : ℤ) : Prop :=
  ∃ x y, Domain H x ∧ Domain H y ∧ Licensed k x ∧ ¬ Licensed k y
def Window (k ell d : ℕ) (H : ℤ) : Prop := Nonconstant k H ∧ Recoverable k ell d H 0
def KnownRecoverable (k ell d : ℕ) (H : ℤ) : Prop :=
  ∃ P : Bool → ℚ → Bool, ∀ s x, Domain H x →
    (P s (stageRow (selectedStage ell d s) x) = true ↔ Licensed k x)

private theorem known_recoverable_iff (k ell d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) (H : ℤ) :
    KnownRecoverable k ell d H ↔ H < K k ell := by
  classical
  constructor
  · rintro ⟨P,hP⟩; by_contra hH
    obtain ⟨x,y,hxy,hcost⟩ := (same_stage_budget k ell hk).2
    have hp := hP false x ⟨hxy.1,(le_max_left _ _).trans (hcost.le.trans (by omega))⟩
    have hq := hP false y ⟨hxy.2.1,(le_max_right _ _).trans (hcost.le.trans (by omega))⟩
    have he : (stageRow ell x : ℚ) = stageRow ell y := by exact_mod_cast hxy.2.2.2
    change P false (stageRow ell x) = true ↔ Licensed k x at hp
    change P false (stageRow ell y) = true ↔ Licensed k y at hq
    rw [← he] at hq
    have ha := hxy.2.2.1; tauto
  · intro hH
    refine ⟨fun s q => decide (∃ x, Domain H x ∧ q = (stageRow (selectedStage ell d s) x : ℚ) ∧ Licensed k x),?_⟩
    intro s x hx
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨y,hy,he,hly⟩; by_contra hlx
      have hc : SameCollision k (selectedStage ell d s) y x :=
        ⟨hy.1,hx.1,iff_of_true hly hlx,by exact_mod_cast he.symm⟩
      have hb := (same_stage_budget k (selectedStage ell d s) hk).1 y x hc
      have hm : K k ell ≤ K k (selectedStage ell d s) := by
        cases s; exact le_rfl; exact K_stage_mono k ell d hk hd
      have hu : cost y x ≤ H := max_le hy.2 hx.2
      omega
    · intro hl; exact ⟨x,hx,rfl,hl⟩

/-- Strict reference loss, the nonconstant recovery interval and all four
    depth/stage windows, including monotonicity and saturation in the stage gap. -/
theorem stage_reference_loss_and_windows (k ell d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (∀ H : ℤ, KnownRecoverable k ell d H ↔ H < K k ell) ∧
    (G k ell d < K k ell ↔ max k d ≤ ell+1) ∧
    (∀ H : ℤ, 1 ≤ H → (Nonconstant k H ↔ N k ≤ H)) ∧
    (∀ (H : ℤ) (E : ℚ), H < N k → Recoverable k ell d H E) ∧
    (∀ H : ℤ, 1 ≤ H → (Window k ell d H ↔ N k ≤ H ∧ H < G k ell d)) ∧
    ((∃ H : ℤ, 1 ≤ H ∧ Window k ell d H) ↔ k ≤ ell+1 ∧ k < d) ∧
    (d ≤ k → G k ell d = N k) ∧
    (k < d → d ≤ ell+1 → G k ell d = N d) ∧
    (ell+2 ≤ d → G k ell d = K k ell) ∧
    (ell+2 ≤ k → G k ell d = N k) ∧
    (∀ d' : ℕ, d ≤ d' → G k ell d ≤ G k ell d') := by
  have T := joint_first_failure_budget k ell d hk hd
  have hNk : 1 ≤ N k := by
    have := a_pos k; have := b_pos k hk; have := abN k; omega
  have nc (H : ℤ) (hH : 1 ≤ H) : Nonconstant k H ↔ N k ≤ H := by
    constructor
    · rintro ⟨x,y,hx,hy,hl,_⟩; exact (licensed_min k hk x hx.1 hl).trans hx.2
    · intro hN
      have hs : Source (a k,b k) := by simpa [advance_e] using advance_source k (1,0) e_source
      exact ⟨_,_,⟨hs,by dsimp [sourceSize]; rw [abN]; exact hN⟩,
        ⟨e_source,hH⟩,ab_licensed k k hk le_rfl,e_unlicensed k⟩
  have win (H : ℤ) (hH : 1 ≤ H) : Window k ell d H ↔ N k ≤ H ∧ H < G k ell d := by
    exact and_congr (nc H hH) (T.2.2.1 H hH)
  have room : N k < G k ell d ↔ k ≤ ell+1 ∧ k < d := by
    rw [T.2.1]
    by_cases hm : max k d ≤ ell+1
    · rw [ite_eq_left hm]
      have hkell := (le_max_left k d).trans hm
      rw [N_strict.lt_iff_lt]
      omega
    · rw [ite_eq_right hm]
      by_cases hkell : k ≤ ell+1
      · have hN : N k ≤ B ell := by rw [← (critical_column ell).2.2]; exact N_strict.monotone hkell
        have hK := (K_bounds k ell hk hkell).2.2
        have hkd : k < d := by omega
        exact iff_of_true (hN.trans_lt hK) ⟨hkell,hkd⟩
      · simp [K,hkell]
  refine ⟨known_recoverable_iff k ell d hk hd,?_,nc,?_,win,?_,?_,?_,?_,?_,?_⟩
  · rw [T.2.1]
    by_cases hm : max k d ≤ ell+1
    · rw [ite_eq_left hm]
      have hN : N (max k d) ≤ B ell := by rw [← (critical_column ell).2.2]; exact N_strict.monotone hm
      exact iff_of_true (hN.trans_lt (K_bounds k ell hk ((le_max_left _ _).trans hm)).2.2) hm
    · simp [hm]
  · intro H E hH
    refine ⟨fun _ => false,?_⟩
    intro s x hx q _
    simp only [Bool.false_eq_true,false_iff]
    intro hl; have := licensed_min k hk x hx.1 hl; have hbound := hx.2; omega
  · constructor
    · rintro ⟨H,hH,hw⟩; exact room.mp (lt_of_le_of_lt ((win H hH).mp hw).1 ((win H hH).mp hw).2)
    · intro h; exact ⟨N k,hNk,(win (N k) hNk).mpr ⟨le_rfl,room.mpr h⟩⟩
  · intro hdk
    rw [T.2.1,max_eq_left hdk]
    by_cases h : k ≤ ell+1 <;> simp [h,K]
  · intro hkd hdell; rw [T.2.1,max_eq_right hkd.le,ite_eq_left hdell]
  · intro hddeep; rw [T.2.1,ite_eq_right (by omega)]
  · intro hkdeep; rw [T.2.1,ite_eq_right (by omega),K,ite_eq_right (by omega)]
  · intro d' hdd
    have hd' : 1 ≤ d' := hd.trans hdd
    rw [T.2.1,(joint_first_failure_budget k ell d' hk hd').2.1]
    by_cases h₁ : max k d ≤ ell+1 <;> by_cases h₂ : max k d' ≤ ell+1
    · rw [ite_eq_left h₁,ite_eq_left h₂]; exact N_strict.monotone (max_le_max le_rfl hdd)
    · rw [ite_eq_left h₁,ite_eq_right h₂]
      have hN : N (max k d) ≤ B ell := by rw [← (critical_column ell).2.2]; exact N_strict.monotone h₁
      exact hN.trans (K_bounds k ell hk ((le_max_left _ _).trans h₁)).2.2.le
    · omega
    · simp [h₁,h₂]

end D5.S3.Arith.FibonacciAtomic.CrossStageCollisionBudget

#print axioms D5.S3.Arith.FibonacciAtomic.CrossStageCollisionBudget.CrossStageSourceExclusionAndEndpointMinimization
#print axioms D5.S3.Arith.FibonacciAtomic.CrossStageCollisionBudget.cross_stage_first_collision_budget
#print axioms D5.S3.Arith.FibonacciAtomic.CrossStageCollisionBudget.joint_first_failure_budget
#print axioms D5.S3.Arith.FibonacciAtomic.CrossStageCollisionBudget.stage_reference_loss_and_windows
