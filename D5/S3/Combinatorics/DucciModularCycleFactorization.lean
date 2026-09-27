/- GID: D5/S3/Combinatorics/DucciModularCycleFactorization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DucciModularCycleFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Data.Fintype.Pigeonhole, mathlib/module/Mathlib.Tactic.LinearCombination, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Every cycle of the modular multiplicative Ducci game factors through one constant and two generator cycles. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DucciModularCycleFactorization

/-- The four corners of the square, so that "the next corner" is addition of one. -/
abbrev Idx : Type := ZMod 4

/-- A position of the game modulo `n`: one residue at each corner. -/
abbrev Tup (n : ℕ) : Type := Idx → ZMod n

variable {n : ℕ}

/-- One move of the game: every corner is replaced by its product with the next corner. -/
def step (u : Tup n) : Tup n := fun i => u i * u (i + 1)

/-- A position is in a cycle when some positive number of moves returns it. -/
def InCycle (u : Tup n) : Prop := ∃ L : ℕ, 0 < L ∧ step^[L] u = u

/-- The position carrying `a` at every corner. -/
def const (a : ZMod n) : Tup n := fun _ => a

/-- A cycle is constant when every position on it carries one value at all four corners. -/
def InConstantCycle (u : Tup n) : Prop :=
  InCycle u ∧ ∀ m : ℕ, ∃ a : ZMod n, step^[m] u = const a

/-- The generator 4-tuple `[1, x, 1, x⁻¹]` of a unit `x`. -/
def gen (x : (ZMod n)ˣ) : Tup n :=
  fun i => if i = 1 then (x : ZMod n) else if i = 3 then ((x⁻¹ : (ZMod n)ˣ) : ZMod n) else 1

/-- A cycle is a generator cycle when some position on it is a generator 4-tuple. -/
def InGeneratorCycle (u : Tup n) : Prop :=
  InCycle u ∧ ∃ (m : ℕ) (x : (ZMod n)ˣ), step^[m] u = gen x

/-- Corner-by-corner product of three positions. -/
def prod3 (A B C : Tup n) : Tup n := fun i => A i * B i * C i

/-- Conjecture 1 of Fellman and Klyve, INTEGERS 23 (2023), #A86, Section 7: "Every cocomposite
cycle is a product of a constant cycle and two generating cycles."  A cycle is cocomposite when
none of the entries of its positions is a unit, which by their Lemma 2 is the alternative to all
entries being units. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ u : Tup n, InCycle u → (∀ i : Idx, ¬ IsUnit (u i)) →
    ∃ A B C : Tup n, InConstantCycle A ∧ InGeneratorCycle B ∧ InGeneratorCycle C ∧
      u = prod3 A B C

/-
proof_shape: result: content
escape_witness: the product invariant `Q (step u) = Q u ^ 2`, the exponent vectors of the third
  and fourth moves, the pigeonhole exponent `t` with `z ^ 2 ^ t = z` on every iterated square,
  and the orthogonal idempotent splitting `x = u 1 * αinv + 1 - ε`
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only)
-/

private lemma idx_cases (i : Idx) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  revert i; decide

private lemma step_apply (u : Tup n) (i : Idx) : step u i = u i * u (i + 1) := rfl

private lemma iter_succ (u : Tup n) (m : ℕ) (i : Idx) :
    step^[m + 1] u i = step^[m] u i * step^[m] u (i + 1) := by
  rw [Function.iterate_succ_apply']; rfl

/-- The product of all four corners. -/
private def prodAll (u : Tup n) : ZMod n := u 0 * u 1 * u 2 * u 3

private lemma step_zero (u : Tup n) : step u 0 = u 0 * u 1 := by
  have h : (0 : Idx) + 1 = 1 := by decide
  rw [step_apply, h]

private lemma step_one (u : Tup n) : step u 1 = u 1 * u 2 := by
  have h : (1 : Idx) + 1 = 2 := by decide
  rw [step_apply, h]

private lemma step_two (u : Tup n) : step u 2 = u 2 * u 3 := by
  have h : (2 : Idx) + 1 = 3 := by decide
  rw [step_apply, h]

private lemma step_three (u : Tup n) : step u 3 = u 3 * u 0 := by
  have h : (3 : Idx) + 1 = 0 := by decide
  rw [step_apply, h]

/-- The product of all four corners squares at every move. -/
private lemma prodAll_step (u : Tup n) : prodAll (step u) = prodAll u ^ 2 := by
  simp only [prodAll, step_zero, step_one, step_two, step_three]
  ring

private lemma prodAll_iter (u : Tup n) : ∀ m : ℕ, prodAll (step^[m] u) = prodAll u ^ 2 ^ m
  | 0 => by simp
  | (m + 1) => by
      rw [Function.iterate_succ_apply', prodAll_step, prodAll_iter u m, ← pow_mul, pow_succ]

/-- Opposite corners of any position reached in one move carry the same product. -/
private lemma cross_zero_two (u : Tup n) : step u 0 * step u 2 = prodAll u := by
  simp only [prodAll, step_zero, step_two]; ring

private lemma cross_one_three (u : Tup n) : step u 1 * step u 3 = prodAll u := by
  simp only [prodAll, step_one, step_three]; ring

private lemma iter_two (u : Tup n) (i : Idx) :
    step^[2] u i = u i * u (i + 1) ^ 2 * u (i + 2) := by
  have h : ∀ j : Idx, j + 1 + 1 = j + 2 := by decide
  have e : step^[2] u i = step^[1] u i * step^[1] u (i + 1) := iter_succ u 1 i
  rw [e]
  simp only [Function.iterate_one, step_apply, h]
  ring

private lemma iter_three (u : Tup n) (i : Idx) :
    step^[3] u i = u i * u (i + 1) ^ 3 * u (i + 2) ^ 3 * u (i + 3) := by
  have h1 : ∀ j : Idx, j + 1 + 1 = j + 2 := by decide
  have h2 : ∀ j : Idx, j + 1 + 2 = j + 3 := by decide
  have e : step^[3] u i = step^[2] u i * step^[2] u (i + 1) := iter_succ u 2 i
  rw [e, iter_two, iter_two, h1, h2]
  ring

private lemma iter_four (u : Tup n) (i : Idx) :
    step^[4] u i = (u i * u (i + 1) ^ 2 * u (i + 2) ^ 3 * u (i + 3) ^ 2) ^ 2 := by
  have h1 : ∀ j : Idx, j + 1 + 1 = j + 2 := by decide
  have h2 : ∀ j : Idx, j + 1 + 2 = j + 3 := by decide
  have h3 : ∀ j : Idx, j + 1 + 3 = j := by decide
  have e : step^[4] u i = step^[3] u i * step^[3] u (i + 1) := iter_succ u 3 i
  rw [e, iter_three, iter_three, h1, h2, h3]
  ring

/-- The monomial whose square is the fourth move. -/
private def gmon (u : Tup n) : Tup n :=
  fun i => u i * u (i + 1) ^ 2 * u (i + 2) ^ 3 * u (i + 3) ^ 2

private lemma gmon_pow (w : Tup n) (k : ℕ) (i : Idx) :
    gmon (fun j => w j ^ 2 ^ k) i = gmon w i ^ 2 ^ k := by
  simp only [gmon]
  ring

/-- After `4 * k` moves every corner is a `2 ^ k`-th power. -/
private lemma iter_four_pow (u : Tup n) :
    ∀ k : ℕ, ∃ w : Tup n, ∀ i : Idx, step^[4 * k] u i = w i ^ 2 ^ k
  | 0 => ⟨u, by intro i; simp⟩
  | (k + 1) => by
      obtain ⟨w, hw⟩ := iter_four_pow u k
      refine ⟨gmon w, fun i => ?_⟩
      have hsplit : 4 * (k + 1) = 4 + 4 * k := by ring
      rw [hsplit, Function.iterate_add_apply, iter_four]
      have hpt : ∀ j : Idx, step^[4 * k] u j = w j ^ 2 ^ k := hw
      rw [hpt, hpt, hpt, hpt]
      rw [show (w i ^ 2 ^ k * (w (i + 1) ^ 2 ^ k) ^ 2 * (w (i + 2) ^ 2 ^ k) ^ 3 *
            (w (i + 3) ^ 2 ^ k) ^ 2) = gmon (fun j => w j ^ 2 ^ k) i from by simp [gmon]]
      rw [gmon_pow, ← pow_mul, ← pow_succ]

private lemma sq_iter (z : ZMod n) : ∀ m : ℕ, (fun y : ZMod n => y ^ 2)^[m] z = z ^ 2 ^ m
  | 0 => by simp
  | (m + 1) => by
      rw [Function.iterate_succ_apply', sq_iter z m, ← pow_mul, ← pow_succ]

/-- If two iterates of squaring agree as maps, every high enough exponent is periodic. -/
private lemma square_period_of_eq {a b : ℕ} (hlt : a < b)
    (hfun : ((fun y : ZMod n => y ^ 2)^[a]) = ((fun y : ZMod n => y ^ 2)^[b])) :
    ∀ m : ℕ, a ≤ m → ∀ w : ZMod n, w ^ 2 ^ (m + (b - a)) = w ^ 2 ^ m := by
  intro m hm w
  have key : ((fun y : ZMod n => y ^ 2)^[m + (b - a)]) = ((fun y : ZMod n => y ^ 2)^[m]) := by
    have h1 : m + (b - a) = (m - a) + b := by omega
    have h2 : (m - a) + a = m := by omega
    rw [h1, Function.iterate_add, ← hfun, ← Function.iterate_add, h2]
  have h3 := congrArg (fun f => f w) key
  simpa [sq_iter] using h3

/-- A single pigeonhole step: the iterated squaring maps of a finite ring repeat. -/
private lemma exists_square_period (n : ℕ) [NeZero n] :
    ∃ i t : ℕ, 0 < t ∧ ∀ m : ℕ, i ≤ m → ∀ w : ZMod n, w ^ 2 ^ (m + t) = w ^ 2 ^ m := by
  obtain ⟨a, b, hab, hfun⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => ((fun y : ZMod n => y ^ 2)^[k]))
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact ⟨a, b - a, by omega, square_period_of_eq hlt hfun⟩
  · exact ⟨b, a - b, by omega, square_period_of_eq hlt hfun.symm⟩


private lemma iter_const (a : ZMod n) : ∀ m : ℕ, step^[m] (const a) = const (a ^ 2 ^ m)
  | 0 => by simp
  | (m + 1) => by
      rw [Function.iterate_succ_apply', iter_const a m]
      funext i
      show (a ^ 2 ^ m) * (a ^ 2 ^ m) = a ^ 2 ^ (m + 1)
      rw [← pow_add, ← two_mul, ← pow_succ']

/-- Turning the square by one corner. -/
private def rot (u : Tup n) : Tup n := fun i => u (i + 1)

private lemma step_rot (u : Tup n) : step (rot u) = rot (step u) := rfl

private lemma iter_rot (u : Tup n) : ∀ m : ℕ, step^[m] (rot u) = rot (step^[m] u)
  | 0 => rfl
  | (m + 1) => by
      have h1 : step^[m + 1] (rot u) = step (step^[m] (rot u)) :=
        Function.iterate_succ_apply' step m (rot u)
      have h2 : step^[m + 1] u = step (step^[m] u) := Function.iterate_succ_apply' step m u
      rw [h1, iter_rot u m, step_rot, ← h2]

private lemma rot_zero (u : Tup n) : rot u 0 = u 1 := by
  show u ((0 : Idx) + 1) = u 1
  rw [show (0 : Idx) + 1 = 1 by decide]

private lemma rot_one (u : Tup n) : rot u 1 = u 2 := by
  show u ((1 : Idx) + 1) = u 2
  rw [show (1 : Idx) + 1 = 2 by decide]

private lemma rot_two (u : Tup n) : rot u 2 = u 3 := by
  show u ((2 : Idx) + 1) = u 3
  rw [show (2 : Idx) + 1 = 3 by decide]

private lemma rot_three (u : Tup n) : rot u 3 = u 0 := by
  show u ((3 : Idx) + 1) = u 0
  rw [show (3 : Idx) + 1 = 0 by decide]

private lemma gen_zero (x : (ZMod n)ˣ) : gen x 0 = 1 := by
  simp [gen, show (0 : Idx) ≠ 1 by decide, show (0 : Idx) ≠ 3 by decide]

private lemma gen_one (x : (ZMod n)ˣ) : gen x 1 = (x : ZMod n) := by simp [gen]

private lemma gen_two (x : (ZMod n)ˣ) : gen x 2 = 1 := by
  simp [gen, show (2 : Idx) ≠ 1 by decide, show (2 : Idx) ≠ 3 by decide]

private lemma gen_three (x : (ZMod n)ˣ) : gen x 3 = ((x⁻¹ : (ZMod n)ˣ) : ZMod n) := by
  simp [gen, show (3 : Idx) ≠ 1 by decide]

/-- Four moves send a generator 4-tuple to the generator 4-tuple of the inverse fourth power. -/
private lemma iter_four_gen (x : (ZMod n)ˣ) : step^[4] (gen x) = gen (x⁻¹ ^ 4) := by
  have hmi : ((x : ZMod n)) * ((x⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := x.mul_inv
  have hv : ∀ z : (ZMod n)ˣ, ((z ^ 4 : (ZMod n)ˣ) : ZMod n) = (z : ZMod n) ^ 4 := by
    intro z; exact Units.val_pow_eq_pow_val z 4
  have hinv : ((x⁻¹ ^ 4 : (ZMod n)ˣ)⁻¹ : (ZMod n)ˣ) = x ^ 4 := by
    rw [← inv_pow, inv_inv]
  funext i
  rcases idx_cases i with h | h | h | h <;> subst h <;>
    rw [iter_four] <;>
    simp only [show (0 : Idx) + 1 = 1 by decide, show (0 : Idx) + 2 = 2 by decide,
      show (0 : Idx) + 3 = 3 by decide, show (1 : Idx) + 1 = 2 by decide,
      show (1 : Idx) + 2 = 3 by decide, show (1 : Idx) + 3 = 0 by decide,
      show (2 : Idx) + 1 = 3 by decide, show (2 : Idx) + 2 = 0 by decide,
      show (2 : Idx) + 3 = 1 by decide, show (3 : Idx) + 1 = 0 by decide,
      show (3 : Idx) + 2 = 1 by decide, show (3 : Idx) + 3 = 2 by decide,
      gen_zero, gen_one, gen_two, gen_three, hinv, hv]
  · calc (1 * (x : ZMod n) ^ 2 * (1 : ZMod n) ^ 3 * (((x⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 2) ^ 2
        = (((x : ZMod n) * ((x⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hmi]; ring
  · calc ((x : ZMod n) * (1 : ZMod n) ^ 2 * (((x⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 3 * (1 : ZMod n) ^ 2) ^ 2
        = ((x : ZMod n) * ((x⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 2 *
            (((x⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 4 := by ring
      _ = (((x⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 4 := by rw [hmi]; ring
  · calc ((1 : ZMod n) * (((x⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 2 * (1 : ZMod n) ^ 3 * (x : ZMod n) ^ 2) ^ 2
        = (((x : ZMod n) * ((x⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hmi]; ring
  · calc ((((x⁻¹ : (ZMod n)ˣ) : ZMod n)) * (1 : ZMod n) ^ 2 * (x : ZMod n) ^ 3 * (1 : ZMod n) ^ 2) ^ 2
        = ((x : ZMod n) * ((x⁻¹ : (ZMod n)ˣ) : ZMod n)) ^ 2 * (x : ZMod n) ^ 4 := by ring
      _ = (x : ZMod n) ^ 4 := by rw [hmi]; ring

private lemma iter_eight_gen (x : (ZMod n)ˣ) : step^[8] (gen x) = gen (x ^ 16) := by
  have h : step^[8] (gen x) = step^[4] (step^[4] (gen x)) := by
    rw [← Function.iterate_add_apply]
  rw [h, iter_four_gen, iter_four_gen]
  congr 1
  rw [← inv_pow, inv_inv, ← pow_mul]

private lemma iter_gen_pow (x : (ZMod n)ˣ) :
    ∀ m : ℕ, step^[8 * m] (gen x) = gen (x ^ 16 ^ m)
  | 0 => by simp
  | (m + 1) => by
      have h : 8 * (m + 1) = 8 + 8 * m := by ring
      rw [h, Function.iterate_add_apply, iter_gen_pow x m, iter_eight_gen, ← pow_mul,
        ← pow_succ]

private lemma pow_fix {M : Type*} [Monoid M] {z : M} {a : ℕ} (h : z ^ a = z) :
    ∀ k : ℕ, z ^ a ^ (k + 1) = z
  | 0 => by simpa using h
  | (k + 1) => by rw [pow_succ, pow_mul, pow_fix h k, h]

private lemma orth_pow {p q : ZMod n} (hpq : p * q = 0) :
    ∀ m : ℕ, (p + q) ^ (m + 1) = p ^ (m + 1) + q ^ (m + 1)
  | 0 => by ring
  | (m + 1) => by
      have hp : p ^ (m + 1) * q = 0 := by
        rw [pow_succ, mul_assoc, hpq, mul_zero]
      have hq : q ^ (m + 1) * p = 0 := by
        rw [pow_succ, mul_assoc, mul_comm q p, hpq, mul_zero]
      calc (p + q) ^ (m + 2) = (p + q) ^ (m + 1) * (p + q) := by ring
        _ = (p ^ (m + 1) + q ^ (m + 1)) * (p + q) := by rw [orth_pow hpq m]
        _ = p ^ (m + 2) + p ^ (m + 1) * q + q ^ (m + 1) * p + q ^ (m + 2) := by ring
        _ = p ^ (m + 2) + q ^ (m + 2) := by rw [hp, hq]; ring

private lemma idem_pow {q : ZMod n} (hq : q * q = q) : ∀ m : ℕ, q ^ (m + 1) = q
  | 0 => by ring
  | (m + 1) => by rw [pow_succ, idem_pow hq m, hq]

/-- Every cycle, coprime or cocomposite, factors through one constant and two generator cycles. -/
private theorem factor (hn : 2 ≤ n) (u : Tup n) (hu : InCycle u) :
    ∃ A B C : Tup n, InConstantCycle A ∧ InGeneratorCycle B ∧ InGeneratorCycle C ∧
      u = prod3 A B C := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨L₀, hL₀pos, hL₀⟩ := hu
  obtain ⟨i₀, t, htpos, hsq⟩ := exists_square_period n
  have hmul : ∀ m : ℕ, step^[m * L₀] u = u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have h : (m + 1) * L₀ = m * L₀ + L₀ := by ring
        rw [h, Function.iterate_add_apply, hL₀, ih]
  set k : ℕ := L₀ * (i₀ + 3) with hkdef
  have hkge : i₀ + 3 ≤ k := by
    have : 1 * (i₀ + 3) ≤ L₀ * (i₀ + 3) := Nat.mul_le_mul_right _ hL₀pos
    simpa [hkdef] using this
  set L : ℕ := 4 * k with hLdef
  have hLu : step^[L] u = u := by
    have h : L = (4 * (i₀ + 3)) * L₀ := by rw [hLdef, hkdef]; ring
    rw [h, hmul]
  have hL3 : 3 ≤ L := by omega
  -- every corner is a `2 ^ k`-th power
  obtain ⟨W, hW⟩ := iter_four_pow u k
  have hWu : ∀ i : Idx, u i = W i ^ 2 ^ k := by
    intro i; rw [← hW i, ← hLdef, hLu]
  have hfix : ∀ z w : ZMod n, z = w ^ 2 ^ k → z ^ 2 ^ t = z := by
    intro z w hz
    have hkk : i₀ ≤ k := by omega
    have := hsq k hkk w
    rw [hz, ← pow_mul, ← pow_add]
    exact this
  have hufix : ∀ i : Idx, u i ^ 2 ^ t = u i := fun i => hfix _ _ (hWu i)
  set Q : ZMod n := prodAll u with hQdef
  have hQfix : Q ^ 2 ^ t = Q := by
    refine hfix _ (W 0 * W 1 * W 2 * W 3) ?_
    rw [hQdef]
    show u 0 * u 1 * u 2 * u 3 = (W 0 * W 1 * W 2 * W 3) ^ 2 ^ k
    rw [hWu 0, hWu 1, hWu 2, hWu 3, mul_pow, mul_pow, mul_pow]
  set D : ℕ := 2 ^ t - 1 with hDdef
  have hD1 : 1 ≤ D := by
    have : 2 ≤ 2 ^ t := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) htpos
    omega
  have hDsucc : D + 1 = 2 ^ t := by omega
  set ε : ZMod n := Q ^ D with hεdef
  have hQabs : ∀ m : ℕ, Q ^ (m + 1) * ε = Q ^ (m + 1) := by
    intro m
    rw [hεdef, ← pow_add, show m + 1 + D = m + (D + 1) by ring, hDsucc, pow_add, hQfix]
    exact (pow_succ Q m).symm
  have hεε : ε * ε = ε := by
    have := hQabs (D - 1)
    rwa [show D - 1 + 1 = D by omega] at this
  have hQD : ∀ j : ℕ, Q ^ ((j + 1) * D) = ε := by
    intro j
    induction j with
    | zero => simp [hεdef]
    | succ j ih =>
        rw [show (j + 1 + 1) * D = (j + 1) * D + D by ring, pow_add, ih, ← hεdef, hεε]
  -- the product of all corners divides every corner
  have hQdvd : ∀ i : Idx, ∃ z : ZMod n, u i = Q * z := by
    intro i
    set v : Tup n := step^[L - 3] u with hvdef
    have hstep : u = step^[3] v := by
      rw [hvdef, ← Function.iterate_add_apply, show 3 + (L - 3) = L by omega, hLu]
    have hQv : prodAll v = Q ^ 2 ^ (L - 3) := by rw [hvdef, prodAll_iter, hQdef]
    have hbig : ∃ z, u i = prodAll v * z := by
      rw [hstep]
      rcases idx_cases i with h | h | h | h <;> subst h <;> rw [iter_three] <;>
        simp only [show (0 : Idx) + 1 = 1 by decide, show (0 : Idx) + 2 = 2 by decide,
          show (0 : Idx) + 3 = 3 by decide, show (1 : Idx) + 1 = 2 by decide,
          show (1 : Idx) + 2 = 3 by decide, show (1 : Idx) + 3 = 0 by decide,
          show (2 : Idx) + 1 = 3 by decide, show (2 : Idx) + 2 = 0 by decide,
          show (2 : Idx) + 3 = 1 by decide, show (3 : Idx) + 1 = 0 by decide,
          show (3 : Idx) + 2 = 1 by decide, show (3 : Idx) + 3 = 2 by decide, prodAll]
      exacts [⟨v 1 ^ 2 * v 2 ^ 2, by ring⟩, ⟨v 2 ^ 2 * v 3 ^ 2, by ring⟩,
        ⟨v 3 ^ 2 * v 0 ^ 2, by ring⟩, ⟨v 0 ^ 2 * v 1 ^ 2, by ring⟩]
    obtain ⟨z, hz⟩ := hbig
    refine ⟨Q ^ (2 ^ (L - 3) - 1) * z, ?_⟩
    rw [hz, hQv, ← mul_assoc, ← pow_succ']
    congr 2
    have : 1 ≤ 2 ^ (L - 3) := Nat.one_le_two_pow
    omega
  have huε : ∀ i : Idx, u i * ε = u i := by
    intro i
    obtain ⟨z, hz⟩ := hQdvd i
    have h1 := hQabs 0
    rw [hz, mul_comm Q z, mul_assoc, show Q * ε = Q ^ (0 + 1) * ε by ring_nf, h1]
    ring
  -- opposite corners
  have hopp : ∀ w : Tup n, step w 0 * step w 2 = step w 1 * step w 3 := by
    intro w; rw [cross_zero_two, cross_one_three]
  have hprev : u = step (step^[L - 1] u) := by
    have h : step^[L - 1 + 1] u = step (step^[L - 1] u) :=
      Function.iterate_succ_apply' step (L - 1) u
    rw [← h, show L - 1 + 1 = L by omega, hLu]
  have hac : u 0 * u 2 = Q ^ 2 ^ (L - 1) := by
    conv_lhs => rw [hprev]
    rw [cross_zero_two, prodAll_iter, hQdef]
  have hbd : u 1 * u 3 = Q ^ 2 ^ (L - 1) := by
    conv_lhs => rw [hprev]
    rw [cross_one_three, prodAll_iter, hQdef]
  set e : ℕ := 2 ^ (L - 2) with hedef
  have he1 : 1 ≤ e := Nat.one_le_two_pow
  have hee : e + e = 2 ^ (L - 1) := by
    rw [hedef, ← two_mul, ← pow_succ', show L - 2 + 1 = L - 1 by omega]
  set α : ZMod n := Q ^ e with hαdef
  have hαsq : α * α = u 0 * u 2 := by rw [hαdef, ← pow_add, hee, hac]
  have hαε : α * ε = α := by
    have := hQabs (e - 1)
    rwa [show e - 1 + 1 = e by omega, ← hαdef] at this
  set s : ℕ := (e + 1) * D - e with hsdef
  have hs1 : 1 ≤ s := by
    have : e + 1 ≤ (e + 1) * D := Nat.le_mul_of_pos_right _ (by omega)
    omega
  set αinv : ZMod n := Q ^ s with hαidef
  have hαinvε : αinv * ε = αinv := by
    have := hQabs (s - 1)
    rwa [show s - 1 + 1 = s by omega, ← hαidef] at this
  have hαα : α * αinv = ε := by
    rw [hαdef, hαidef, ← pow_add, show e + s = (e + 1) * D by
      have : e + 1 ≤ (e + 1) * D := Nat.le_mul_of_pos_right _ (by omega)
      rw [hsdef]; omega]
    exact hQD e
  set w0 : ZMod n := u 1 * u 2 * u 3 * Q ^ (D - 1) with hw0def
  set w1 : ZMod n := u 0 * u 2 * u 3 * Q ^ (D - 1) with hw1def
  have hQpow : Q * Q ^ (D - 1) = ε := by
    rw [hεdef, ← pow_succ']
    congr 1
    omega
  have hu0w0 : u 0 * w0 = ε := by
    rw [hw0def, ← hQpow, hQdef, prodAll]; ring
  have hu1w1 : u 1 * w1 = ε := by
    rw [hw1def, ← hQpow, hQdef, prodAll]; ring
  -- the two units
  set x : ZMod n := u 1 * αinv + 1 - ε with hxdef
  set xi : ZMod n := α * w1 + 1 - ε with hxidef
  set y : ZMod n := u 0 * αinv + 1 - ε with hydef
  set yi : ZMod n := α * w0 + 1 - ε with hyidef
  have hmulunit : ∀ (c d : ZMod n), c * d = ε → c * ε = c →
      (c * αinv + 1 - ε) * (α * d + 1 - ε) = 1 := by
    intro c d hcd _
    have expand : (c * αinv + 1 - ε) * (α * d + 1 - ε)
        = (c * d) * (α * αinv) + c * (αinv - αinv * ε) + d * (α - α * ε)
          + (1 - 2 * ε + ε * ε) := by ring
    rw [expand, hcd, hαα, hεε, hαinvε, hαε]
    ring
  have hxxi : x * xi = 1 := by
    rw [hxdef, hxidef]; exact hmulunit (u 1) w1 hu1w1 (huε 1)
  have hyyi : y * yi = 1 := by
    rw [hydef, hyidef]; exact hmulunit (u 0) w0 hu0w0 (huε 0)
  set xu : (ZMod n)ˣ := ⟨x, xi, hxxi, by rw [mul_comm]; exact hxxi⟩ with hxudef
  set yu : (ZMod n)ˣ := ⟨y, yi, hyyi, by rw [mul_comm]; exact hyyi⟩ with hyudef
  have hxuval : (xu : ZMod n) = x := rfl
  have hxuinv : ((xu⁻¹ : (ZMod n)ˣ) : ZMod n) = xi := rfl
  have hyuval : (yu : ZMod n) = y := rfl
  have hyuinv : ((yu⁻¹ : (ZMod n)ˣ) : ZMod n) = yi := rfl
  -- the two units survive squaring `t` times
  have hqidem : (1 - ε) * (1 - ε) = 1 - ε := by
    have : (1 - ε) * (1 - ε) = 1 - 2 * ε + ε * ε := by ring
    rw [this, hεε]; ring
  have hsplit : ∀ c : ZMod n, c * ε = c → c ^ 2 ^ t = c →
      (c * αinv + 1 - ε) ^ 2 ^ t = c * αinv + 1 - ε := by
    intro c hcε hcfix
    have hpq : (c * αinv) * (1 - ε) = 0 := by
      have : (c * αinv) * (1 - ε) = c * (αinv - αinv * ε) := by ring
      rw [this, hαinvε]; ring
    obtain ⟨m, hm⟩ : ∃ m : ℕ, 2 ^ t = m + 1 := by
      refine ⟨2 ^ t - 1, ?_⟩
      have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
      omega
    have hsum : c * αinv + 1 - ε = (c * αinv) + (1 - ε) := by ring
    rw [hsum, hm, orth_pow hpq m, ← hm]
    have hαfix : αinv ^ 2 ^ t = αinv := by
      rw [hαidef, ← pow_mul, mul_comm, pow_mul, hQfix]
    rw [mul_pow, hcfix, hαfix, hm, idem_pow hqidem m]
  have hxfix : x ^ 2 ^ t = x := by rw [hxdef]; exact hsplit (u 1) (huε 1) (hufix 1)
  have hyfix : y ^ 2 ^ t = y := by rw [hydef]; exact hsplit (u 0) (huε 0) (hufix 0)
  have hxufix : xu ^ 2 ^ t = xu := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hxuval, hxfix]
  have hyufix : yu ^ 2 ^ t = yu := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hyuval, hyfix]
  have hgenper : ∀ z : (ZMod n)ˣ, z ^ 2 ^ t = z → step^[8 * t] (gen z) = gen z := by
    intro z hz
    rw [iter_gen_pow]
    congr 1
    have h16 : (16 : ℕ) ^ t = (2 ^ t) ^ 4 := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h16]
    exact pow_fix hz 3
  -- the three factors
  refine ⟨const α, gen xu, rot (gen yu), ⟨⟨t, htpos, ?_⟩, fun m => ⟨α ^ 2 ^ m, iter_const α m⟩⟩,
    ⟨⟨8 * t, by omega, hgenper xu hxufix⟩, ⟨0, xu, rfl⟩⟩,
    ⟨⟨8 * t, by omega, ?_⟩, ⟨2, yu⁻¹ ^ 2, ?_⟩⟩, ?_⟩
  · rw [iter_const]
    congr 1
    rw [hαdef, ← pow_mul, mul_comm, pow_mul, hQfix]
  · rw [iter_rot, hgenper yu hyufix]
  · rw [iter_rot]
    funext i
    have hgy : ∀ j : Idx, step^[2] (gen yu) j
        = gen yu j * gen yu (j + 1) ^ 2 * gen yu (j + 2) := fun j => iter_two _ j
    have hmi : (yu : ZMod n) * ((yu⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := yu.mul_inv
    have hinv2 : (((yu⁻¹ ^ 2 : (ZMod n)ˣ)⁻¹ : (ZMod n)ˣ) : ZMod n) = (yu : ZMod n) ^ 2 := by
      rw [← inv_pow, inv_inv, Units.val_pow_eq_pow_val]
    have hv2 : ((yu⁻¹ ^ 2 : (ZMod n)ˣ) : ZMod n) = ((yu⁻¹ : (ZMod n)ˣ) : ZMod n) ^ 2 :=
      Units.val_pow_eq_pow_val _ 2
    rcases idx_cases i with h | h | h | h <;> subst h <;>
      simp only [rot_zero, rot_one, rot_two, rot_three, hgy, gen_zero, gen_one, gen_two,
        gen_three, hinv2, hv2,
        show (0 : Idx) + 1 = 1 by decide, show (0 : Idx) + 2 = 2 by decide,
        show (1 : Idx) + 1 = 2 by decide, show (1 : Idx) + 2 = 3 by decide,
        show (2 : Idx) + 1 = 3 by decide, show (2 : Idx) + 2 = 0 by decide,
        show (3 : Idx) + 1 = 0 by decide, show (3 : Idx) + 2 = 1 by decide]
    · linear_combination hmi
    · ring
    · linear_combination hmi
    · ring
  · funext i
    have h0 : α * y = u 0 := by
      rw [hydef]
      calc α * (u 0 * αinv + 1 - ε) = u 0 * (α * αinv) + (α - α * ε) := by ring
        _ = u 0 * ε := by rw [hαα, hαε]; ring
        _ = u 0 := huε 0
    have h1 : α * x = u 1 := by
      rw [hxdef]
      calc α * (u 1 * αinv + 1 - ε) = u 1 * (α * αinv) + (α - α * ε) := by ring
        _ = u 1 * ε := by rw [hαα, hαε]; ring
        _ = u 1 := huε 1
    have h2 : α * yi = u 2 := by
      rw [hyidef]
      calc α * (α * w0 + 1 - ε) = (α * α) * w0 + (α - α * ε) := by ring
        _ = (u 0 * u 2) * w0 := by rw [hαsq, hαε]; ring
        _ = u 2 * (u 0 * w0) := by ring
        _ = u 2 := by rw [hu0w0]; exact huε 2
    have h3 : α * xi = u 3 := by
      rw [hxidef]
      calc α * (α * w1 + 1 - ε) = (α * α) * w1 + (α - α * ε) := by ring
        _ = (u 0 * u 2) * w1 := by rw [hαsq, hαε]; ring
        _ = (u 1 * u 3) * w1 := by rw [hac, ← hbd]
        _ = u 3 * (u 1 * w1) := by ring
        _ = u 3 := by rw [hu1w1]; exact huε 3
    rcases idx_cases i with h | h | h | h <;> subst h <;>
      simp only [prod3, const, rot_zero, rot_one, rot_two, rot_three, gen_zero, gen_one,
        gen_two, gen_three, hxuval, hxuinv, hyuval, hyuinv]
    · rw [← h0]; ring
    · rw [← h1]; ring
    · rw [← h2]; ring
    · rw [← h3]; ring

theorem result : claim := by
  intro n hn u hu _
  exact factor hn u hu

end D5.S3.Combinatorics.DucciModularCycleFactorization
