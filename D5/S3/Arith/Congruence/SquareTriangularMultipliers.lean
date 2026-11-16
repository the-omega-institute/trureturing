/- GID: D5/S3/Arith/Congruence/SquareTriangularMultipliers
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/SquareTriangularMultipliers
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Every natural index has a least positive square-and-triangular multiplier. -/
import Mathlib.NumberTheory.PellMatiyasevic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Positive square-and-triangular multipliers

The source is OEIS A400520 by Alex Ratushnyak, https://oeis.org/A400520.
The Pell orbit with parameter three supplies square triangular multiples of
every positive natural number. The final statement concerns the original
least-positive-multiplier predicate, including the index zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.SquareTriangularMultipliers

/-- Squares include zero and use natural square roots. -/
def Sq (x : ℕ) : Prop := ∃ s : ℕ, x = s ^ 2

/-- Triangular numbers include zero and use natural indices. -/
def Tri (x : ℕ) : Prop := ∃ t : ℕ, 2 * x = t * (t + 1)

/-- The two choices between the product and its successor are independent. -/
def P (n k : ℕ) : Prop :=
  (Sq (n * k) ∨ Sq (n * k + 1)) ∧ (Tri (n * k) ∨ Tri (n * k + 1))

/-- The source sequence, with the positive-multiplier convention and failure value. -/
noncomputable def a (n : ℕ) : ℤ := by
  classical
  exact if h : ∃ k : ℕ, 1 ≤ k ∧ P n k then (Nat.find h : ℤ) else -1

private def step (n : ℕ) (v : ZMod n × ZMod n) : ZMod n × ZMod n :=
  (3 * v.1 + 8 * v.2, v.1 + 3 * v.2)

private theorem step_injective (n : ℕ) : Function.Injective (step n) := by
  let inverse : ZMod n × ZMod n → ZMod n × ZMod n :=
    fun v => (3 * v.1 - 8 * v.2, -v.1 + 3 * v.2)
  apply Function.LeftInverse.injective (f := step n) (g := inverse)
  intro v
  ext <;> dsimp [inverse, step] <;> ring

private theorem reduced_orbit (n j : ℕ) :
    (step n)^[j] (1, 0) =
      ((Pell.xn (by decide : 1 < (3 : ℕ)) j : ZMod n),
       (Pell.yn (by decide : 1 < (3 : ℕ)) j : ZMod n)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hx : Pell.xn (by decide : 1 < (3 : ℕ)) (j + 1) =
        Pell.xn (by decide : 1 < (3 : ℕ)) j * 3 +
          8 * Pell.yn (by decide : 1 < (3 : ℕ)) j := rfl
    have hy : Pell.yn (by decide : 1 < (3 : ℕ)) (j + 1) =
        Pell.xn (by decide : 1 < (3 : ℕ)) j +
          Pell.yn (by decide : 1 < (3 : ℕ)) j * 3 := rfl
    rw [Function.iterate_succ_apply', ih]
    ext <;> simp only [step, hx, hy, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    all_goals ring

private theorem simultaneous_multiple (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, 1 ≤ k ∧ Sq (n * k) ∧ Tri (n * k) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hperiod := (step_injective n).mem_periodicPts (1, 0)
  rw [Function.mem_periodicPts] at hperiod
  obtain ⟨j, hj, hreturn⟩ := hperiod
  have hcoord : (Pell.yn (by decide : 1 < (3 : ℕ)) j : ZMod n) = 0 := by
    have heq := congrArg Prod.snd hreturn
    rw [reduced_orbit] at heq
    exact heq
  have hdvd : n ∣ Pell.yn (by decide : 1 < (3 : ℕ)) j :=
    (ZMod.natCast_eq_zero_iff _ _).mp hcoord
  let x := Pell.xn (by decide : 1 < (3 : ℕ)) j
  let y := Pell.yn (by decide : 1 < (3 : ℕ)) j
  have hy : 0 < y := lt_of_lt_of_le hj (Pell.yn_ge_n _ j)
  have hpell : x * x = 8 * y * y + 1 := by
    have h := Pell.pell_eqz (by decide : 1 < (3 : ℕ)) j
    change (x : ℤ) * x - 8 * y * y = 1 at h
    exact_mod_cast (show (x : ℤ) * x = 8 * y * y + 1 by linarith)
  have hodd : ∀ i, Pell.xn (by decide : 1 < (3 : ℕ)) i % 2 = 1 := by
    intro i
    induction i with
    | zero => decide
    | succ i ih =>
      rw [Pell.xn_succ]
      change (Pell.xn _ i * 3 + 8 * Pell.yn _ i) % 2 = 1
      omega
  obtain ⟨t, ht⟩ := (Nat.odd_iff.mpr (hodd j)).exists_bit1
  obtain ⟨q, hq⟩ := hdvd
  have hqpos : 0 < q := by
    by_contra h
    have : q = 0 := by omega
    rw [this, mul_zero] at hq
    exact (Nat.ne_of_gt hy) hq
  refine ⟨n * q ^ 2, by nlinarith, ?_, ?_⟩
  · refine ⟨y, ?_⟩
    dsimp [y]
    rw [hq]
    ring
  · refine ⟨t, ?_⟩
    have hxt : x = 2 * t + 1 := ht
    have hyt : 2 * (y * y) = t * (t + 1) := by nlinarith [hpell]
    rw [← hyt]
    dsimp [y]
    rw [hq]
    ring

private theorem witnesses (n : ℕ) : ∃ k : ℕ, 1 ≤ k ∧ P n k := by
  by_cases hn : n = 0
  · subst n
    exact ⟨1, le_rfl, Or.inl ⟨0, by simp⟩, Or.inl ⟨0, by simp⟩⟩
  · obtain ⟨k, hk, hs, ht⟩ := simultaneous_multiple n (Nat.pos_of_ne_zero hn)
    exact ⟨k, hk, Or.inl hs, Or.inl ht⟩

private theorem least_spec (n : ℕ) :
    0 < a n ∧ ∃ k : ℕ, 1 ≤ k ∧ P n k ∧ a n = (k : ℤ) ∧
      ∀ j : ℕ, 1 ≤ j → P n j → k ≤ j := by
  classical
  have h := witnesses n
  have hk := Nat.find_spec h
  have ha : a n = (Nat.find h : ℤ) := dif_pos h
  constructor
  · rw [ha]
    exact_mod_cast (show 0 < Nat.find h by omega)
  · exact ⟨Nat.find h, hk.1, hk.2, ha, fun j hj hp => Nat.find_min' h ⟨hj, hp⟩⟩

private theorem least_one (n : ℕ) (h : P n 1) : a n = 1 := by
  obtain ⟨_, k, hk, _, ha, hmin⟩ := least_spec n
  have hkone : k = 1 := by have := hmin 1 le_rfl h; omega
  simpa [hkone] using ha

/-- A400520 is positive at every natural index, with its exact least-witness
semantics; the two initial values are both one. -/
theorem result :
    (∀ n : ℕ, 0 < a n ∧ ∃ k : ℕ, 1 ≤ k ∧ P n k ∧ a n = (k : ℤ) ∧
      ∀ j : ℕ, 1 ≤ j → P n j → k ≤ j) ∧ a 0 = 1 ∧ a 1 = 1 := by
  refine ⟨least_spec, least_one 0 ?_, least_one 1 ?_⟩
  · exact ⟨Or.inl ⟨0, by simp⟩, Or.inl ⟨0, by simp⟩⟩
  · exact ⟨Or.inl ⟨1, by simp⟩, Or.inl ⟨1, by simp⟩⟩

end D5.S3.Arith.Congruence.SquareTriangularMultipliers
