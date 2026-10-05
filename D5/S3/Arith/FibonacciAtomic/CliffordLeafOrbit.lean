/- GID: D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/CliffordLeafOrbit
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact six-phase fibers of the actual Clifford leaf product. -/

import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.Arith.FibonacciAtomic.CliffordLeafOrbit

open GenealogicalFiberTransport (Source substitution composition)
open GraftAffineClosure (atomicBlock)

/-- The quadratic form on the ordered pair of real coordinates. -/
noncomputable def Q : QuadraticForm ℝ (ℝ × ℝ) :=
  QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ) +
  QuadraticMap.linMulLin (LinearMap.fst ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ) -
  QuadraticMap.linMulLin (LinearMap.snd ℝ ℝ ℝ) (LinearMap.snd ℝ ℝ ℝ)

local notation "C" => CliffordAlgebra Q
local notation "A" => CliffordAlgebra.ι Q (1, 0)
local notation "B" => CliffordAlgebra.ι Q (0, 1)
local notation "α" => (FreeMagma.of true : Source)
local notation "β" => (FreeMagma.of false : Source)
local notation "T" => (fun j : ℕ => substitution^[j] α)

/-- Ordered leaf multiplication in the actual Clifford algebra. -/
noncomputable def E : Source →ₙ* C := FreeMagma.lift fun b => if b then A else B

/-- Clifford observations of the canonical substituted source. -/
noncomputable def X (j : ℕ) : C := E (T j)

/-- The six algebra elements in chronological order. -/
noncomputable def phases : Fin 6 → C := ![A, B, B * A, A + B, -B, A * B]

/-- A reader receives only the algebra observation. -/
def Factors {Y : Type*} (g : ℕ → Y) : Prop :=
  ∃ f : Set.range X → Y, ∀ j, f ⟨X j, ⟨j, rfl⟩⟩ = g j

/-- Exact observation fibers, source composition, and autonomous canonical successor. -/
theorem result :
    (∀ j, composition (T j) = atomicBlock j) ∧
    (∀ j, X j = phases ⟨j % 6, Nat.mod_lt j (by decide)⟩) ∧
    (∀ j k, X j = X k ↔ j % 6 = k % 6) ∧
    (∀ (Y : Type u) (g : ℕ → Y), Factors g ↔ ∀ j, g (j + 6) = g j) ∧
    Factors (fun j => X (j + 1)) := by
  classical
  have aa : A * A = 1 := by
    rw [CliffordAlgebra.ι_sq_scalar, show Q (1, 0) = 1 by
      norm_num [Q, QuadraticMap.linMulLin_apply], map_one]
  have bb : B * B = -1 := by
    rw [CliffordAlgebra.ι_sq_scalar, show Q (0, 1) = -1 by
      norm_num [Q, QuadraticMap.linMulLin_apply], map_neg, map_one]
  have swap : A * B + B * A = 1 := by
    have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q) (1, 0) (0, 1)
    rw [show QuadraticMap.polar (fun v => Q v) (1, 0) (0, 1) = 1 by
      norm_num [QuadraticMap.polar, Q, QuadraticMap.linMulLin_apply], map_one] at h
    exact h
  have ba : B * A = 1 - A * B := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using swap
  have aba : A * B * A = A - B := by
    rw [mul_assoc, ba, mul_sub, mul_one, ← mul_assoc, aa, one_mul]
  have bab : B * A * B = A + B := by
    rw [ba, sub_mul, one_mul, mul_assoc, bb, mul_neg_one]
    abel
  have recurrence (j : ℕ) : X (j + 2) = X (j + 1) * X j := by
    have tree (n : ℕ) : T (n + 2) = FreeMagma.mul (T (n + 1)) (T n) := by
      induction n with
      | zero => rfl
      | succ n ih =>
        change substitution^[n + 1 + 2] α = _
        rw [show n + 1 + 2 = (n + 2) + 1 by omega, Function.iterate_succ_apply']
        change substitution (T (n + 2)) = _
        conv_lhs => rw [ih]
        change substitution (T (n + 1)) * substitution (T n) = _
        dsimp only
        rw [Function.iterate_succ_apply' substitution (n + 1) α,
          Function.iterate_succ_apply' substitution n α]
        rfl
    rw [X, tree]
    exact E.map_mul _ _
  have phase_rec (i : Fin 6) :
      phases ⟨(i.val + 2) % 6, Nat.mod_lt _ (by decide)⟩ =
        phases ⟨(i.val + 1) % 6, Nat.mod_lt _ (by decide)⟩ * phases i := by
    fin_cases i
    · rfl
    · change A + B = B * A * B
      exact bab.symm
    · change -B = (A + B) * (B * A)
      rw [add_mul, ← mul_assoc, aba, ← mul_assoc B B A, bb, neg_one_mul]
      abel
    · change A * B = -B * (A + B)
      rw [neg_mul, mul_add, bb, ba]
      noncomm_ring
    · change A = (A * B) * -B
      rw [mul_neg, mul_assoc, bb, mul_neg_one, neg_neg]
    · change B = A * (A * B)
      rw [← mul_assoc, aa, one_mul]
  have orbit (j : ℕ) : X j = phases ⟨j % 6, Nat.mod_lt _ (by decide)⟩ ∧
      X (j + 1) = phases ⟨(j + 1) % 6, Nat.mod_lt _ (by decide)⟩ := by
    induction j with
    | zero => exact ⟨rfl, rfl⟩
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [show j + 1 + 1 = j + 2 by omega, recurrence, ih.1, ih.2]
      have h := phase_rec ⟨j % 6, Nat.mod_lt _ (by decide)⟩
      simpa only [Nat.add_mod, Nat.mod_mod] using h.symm
  let m : (ℝ × ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    (LinearMap.fst ℝ ℝ ℝ).smulRight !![1, 0; 0, -1] +
    (LinearMap.snd ℝ ℝ ℝ).smulRight !![1/2, 1; -5/4, -1/2]
  have square (v : ℝ × ℝ) : m v * m v = algebraMap ℝ _ (Q v) := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [m, Q, QuadraticMap.linMulLin_apply, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.algebraMap_eq_diagonal] <;> ring
  let rep : C →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := CliffordAlgebra.lift Q ⟨m, square⟩
  have images (i : Fin 6) : rep (phases i) =
      ![!![1, 0; 0, -1], !![1/2, 1; -5/4, -1/2],
        !![1/2, -1; -5/4, 1/2], !![3/2, 1; -5/4, -3/2],
        !![-1/2, -1; 5/4, 1/2], !![1/2, 1; 5/4, 1/2]] i := by
    fin_cases i
    all_goals simp only [phases, map_add, map_neg, map_mul, rep,
      CliffordAlgebra.lift_ι_apply]
    all_goals ext r s
    all_goals fin_cases r <;> fin_cases s <;>
      norm_num [m, Matrix.mul_apply, Fin.sum_univ_two]
  have distinct : Function.Injective phases := by
    intro i k h
    have h' := congrArg rep h
    rw [images, images] at h'
    have h00 := congrArg (fun z : Matrix (Fin 2) (Fin 2) ℝ => z 0 0) h'
    have h01 := congrArg (fun z : Matrix (Fin 2) (Fin 2) ℝ => z 0 1) h'
    have h10 := congrArg (fun z : Matrix (Fin 2) (Fin 2) ℝ => z 1 0) h'
    fin_cases i
    all_goals fin_cases k
    all_goals try norm_num at h00
    all_goals try norm_num at h01
    all_goals try norm_num at h10
    all_goals rfl
  have fibers (j k : ℕ) : X j = X k ↔ j % 6 = k % 6 := by
    rw [(orbit j).1, (orbit k).1, distinct.eq_iff, Fin.mk.injEq]
  have periodic (j : ℕ) : X (j + 6) = X j := (fibers _ _).mpr (by omega)
  have criterion (Y : Type u) (g : ℕ → Y) : Factors g ↔ ∀ j, g (j + 6) = g j := by
    constructor
    · rintro ⟨f, hf⟩ j
      rw [← hf (j + 6), ← hf j]
      congr 1
      exact Subtype.ext (periodic j)
    · intro hg
      have reduce := Function.Periodic.map_mod_nat (show Function.Periodic g 6 from hg)
      refine ⟨fun x => g ((Classical.choose x.property) % 6), ?_⟩
      intro j
      have h := (fibers (Classical.choose (show X j ∈ Set.range X from ⟨j, rfl⟩)) j).mp
        (Classical.choose_spec (show X j ∈ Set.range X from ⟨j, rfl⟩))
      change g _ = g j
      rw [h, reduce j]
  refine ⟨?_, fun j => (orbit j).1, fibers, criterion, ?_⟩
  · intro j
    exact (GenealogicalFiberTransport.fiberMap (1, 0) j ⟨α, rfl⟩).property
  · refine ⟨fun x => X (Classical.choose x.property + 1), ?_⟩
    intro j
    apply (fibers _ _).mpr
    have h := (fibers (Classical.choose (show X j ∈ Set.range X from ⟨j, rfl⟩)) j).mp
      (Classical.choose_spec (show X j ∈ Set.range X from ⟨j, rfl⟩))
    omega

end D5.S3.Arith.FibonacciAtomic.CliffordLeafOrbit
