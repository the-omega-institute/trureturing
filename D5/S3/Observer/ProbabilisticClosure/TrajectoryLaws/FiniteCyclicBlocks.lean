/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteCyclicBlocks
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteCyclicBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual primitive stochastic phase blocks for genuine finite closed-class periods. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteGenuinePeriods

open Finset Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteCyclicBlocks
open FiniteClosedClasses FiniteGenuinePeriods
noncomputable section
universe u
variable {X : Type u} [Fintype X] [DecidableEq X]
variable {P : Matrix X X ℝ} {C : ClosedClass P}

/-- An actual cyclic phase inside the actual original closed class. -/
abbrev Phase (K : ClassPeriods P C)
    (j : ZMod (period (restriction P C.val) K.base)) := {x : C.val // K.phase x = j}

/-- The genuine-period power, restricted to the actual phase subtype. -/
def block (K : ClassPeriods P C)
    (j : ZMod (period (restriction P C.val) K.base)) : Matrix (Phase K j) (Phase K j) ℝ :=
  ((restriction P C.val) ^ period (restriction P C.val) K.base).submatrix
    Subtype.val Subtype.val

private theorem block_nonempty (K : ClassPeriods P C)
    (j : ZMod (period (restriction P C.val) K.base)) : Nonempty (Phase K j) := by
  obtain ⟨x, hx⟩ := K.onto j
  exact ⟨⟨x, hx⟩⟩

private theorem off_phase_zero (hP : P ∈ rowStochastic ℝ X) (K : ClassPeriods P C)
    (j : ZMod (period (restriction P C.val) K.base)) (n : ℕ)
    (x : Phase K j) (y : C.val) (hy : K.phase y ≠ j) :
    (restriction P C.val ^ (period (restriction P C.val) K.base * n)) x.val y = 0 := by
  have hS := actual_structure P hP
  apply le_antisymm _ (Matrix.pow_apply_nonneg (hS.class_stochastic C).1 _ _ _)
  apply le_of_not_gt
  intro hp
  have he := K.path_residue _ x.val y ((hS.class_powers C _ x.val y) ▸ hp)
  simp only [Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, x.property] at he
  exact hy he.symm

private theorem block_stochastic (hP : P ∈ rowStochastic ℝ X)
    (K : ClassPeriods P C) (j : ZMod (period (restriction P C.val) K.base)) :
    block K j ∈ rowStochastic ℝ (Phase K j) := by
  classical
  have hS := actual_structure P hP
  have hs := (rowStochastic ℝ C.val).pow_mem (hS.class_stochastic C)
    (period (restriction P C.val) K.base)
  apply mem_rowStochastic_iff_sum.mpr
  refine ⟨fun x y => hs.1 x.val y.val, fun x => ?_⟩
  change ∑ y : Phase K j, (restriction P C.val ^ period (restriction P C.val) K.base) x.val y.val = 1
  rw [← Finset.sum_subtype (p := fun y : C.val => K.phase y = j)
    (univ.filter (fun y => K.phase y = j)) (fun _ => by simp), sum_filter]
  calc
    _ = ∑ y : C.val, (restriction P C.val ^ period (restriction P C.val) K.base) x.val y := by
      apply sum_congr rfl
      intro y _
      by_cases hy : K.phase y = j
      · simp [hy]
      · simp [hy, show (restriction P C.val ^ period (restriction P C.val) K.base) x.val y = 0 by
          simpa using off_phase_zero hP K j 1 x y hy]
    _ = 1 := sum_row_of_mem_rowStochastic hs x.val

private theorem block_powers (hP : P ∈ rowStochastic ℝ X)
    (K : ClassPeriods P C) (j : ZMod (period (restriction P C.val) K.base))
    (n : ℕ) (x y : Phase K j) :
    (block K j ^ n) x y = (P ^ (period (restriction P C.val) K.base * n)) x.val.val y.val.val := by
  classical
  have hS := actual_structure P hP
  suffices he : (block K j ^ n) x y =
      (restriction P C.val ^ (period (restriction P C.val) K.base * n)) x.val y.val by
    exact he.trans (hS.class_powers C _ _ _)
  induction n generalizing x y with
  | zero =>
    by_cases he : x = y
    · subst y; simp
    · have hv : x.val ≠ y.val := fun h => he (Subtype.ext h)
      simp [he, hv]
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ, pow_add, Matrix.mul_apply, Matrix.mul_apply]
    calc
      ∑ k : Phase K j, (block K j ^ n) x k * block K j k y =
          ∑ k : Phase K j,
            (restriction P C.val ^ (period (restriction P C.val) K.base * n)) x.val k.val *
            (restriction P C.val ^ period (restriction P C.val) K.base) k.val y.val := by
        apply sum_congr rfl
        intro k _
        rw [ih]
        rfl
      _ = ∑ k : C.val,
            (restriction P C.val ^ (period (restriction P C.val) K.base * n)) x.val k *
            (restriction P C.val ^ period (restriction P C.val) K.base) k y.val := by
        rw [← Finset.sum_subtype (p := fun k : C.val => K.phase k = j)
          (univ.filter (fun k => K.phase k = j)) (fun _ => by simp)
          (fun k => (restriction P C.val ^ (period (restriction P C.val) K.base * n)) x.val k *
            (restriction P C.val ^ period (restriction P C.val) K.base) k y.val), sum_filter]
        apply sum_congr rfl
        intro k _
        by_cases hk : K.phase k = j
        · simp [hk]
        · simp [hk, off_phase_zero hP K j n x k hk]

private theorem block_primitive (hP : P ∈ rowStochastic ℝ X)
    (K : ClassPeriods P C) (j : ZMod (period (restriction P C.val) K.base)) :
    Matrix.IsPrimitive (block K j) := by
  classical
  let N : Phase K j × Phase K j → ℕ := fun xy => (K.eventual xy.1.val xy.2.val).choose
  let M : ℕ := (univ : Finset (Phase K j × Phase K j)).sup N
  let p := period (restriction P C.val) K.base
  refine ⟨(block_stochastic hP K j).1, M + 1, Nat.succ_pos _, fun x y => ?_⟩
  rw [block_powers hP K j]
  apply (K.eventual x.val y.val).choose_spec
  · have hm : N (x, y) ≤ M := le_sup (f := N) (mem_univ (x, y))
    have hp : 0 < p := K.positive
    change N (x, y) ≤ p * (M + 1)
    have he : M + 1 ≤ p * (M + 1) := Nat.le_mul_of_pos_left _ hp
    omega
  · simp only [Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, x.property, y.property]

/-- These fields describe the actual ambient powers, not an independent phase matrix. -/
structure Blocks (K : ClassPeriods P C) : Prop where
  nonempty : ∀ j, Nonempty (Phase K j)
  stochastic : ∀ j, block K j ∈ rowStochastic ℝ (Phase K j)
  primitive : ∀ j, Matrix.IsPrimitive (block K j)
  powers : ∀ j n (x y : Phase K j),
    (block K j ^ n) x y = (P ^ (period (restriction P C.val) K.base * n)) x.val.val y.val.val
  other_class_zero : ∀ D : ClosedClass P, D ≠ C → ∀ n (x : D.val) (y : C.val),
    (P ^ n) x.val y.val = 0

/-- Actual genuine cyclic blocks are nonempty, row stochastic and primitive, with exact ambient powers. -/
theorem actual_blocks (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X)
    (C : ClosedClass P) : ∃ K : ClassPeriods P C, Blocks K := by
  obtain ⟨K⟩ := actual_periods P hP C
  have hS := actual_structure P hP
  refine ⟨K, {
    nonempty := block_nonempty K
    stochastic := block_stochastic hP K
    primitive := block_primitive hP K
    powers := block_powers hP K
    other_class_zero := ?_ }⟩
  intro D hDC n x y
  apply hS.class_no_exit D n x y.val
  intro hy
  exact (Finset.disjoint_left.mp (hS.disjoint D C hDC)) hy y.property

end
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteCyclicBlocks
