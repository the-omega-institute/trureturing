module

public import OmegaMath.Combinatorics.Turnpike.PrunedTriangleLP
public import Mathlib.Data.Fin.VecNotation

/-! Omega original.
# Exact singleton-cut certificate

The integer assignment and every cut shard form the finite certificate consumed
by the realizable pruned-projection obstruction. Indices are zero-based.
-/
@[expose] public section
namespace Omega.Turnpike.PrunedSingletonCutCertificate
open Omega.Turnpike
open scoped BigOperators
noncomputable section

def values : Fin 20 → ℕ := ![22, 21, 20, 19, 17, 16, 15, 14, 13, 12, 11, 10, 9, 8, 6, 5, 4, 3, 2, 1]
def y : Fin 20 → ℝ := fun q => values q
def μ : Fin 20 → ℕ := ![1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 2, 2, 1, 2, 3, 4]
def numerator (e : Interval 9) (q : Fin 20) : ℕ :=
  match e.1.1.val, e.1.2.val with
  | 0, 1 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 10, 20] q
  | 0, 2 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 12, 0, 0, 12, 0] q
  | 0, 3 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 19, 22, 8, 0, 0, 12, 0, 0] q
  | 0, 4 => ![0, 0, 0, 0, 0, 0, 0, 2, 8, 4, 10, 31, 7, 0, 0, 0, 0, 0, 0, 0] q
  | 0, 5 => ![0, 0, 0, 32, 0, 8, 0, 10, 10, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 0, 6 => ![0, 0, 32, 0, 10, 16, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 0, 7 => ![0, 42, 8, 0, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 0, 8 => ![62, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 1, 2 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 8, 0, 44] q
  | 1, 3 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 8, 9, 0, 11, 13, 11, 9] q
  | 1, 4 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 10, 11, 0, 0, 23, 7, 0, 0, 0] q
  | 1, 5 => ![0, 0, 0, 0, 0, 0, 8, 32, 10, 0, 10, 2, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 1, 6 => ![0, 0, 0, 0, 0, 4, 50, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 1, 7 => ![0, 0, 0, 18, 0, 40, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 1, 8 => ![0, 20, 10, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 2, 3 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 22, 19, 20] q
  | 2, 4 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 6, 0, 9, 6, 26, 7, 0, 0] q
  | 2, 5 => ![0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 12, 6, 12, 0, 0, 0, 0, 0, 0, 0] q
  | 2, 6 => ![0, 0, 0, 0, 0, 0, 4, 36, 0, 4, 18, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 2, 7 => ![0, 0, 0, 0, 0, 6, 50, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 2, 8 => ![0, 0, 12, 0, 12, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 3, 4 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 4, 11, 0, 2, 17, 18] q
  | 3, 5 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 27, 0, 0, 0, 7, 0, 0, 3, 0] q
  | 3, 6 => ![0, 0, 0, 0, 0, 0, 0, 0, 8, 12, 23, 8, 11, 0, 0, 0, 0, 0, 0, 0] q
  | 3, 7 => ![0, 0, 0, 0, 0, 0, 8, 8, 26, 11, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 3, 8 => ![0, 0, 0, 12, 0, 8, 0, 22, 19, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] q
  | 4, 5 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 0, 1, 5, 0, 6, 18, 1] q
  | 4, 6 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 25, 0, 0, 16, 0, 0, 8, 6, 0] q
  | 4, 7 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 7, 5, 0, 2, 0, 6, 2, 2, 0] q
  | 4, 8 => ![0, 0, 0, 0, 0, 0, 0, 0, 7, 31, 10, 4, 8, 2, 0, 0, 0, 0, 0, 0] q
  | 5, 6 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 6, 10, 44] q
  | 5, 7 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 10, 6, 0, 0, 0, 34, 10] q
  | 5, 8 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 10, 10, 8, 0, 0, 32, 0, 0] q
  | 6, 7 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 6, 6, 4, 40] q
  | 6, 8 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 16, 10, 0, 0, 32, 0] q
  | 7, 8 => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 8, 0, 0, 8, 42] q
  | _, _ => 0
def assignment : Assignment 9 20 := fun e q => (numerator e q : ℝ) / 62
def inverse (z : ℤ) : Fin 20 :=
  match z with
  | 22 => 0 | 21 => 1 | 20 => 2 | 19 => 3 | 17 => 4 | 16 => 5
  | 15 => 6 | 14 => 7 | 13 => 8 | 12 => 9 | 11 => 10 | 10 => 11
  | 9 => 12 | 8 => 13 | 6 => 14 | 5 => 15 | 4 => 16 | 3 => 17
  | 2 => 18 | 1 => 19 | _ => 0
def candidate (u v : Fin 3) (a b : Fin 20) : Fin 20 × Fin 20 × Fin 20 :=
  if u = 0 then
    if v = 1 then (a,b,inverse ((values a : ℤ) + values b))
    else (a,inverse ((values b : ℤ) - values a),b)
  else (inverse ((values b : ℤ) - values a),a,b)
def CutCheck (τ : Triangle 9) (u v w : Fin 3) (a b : Fin 20) : Prop :=
  numerator (edge τ u) a + numerator (edge τ v) b ≤ 62 ∨
  let r := candidate u v a b
  values r.1 + values r.2.1 = values r.2.2 ∧
  (r.1 ≠ r.2.1 ∨ 2 ≤ μ r.1) ∧ ProductAllowed μ τ r ∧
  coordinate u r = a ∧ coordinate v r = b ∧
  numerator (edge τ u) a + numerator (edge τ v) b ≤
    62 + numerator (edge τ w) (coordinate w r)
private theorem cut_012_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,2),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_012_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,2),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_012_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,2),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_013_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,3),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_013_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,3),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_013_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,3),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_014_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_014_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_014_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_015_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_015_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_015_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_016_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_016_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_016_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_017_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_017_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_017_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_018_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_018_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_018_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,1,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_023_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,3),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_023_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,3),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_023_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,3),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_024_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_024_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_024_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_025_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_025_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_025_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_026_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_026_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_026_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_027_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_027_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_027_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_028_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_028_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_028_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,2,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_034_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_034_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_034_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_035_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_035_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_035_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_036_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_036_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_036_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_037_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_037_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_037_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_038_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_038_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_038_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,3,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_045_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_045_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_045_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_046_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_046_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_046_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_047_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_047_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_047_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_048_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_048_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_048_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_056_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_056_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_056_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_057_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_057_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_057_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_058_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_058_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_058_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_067_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_067_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_067_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_068_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_068_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_068_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_078_01 : ∀ a b : Fin 20,
    CutCheck ⟨(0,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_078_02 : ∀ a b : Fin 20,
    CutCheck ⟨(0,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_078_12 : ∀ a b : Fin 20,
    CutCheck ⟨(0,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_123_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,3),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_123_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,3),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_123_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,3),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_124_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_124_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_124_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_125_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_125_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_125_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_126_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_126_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_126_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_127_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_127_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_127_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_128_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_128_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_128_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,2,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_134_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_134_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_134_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_135_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_135_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_135_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_136_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_136_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_136_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_137_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_137_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_137_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_138_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_138_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_138_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,3,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_145_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_145_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_145_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_146_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_146_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_146_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_147_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_147_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_147_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_148_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_148_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_148_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_156_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_156_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_156_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_157_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_157_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_157_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_158_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_158_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_158_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_167_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_167_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_167_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_168_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_168_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_168_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_178_01 : ∀ a b : Fin 20,
    CutCheck ⟨(1,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_178_02 : ∀ a b : Fin 20,
    CutCheck ⟨(1,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_178_12 : ∀ a b : Fin 20,
    CutCheck ⟨(1,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_234_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,4),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_234_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,4),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_234_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,4),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_235_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_235_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_235_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_236_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_236_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_236_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_237_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_237_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_237_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_238_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_238_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_238_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,3,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_245_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_245_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_245_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_246_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_246_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_246_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_247_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_247_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_247_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_248_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_248_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_248_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_256_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_256_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_256_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_257_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_257_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_257_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_258_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_258_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_258_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_267_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_267_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_267_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_268_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_268_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_268_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_278_01 : ∀ a b : Fin 20,
    CutCheck ⟨(2,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_278_02 : ∀ a b : Fin 20,
    CutCheck ⟨(2,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_278_12 : ∀ a b : Fin 20,
    CutCheck ⟨(2,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_345_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,5),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_345_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,5),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_345_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,5),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_346_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_346_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_346_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_347_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_347_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_347_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_348_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_348_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_348_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,4,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_356_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_356_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_356_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_357_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_357_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_357_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_358_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_358_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_358_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_367_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_367_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_367_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_368_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_368_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_368_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_378_01 : ∀ a b : Fin 20,
    CutCheck ⟨(3,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_378_02 : ∀ a b : Fin 20,
    CutCheck ⟨(3,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_378_12 : ∀ a b : Fin 20,
    CutCheck ⟨(3,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_456_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,6),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_456_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,6),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_456_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,6),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_457_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_457_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_457_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_458_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_458_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_458_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,5,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_467_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_467_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_467_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_468_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_468_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_468_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_478_01 : ∀ a b : Fin 20,
    CutCheck ⟨(4,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_478_02 : ∀ a b : Fin 20,
    CutCheck ⟨(4,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_478_12 : ∀ a b : Fin 20,
    CutCheck ⟨(4,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_567_01 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,7),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_567_02 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,7),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_567_12 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,7),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_568_01 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_568_02 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_568_12 : ∀ a b : Fin 20,
    CutCheck ⟨(5,6,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_578_01 : ∀ a b : Fin 20,
    CutCheck ⟨(5,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_578_02 : ∀ a b : Fin 20,
    CutCheck ⟨(5,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_578_12 : ∀ a b : Fin 20,
    CutCheck ⟨(5,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_678_01 : ∀ a b : Fin 20,
    CutCheck ⟨(6,7,8),by decide⟩ 0 1 2 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_678_02 : ∀ a b : Fin 20,
    CutCheck ⟨(6,7,8),by decide⟩ 0 2 1 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel
private theorem cut_678_12 : ∀ a b : Fin 20,
    CutCheck ⟨(6,7,8),by decide⟩ 1 2 0 a b := by
  unfold CutCheck ProductAllowed RankAllowed
  decide +kernel

private def triangleCover : List (Triangle 9) :=
  [⟨(0,1,2),by decide⟩,
   ⟨(0,1,3),by decide⟩,
   ⟨(0,1,4),by decide⟩,
   ⟨(0,1,5),by decide⟩,
   ⟨(0,1,6),by decide⟩,
   ⟨(0,1,7),by decide⟩,
   ⟨(0,1,8),by decide⟩,
   ⟨(0,2,3),by decide⟩,
   ⟨(0,2,4),by decide⟩,
   ⟨(0,2,5),by decide⟩,
   ⟨(0,2,6),by decide⟩,
   ⟨(0,2,7),by decide⟩,
   ⟨(0,2,8),by decide⟩,
   ⟨(0,3,4),by decide⟩,
   ⟨(0,3,5),by decide⟩,
   ⟨(0,3,6),by decide⟩,
   ⟨(0,3,7),by decide⟩,
   ⟨(0,3,8),by decide⟩,
   ⟨(0,4,5),by decide⟩,
   ⟨(0,4,6),by decide⟩,
   ⟨(0,4,7),by decide⟩,
   ⟨(0,4,8),by decide⟩,
   ⟨(0,5,6),by decide⟩,
   ⟨(0,5,7),by decide⟩,
   ⟨(0,5,8),by decide⟩,
   ⟨(0,6,7),by decide⟩,
   ⟨(0,6,8),by decide⟩,
   ⟨(0,7,8),by decide⟩,
   ⟨(1,2,3),by decide⟩,
   ⟨(1,2,4),by decide⟩,
   ⟨(1,2,5),by decide⟩,
   ⟨(1,2,6),by decide⟩,
   ⟨(1,2,7),by decide⟩,
   ⟨(1,2,8),by decide⟩,
   ⟨(1,3,4),by decide⟩,
   ⟨(1,3,5),by decide⟩,
   ⟨(1,3,6),by decide⟩,
   ⟨(1,3,7),by decide⟩,
   ⟨(1,3,8),by decide⟩,
   ⟨(1,4,5),by decide⟩,
   ⟨(1,4,6),by decide⟩,
   ⟨(1,4,7),by decide⟩,
   ⟨(1,4,8),by decide⟩,
   ⟨(1,5,6),by decide⟩,
   ⟨(1,5,7),by decide⟩,
   ⟨(1,5,8),by decide⟩,
   ⟨(1,6,7),by decide⟩,
   ⟨(1,6,8),by decide⟩,
   ⟨(1,7,8),by decide⟩,
   ⟨(2,3,4),by decide⟩,
   ⟨(2,3,5),by decide⟩,
   ⟨(2,3,6),by decide⟩,
   ⟨(2,3,7),by decide⟩,
   ⟨(2,3,8),by decide⟩,
   ⟨(2,4,5),by decide⟩,
   ⟨(2,4,6),by decide⟩,
   ⟨(2,4,7),by decide⟩,
   ⟨(2,4,8),by decide⟩,
   ⟨(2,5,6),by decide⟩,
   ⟨(2,5,7),by decide⟩,
   ⟨(2,5,8),by decide⟩,
   ⟨(2,6,7),by decide⟩,
   ⟨(2,6,8),by decide⟩,
   ⟨(2,7,8),by decide⟩,
   ⟨(3,4,5),by decide⟩,
   ⟨(3,4,6),by decide⟩,
   ⟨(3,4,7),by decide⟩,
   ⟨(3,4,8),by decide⟩,
   ⟨(3,5,6),by decide⟩,
   ⟨(3,5,7),by decide⟩,
   ⟨(3,5,8),by decide⟩,
   ⟨(3,6,7),by decide⟩,
   ⟨(3,6,8),by decide⟩,
   ⟨(3,7,8),by decide⟩,
   ⟨(4,5,6),by decide⟩,
   ⟨(4,5,7),by decide⟩,
   ⟨(4,5,8),by decide⟩,
   ⟨(4,6,7),by decide⟩,
   ⟨(4,6,8),by decide⟩,
   ⟨(4,7,8),by decide⟩,
   ⟨(5,6,7),by decide⟩,
   ⟨(5,6,8),by decide⟩,
   ⟨(5,7,8),by decide⟩,
   ⟨(6,7,8),by decide⟩]

private theorem triangleCovered (τ : Triangle 9) : τ ∈ triangleCover := by
  revert τ
  decide +kernel

private theorem cuts_01 : ∀ τ ∈ triangleCover, ∀ a b : Fin 20,
    CutCheck τ 0 1 2 a b := by
  simp only [triangleCover, List.forall_mem_cons]
  exact ⟨cut_012_01,
    cut_013_01,
    cut_014_01,
    cut_015_01,
    cut_016_01,
    cut_017_01,
    cut_018_01,
    cut_023_01,
    cut_024_01,
    cut_025_01,
    cut_026_01,
    cut_027_01,
    cut_028_01,
    cut_034_01,
    cut_035_01,
    cut_036_01,
    cut_037_01,
    cut_038_01,
    cut_045_01,
    cut_046_01,
    cut_047_01,
    cut_048_01,
    cut_056_01,
    cut_057_01,
    cut_058_01,
    cut_067_01,
    cut_068_01,
    cut_078_01,
    cut_123_01,
    cut_124_01,
    cut_125_01,
    cut_126_01,
    cut_127_01,
    cut_128_01,
    cut_134_01,
    cut_135_01,
    cut_136_01,
    cut_137_01,
    cut_138_01,
    cut_145_01,
    cut_146_01,
    cut_147_01,
    cut_148_01,
    cut_156_01,
    cut_157_01,
    cut_158_01,
    cut_167_01,
    cut_168_01,
    cut_178_01,
    cut_234_01,
    cut_235_01,
    cut_236_01,
    cut_237_01,
    cut_238_01,
    cut_245_01,
    cut_246_01,
    cut_247_01,
    cut_248_01,
    cut_256_01,
    cut_257_01,
    cut_258_01,
    cut_267_01,
    cut_268_01,
    cut_278_01,
    cut_345_01,
    cut_346_01,
    cut_347_01,
    cut_348_01,
    cut_356_01,
    cut_357_01,
    cut_358_01,
    cut_367_01,
    cut_368_01,
    cut_378_01,
    cut_456_01,
    cut_457_01,
    cut_458_01,
    cut_467_01,
    cut_468_01,
    cut_478_01,
    cut_567_01,
    cut_568_01,
    cut_578_01,
    cut_678_01, List.forall_mem_nil _⟩

private theorem cuts_02 : ∀ τ ∈ triangleCover, ∀ a b : Fin 20,
    CutCheck τ 0 2 1 a b := by
  simp only [triangleCover, List.forall_mem_cons]
  exact ⟨cut_012_02,
    cut_013_02,
    cut_014_02,
    cut_015_02,
    cut_016_02,
    cut_017_02,
    cut_018_02,
    cut_023_02,
    cut_024_02,
    cut_025_02,
    cut_026_02,
    cut_027_02,
    cut_028_02,
    cut_034_02,
    cut_035_02,
    cut_036_02,
    cut_037_02,
    cut_038_02,
    cut_045_02,
    cut_046_02,
    cut_047_02,
    cut_048_02,
    cut_056_02,
    cut_057_02,
    cut_058_02,
    cut_067_02,
    cut_068_02,
    cut_078_02,
    cut_123_02,
    cut_124_02,
    cut_125_02,
    cut_126_02,
    cut_127_02,
    cut_128_02,
    cut_134_02,
    cut_135_02,
    cut_136_02,
    cut_137_02,
    cut_138_02,
    cut_145_02,
    cut_146_02,
    cut_147_02,
    cut_148_02,
    cut_156_02,
    cut_157_02,
    cut_158_02,
    cut_167_02,
    cut_168_02,
    cut_178_02,
    cut_234_02,
    cut_235_02,
    cut_236_02,
    cut_237_02,
    cut_238_02,
    cut_245_02,
    cut_246_02,
    cut_247_02,
    cut_248_02,
    cut_256_02,
    cut_257_02,
    cut_258_02,
    cut_267_02,
    cut_268_02,
    cut_278_02,
    cut_345_02,
    cut_346_02,
    cut_347_02,
    cut_348_02,
    cut_356_02,
    cut_357_02,
    cut_358_02,
    cut_367_02,
    cut_368_02,
    cut_378_02,
    cut_456_02,
    cut_457_02,
    cut_458_02,
    cut_467_02,
    cut_468_02,
    cut_478_02,
    cut_567_02,
    cut_568_02,
    cut_578_02,
    cut_678_02, List.forall_mem_nil _⟩

private theorem cuts_12 : ∀ τ ∈ triangleCover, ∀ a b : Fin 20,
    CutCheck τ 1 2 0 a b := by
  simp only [triangleCover, List.forall_mem_cons]
  exact ⟨cut_012_12,
    cut_013_12,
    cut_014_12,
    cut_015_12,
    cut_016_12,
    cut_017_12,
    cut_018_12,
    cut_023_12,
    cut_024_12,
    cut_025_12,
    cut_026_12,
    cut_027_12,
    cut_028_12,
    cut_034_12,
    cut_035_12,
    cut_036_12,
    cut_037_12,
    cut_038_12,
    cut_045_12,
    cut_046_12,
    cut_047_12,
    cut_048_12,
    cut_056_12,
    cut_057_12,
    cut_058_12,
    cut_067_12,
    cut_068_12,
    cut_078_12,
    cut_123_12,
    cut_124_12,
    cut_125_12,
    cut_126_12,
    cut_127_12,
    cut_128_12,
    cut_134_12,
    cut_135_12,
    cut_136_12,
    cut_137_12,
    cut_138_12,
    cut_145_12,
    cut_146_12,
    cut_147_12,
    cut_148_12,
    cut_156_12,
    cut_157_12,
    cut_158_12,
    cut_167_12,
    cut_168_12,
    cut_178_12,
    cut_234_12,
    cut_235_12,
    cut_236_12,
    cut_237_12,
    cut_238_12,
    cut_245_12,
    cut_246_12,
    cut_247_12,
    cut_248_12,
    cut_256_12,
    cut_257_12,
    cut_258_12,
    cut_267_12,
    cut_268_12,
    cut_278_12,
    cut_345_12,
    cut_346_12,
    cut_347_12,
    cut_348_12,
    cut_356_12,
    cut_357_12,
    cut_358_12,
    cut_367_12,
    cut_368_12,
    cut_378_12,
    cut_456_12,
    cut_457_12,
    cut_458_12,
    cut_467_12,
    cut_468_12,
    cut_478_12,
    cut_567_12,
    cut_568_12,
    cut_578_12,
    cut_678_12, List.forall_mem_nil _⟩

theorem cut_checks (τ : Triangle 9) (u v w : Fin 3)
    (huv : u < v) (hwu : w ≠ u) (hwv : w ≠ v) (a b : Fin 20) :
    CutCheck τ u v w a b := by
  have hp : (u = 0 ∧ v = 1 ∧ w = 2) ∨
      (u = 0 ∧ v = 2 ∧ w = 1) ∨ (u = 1 ∧ v = 2 ∧ w = 0) := by
    fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all
  rcases hp with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact cuts_01 τ (triangleCovered τ) a b
  · exact cuts_02 τ (triangleCovered τ) a b
  · exact cuts_12 τ (triangleCovered τ) a b

end
end Omega.Turnpike.PrunedSingletonCutCertificate
