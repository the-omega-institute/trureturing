/- GID: D5/S3/Combinatorics/Turnpike/PrunedSingletonCutData
   generality: G
   mirror-B: none(waiver:covered-by-pruned-singleton-projection-obstruction-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Shared singleton-cut data and triangle coverage -/

module

public import D5.S3.Combinatorics.Turnpike.PrunedTriangleLP
public import Mathlib.Data.Fin.VecNotation

/-! Omega original.
# Shared singleton-cut data and triangle coverage

The integer assignment, completion candidate and complete triangle cover are
shared by the three coordinate-pair certificates. Indices are zero-based.
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

def triangleCover : List (Triangle 9) :=
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

theorem triangleCovered (τ : Triangle 9) : τ ∈ triangleCover := by
  revert τ
  decide +kernel

end
end Omega.Turnpike.PrunedSingletonCutCertificate
