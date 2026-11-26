module
public import Init.Omega.IntList
import Init.Data.Int.Lemmas

open Lean.Omega IntList

namespace OmegaChecks.InitPort.Alternatives

public theorem Lean.Omega.IntList.nil_add : type_of% @_root_.Lean.Omega.IntList.nil_add := by
  intro xs
  rw [add_def, List.nil_zipWithAll]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (0 + x) :: _ = x :: xs
    rw [Int.zero_add, ih]

public theorem Lean.Omega.IntList.add_nil : type_of% @_root_.Lean.Omega.IntList.add_nil := by
  intro xs
  rw [add_def, List.zipWithAll_nil]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (x + 0) :: _ = x :: xs
    rw [Int.add_zero, ih]

public theorem Lean.Omega.IntList.combo_eq_smul_add_smul : type_of% @_root_.Lean.Omega.IntList.combo_eq_smul_add_smul := by
  intro a xs b ys
  have map_eq (f g : Int → Int) (same : ∀ x, f x = g x) (l : IntList) : l.map f = l.map g := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
      change f x :: xs.map f = g x :: xs.map g
      rw [same, ih]
  induction xs generalizing ys with
  | nil =>
    rw [smul_nil, Lean.Omega.IntList.nil_add]
    exact map_eq _ _ (fun y => (congrArg (· + b * y) (Int.mul_zero a)).trans (Int.zero_add _)) ys
  | cons x xs ih =>
    cases ys with
    | nil =>
      rw [smul_nil, Lean.Omega.IntList.add_nil]
      exact map_eq _ _ (fun x => (congrArg (a * x + ·) (Int.mul_zero b)).trans (Int.add_zero _)) (x :: xs)
    | cons y ys =>
      exact congrArg (List.cons (a * x + b * y)) (ih ys)

public theorem Lean.Omega.IntList.mul_distrib_left : type_of% @_root_.Lean.Omega.IntList.mul_distrib_left := by
  intro xs ys zs
  induction xs generalizing ys zs with
  | nil => rw [Lean.Omega.IntList.nil_add, mul_nil_left, Lean.Omega.IntList.nil_add]
  | cons x xs ih =>
    cases ys with
    | nil => rw [Lean.Omega.IntList.add_nil, mul_nil_left, Lean.Omega.IntList.add_nil]
    | cons y ys =>
      cases zs with
      | nil => rw [mul_nil_right, mul_nil_right, mul_nil_right]; rfl
      | cons z zs =>
        change ((x + y) * z) :: ((xs + ys) * zs) = (x * z + y * z) :: (xs * zs + ys * zs)
        rw [Int.add_mul, ih]

public theorem Lean.Omega.IntList.sum_add : type_of% @_root_.Lean.Omega.IntList.sum_add := by
  intro xs ys
  induction xs generalizing ys with
  | nil => rw [Lean.Omega.IntList.nil_add, sum_nil, Int.zero_add]
  | cons x xs ih =>
    cases ys with
    | nil => rw [Lean.Omega.IntList.add_nil, sum_nil, Int.add_zero]
    | cons y ys =>
      rw [cons_add_cons, sum_cons, sum_cons, sum_cons, ih, Int.add_assoc x y,
        Int.add_left_comm y (sum xs), ← Int.add_assoc]

end OmegaChecks.InitPort.Alternatives
