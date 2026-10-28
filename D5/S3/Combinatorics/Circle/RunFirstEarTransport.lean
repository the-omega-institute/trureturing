/- GID: D5/S3/Combinatorics/Circle/RunFirstEarTransport
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/RunFirstEarTransport
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate]
   utility: none
   digest: Native same-cut dyadic transport of joint physical source orders. -/
import D5.S3.Combinatorics.Circle.PeriodicShortening
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.RunFirstEarTransport
open SourceWidth PeriodicShorteningArithmetic PeriodicShortening
open scoped BigOperators

/-- Insert the new physical label, retaining every old physical occurrence. -/
def earWord (d : ℕ) (sigma : List (Fin d)) (r : ℕ) : List (Fin (d + 1)) :=
  (sigma.take r).map Fin.castSucc ++ [Fin.last d] ++ (sigma.drop r).map Fin.castSucc

/-- Extend old-source rotation by fixing the inserted physical label. -/
def earRelabel (d h : ℕ) : Equiv.Perm (Fin (d + 1)) where
  toFun := Fin.lastCases (Fin.last d)
    (fun i => (((finRotate d : Equiv.Perm (Fin d)) ^ h) i).castSucc)
  invFun := Fin.lastCases (Fin.last d)
    (fun i => (((finRotate d : Equiv.Perm (Fin d)) ^ h).symm i).castSucc)
  left_inv j := by
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  right_inv j := by
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

private theorem ear_prefix (d : ℕ) (sigma : List (Fin d)) (r : ℕ)
    (hr : r ≤ sigma.length) (f : Fin (d + 1) → ℤ) (n : ℕ) :
    (((earWord d sigma r).take n).map f).sum =
      ((sigma.take (if n ≤ r then n else n - 1)).map (fun i => f i.castSucc)).sum +
        (if n ≤ r then 0 else f (Fin.last d)) := by
  induction sigma generalizing r n with
  | nil =>
    have : r = 0 := by simpa using hr
    subst r
    cases n <;> simp [earWord]
  | cons x xs ih =>
    cases r with
    | zero =>
      cases n with
      | zero => simp [earWord]
      | succ n => simp [earWord, List.map_map, add_comm]
    | succ r =>
      have hr' : r ≤ xs.length := by simpa using hr
      cases n with
      | zero => simp [earWord]
      | succ n =>
        have he := ih r hr' n
        simp only [earWord, List.take_succ_cons, List.drop_succ_cons, List.map_cons,
          List.cons_append, List.take_succ_cons, List.sum_cons] at he ⊢
        split_ifs with hn
        · have hn' : n ≤ r := by omega
          simpa [hn', List.take_succ_cons, List.sum_cons, add_assoc] using congrArg (f x.castSucc + ·) he
        · have hn' : ¬ n ≤ r := by omega
          simpa [hn', show n + 1 - 1 = (n - 1) + 1 by omega,
            List.take_succ_cons, List.sum_cons, add_assoc] using congrArg (f x.castSucc + ·) he

private theorem ear_perm (d : ℕ) (sigma : List (Fin d)) (r : ℕ)
    (hs : sigma.Perm (List.finRange d)) :
    (earWord d sigma r).Perm (List.finRange (d + 1)) := by
  have he : (earWord d sigma r).Perm (sigma.map Fin.castSucc ++ [Fin.last d]) := by
    unfold earWord
    rw [← List.map_take, ← List.map_drop]
    simpa [List.append_assoc, List.take_append_drop] using
      (List.perm_append_comm : ([Fin.last d] ++ (sigma.map Fin.castSucc).drop r).Perm
        ((sigma.map Fin.castSucc).drop r ++ [Fin.last d])).append_left
          ((sigma.map Fin.castSucc).take r)
  exact he.trans (by simpa [List.finRange_succ_last] using (hs.map Fin.castSucc).append_right [Fin.last d])

end D5.S3.Combinatorics.Circle.RunFirstEarTransport
