/- GID: D5/S0/Computability/NatPresburgerEnvironment
   generality: G
   mirror-B: D5/B/S0/Computability/NatPresburgerEnvironment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Affine coordinates for reversed bound and native free Nat valuations. -/

import D5.S0.Computability.PresburgerSyntax
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic

namespace NatPresburger

open PresburgerArithmetic

/-- Backend valuations place the newest bound variable at the head. -/
def environment {m n : Nat} (v : Fin m → Nat) (xs : Fin n → Nat) : List Int :=
  (List.ofFn (fun i => Int.ofNat (xs i))).reverse ++
    List.ofFn (fun i => Int.ofNat (v i))

/-- Native bound coordinates are reversed; free coordinates follow them. -/
def position {m n : Nat} : Fin m ⊕ Fin n → Nat
  | .inl i => n + i.val
  | .inr i => n - 1 - i.val

/-- A single executable affine coordinate, with missing values interpreted as zero. -/
def basis : Nat → Affine
  | 0 => .consCoeff 1 (.const 0)
  | k + 1 => .consCoeff 0 (basis k)

theorem eval_basis (k : Nat) (env : List Int) :
    (basis k).eval env = (env[k]?).getD 0 := by
  induction k generalizing env with
  | zero => cases env <;> simp [basis, Affine.consCoeff, Affine.eval, Affine.dot,
      Affine.const]
  | succ k ih =>
    cases env with
    | nil =>
      simpa [basis, Affine.consCoeff, Affine.eval, Affine.dot] using ih []
    | cons x xs =>
      simpa only [basis, Affine.eval_consCoeff, zero_mul, zero_add,
        List.getElem?_cons_succ] using ih xs

theorem environment_lookup {m n : Nat} (v : Fin m → Nat) (xs : Fin n → Nat)
    (i : Fin m ⊕ Fin n) :
    ((environment v xs)[position i]?).getD 0 = Int.ofNat (Sum.elim v xs i) := by
  cases i with
  | inl i =>
    have h : ((environment v xs)[n+i.val]?) = some (Int.ofNat (v i)) := by
      unfold environment
      rw [List.getElem?_append_right (by simp)]
      simp
    simpa [position] using congrArg (fun o : Option Int => o.getD 0) h
  | inr i =>
    have h : ((environment v xs)[n-1-i.val]?) = some (Int.ofNat (xs i)) := by
      unfold environment
      rw [List.getElem?_append_left (by simp; omega)]
      rw [List.getElem?_reverse' (j := i.val) (by simp; omega)]
      simp
    simpa [position] using congrArg (fun o : Option Int => o.getD 0) h

theorem environment_snoc {m n : Nat} (v : Fin m → Nat) (xs : Fin n → Nat)
    (x : Nat) : environment v (Fin.snoc (α := fun _ => Nat) xs x) =
      (x : Int) :: environment v xs := by
  unfold environment
  rw [List.ofFn_succ']
  simp

end NatPresburger
