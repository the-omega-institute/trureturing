module

import Init.Data.List.SplitOn.Basic
public import OmegaChecks.Interface.Equations.List
public import OmegaChecks.Interface.Equations.Logic
public import OmegaChecks.InitPort.ReferenceSwap
public import OmegaChecks.InitPort.ReferenceSpecialization
public import OmegaChecks.InitPort.LawfulLoop
public import OmegaChecks.InitPort.PatternMatch
public import OmegaChecks.InitPort.LogicalHandle
public import OmegaChecks.InitPort.StateToken
public import OmegaChecks.InitPort.TypeName
public import OmegaChecks.InitPort.FloatFraction
public import OmegaChecks.InitPort.Alternatives.GrindRing
public import OmegaChecks.Interface.Equations.Array
public import OmegaChecks.Interface.Equations.Collect
public import OmegaChecks.Interface.Equations.FilePath
public import OmegaChecks.Interface.Equations.String
public import OmegaChecks.Interface.Equations.Uri
public import OmegaChecks.Interface.Equations.Bitwise
public import OmegaChecks.Interface.Equations.NatFold
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-! Pointwise equations for strict arithmetic algorithms interpreted over official types. -/

namespace OmegaChecks.Interface.Equations

open Lean.Grind Lean.Grind.CommRing in
public theorem Lean.Grind.CommRing.Expr.denoteSAsRing {α : Type u} [Lean.Grind.Semiring α]
    (ctx : Context α) (e : Expr) :
    OmegaChecks.InitPort.Alternatives.Lean.Grind.CommRing.Expr.denoteSAsRing ctx e = e.denoteSAsRing ctx :=
  (OmegaChecks.InitPort.Alternatives.Lean.Grind.CommRing.Expr.denoteAsRing_eq ctx e).trans
    (e.denoteAsRing_eq ctx).symm

public theorem List.splitOnPTR {α : Type u} (p : α → Bool) (xs : List α) :
    xs.splitOnP p = _root_.List.splitOnPTR p xs :=
  congrFun (congrFun (congrFun _root_.List.splitOnP_eq_splitOnPTR α) p) xs

@[expose] public def pair (n : Nat) : Bool → Nat :=
  Nat.rec (motive := fun _ => Bool → Nat) (Bool.rec 0 1)
    (fun _ p => Bool.rec (p true) (p true + p false)) n

public theorem Nat.fib (n : Nat) : pair n false = n.fib := by
  suffices h : pair n false = n.fib ∧ pair n true = n.succ.fib from h.1
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    change pair n true + pair n false = n.succ.succ.fib
    rw [ih.1, ih.2, _root_.Nat.fib_add_two, _root_.Nat.add_comm]

@[expose] public def pascal (n k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (Nat.rec 1 (fun _ _ => 0))
    (fun _ previous => Nat.rec 1 (fun j _ => previous j + previous j.succ)) n k

public theorem Nat.choose (n k : Nat) : pascal n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change pascal n k + pascal n k.succ = n.succ.choose k.succ
      rw [ih, ih, _root_.Nat.choose_succ_succ]

public theorem Nat.add (a b : Nat) :
    Nat.rec a (fun _ r => Nat.succ r) b = a + b := by
  induction b with
  | zero => rfl
  | succ b ih => exact congrArg Nat.succ ih

public theorem Nat.pow (m n : Nat) :
    Nat.rec 1 (fun _ p => _root_.Nat.mul p m) n = _root_.Nat.pow m n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun p => _root_.Nat.mul p m) ih

public theorem Nat.le (a b : Nat) :
    Nat.rec (motive := fun _ => Nat → Prop) (fun _ => True)
      (fun _ smaller n => Nat.rec (motive := fun _ => Prop) False (fun k _ => smaller k) n) a b
      = (a ≤ b) := by
  apply propext
  induction a generalizing b with
  | zero => exact ⟨fun _ => Nat.zero_le b, fun _ => True.intro⟩
  | succ a ih =>
    cases b with
    | zero => exact ⟨False.elim, Nat.not_succ_le_zero _⟩
    | succ b => exact (ih b).trans Nat.succ_le_succ_iff.symm

/-- Recursively cancel common successors before constructing the signed difference. -/
@[expose] public def difference (m n : Nat) : Int :=
  Nat.rec (motive := fun _ => Nat → Int) Int.negOfNat
    (fun a diff b => Nat.rec (Int.ofNat a.succ) (fun k _ => diff k) b) m n

public theorem Int.subNatNat (m n : Nat) : difference m n = _root_.Int.subNatNat m n := by
  induction m generalizing n with
  | zero => cases n <;> simp [difference, _root_.Int.negOfNat, _root_.Int.subNatNat]
  | succ m ih =>
    cases n with
    | zero => simp [difference, _root_.Int.subNatNat]
    | succ n => simpa [difference, _root_.Int.subNatNat] using ih n

/-- The divisor characterization computes the pinned prime predicate at every input. -/
public theorem Nat.Prime (p : Nat) :
    (2 ≤ p ∧ ∀ m, (∃ k, p = m * k) → m = 1 ∨ m = p) = _root_.Nat.Prime p :=
  propext _root_.Nat.prime_def.symm

public theorem Ordering.«then» (a b : Ordering) :
    _root_.Ordering.rec a b a a = a.then b := by
  cases a <;> rfl

public theorem Ordering.isEq (o : Ordering) :
    _root_.Ordering.rec false true false o = o.isEq := by
  cases o <;> rfl

public theorem Ordering.isNe (o : Ordering) :
    _root_.Ordering.rec true false true o = o.isNe := by
  cases o <;> rfl

public theorem Ordering.isLE (o : Ordering) :
    _root_.Ordering.rec true true false o = o.isLE := by
  cases o <;> rfl

public theorem Ordering.isLT (o : Ordering) :
    _root_.Ordering.rec true false false o = o.isLT := by
  cases o <;> rfl

public theorem Ordering.isGT (o : Ordering) :
    _root_.Ordering.rec false false true o = o.isGT := by
  cases o <;> rfl

public theorem Ordering.isGE (o : Ordering) :
    _root_.Ordering.rec false true true o = o.isGE := by
  cases o <;> rfl

public theorem Nat.beq (a b : Nat) :
    Nat.rec (motive := fun _ => Nat → Bool) (Nat.rec true (fun _ _ => false))
      (fun _ smaller => Nat.rec false (fun k _ => smaller k)) a b = _root_.Nat.beq a b := by
  induction a generalizing b with
  | zero => cases b <;> rfl
  | succ a ih => cases b with
    | zero => rfl
    | succ b => exact ih b

public theorem Nat.ble (a b : Nat) :
    Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun _ smaller => Nat.rec false (fun k _ => smaller k)) a b = _root_.Nat.ble a b := by
  induction a generalizing b with
  | zero => cases b <;> rfl
  | succ a ih => cases b with
    | zero => rfl
    | succ b => exact ih b

@[expose] public noncomputable def divisionSteps (d : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ previous x => Bool.rec 0 ((previous (x - d.succ)).succ) (_root_.Nat.ble d.succ x))

private theorem divisionSteps_eq (d fuel x : Nat) (h : x < fuel) :
    divisionSteps d fuel x = x / d.succ := by
  induction fuel generalizing x with
  | zero => exact False.elim ((Nat.not_lt_zero x) h)
  | succ fuel ih =>
    change Bool.rec 0 ((divisionSteps d fuel (x - d.succ)).succ)
      (_root_.Nat.ble d.succ x) = x / d.succ
    rw [Nat.div_eq_ite x d.succ]
    by_cases le : d.succ ≤ x
    · rw [Nat.ble_eq_true_of_le le, ite_eq_left ⟨Nat.succ_pos _, le⟩]
      have smaller := Nat.sub_lt_of_pos_le (Nat.succ_pos d) le
      exact congrArg Nat.succ (ih _ (Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ h)))
    · have hb : _root_.Nat.ble d.succ x = false :=
        Bool.eq_false_of_ne_true (fun ht => le (Nat.le_of_ble_eq_true ht))
      rw [hb, ite_eq_right (fun both => le both.2)]

public theorem Nat.div (x y : Nat) :
    Nat.rec 0 (fun d _ => divisionSteps d x.succ x) y = _root_.Nat.div x y := by
  cases y with
  | zero => exact (Nat.div_zero x).symm
  | succ d => exact divisionSteps_eq d _ x (Nat.lt_succ_self x)

public theorem Nat.mod (x y : Nat) :
    Nat.casesOn x 0 (fun k => if y ≤ k.succ then _root_.Nat.modCore k.succ y else k.succ) =
      _root_.Nat.mod x y := by
  cases x <;> rfl

public theorem Nat.modCore (x y : Nat) : _root_.Nat.mod x y = _root_.Nat.modCore x y :=
  (_root_.Nat.modCore_eq_mod x y).symm

@[expose] public noncomputable def euclideanSteps : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ n => n)
    (fun _ smaller m n => Nat.rec n (fun d _ => smaller (n % d.succ) d.succ) m)

private theorem euclideanSteps_eq (fuel m n : Nat) (h : m < fuel) :
    euclideanSteps fuel m n = _root_.Nat.gcd m n := by
  induction fuel generalizing m n with
  | zero => exact False.elim ((Nat.not_lt_zero m) h)
  | succ fuel ih =>
    cases m with
    | zero => exact (Nat.gcd_zero_left n).symm
    | succ m =>
      rw [Nat.gcd_succ]
      exact ih _ _ (Nat.lt_of_lt_of_le (Nat.mod_lt n (Nat.succ_pos m)) (Nat.le_of_lt_succ h))

public theorem Nat.gcd (m n : Nat) : euclideanSteps m.succ m n = _root_.Nat.gcd m n :=
  euclideanSteps_eq _ m n (Nat.lt_succ_self m)

end OmegaChecks.Interface.Equations
