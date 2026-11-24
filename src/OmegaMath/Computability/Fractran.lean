module
prelude
public import OmegaMath.Computability.Fractran.Division

/-!
Omega original.

Ordered fraction programs with positive rule entries and exact denominator guards.
A rule tests its stored denominator against the input. Reduced fractions give
the ordinary FRACTRAN test for an integral product.
-/

noncomputable section

@[expose] public section

namespace Omega.Fractran

open Omega

/-- Each entry is represented by its predecessor, so both entries are positive. -/
structure Rule where
  numeratorPred : Nat
  denominatorPred : Nat

def Rule.numerator (rule : Rule) : Nat := rule.numeratorPred.succ
def Rule.denominator (rule : Rule) : Nat := rule.denominatorPred.succ

inductive Program where
  | nil
  | cons (rule : Rule) (tail : Program)

def Divides (rule : Rule) (n : Nat) : Prop :=
  Exists (fun q => Eq (rule.denominator.mul q) n)

def fireOrElse (rule : Rule) (rest : Result) : Result → Result :=
  Result.rec (motive := fun _ => Result) rest (fun q => .some (q.mul rule.numerator))

def step (prog : Program) (n : Nat) : Result :=
  Program.rec .none (fun rule _ rest =>
    fireOrElse rule rest (exactQuotient n rule.denominatorPred)) prog

/-- A transition fires the first enabled rule in program order. -/
def Step (prog : Program) (n m : Nat) : Prop :=
  Program.rec (motive := fun _ => Prop) False (fun rule _ tail =>
    Or (Exists (fun q => And (Eq (rule.denominator.mul q) n) (Eq (q.mul rule.numerator) m)))
      (And (Not (Divides rule n)) tail)) prog

theorem Step.fire {rule : Rule} {rest : Program} {n q : Nat} (h : Eq (rule.denominator.mul q) n) :
    Step (.cons rule rest) n (q.mul rule.numerator) :=
  Or.inl (Exists.intro q (And.intro h Eq.refl))

theorem Step.skip {rule : Rule} {rest : Program} {n m : Nat} (h : Not (Divides rule n))
    (later : Step rest n m) : Step (.cons rule rest) n m :=
  Or.inr (And.intro h later)

/-- A program halts at a state exactly when every denominator fails its guard. -/
def Halts (prog : Program) (n : Nat) : Prop :=
  Program.rec (motive := fun _ => Prop) True (fun rule _ tail => And (Not (Divides rule n)) tail) prog

private theorem no_quotient (rule : Rule) (n : Nat) :
    Iff (Eq (exactQuotient n rule.denominatorPred) .none) (Not (Divides rule n)) :=
  Iff.intro
    (fun none divides => divides.elim (fun q h =>
      Result.none_ne_some q (none.symm.trans ((exactQuotient_spec n _ q).mpr h))))
    (fun bad =>
      (Result.rec (motive := fun r => Eq (exactQuotient n rule.denominatorPred) r → Eq r .none)
        (fun _ => Eq.refl)
        (fun q h => False.elim (bad (Exists.intro q ((exactQuotient_spec n _ q).mp h))))
        (exactQuotient n rule.denominatorPred) Eq.refl))

theorem step_deterministic (prog : Program) (n m₁ m₂ : Nat)
    (h₁ : Eq (step prog n) (.some m₁)) (h₂ : Eq (step prog n) (.some m₂)) : Eq m₁ m₂ :=
  Result.some_inj (h₁.symm.trans h₂)

theorem Step.sound {prog : Program} {n m : Nat} (h : Step prog n m) :
    Eq (step prog n) (.some m) :=
  (Program.rec (motive := fun prog => Step prog n m → Eq (step prog n) (.some m))
    (fun h => False.elim h)
    (fun rule rest ih branch =>
      let emit := fireOrElse rule (step rest n)
      branch.elim
        (fun enabled => enabled.elim (fun q exact =>
          (congrArg emit ((exactQuotient_spec n rule.denominatorPred q).mpr exact.left)).trans
            (congrArg Result.some exact.right)))
        (fun skipped => (congrArg emit ((no_quotient rule n).mpr skipped.left)).trans
          (ih skipped.right))) prog) h

theorem step_complete (prog : Program) (n m : Nat) (h : Eq (step prog n) (.some m)) :
    Step prog n m :=
  (Program.rec (motive := fun prog => Eq (step prog n) (.some m) → Step prog n m)
    (fun h => False.elim (Result.none_ne_some m h))
    (fun rule rest ih =>
      let select := fireOrElse rule (step rest n)
      Result.rec (motive := fun r => Eq (exactQuotient n rule.denominatorPred) r →
          Eq (select r) (.some m) → Step (.cons rule rest) n m)
        (fun none stepEq => Step.skip ((no_quotient rule n).mp none) (ih stepEq))
        (fun q exact stepEq => Eq.subst (Step (.cons rule rest) n) (Result.some_inj stepEq)
          (Step.fire ((exactQuotient_spec n rule.denominatorPred q).mp exact)))
        (exactQuotient n rule.denominatorPred) Eq.refl) prog) h

theorem step_iff (prog : Program) (n m : Nat) :
    Iff (Eq (step prog n) (.some m)) (Step prog n m) :=
  Iff.intro (step_complete prog n m) Step.sound

theorem Step.deterministic {prog : Program} {n m₁ m₂ : Nat} (h₁ : Step prog n m₁)
    (h₂ : Step prog n m₂) : Eq m₁ m₂ :=
  step_deterministic prog n m₁ m₂ h₁.sound h₂.sound

theorem halts_iff (prog : Program) (n : Nat) : Iff (Halts prog n) (Eq (step prog n) .none) :=
  Program.rec (motive := fun prog => Iff (Halts prog n) (Eq (step prog n) .none))
    (Iff.intro (fun _ => Eq.refl) (fun _ => True.intro))
    (fun rule rest ih =>
      let select := fireOrElse rule (step rest n)
      Result.rec (motive := fun r => Eq (exactQuotient n rule.denominatorPred) r →
          Iff (Halts (.cons rule rest) n) (Eq (select r) .none))
        (fun none => Iff.intro (fun h => ih.mp h.right)
          (fun h => And.intro ((no_quotient rule n).mp none) (ih.mpr h)))
        (fun q exact => Iff.intro
          (fun h => False.elim (h.left (Exists.intro q ((exactQuotient_spec n _ q).mp exact))))
          (fun h => False.elim (Result.none_ne_some _ h.symm)))
        (exactQuotient n rule.denominatorPred) Eq.refl) prog

private theorem positive_iff (n : Nat) : Iff (Nat.lt Nat.zero n) (Not (Eq n Nat.zero)) :=
  Nat.rec (motive := fun n => Iff (Nat.lt Nat.zero n) (Not (Eq n Nat.zero)))
    (Iff.intro (fun h => False.elim h) (fun h => h Eq.refl))
    (fun n _ => Iff.intro (fun _ => Nat.succ_ne_zero n) (fun _ => Nat.zero_le n)) n

theorem Step.positive {prog : Program} {n m : Nat} (h : Step prog n m) :
    Nat.lt Nat.zero n → Nat.lt Nat.zero m :=
  (Program.rec (motive := fun prog => Step prog n m → Nat.lt Nat.zero n → Nat.lt Nat.zero m)
    (fun h => False.elim h)
    (fun rule _ ih branch positive => branch.elim
      (fun enabled => enabled.elim (fun q exact =>
        Eq.subst (Nat.lt Nat.zero) exact.right
          ((positive_iff (q.mul rule.numerator)).mpr (fun zero => (Nat.mul_eq_zero.mp zero).elim
            (fun quotientZero => (positive_iff n).mp positive (exact.left.symm.trans
              ((congrArg rule.denominator.mul quotientZero).trans (Nat.mul_zero _))))
            (Nat.succ_ne_zero rule.numeratorPred)))))
      (fun skipped => ih skipped.right positive)) prog) h

def advance (prog : Program) (n : Nat) : Nat := Result.rec (motive := fun _ => Nat) n (fun m => m) (step prog n)

def run (prog : Program) (k n : Nat) : Nat :=
  Nat.rec n (fun _ => advance prog) k

theorem run_positive (prog : Program) (k n : Nat) (h : Nat.lt Nat.zero n) :
    Nat.lt Nat.zero (run prog k n) :=
  Nat.rec (motive := fun k => Nat.lt Nat.zero (run prog k n)) h
    (fun k ih =>
      let s := run prog k n
      (Result.rec (motive := fun r => Eq (step prog s) r →
          Nat.lt Nat.zero (Result.rec (motive := fun _ => Nat) s (fun m => m) r))
        (fun _ => ih) (fun m eq => (step_complete prog s m eq).positive ih) (step prog s)) Eq.refl) k

theorem run_fixed_of_halts (prog : Program) (n : Nat) (h : Halts prog n) (k : Nat) :
    Eq (run prog k n) n :=
  have fixed : Eq (advance prog n) n := congrArg (Result.rec (motive := fun _ => Nat) n (fun m => m)) ((halts_iff prog n).mp h)
  Nat.rec (motive := fun k => Eq (run prog k n) n) Eq.refl
    (fun _ ih => (congrArg (advance prog) ih).trans fixed) k

theorem run_stable (prog : Program) (k n : Nat) (h : Halts prog (run prog k n)) (extra : Nat) :
    Eq (run prog (k.add extra) n) (run prog k n) :=
  have append : Eq (run prog (k.add extra) n) (run prog extra (run prog k n)) :=
    Nat.rec (motive := fun t => Eq (run prog (k.add t) n) (run prog t (run prog k n)))
      Eq.refl (fun _ => congrArg (advance prog)) extra
  append.trans (run_fixed_of_halts prog (run prog k n) h extra)

end Omega.Fractran
