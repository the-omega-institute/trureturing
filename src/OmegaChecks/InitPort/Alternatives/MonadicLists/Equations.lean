module

import all Init.Data.Vector.Basic
import all Init.Data.Array.BasicAux
import all Init.Data.Vector.OfFn
import all Init.Data.Array.Basic

/-! The fuel of each indexed traversal falls by exactly one per processed element. -/

namespace OmegaChecks.InitPort.Alternatives

private theorem fixAt {A : Sort u} {B : A → Sort v} (measure : A → Nat)
    (step : (x : A) → ((y : A) → measure y < measure x → B y) → B x) (x : A) (fuel : Nat)
    (size : WellFounded.Nat.eager (measure x + 1) = fuel) :
    WellFounded.Nat.fix measure step x = WellFounded.Nat.fix.go measure step fuel x
      (size ▸ WellFounded.Nat.eager_eq _ ▸ Nat.lt_add_one _) := by
  cases size
  rfl

private theorem nextFuel (h : i < n) :
    WellFounded.Nat.eager (n - i + 1) = WellFounded.Nat.eager (n - (i + 1) + 1) + 1 := by
  rw [WellFounded.Nat.eager_eq, WellFounded.Nat.eager_eq, Nat.sub_succ]
  exact congrArg Nat.succ (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)).symm

private theorem endFuel (h : ¬i < n) : WellFounded.Nat.eager (n - i + 1) = Nat.succ 0 := by
  rw [WellFounded.Nat.eager_eq, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)]

public theorem Vector.mapM.go._unary.eq_def.{u,v,w} :
    type_of% (private_decl% @Vector.mapM.go._unary.eq_def.{u,v,w}) := by
  intro m α β n _ f xs p
  obtain ⟨i, hi, acc⟩ := p
  let measure (p : (k : Nat) ×' (_ : k ≤ n) ×' Vector β k) : Nat :=
    p.casesOn fun k t => t.casesOn fun _ _ => n - k
  dsimp only
  by_cases h : i < n
  · rw [dite_eq_left h]
    delta Vector.mapM.go._unary
    refine (fixAt measure _ ⟨i, hi, acc⟩ _ (nextFuel h)).trans ?_
    dsimp only [WellFounded.Nat.fix.go]
    rw [dite_eq_left h]
    rfl
  · rw [dite_eq_right h]
    delta Vector.mapM.go._unary
    refine (fixAt measure _ ⟨i, hi, acc⟩ _ (endFuel h)).trans ?_
    dsimp only [WellFounded.Nat.fix.go]
    rw [dite_eq_right h]

public theorem Vector.flatMapM.go._unary.eq_def.{u,v,w} :
    type_of% (private_decl% @Vector.flatMapM.go._unary.eq_def.{u,v,w}) := by
  intro m α n β k _ xs f p
  obtain ⟨i, hi, acc⟩ := p
  let measure (p : (j : Nat) ×' (_ : j ≤ n) ×' Vector β (j * k)) : Nat :=
    p.casesOn fun k t => t.casesOn fun _ _ => n - k
  dsimp only
  by_cases h : i < n
  · rw [dite_eq_left h]
    delta Vector.flatMapM.go._unary
    refine (fixAt measure _ ⟨i, hi, acc⟩ _ (nextFuel h)).trans ?_
    dsimp only [WellFounded.Nat.fix.go]
    rw [dite_eq_left h]
    rfl
  · rw [dite_eq_right h]
    delta Vector.flatMapM.go._unary
    refine (fixAt measure _ ⟨i, hi, acc⟩ _ (endFuel h)).trans ?_
    dsimp only [WellFounded.Nat.fix.go]
    rw [dite_eq_right h]

public theorem Vector.ofFnM.go._unary.eq_def.{u,v} :
    type_of% (private_decl% @Vector.ofFnM.go._unary.eq_def.{u,v}) := by
  intro m α n _ f p
  obtain ⟨i, hi, acc, hsize⟩ := p
  let measure (p : (k : Nat) ×' (_ : k ≤ n) ×' (acc : Array α) ×' acc.size = k) : Nat :=
    p.casesOn fun k t => t.casesOn fun _ s => s.casesOn fun _ _ => n - k
  dsimp only
  by_cases h : i < n
  · rw [dite_eq_left h]
    delta Vector.ofFnM.go._unary
    refine (fixAt measure _ ⟨i, hi, acc, hsize⟩ _ (nextFuel h)).trans ?_
    dsimp only [WellFounded.Nat.fix.go]
    rw [dite_eq_left h]
    rfl
  · rw [dite_eq_right h]
    delta Vector.ofFnM.go._unary
    refine (fixAt measure _ ⟨i, hi, acc, hsize⟩ _ (endFuel h)).trans ?_
    dsimp only [WellFounded.Nat.fix.go]
    rw [dite_eq_right h]

public theorem Array.mapM.map._unary.eq_def :
    type_of% @Array.mapM.map._unary.eq_def := by
  intro α β m _ f xs p
  obtain ⟨i, acc⟩ := p
  let measure (p : (_ : Nat) ×' Array β) : Nat :=
    p.casesOn fun k _ => xs.size - k
  dsimp only
  by_cases h : i < xs.size
  · rw [dite_eq_left h]
    delta Array.mapM.map._unary
    refine (fixAt measure _ ⟨i, acc⟩ _ (nextFuel h)).trans ?_
    dsimp only [WellFounded.Nat.fix.go]
    rw [dite_eq_left h]
    rfl
  · rw [dite_eq_right h]
    delta Array.mapM.map._unary
    refine (fixAt measure _ ⟨i, acc⟩ _ (endFuel h)).trans ?_
    dsimp only [WellFounded.Nat.fix.go]
    rw [dite_eq_right h]

public theorem Array.mapM'.go._unary.eq_def.{u,v,w} :
    type_of% (private_decl% @Array.mapM'.go._unary.eq_def.{u,v,w}) := by
  intro m α β _ f xs p
  obtain ⟨i, acc, hle⟩ := p
  let measure (p : (j : Nat) ×' (_ : {ys : Array β // ys.size = j}) ×' j ≤ xs.size) : Nat :=
    p.casesOn fun j t => t.casesOn fun _ _ => xs.size - j
  dsimp only
  by_cases he : i = xs.size
  · rw [dite_eq_left he]
    delta Array.mapM'.go._unary
    refine (fixAt measure _ ⟨i, acc, hle⟩ _ (endFuel (Nat.not_lt_of_ge (Nat.le_of_eq he.symm)))).trans ?_
    dsimp only [WellFounded.Nat.fix.go]
    rw [dite_eq_left he]
  · rw [dite_eq_right he]
    delta Array.mapM'.go._unary
    refine (fixAt measure _ ⟨i, acc, hle⟩ _ (nextFuel (Nat.lt_of_le_of_ne hle he))).trans ?_
    dsimp only [WellFounded.Nat.fix.go]
    rw [dite_eq_right he]
    rfl

end OmegaChecks.InitPort.Alternatives
