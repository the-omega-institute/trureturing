/- GID: D5/S0/Rewriting/UniformNativeUnificationDomain
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original-domain interface and exact native unification projection. -/

import D5.S0.Rewriting.UnificationFuel
import D5.S0.Computability.PreorderTreeEvaluation
import Mathlib.Computability.PartrecCode

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace Lambda.UniformNativeUnification
open Strata.Util NativeTermUnification
open D5.S0.Computability.PreorderTreeEvaluation

abbrev TermN := Term Nat
abbrev Equations (X : Type) := List (Term X × Term X)
abbrev SolverInput := Nat × Equations Nat
abbrev SolverOutput := Option (Option (List (Nat × TermN)))

/-- Boolean labels and ordered constructors are unchanged. -/
def liftTerm {n : Nat} : Term (Fin n) → TermN :=
  FreeMagma.map (Sum.map id Fin.val)

def liftEquations {n : Nat} (E : Equations (Fin n)) : Equations Nat :=
  E.map (fun e => (liftTerm e.1, liftTerm e.2))

/-- Repeated occurrences are checked independently; no variable is renamed. -/
def inRange (n : Nat) : TermN → Bool
  | .of (.inl _) => true
  | .of (.inr x) => decide (x < n)
  | .mul l r => inRange n l && inRange n r

/-- Finite-domain reconstruction rejects each out-of-range occurrence. -/
def lowerTerm (n : Nat) : TermN → Option (Term (Fin n))
  | .of (.inl b) => some (.of (.inl b))
  | .of (.inr x) => if h : x < n then some (.of (.inr ⟨x,h⟩)) else none
  | .mul l r => do
      let l' ← lowerTerm n l
      let r' ← lowerTerm n r
      some (.mul l' r')

def lowerEquations (n : Nat) (E : Equations Nat) : Option (Equations (Fin n)) :=
  E.foldr (fun e rest => do
    let l ← lowerTerm n e.1
    let r ← lowerTerm n e.2
    let tail ← rest
    some ((l,r) :: tail)) (some [])

private theorem lower_lift (n : Nat) (t : Term (Fin n)) :
    lowerTerm n (liftTerm t) = some t := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl b => rfl
    | inr x => simp [liftTerm, FreeMagma.map, lowerTerm, x.isLt]
  | mul l r hl hr =>
      change ((lowerTerm n (liftTerm l)).bind fun l' =>
        (lowerTerm n (liftTerm r)).bind fun r' => some (FreeMagma.mul l' r')) = some (FreeMagma.mul l r)
      rw [hl, hr]; rfl

private theorem lower_equations_lift (n : Nat) (E : Equations (Fin n)) :
    lowerEquations n (liftEquations E) = some E := by
  induction E with
  | nil => rfl
  | cons e E ih =>
      change ((lowerTerm n (liftTerm e.1)).bind fun l =>
        (lowerTerm n (liftTerm e.2)).bind fun r =>
        (lowerEquations n (liftEquations E)).bind fun tail => some ((l,r) :: tail)) = _
      rw [lower_lift, lower_lift, ih]
      rfl

theorem lower_range (n : Nat) (t : TermN) :
    (lowerTerm n t).isSome = inRange n t := by
  induction t using FreeMagma.recOn with
  | of a => cases a with
    | inl b => rfl
    | inr x => simp only [lowerTerm, inRange]; split <;> simp_all
  | mul l r hl hr =>
      simp only [lowerTerm, inRange]
      cases hleft : lowerTerm n l <;> cases hright : lowerTerm n r <;>
        simp_all

theorem lower_equations_range (n : Nat) (E : Equations Nat) :
    (lowerEquations n E).isSome = E.all (fun e => inRange n e.1 && inRange n e.2) := by
  induction E with
  | nil => rfl
  | cons e E ih =>
      have hL := lower_range n e.1
      have hR := lower_range n e.2
      change ((lowerTerm n e.1).bind fun l => (lowerTerm n e.2).bind fun r =>
        (lowerEquations n E).bind fun tail => some ((l,r) :: tail)).isSome = _
      simp only [List.all_cons]
      cases hl : lowerTerm n e.1 <;> cases hr : lowerTerm n e.2 <;>
        cases ht : lowerEquations n E
      all_goals
        simp only [hl, hr, ht, Option.isSome_none, Option.isSome_some] at hL hR ih
        rw [← hL, ← hR, ← ih]
        rfl

/-- Projection uses ascending original keys and the fully composed native
substitution action, including aliases to unbound original variables. -/
def project (n : Nat) (S : Subst) : List (Nat × TermN) :=
  ((List.finRange n).filter (fun i => (finPresentation n).code i ∈ S.keys)).map
    (fun i => (i.val, liftTerm
      ((nativeDecode (finPresentation n) (LMonoTy.subst S (.ftvar ((finPresentation n).code i)))).getD (.of (.inr i)))))

/-- One total executable function accepts all finite Nat-indexed equations.
Outer failure is malformed input; inner failure is the exact native failure. -/
def F (input : SolverInput) : SolverOutput :=
  match lowerEquations input.1 input.2 with
  | none => none
  | some E =>
      let p := finPresentation input.1
      let cs := E.map (fun e => (encode p e.1, encode p e.2))
      match UnificationFuel.run cs SubstInfo.empty with
      | .error _ => some none
      | .ok S => some (some (project input.1 S))

/-- All finite domains, equations, native branches and original actions are
retained. No MGU, ground valuation or totality evalCode is an input. -/
theorem exact_native (n : Nat) (E : Equations (Fin n)) :
    F (n,liftEquations E) =
      match Constraints.unify (E.map (fun e => (encode (finPresentation n) e.1,
        encode (finPresentation n) e.2))) SubstInfo.empty with
      | .error _ => some none
      | .ok S => some (some (project n S.subst)) := by
  simp only [F, lower_equations_lift]
  rw [(UnificationFuel.exact_fuel_simulation _ SubstInfo.empty).2.2]
  cases Constraints.unify (E.map (fun e => (encode (finPresentation n) e.1,
    encode (finPresentation n) e.2))) SubstInfo.empty <;> rfl

/-- Rejection is exactly the occurrence of an index outside the declared domain,
including every variable when n = 0. Solver failure is never outer rejection. -/
theorem rejection_exact (n : Nat) (E : Equations Nat) :
    F (n,E) = none ↔ E.all (fun e => inRange n e.1 && inRange n e.2) = false := by
  rw [← lower_equations_range]
  unfold F
  cases hl : lowerEquations n E with
  | none => simp
  | some es =>
      simp only [Option.isSome_some, Bool.true_eq_false, iff_false]
      cases UnificationFuel.run
        (List.map (fun e => (encode (finPresentation n) e.1,
          encode (finPresentation n) e.2)) es) SubstInfo.empty <;> simp


namespace Code

abbrev Store := List (Nat × TermN)

/-- A finite list representation uses ordinal keys and finite native trees. -/
def nativeTerm : TermN → LMonoTy
  | .of (.inl b) => leaf b
  | .of (.inr x) => .ftvar (finName x)
  | .mul l r => pair (nativeTerm l) (nativeTerm r)

end Code

end Lambda.UniformNativeUnification
