/- GID: D5/S3/ObserverMemory/Algorithms/FixedResponsePresburger
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/FixedResponsePresburger
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: Computed Presburger syntax describes exact fixed paths and final-update crossings. -/

import D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic
import Mathlib.ModelTheory.Arithmetic.Presburger.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger

open GuardedPhaseExecution FixedResponseArithmetic FirstOrder Language

universe u v w
variable {Q : Type u} {A : Type v} {R : Type w}

/-- The free variable is the update count. The only multiplication is a
computed constant acting by repeated addition on one bound variable. -/
def progressionFormula (a C : Nat) : presburger.Formula Unit :=
  if C = 0 then (Term.var ()).equal (a : presburger.Term Unit)
  else (BoundedFormula.equal
    (Term.var (Sum.inl ()))
    ((a : presburger.Term (Unit ⊕ Fin 1)) + C • Term.var (Sum.inr 0))).ex

private theorem realize_progression (a C d : Nat) :
    (progressionFormula a C).Realize (fun _ => d) ↔ ∃ m : Nat, d = a + C * m := by
  by_cases hC : C = 0
  · simp [progressionFormula, hC]
  · simp [progressionFormula, hC, Formula.Realize, BoundedFormula.Realize,
      Term.realize, Fin.snoc_zero]

/-- A list fold preserves endpoint tags before forming its finite disjunction. -/
def pathListFormula [DecidableEq Q] (data : List (Record Q)) (y : Q) :
    presburger.Formula Unit :=
  data.foldr (fun rec rest =>
    (if rec.endpoint = some y then progressionFormula rec.offset rec.increment else ⊥) ⊔ rest) ⊥

/-- A crossing retains only records ending at a genuine update predecessor.
The final edge shifts the offset by exactly one. -/
def crossingListFormula [DecidableEq Q] (prog : Q → Instruction Q A R)
    (data : List (Record Q)) (y : Q) : presburger.Formula Unit :=
  data.foldr (fun rec rest =>
    (match rec.endpoint with
      | none => ⊥
      | some z => match prog z with
        | .update t => if t = y then progressionFormula (rec.offset + 1) rec.increment else ⊥
        | _ => ⊥) ⊔ rest) ⊥

/-- Executable syntax for the fixed-response relation. -/
def pathFormula [Fintype Q] [DecidableEq Q]
    (prog : Q → Instruction Q A R) (reply : A → R) (x y : Q) : presburger.Formula Unit :=
  pathListFormula (records prog reply x) y

/-- Executable syntax for a path whose final edge is a real unit update. -/
def crossingFormula [Fintype Q] [DecidableEq Q]
    (prog : Q → Instruction Q A R) (reply : A → R) (x y : Q) : presburger.Formula Unit :=
  crossingListFormula prog (records prog reply x) y

private theorem realize_path_list [DecidableEq Q] (data : List (Record Q)) (y : Q) (d : Nat) :
    (pathListFormula data y).Realize (fun _ => d) ↔ Supports data y d := by
  let atom (rec : Record Q) : presburger.Formula Unit :=
    if rec.endpoint = some y then progressionFormula rec.offset rec.increment else ⊥
  have hfold : pathListFormula data y = (data.map atom).foldr (· ⊔ ·) ⊥ := by
    simp only [pathListFormula, List.foldr_map]
    rfl
  rw [hfold]
  simp only [Formula.Realize, BoundedFormula.realize_foldr_sup, List.mem_map]
  constructor
  · rintro ⟨formula, ⟨rec, hrec, rfl⟩, hf⟩
    by_cases he : rec.endpoint = some y
    · exact ⟨rec, hrec, he, (realize_progression rec.offset rec.increment d).mp
        (by simpa only [atom, if_pos he, Formula.Realize] using hf)⟩
    · simp [atom, he] at hf
  · rintro ⟨rec, hrec, he, hm⟩
    refine ⟨atom rec, ⟨rec, hrec, rfl⟩, ?_⟩
    simpa only [atom, if_pos he, Formula.Realize] using
      (realize_progression rec.offset rec.increment d).mpr hm

private theorem realize_crossing_list [DecidableEq Q] (prog : Q → Instruction Q A R)
    (data : List (Record Q)) (y : Q) (d : Nat) :
    (crossingListFormula prog data y).Realize (fun _ => d) ↔
      ∃ rec ∈ data, ∃ z, rec.endpoint = some z ∧ prog z = .update y ∧
        ∃ m, d = rec.offset + 1 + rec.increment * m := by
  let atom (rec : Record Q) : presburger.Formula Unit :=
    match rec.endpoint with
    | none => ⊥
    | some z => match prog z with
      | .update t => if t = y then progressionFormula (rec.offset + 1) rec.increment else ⊥
      | _ => ⊥
  have hfold : crossingListFormula prog data y = (data.map atom).foldr (· ⊔ ·) ⊥ := by
    simp only [crossingListFormula, List.foldr_map]
    rfl
  have per (rec : Record Q) : (atom rec).Realize (fun _ => d) ↔
      ∃ z, rec.endpoint = some z ∧ prog z = .update y ∧
        ∃ m, d = rec.offset + 1 + rec.increment * m := by
      cases he : rec.endpoint with
      | none => simp [atom, he, Formula.Realize]
      | some z =>
          cases hop : prog z with
          | read a k => simp [atom, he, hop, Formula.Realize]
          | halt => simp [atom, he, hop, Formula.Realize]
          | update t =>
              by_cases ht : t = y
              · subst t
                simp [atom, he, hop, realize_progression]
              · simp [atom, he, hop, ht, Formula.Realize]
  rw [hfold]
  simp only [Formula.Realize, BoundedFormula.realize_foldr_sup, List.mem_map]
  constructor
  · rintro ⟨formula, ⟨rec, hrec, rfl⟩, hf⟩
    exact ⟨rec, hrec, (per rec).mp hf⟩
  · rintro ⟨rec, hrec, hr⟩
    exact ⟨atom rec, ⟨rec, hrec, rfl⟩, (per rec).mpr hr⟩

/-- Both computed formulas are exact for the same program, response vector,
initial control, terminal control and arbitrary natural update count. -/
theorem fixed_response_formulas_correct [Fintype Q] [DecidableEq Q]
    (prog : Q → Instruction Q A R) (reply : A → R) (x y : Q) (d : Nat) :
    ((pathFormula prog reply x y).Realize (fun _ => d) ↔ FixedPath prog reply x y d) ∧
    ((crossingFormula prog reply x y).Realize (fun _ => d) ↔ Crossing prog reply x y d) := by
  constructor
  · exact (realize_path_list (records prog reply x) y d).trans
      (fixed_path_iff_support prog reply x y d).symm
  · rw [crossingFormula, realize_crossing_list]
    constructor
    · rintro ⟨rec, hrec, z, he, hop, m, hd⟩
      refine ⟨z, rec.offset + rec.increment * m, ?_, hop, by omega⟩
      exact (fixed_path_iff_support prog reply x z _).mpr ⟨rec, hrec, he, m, rfl⟩
    · rintro ⟨z, c, path, hop, hd⟩
      obtain ⟨rec, hrec, he, m, hc⟩ := (fixed_path_iff_support prog reply x z c).mp path
      exact ⟨rec, hrec, z, he, hop, m, by omega⟩

#print axioms fixed_response_formulas_correct

end D5.S3.ObserverMemory.Algorithms.FixedResponsePresburger
