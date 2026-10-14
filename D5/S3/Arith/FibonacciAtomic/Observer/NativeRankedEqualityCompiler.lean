/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedEqualityCompiler
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact finite offset equations for native ranked expression equality. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization
import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
import Mathlib.ModelTheory.Complexity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler

open GenealogicalFiberTransport (Source substitution)
open NativePrefixIdentityReflection (MixedExpr eval kappa kappa_iterate)
open NativeUniformResidualRealization (RankedExpr rankedEval)

/-- A shared scalar variable plus a fixed offset, or a fixed natural number. -/
abbrev Offset (k : Nat) := Option (Fin k) × Nat

def offsetValue {k : Nat} (n : Fin k → Nat) (q : Offset k) : Nat :=
  (q.1.map n).getD 0 + q.2

def addOffset {k : Nat} (q : Offset k) (a : Nat) : Offset k := (q.1, q.2 + a)

/-- Leaves denote atomic iterates; pairs retain the native ordered tree structure. -/
abbrev RankTerm (k : Nat) := FreeMagma (Offset k)

def termValue {k : Nat} (n : Fin k → Nat) : RankTerm k → Source
  | .of q => substitution^[offsetValue n q] (.of true)
  | .mul A B => .mul (termValue n A) (termValue n B)

def groundTerm {k : Nat} : Source → RankTerm k
  | .of true => .of (none, 0)
  | .of false => .of (none, 1)
  | .mul A B => .mul (groundTerm A) (groundTerm B)

/-- Fix only finite residual inputs, retaining the scalar variables symbolically. -/
def normalize {k m : Nat} (z : Fin m → Source) : RankedExpr k m → RankTerm k
  | .ground g => groundTerm g
  | .residual a (.inl j) => .of (some j, a)
  | .residual a (.inr i) => groundTerm (substitution^[a] (z i))
  | .pair A B => .mul (normalize z A) (normalize z B)

private theorem ground_value {k : Nat} (n : Fin k → Nat) (g : Source) :
    termValue n (groundTerm g) = g := by
  induction g with
  | of b => cases b <;> rfl
  | mul A B ihA ihB => exact congrArg₂ FreeMagma.mul ihA ihB

private theorem normalize_value {k m : Nat} (n : Fin k → Nat) (z : Fin m → Source)
    (E : RankedExpr k m) : termValue n (normalize z E) = rankedEval n z E := by
  induction E with
  | ground g => exact ground_value n g
  | residual a i => cases i with
    | inl j =>
        change substitution^[n j + a] (.of true) =
          substitution^[a] (substitution^[n j] (.of true))
        rw [Nat.add_comm, Function.iterate_add_apply]
    | inr i => exact ground_value n _
  | pair A B ihA ihB => exact congrArg₂ FreeMagma.mul ihA ihB

private theorem add_value {k : Nat} (n : Fin k → Nat) (q : Offset k) (a : Nat) :
    offsetValue n (addOffset q a) = offsetValue n q + a := by
  simp [offsetValue, addOffset, Nat.add_assoc]

theorem atomic_injective :
    Function.Injective (fun r : Nat => substitution^[r] (.of true)) := by
  intro a b h
  have clock := congrArg kappa h
  simpa only [kappa_iterate, kappa, Nat.zero_add] using clock

theorem atomic_pair (s : Nat) :
    substitution^[s+2] (.of true) =
      .mul (substitution^[s+1] (.of true)) (substitution^[s] (.of true)) := by
  rw [Function.iterate_add_apply]
  change substitution^[s] (.mul (.of false) (.of true)) = _
  rw [Function.Semiconj₂.iterate
    (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
      fun A B => substitution.map_mul A B) s (.of false) (.of true)]
  congr 1

/-- The existing native right clock expressed as one scalar offset. -/
def clock {k : Nat} : RankTerm k → Offset k
  | .of q => q
  | .mul _ B => addOffset (clock B) 2

def Satisfies {k : Nat} (n : Fin k → Nat) (C : List (Offset k × Offset k)) : Prop :=
  ∀ p ∈ C, offsetValue n p.1 = offsetValue n p.2

private theorem satisfies_append {k : Nat} (n : Fin k → Nat)
    (C D : List (Offset k × Offset k)) :
    Satisfies n (C ++ D) ↔ Satisfies n C ∧ Satisfies n D := by
  simp only [Satisfies, List.mem_append, or_imp, forall_and]

private theorem satisfies_singleton {k : Nat} (n : Fin k → Nat) (q r : Offset k) :
    Satisfies n [(q,r)] ↔ offsetValue n q = offsetValue n r := by
  simp only [Satisfies, List.mem_singleton, forall_eq]

/-- Each pair is atomic exactly when its children are atomic with consecutive ranks. -/
def atomicConditions {k : Nat} : RankTerm k → List (Offset k × Offset k)
  | .of _ => []
  | .mul A B => atomicConditions A ++ atomicConditions B ++
      [(clock A, addOffset (clock B) 1)]

private theorem atomic_conditions_iff {k : Nat} (n : Fin k → Nat) (T : RankTerm k)
    (r : Nat) : termValue n T = substitution^[r] (.of true) ↔
      Satisfies n (atomicConditions T) ∧ offsetValue n (clock T) = r := by
  induction T generalizing r with
  | of q =>
      simp only [termValue, atomic_injective.eq_iff, atomicConditions, clock,
        Satisfies, List.not_mem_nil, false_implies, forall_const, true_and]
  | mul A B ihA ihB =>
      have split : Satisfies n (atomicConditions (.mul A B)) ↔
          Satisfies n (atomicConditions A) ∧ Satisfies n (atomicConditions B) ∧
            offsetValue n (clock A) = offsetValue n (clock B) + 1 := by
        simp only [atomicConditions, satisfies_append, satisfies_singleton, add_value, and_assoc]
      rw [split]
      change termValue n (.mul A B) = substitution^[r] (.of true) ↔
        _ ∧ offsetValue n (addOffset (clock B) 2) = r
      rw [add_value]
      constructor
      · intro h
        cases r with
        | zero => cases h
        | succ r => cases r with
          | zero => cases h
          | succ s =>
              rw [show s+1+1 = s+2 by omega, atomic_pair] at h
              have sides : termValue n A = substitution^[s+1] (.of true) ∧
                  termValue n B = substitution^[s] (.of true) := by
                injection h with ha hb; exact ⟨ha,hb⟩
              obtain ⟨ha, ka⟩ := (ihA (s+1)).mp sides.1
              obtain ⟨hb, kb⟩ := (ihB s).mp sides.2
              exact ⟨⟨ha, hb, by omega⟩, by omega⟩
      · rintro ⟨⟨ha, hb, ranks⟩, rfl⟩
        rw [atomic_pair]
        exact congrArg₂ FreeMagma.mul ((ihA _).mpr ⟨ha, ranks⟩)
          ((ihB _).mpr ⟨hb, rfl⟩)

/-- Native equality produces a conjunction of affine rank equalities. -/
def equalityConditions {k : Nat} : RankTerm k → RankTerm k → List (Offset k × Offset k)
  | .of q, .of r => [(q,r)]
  | .of q, .mul A B => atomicConditions (.mul A B) ++ [(q,clock (.mul A B))]
  | .mul A B, .of q => atomicConditions (.mul A B) ++ [(clock (.mul A B),q)]
  | .mul A B, .mul C D => equalityConditions A C ++ equalityConditions B D

private theorem equality_conditions_iff {k : Nat} (n : Fin k → Nat) (T U : RankTerm k) :
    Satisfies n (equalityConditions T U) ↔ termValue n T = termValue n U := by
  induction T generalizing U with
  | of q => cases U with
    | of r => simp only [equalityConditions, satisfies_singleton, termValue,
        atomic_injective.eq_iff]
    | mul A B =>
        simpa only [equalityConditions, satisfies_append, satisfies_singleton,
          termValue, eq_comm] using
          (atomic_conditions_iff n (.mul A B) (offsetValue n q)).symm
  | mul A B ihA ihB => cases U with
    | of q =>
        simpa only [equalityConditions, satisfies_append, satisfies_singleton, termValue] using
          (atomic_conditions_iff n (.mul A B) (offsetValue n q)).symm
    | mul C D =>
        rw [equalityConditions, satisfies_append, ihA C, ihB D]
        change (_ = _ ∧ _ = _) ↔ FreeMagma.mul _ _ = FreeMagma.mul _ _
        constructor
        · rintro ⟨hA,hB⟩; exact congrArg₂ FreeMagma.mul hA hB
        · intro h; injection h with hA hB; exact ⟨hA,hB⟩

/-- All ranks remain free in this finite output. -/
def compileEquality {k m : Nat} (z : Fin m → Source) (E F : RankedExpr k m) :
    List (Offset k × Offset k) := equalityConditions (normalize z E) (normalize z F)

/-- The compiler is exact for every scalar tuple and every fixed finite residual tuple. -/
private theorem compile_equality_correct {k m : Nat} (z : Fin m → Source)
    (E F : RankedExpr k m) (n : Fin k → Nat) :
    Satisfies n (compileEquality z E F) ↔ rankedEval n z E = rankedEval n z F := by
  simpa only [compileEquality, normalize_value] using
    equality_conditions_iff n (normalize z E) (normalize z F)

open FirstOrder.Language

/-- Natural Presburger terms preserve constants and the original free scalar names. -/
def offsetTerm {k : Nat} (q : Offset k) : presburger.Term (Fin k ⊕ Fin 0) :=
  match q.1 with
  | none => (q.2 : presburger.Term (Fin k ⊕ Fin 0))
  | some j => .var (.inl j) + (q.2 : presburger.Term (Fin k ⊕ Fin 0))

/-- A list of rank equalities becomes a quantifier-free Presburger conjunction. -/
def conditionsFormula {k : Nat} (C : List (Offset k × Offset k)) :
    presburger.Formula (Fin k) :=
  (C.map fun p => (offsetTerm p.1).bdEqual (offsetTerm p.2)).foldr (· ⊓ ·) ⊤

private theorem offset_realize {k : Nat} (n : Fin k → Nat) (q : Offset k)
    (empty : Fin 0 → Nat) :
    (offsetTerm q).realize (Sum.elim n empty) = offsetValue n q := by
  rcases q with ⟨q,a⟩
  cases q <;> simp [offsetTerm, offsetValue]

private theorem conditions_qf {k : Nat} (C : List (Offset k × Offset k)) :
    (conditionsFormula C).IsQF := by
  induction C with
  | nil => exact BoundedFormula.IsQF.top
  | cons p C ih =>
      exact (BoundedFormula.IsAtomic.equal _ _).isQF.inf ih

private theorem conditions_realize {k : Nat} (n : Fin k → Nat)
    (C : List (Offset k × Offset k)) :
    (conditionsFormula C).Realize n ↔ Satisfies n C := by
  simp only [conditionsFormula, Formula.Realize, BoundedFormula.realize_foldr_inf,
    List.forall_mem_map, BoundedFormula.realize_bdEqual, offset_realize, Satisfies]

/-- The produced formula is finite and keeps every original scalar free. -/
def equalityFormula {k m : Nat} (z : Fin m → Source) (E F : RankedExpr k m) :
    presburger.Formula (Fin k) := conditionsFormula (compileEquality z E F)

/-- Quantifier-free scalar formulas exactly express native equality at fixed residuals. -/
theorem ranked_equality_compilation (k m : Nat) (z : Fin m → Source)
    (E F : RankedExpr k m) :
    (equalityFormula z E F).IsQF ∧ ∀ n : Fin k → Nat,
      (equalityFormula z E F).Realize n ↔ rankedEval n z E = rankedEval n z F := by
  refine ⟨conditions_qf _, fun n => ?_⟩
  exact (conditions_realize n _).trans (compile_equality_correct z E F n)

/-- A single uniform residual tuple is substituted into the entire negative list. -/
def supportFormula {k m : Nat} (pairs : List (RankedExpr k m × RankedExpr k m)) :
    presburger.Formula (Fin k) :=
  ((pairs.map fun p => (equalityFormula
    (NativeUniformResidualRealization.uniformSeparator pairs) p.1 p.2).not)).foldr (· ⊓ ·) ⊤

/-- The exact feasible-rank support is computed without enumerating any ranks. -/
theorem support_compilation (k m : Nat)
    (pairs : List (RankedExpr k m × RankedExpr k m)) :
    (supportFormula pairs).IsQF ∧ ∀ n : Fin k → Nat,
      (supportFormula pairs).Realize n ↔ ∃ z : Fin m → Source,
        ∀ p ∈ pairs, rankedEval n z p.1 ≠ rankedEval n z p.2 := by
  constructor
  · unfold supportFormula
    have qf : ∀ f ∈ pairs.map (fun p => (equalityFormula
        (NativeUniformResidualRealization.uniformSeparator pairs) p.1 p.2).not),
        f.IsQF := by
      intro f hf
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp hf
      exact (ranked_equality_compilation k m _ _ _).1.not
    generalize pairs.map (fun p => (equalityFormula
        (NativeUniformResidualRealization.uniformSeparator pairs) p.1 p.2).not) = fs at *
    induction fs with
    | nil => exact BoundedFormula.IsQF.top
    | cons f fs ih =>
        exact (qf f (by simp)).inf (ih (fun g hg => qf g (by simp [hg])))
  · intro n
    have formula : (supportFormula pairs).Realize n ↔ ∀ p ∈ pairs,
        rankedEval n (NativeUniformResidualRealization.uniformSeparator pairs) p.1 ≠
          rankedEval n (NativeUniformResidualRealization.uniformSeparator pairs) p.2 := by
      simp only [supportFormula, Formula.Realize, BoundedFormula.realize_foldr_inf,
        List.forall_mem_map, BoundedFormula.realize_not]
      exact forall_congr' fun p => forall_congr' fun _ => not_congr
        ((ranked_equality_compilation k m _ p.1 p.2).2 n)
    rw [formula]
    constructor
    · intro h; exact ⟨NativeUniformResidualRealization.uniformSeparator pairs,h⟩
    · rintro ⟨z,h⟩
      exact (NativeUniformResidualRealization.simultaneous_completion k m pairs n).mp
        (fun p hp => ⟨z,h p hp⟩)

#print axioms ranked_equality_compilation
#print axioms support_compilation
end D5.S3.Arith.FibonacciAtomic.Observer.NativeRankedEqualityCompiler
