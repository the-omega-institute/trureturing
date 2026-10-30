/- GID: D5/S3/Observer/Completion/TypedCocycleSource
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/TypedCocycleSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exhaustive legal words and native totals on the shared-name two-loop source. -/

import Mathlib.Tactic
import Mathlib.Data.List.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Completion.TypedCocycleSource

inductive Vertex | p | s | t deriving DecidableEq
inductive Name | a | c | e deriving DecidableEq

instance : Fintype Vertex where
  elems := {.p, .s, .t}
  complete x := by cases x <;> simp
instance : Fintype Name where
  elems := {.a, .c, .e}
  complete x := by cases x <;> simp

/-- Exactly the four legal edges, with one shared name a and no Stop edge. -/
def transition : Vertex → Name → Option Vertex
  | .p, .a => some .p
  | .p, .c => some .s
  | .s, .a => some .s
  | .s, .e => some .t
  | _, _ => none

/-- Execution starts at the supplied vertex; illegal names reject. -/
def execute (z : Vertex) : List Name → Option Vertex
  | [] => some z
  | b :: w => (transition z b).bind fun z' => execute z' w

/-- All nonnegative lap counts, including empty and zero-lap histories. -/
inductive History
  | pre (m : ℕ)
  | mid (m n : ℕ)
  | terminal (m n : ℕ)
  deriving DecidableEq

def endpoint : History → Vertex
  | .pre _ => .p
  | .mid _ _ => .s
  | .terminal _ _ => .t

def word : History → List Name
  | .pre m => List.replicate m .a
  | .mid m n => List.replicate m .a ++ [.c] ++ List.replicate n .a
  | .terminal m n => List.replicate m .a ++ [.c] ++ List.replicate n .a ++ [.e]

/-- An executed name extends a history only when legal at its endpoint. -/
def advance : History → Name → Option History
  | .pre m, .a => some (.pre (m + 1))
  | .pre m, .c => some (.mid m 0)
  | .mid m n, .a => some (.mid m (n + 1))
  | .mid m n, .e => some (.terminal m n)
  | _, _ => none

private theorem execute_append (z : Vertex) (u v : List Name) :
    execute z (u ++ v) = (execute z u).bind (fun z' => execute z' v) := by
  induction u generalizing z with
  | nil => rfl
  | cons b u ih =>
    simp only [List.cons_append, execute]
    cases hh : transition z b <;> simp [hh, ih]

private theorem execute_replicate_a (m : ℕ) :
    execute .p (List.replicate m .a) = some .p ∧
    execute .s (List.replicate m .a) = some .s := by
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih => simpa [List.replicate_succ, execute, transition] using ih

private theorem executes (u : History) : execute .p (word u) = some (endpoint u) := by
  cases u with
  | pre m => exact (execute_replicate_a m).1
  | mid m n => simp [word, endpoint, execute_append, execute_replicate_a, execute, transition]
  | terminal m n => simp [word, endpoint, execute_append, execute_replicate_a, execute, transition]

private theorem extension (u : History) (b : Name) (z : Vertex)
    (hh : transition (endpoint u) b = some z) :
    ∃ v : History, advance u b = some v ∧ word v = word u ++ [b] ∧ endpoint v = z := by
  cases u <;> cases b <;> simp [endpoint, transition] at hh
  all_goals subst z
  · refine ⟨.pre _, rfl, ?_, rfl⟩
    simp [word, List.replicate_succ', List.append_assoc]
  · exact ⟨.mid _ 0, rfl, by simp [word], rfl⟩
  · refine ⟨.mid _ _, rfl, ?_, rfl⟩
    simp [word, List.replicate_succ', List.append_assoc]
  · exact ⟨.terminal _ _, rfl, rfl, rfl⟩

private theorem exhaustive (w : List Name) (z : Vertex) (hh : execute .p w = some z) :
    ∃ u : History, word u = w ∧ endpoint u = z := by
  induction w using List.reverseRecOn generalizing z with
  | nil =>
    have hz : Vertex.p = z := by simpa [execute] using hh
    exact ⟨.pre 0, rfl, hz⟩
  | append_singleton w b ih =>
    rw [execute_append] at hh
    cases hw : execute .p w with
    | none => simp [hw] at hh
    | some v =>
      obtain ⟨u, hu, hv⟩ := ih v hw
      have hb : transition (endpoint u) b = some z := by
        simpa [hw, execute, hv] using hh
      obtain ⟨v', _, hw', hz'⟩ := extension u b z hb
      exact ⟨v', by simpa [hu] using hw', hz'⟩

private theorem word_injective : Function.Injective word := by
  intro u v huv
  have hep : endpoint u = endpoint v := by
    have hh := executes u
    rw [huv, executes v] at hh
    exact (Option.some.inj hh).symm
  cases u with
  | pre m =>
    cases v with
    | pre m' =>
      have hh := congrArg List.length huv
      simp [word] at hh
      exact congrArg History.pre hh
    | mid => cases hep
    | terminal => cases hep
  | mid m n =>
    cases v with
    | pre => cases hep
    | terminal => cases hep
    | mid m' n' =>
      have hm := congrArg (fun w : List Name => (w.takeWhile (· == .a)).length) huv
      have hn := congrArg List.length huv
      simp [word, List.takeWhile_append, List.takeWhile_replicate] at hm
      have hm' : m = m' := by simpa using hm
      have hn' : n = n' := by simp [word] at hn; omega
      exact congrArg₂ History.mid hm' hn'
  | terminal m n =>
    cases v with
    | pre => cases hep
    | mid => cases hep
    | terminal m' n' =>
      have hm := congrArg (fun w : List Name => (w.takeWhile (· == .a)).length) huv
      have hn := congrArg List.length huv
      simp [word, List.takeWhile_append, List.takeWhile_replicate] at hm
      have hm' : m = m' := by simpa using hm
      have hn' : n = n' := by simp [word] at hn; omega
      exact congrArg₂ History.terminal hm' hn'

abbrev Vector := ℝ × ℝ

/-- The fixed native edge vectors A=h(1,1), B=h(1,2), C and E. -/
def edgeVector (h : ℝ) (C E : Vector) : Vertex → Name → Vector
  | .p, .a => (h, h)
  | .s, .a => (h, 2 * h)
  | .p, .c => C
  | .s, .e => E
  | _, _ => 0

/-- Additive native total on actual executions; illegal histories reject. -/
def accumulate (h : ℝ) (C E : Vector) (z : Vertex) : List Name → Option Vector
  | [] => some 0
  | b :: w => (transition z b).bind fun z' =>
      (accumulate h C E z' w).map (edgeVector h C E z b + ·)

def native (h : ℝ) (C E : Vector) : History → Vector
  | .pre m => (h * m, h * m)
  | .mid m n => (C.1 + h * (m + n), C.2 + h * (m + 2 * n))
  | .terminal m n => (C.1 + E.1 + h * (m + n), C.2 + E.2 + h * (m + 2 * n))

private theorem accumulate_append (h : ℝ) (C E : Vector) (z z' : Vertex)
    (u v : List Name) (hu : execute z u = some z') :
    accumulate h C E z (u ++ v) =
      (accumulate h C E z u).bind fun x => (accumulate h C E z' v).map (x + ·) := by
  induction u generalizing z with
  | nil => simp [execute] at hu; subst z'; simp [accumulate]
  | cons b u ih =>
    cases hb : transition z b with
    | none => simp [execute, hb] at hu
    | some z'' =>
      simp [execute, hb] at hu
      simp only [List.cons_append, accumulate, hb, Option.bind_some]
      rw [ih z'' hu]
      cases hx : accumulate h C E z'' u <;> cases hy : accumulate h C E z' v <;>
        simp [hx, hy, add_assoc]

private theorem accumulate_a (h : ℝ) (C E : Vector) (m : ℕ) :
    accumulate h C E .p (List.replicate m .a) = some (h * m, h * m) ∧
    accumulate h C E .s (List.replicate m .a) = some (h * m, 2 * h * m) := by
  induction m with
  | zero => constructor <;> simp [accumulate] <;> rfl
  | succ m ih =>
    simp only [List.replicate_succ, accumulate, transition, Option.bind_some, ih,
      Option.map_some, edgeVector, Prod.mk_add_mk, Nat.cast_add, Nat.cast_one]
    constructor <;> congr 2 <;> ring

private theorem totals_mid (h : ℝ) (C E : Vector) (m n : ℕ) :
    accumulate h C E .p (word (.mid m n)) = some (native h C E (.mid m n)) := by
  simp [word, native, accumulate_append h C E .p .p _ _ (execute_replicate_a m).1,
    accumulate_a, accumulate, transition, edgeVector, Prod.mk_add_mk]
  apply Prod.ext <;> dsimp <;> ring

private theorem totals (h : ℝ) (C E : Vector) (u : History) :
    accumulate h C E .p (word u) = some (native h C E u) := by
  cases u with
  | pre m => exact (accumulate_a h C E m).1
  | mid m n => exact totals_mid h C E m n
  | terminal m n =>
    have hw : word (.terminal m n) = word (.mid m n) ++ [.e] := by
      simp [word, List.append_assoc]
    rw [hw, accumulate_append h C E .p .s _ [.e] (executes (.mid m n))]
    have hm := totals_mid h C E m n
    simp only [word] at hm
    rw [hm]
    simp [accumulate, transition, edgeVector, native, Prod.mk_add_mk]
    apply Prod.ext <;> dsimp <;> ring

/-- Faithful ordered-word bijection with all legal root histories, together with
native totals obtained from exactly the four source edges. This includes every
finite cut, without adding an operation for stopping. -/
theorem source_correspondence (h : ℝ) (C E : Vector) :
    Function.Injective word ∧
    (∀ w z, execute .p w = some z ↔ ∃ u : History, word u = w ∧ endpoint u = z) ∧
    (∀ u, execute .p (word u) = some (endpoint u) ∧
      accumulate h C E .p (word u) = some (native h C E u)) := by
  refine ⟨word_injective, ?_, fun u => ⟨executes u, totals h C E u⟩⟩
  intro w z
  constructor
  · exact exhaustive w z
  · rintro ⟨u, rfl, rfl⟩
    exact executes u

#print axioms source_correspondence
end D5.S3.Observer.Completion.TypedCocycleSource
