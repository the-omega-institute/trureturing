/- GID: D5/S3/ObserverMemory/Algorithms/GuardedPhaseExecution
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/GuardedPhaseExecution
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: Same-source guarded weighted paths recover exact finite executions. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution

universe u v w

/-- Instructions inspect a single literal address, update once, or halt. -/
inductive Instruction (Q : Type u) (A : Type v) (R : Type w) where
  | read : A → (R → Q) → Instruction Q A R
  | update : Q → Instruction Q A R
  | halt : Instruction Q A R

variable {Q : Type u} {A : Type v} {R : Type w}

/-- A finite actual path, retaining the original source's one observation field.
A halt instruction has no outgoing edge. -/
inductive Run (prog : Q → Instruction Q A R) (obs : Nat → A → R) :
    Q → Nat → Q → Nat → Prop where
  | refl (x : Q) (a : Nat) : Run prog obs x a x a
  | read {x : Q} {p : A} {k : R → Q} {a : Nat} {y : Q} {b : Nat} :
      prog x = .read p k → Run prog obs (k (obs a p)) a y b → Run prog obs x a y b
  | update {x z : Q} {a : Nat} {y : Q} {b : Nat} :
      prog x = .update z → Run prog obs z (a + 1) y b → Run prog obs x a y b

/-- A fixed-response path carries its exact number of updates. -/
inductive FixedPath (prog : Q → Instruction Q A R) (reply : A → R) :
    Q → Q → Nat → Prop where
  | refl (x : Q) : FixedPath prog reply x x 0
  | read {x : Q} {p : A} {k : R → Q} {y : Q} {d : Nat} :
      prog x = .read p k → FixedPath prog reply (k (reply p)) y d →
      FixedPath prog reply x y d
  | update {x z y : Q} {d : Nat} :
      prog x = .update z → FixedPath prog reply z y d →
      FixedPath prog reply x y (d + 1)

/-- The last edge crosses the boundary by exactly one real update. -/
def Crossing (prog : Q → Instruction Q A R) (reply : A → R)
    (x y : Q) (d : Nat) : Prop :=
  ∃ z c, FixedPath prog reply x z c ∧ prog z = .update y ∧ d = c + 1

/-- Every epoch in a half-open interval has one response vector on the same source. -/
def Guard (obs : Nat → A → R) (reply : A → R) (a b : Nat) : Prop :=
  ∀ j, a ≤ j → j < b → obs j = reply

/-- A nonempty, strictly increasing partition with its terminal delimiter. -/
def Partition (obs : Nat → A → R) (a last : Nat) : List (Nat × (A → R)) → Prop
  | [] => False
  | [(b, reply)] => a < b ∧ b = last ∧ Guard obs reply a b
  | (b, reply) :: next :: rest =>
      a < b ∧ Guard obs reply a b ∧ Partition obs b last (next :: rest)

/-- Endpoint-exact paths, with a final update at every internal boundary.
The last delimiter is one epoch after the final state, not an extra update. -/
def PhasePaths (prog : Q → Instruction Q A R) (x : Q) (a : Nat) (h : Q) (J : Nat) :
    List (Nat × (A → R)) → Prop
  | [] => False
  | [(b, reply)] => b = J + 1 ∧ FixedPath prog reply x h (J - a)
  | (b, reply) :: next :: rest =>
      ∃ y, Crossing prog reply x y (b - a) ∧ PhasePaths prog y b h J (next :: rest)

theorem run_epochs {prog : Q → Instruction Q A R} {obs : Nat → A → R}
    {x y : Q} {a b : Nat} (path : Run prog obs x a y b) : a ≤ b := by
  induction path with
  | refl => exact le_rfl
  | read _ _ ih => exact ih
  | update _ _ ih => omega

private theorem run_trans {prog : Q → Instruction Q A R} {obs : Nat → A → R}
    {x y z : Q} {a b c : Nat} (left : Run prog obs x a y b)
    (right : Run prog obs y b z c) : Run prog obs x a z c := by
  induction left generalizing z c with
  | refl => exact right
  | read hop _ ih => exact .read hop (ih right)
  | update hop _ ih => exact .update hop (ih right)

private theorem fixed_to_run {prog : Q → Instruction Q A R} {obs : Nat → A → R}
    {reply : A → R} {x y : Q} {d : Nat} (path : FixedPath prog reply x y d)
    (a : Nat) (guard : ∀ j, a ≤ j → j ≤ a + d → obs j = reply) :
    Run prog obs x a y (a + d) := by
  induction path generalizing a with
  | refl => simpa using Run.refl _ _
  | @read x p k y d hop tail ih =>
      have response := congrFun (guard a (by omega) (by omega)) p
      have next := ih a guard
      rw [← response] at next
      exact .read hop next
  | @update x z y d hop tail ih =>
      have next := ih (a + 1) (by
        intro j hj hk
        exact guard j (by omega) (by omega))
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Run.update hop next

private theorem run_to_fixed {prog : Q → Instruction Q A R} {obs : Nat → A → R}
    {reply : A → R} {x y : Q} {a b : Nat} (path : Run prog obs x a y b)
    (guard : ∀ j, a ≤ j → j ≤ b → obs j = reply) :
    FixedPath prog reply x y (b - a) := by
  induction path with
  | refl => simpa using FixedPath.refl _
  | @read x p k a y b hop tail ih =>
      have response := congrFun (guard a (by omega) (run_epochs tail)) p
      have next := ih guard
      rw [response] at next
      exact .read hop next
  | @update x z a y b hop tail ih =>
      have hab := run_epochs tail
      have next := ih (by intro j hj hk; exact guard j (by omega) hk)
      convert FixedPath.update hop next using 1; omega

/-- A prescribed later epoch is first entered by a final unit update. -/
private theorem run_split {prog : Q → Instruction Q A R} {obs : Nat → A → R}
    {x y : Q} {a b c : Nat} (path : Run prog obs x a y b)
    (lower : a < c) (upper : c ≤ b) :
    ∃ z t, Run prog obs x a z (c - 1) ∧ prog z = .update t ∧ Run prog obs t c y b := by
  induction path with
  | refl => omega
  | @read x p k a y b hop tail ih =>
      obtain ⟨z, t, initialPath, update, suffix⟩ := ih lower upper
      exact ⟨z, t, .read hop initialPath, update, suffix⟩
  | @update x z a y b hop tail ih =>
      by_cases boundary : a + 1 = c
      · exact ⟨x, z, by simpa [← boundary] using Run.refl x a, hop,
          by simpa [← boundary] using tail⟩
      · obtain ⟨p, t, initialPath, update, suffix⟩ := ih (by omega) upper
        exact ⟨p, t, .update hop initialPath, update, suffix⟩

private theorem partition_nonempty {obs : Nat → A → R} {a b : Nat}
    {blocks : List (Nat × (A → R))} (partition : Partition obs a b blocks) : a < b := by
  induction blocks generalizing a with
  | nil => exact partition.elim
  | cons block rest ih =>
      rcases block with ⟨c, reply⟩
      cases rest with
      | nil => exact partition.2.1 ▸ partition.1
      | cons next rest => exact lt_trans partition.1 (ih partition.2.2)

/-- For any guarded partition, phase paths describe exactly the actual finite
execution with the same starting and ending controls and epochs. -/
theorem guarded_phase_execution {prog : Q → Instruction Q A R} {obs : Nat → A → R}
    {x h : Q} {a J : Nat} {blocks : List (Nat × (A → R))}
    (partition : Partition obs a (J + 1) blocks) :
    PhasePaths prog x a h J blocks ↔ Run prog obs x a h J := by
  induction blocks generalizing x a with
  | nil => exact partition.elim
  | cons block rest ih =>
      rcases block with ⟨b, reply⟩
      cases rest with
      | nil =>
          rcases partition with ⟨hab, rfl, guard⟩
          constructor
          · rintro ⟨_, path⟩
            have actual := fixed_to_run path a (by
              intro j hj hk
              exact guard j hj (by omega))
            simpa [Nat.add_sub_of_le (show a ≤ J by omega)] using actual
          · intro path
            exact ⟨rfl, run_to_fixed path (by intro j hj hk; exact guard j hj (by omega))⟩
      | cons next rest =>
          rcases partition with ⟨hab, guard, remaining⟩
          have hbJ := partition_nonempty remaining
          constructor
          · rintro ⟨y, ⟨z, c, initialPath, hop, count⟩, suffix⟩
            have first := fixed_to_run initialPath a (by
              intro j hj hk
              exact guard j hj (by omega))
            have last := Run.update (obs := obs) (a := a + c) hop
              (Run.refl y (a + c + 1))
            have endpoint : a + c + 1 = b := by omega
            rw [endpoint] at last
            exact run_trans (run_trans first last) ((ih remaining).mp suffix)
          · intro path
            obtain ⟨z, y, initialPath, hop, suffix⟩ := run_split path hab (by omega)
            have fixed := run_to_fixed initialPath (by
              intro j hj hk
              exact guard j hj (by omega))
            exact ⟨y, ⟨z, b - 1 - a, fixed, hop, by omega⟩, (ih remaining).mpr suffix⟩

#print axioms guarded_phase_execution

end D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
