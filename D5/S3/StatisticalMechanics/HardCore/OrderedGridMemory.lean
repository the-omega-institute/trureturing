/- GID: D5/S3/StatisticalMechanics/HardCore/OrderedGridMemory
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/HardCore/OrderedGridMemory
   mirror-E: none(waiver:symbolic-geometric-simulation)
   anchors: []
   digest: Truncated geometric blockers cover exact ordered square-grid deletion paths. -/

import D5.S3.StatisticalMechanics.HardCore.BranchingPotential

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory

open scoped BigOperators
open D5.S3.StatisticalMechanics.HardCore.BranchingPotential

/-- Integer square-grid coordinates relative to an east-facing incoming edge. -/
abbrev Point := ℤ × ℤ

/-- Forward, right, left. The parent direction is already deleted. -/
def direction (d : Fin 3) : Point :=
  if d = 0 then (1, 0) else if d = 1 then (0, -1) else (0, 1)

/-- Positions in the six permutations SRL, SLR, RSL, RLS, LSR, LRS. -/
def position (a : Fin 6) (d : Fin 3) : ℕ :=
  match a.val, d.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, _ => 2
  | 1, 0 => 0 | 1, 1 => 2 | 1, _ => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, _ => 2
  | 3, 0 => 2 | 3, 1 => 0 | 3, _ => 1
  | 4, 0 => 1 | 4, 1 => 2 | 4, _ => 0
  | _, 0 => 2 | _, 1 => 1 | _, _ => 0

/-- Vertices deleted before following the selected child. Earlier absent
neighbors may be included: deleting them again has no effect. -/
def deleted (a : Fin 6) (d : Fin 3) : Finset Point :=
  insert (0, 0) ((Finset.univ.filter fun e => position a e < position a d).image direction)

/-- Translate to the chosen neighbor and rotate its incoming heading to east. -/
def recenter (d : Fin 3) (p : Point) : Point :=
  if d = 0 then (p.1 - 1, p.2)
  else if d = 1 then (-p.2 - 1, p.1)
  else (p.2 - 1, -p.1)

/-- These coordinate changes preserve vertex identities. -/
theorem recenter_injective (d : Fin 3) : Function.Injective (recenter d) := by
  intro x y h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext
  · fin_cases d <;> simp [recenter] at hx hy ⊢ <;> omega
  · fin_cases d <;> simp [recenter] at hx hy ⊢ <;> omega

/-- The exact remaining finite vertex domain after an ordered deletion step. -/
def advance (V : Finset Point) (a : Fin 6) (d : Fin 3) : Finset Point :=
  (V \ deleted a d).image (recenter d)

/-- Retain known deleted vertices only within the prescribed Manhattan radius.
Discarding a blocker can add paths; it cannot remove a genuine path. -/
def memoryStep (radius : ℕ) (F : Finset Point) (a : Fin 6) (d : Fin 3) :
    Finset Point :=
  ((F ∪ deleted a d).image (recenter d)).filter fun p =>
    p.1.natAbs + p.2.natAbs ≤ radius

/-- A domain disjoint from its recorded blockers remains so after the actual
geometric deletion and recentering, for every radius and every ordering. -/
theorem advance_disjoint_memoryStep (radius : ℕ) (V F : Finset Point)
    (a : Fin 6) (d : Fin 3) (h : Disjoint V F) :
    Disjoint (advance V a d) (memoryStep radius F a d) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hy
  rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
  rcases Finset.mem_filter.mp hy with ⟨hy, _⟩
  rcases Finset.mem_image.mp hy with ⟨v, hv, heq⟩
  have hvu : v = u := recenter_injective d heq
  subst v
  rcases Finset.mem_sdiff.mp hu with ⟨huV, huD⟩
  rcases Finset.mem_union.mp hv with huF | huK
  · exact h huV huF
  · exact huD huK

/-- Exact ordered deletion-path count on a finite domain. Child availability
is decided solely by membership in V. A missing table entry uses a fallback
state, so coverage is an obligation proved separately, never built into the count. -/
def orderedCount {State : Type*}
    (step : State → Fin 6 → Fin 3 → Option State)
    (choose : State → Fin 6) (fallback : State) : ℕ → Finset Point → State → ℕ
  | 0, _, _ => 1
  | n + 1, V, i => ∑ d : Fin 3,
      if direction d ∈ V then
        orderedCount step choose fallback n (advance V (choose i) d)
          ((step i (choose i) d).getD fallback)
      else 0

/-- Full finite-domain simulation. The only table obligations are rejection
exactly at recorded blockers and equality with the actual geometric update. -/
theorem orderedCount_le_pathCount {State : Type*}
    (step : State → Fin 6 → Fin 3 → Option State)
    (choose : State → Fin 6) (fallback : State) (mask : State → Finset Point)
    (radius : ℕ)
    (hblocked : ∀ i a d, step i a d = none ↔ direction d ∈ mask i)
    (hnext : ∀ i a d j, step i a d = some j →
      mask j = memoryStep radius (mask i) a d)
    (n : ℕ) (V : Finset Point) (i : State) (history : List (Fin 3))
    (hdis : Disjoint V (mask i)) :
    orderedCount step choose fallback n V i ≤
      pathCount step (fun _ j => choose j) n history i := by
  induction n generalizing V i history with
  | zero => simp [orderedCount, pathCount]
  | succ n ih =>
      simp only [orderedCount, pathCount]
      apply Finset.sum_le_sum
      intro d _
      by_cases hv : direction d ∈ V
      · rw [if_pos hv]
        cases hs : step i (choose i) d with
        | none =>
            have hm := (hblocked i (choose i) d).mp hs
            exact False.elim ((Finset.disjoint_left.mp hdis) hv hm)
        | some j =>
            have hj : Disjoint (advance V (choose i) d) (mask j) := by
              rw [hnext i (choose i) d j hs]
              exact advance_disjoint_memoryStep radius V (mask i) (choose i) d hdis
            simpa using ih (advance V (choose i) d) j (d :: history) hj
      · simp [hv]

#print axioms recenter_injective
#print axioms advance_disjoint_memoryStep
#print axioms orderedCount_le_pathCount

end D5.S3.StatisticalMechanics.HardCore.OrderedGridMemory
