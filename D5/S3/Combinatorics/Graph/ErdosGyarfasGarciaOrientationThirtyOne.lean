/- GID: D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.claim; result=D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.result; claim=D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.claim
   digest: No orientation of the four Garcia affine bases avoids a length-64 replacement cycle. -/

import Mathlib.Tactic
import D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationBase

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationThirtyOne

open D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationBase

private instance : Fact (Nat.Prime 31) := ⟨by decide⟩

private def word4 (a : ℕ) : Fin 14 → Fin 3 :=
  if a = 11 then ![0,1,0,2,2,0,2,2,2,0,1,1,1,1]
  else if a = 17 then ![0,1,0,1,1,1,1,0,2,2,2,0,2,2]
  else if a = 22 then ![0,1,0,1,0,2,2,2,2,2,0,1,1,1]
  else ![0,1,0,1,0,1,1,1,0,2,2,2,2,2]

private def word6 (a : ℕ) : Fin 14 → Fin 3 :=
  if a = 11 then ![0,1,0,1,0,1,0,1,0,2,0,2,2,2]
  else if a = 17 then ![0,1,0,1,0,1,0,1,0,2,2,2,0,2]
  else if a = 22 then ![0,1,0,1,0,2,0,1,1,0,2,2,0,2]
  else ![0,1,0,1,0,2,0,2,2,0,1,1,0,2]

private theorem certificate (a : ℕ) (ha : a ∈ ({11,17,22,24} : Finset ℕ)) (six : Bool) :
    Function.Injective (cycleVertex (p := 31) a (if six then word6 a else word4 a)) ∧
    (∀ i, cycleVertex (p := 31) a (if six then word6 a else word4 a) (i + 1) =
      cycleVertex (p := 31) a (if six then word6 a else word4 a) i *
        generator a (outgoing (if six then word6 a else word4 a) i)) ∧
    (∀ i, outgoing (if six then word6 a else word4 a) i ≠ incoming (if six then word6 a else word4 a) i ∧
      ∀ j, j ≠ unused (if six then word6 a else word4 a) i ↔
        j = outgoing (if six then word6 a else word4 a) i ∨
        j = incoming (if six then word6 a else word4 a) i) ∧
    (∀ j : Fin 3, (∑ i : Fin 14,
      if unused (if six then word6 a else word4 a) i = j then 1 else 0 : ℕ) =
      if six then (if j = 0 then 2 else 6) else (if j = 0 then 6 else 4)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> cases six <;> decide +kernel

def claim : Prop :=
  ∃ a : ℕ, a ∈ ({11, 17, 22, 24} : Finset ℕ) ∧
  ∃ sigma : Affine 31 → Fin 3, ∃ tau : Affine 31 → (Fin 3 ≃ Fin 3),
    (∀ v, tau v (sigma v) = 0) ∧
    ∀ v : Affine 31 × Fin 15, ∀ p : (replacement a tau).Walk v v,
      p.IsCycle → p.length ≠ 64

theorem result : ¬ claim := by
  classical
  rintro ⟨a, ha, sigma, tau, htau, havoid⟩
  have h4 := certificate a ha false
  have h6 := certificate a ha true
  exact refutes_of_certificates a (word4 a) (word6 a)
    h4.1 h4.2.1 h4.2.2.1 h4.2.2.2
    h6.1 h6.2.1 h6.2.2.1 h6.2.2.2
    ⟨sigma, tau, htau, havoid⟩

end D5.S3.Combinatorics.Graph.ErdosGyarfasGarciaOrientationThirtyOne
