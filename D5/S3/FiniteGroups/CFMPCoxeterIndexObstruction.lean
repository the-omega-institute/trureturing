/- GID: D5/S3/FiniteGroups/CFMPCoxeterIndexObstruction
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/CFMPCoxeterIndexObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/FiniteGroups/CFMPCoxeterIndexObstruction.claim; result=D5/S3/FiniteGroups/CFMPCoxeterIndexObstruction.result; claim=D5/S3/FiniteGroups/CFMPCoxeterIndexObstruction.claim
   digest: Native torsionfree orientation quotients of the Coxeter group [4,9,3] cannot have index seventy-two. -/

import D5.S3.FiniteGroups.CycleNineThreeObstruction
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace D5.S3.FiniteGroups.CFMPCoxeterIndexObstruction

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- The Coxeter matrix with string labels four, nine and three. -/
def diagram : CoxeterMatrix (Fin 4) where
  M := !![1, 4, 2, 2; 4, 1, 9, 2; 2, 9, 1, 3; 2, 2, 3, 1]
  isSymm := by decide
  diagonal := by decide
  off_diagonal := by decide

abbrev W := diagram.Group
abbrev canonical := diagram.toCoxeterSystem

/-- The even subgroup, the kernel of the homomorphism sending every reflection to minus one. -/
def orientation : Subgroup W := canonical.lengthParity.ker

/-- Existence of a torsionfree normal subgroup of orientation index seventy-two. -/
def claim : Prop := ∃ Γ : Subgroup orientation,
  Γ.Normal ∧ IsMulTorsionFree Γ ∧ Γ.index = 72

private def reflection (i : Fin 4) : Matrix (Fin 3) (Fin 3) (ZMod 19) :=
  if i = 0 then 1 else if i = 1 then !![-1,12,0;0,1,0;0,0,1]
  else if i = 2 then !![1,0,0;12,-1,1;0,0,1]
  else !![1,0,0;0,1,0;0,1,-1]

private theorem reflection_relations : diagram.IsLiftable reflection := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

private def representation : W →* Matrix (Fin 3) (Fin 3) (ZMod 19) :=
  canonical.lift ⟨reflection, reflection_relations⟩

private theorem pair_order (i j : Fin 4) (n : ℕ)
    (hn : diagram i j = n)
    (hsep : orderOf (reflection i * reflection j) = n) :
    orderOf (canonical.simple i * canonical.simple j) = n := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    simpa only [← hn] using canonical.simple_mul_simple_pow i j
  · have h := orderOf_map_dvd representation (canonical.simple i * canonical.simple j)
    simpa only [map_mul, representation, CoxeterSystem.lift_apply_simple, hsep] using h

private theorem native_orders :
    orderOf (canonical.simple 1 * canonical.simple 2) = 9 ∧
    orderOf (canonical.simple 2 * canonical.simple 3) = 3 ∧
    orderOf (canonical.simple 1 * canonical.simple 3) = 2 := by
  refine ⟨pair_order 1 2 9 rfl ?_, pair_order 2 3 3 rfl ?_, pair_order 1 3 2 rfl ?_⟩
  all_goals
    apply orderOf_eq_of_pow_and_pow_div_prime
    · decide
    · intro p hp hd
      interval_cases p <;> norm_num at hp hd ⊢ <;> decide

end D5.S3.FiniteGroups.CFMPCoxeterIndexObstruction
