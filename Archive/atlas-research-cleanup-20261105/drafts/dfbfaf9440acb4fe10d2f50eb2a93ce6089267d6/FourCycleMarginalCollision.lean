/- GID: D5/S3/Combinatorics/CircularWords/FourCycleMarginalCollision
   generality: S
   mirror-B: D5/B/S3/Combinatorics/CircularWords/FourCycleMarginalCollision
   mirror-E: none(waiver:research-draft)
   anchors: [mathlib/module/Mathlib.Data.Finsupp.Basic]
   utility: none
   digest: All four one-deletion marginals agree for two disjoint finite cycle laws. -/
import D5.S3.Combinatorics.CircularWords.CircularDeletionTransport
import Mathlib.Data.Finsupp.Basic

/-! An actual four-cycle collision for all individual deletion marginals. -/

set_option autoImplicit false
namespace D5.S3.Combinatorics.CircularWords.FourCycleMarginalCollision
open CircularDeletionTransport

/-- These are actual rotation classes of words on the four natural labels. -/
def X1 : Cycle ℕ := ([0,1,2,3] : List ℕ)
def X2 : Cycle ℕ := ([0,3,2,1] : List ℕ)
def Y1 : Cycle ℕ := ([0,1,3,2] : List ℕ)
def Y2 : Cycle ℕ := ([0,2,3,1] : List ℕ)

noncomputable def mu : Cycle ℕ →₀ ℚ := Finsupp.single X1 (1/2) + Finsupp.single X2 (1/2)
noncomputable def nu : Cycle ℕ →₀ ℚ := Finsupp.single Y1 (1/2) + Finsupp.single Y2 (1/2)

/-- Paired readout from the same cycle, never a product of marginal laws. -/
def J02 (C : Cycle ℕ) : Cycle ℕ × Cycle ℕ := (delete 0 C, delete 2 C)

/-- Event containing precisely the two paired readings of mu's support. -/
def pairedEvent (p : Cycle ℕ × Cycle ℕ) : Bool :=
  decide (p = J02 X1 ∨ p = J02 X2)

/-- Both laws are supported on the stipulated nodup states on {0,1,2,3}.
Their masses are nonnegative and normalized; the supports are disjoint.
All individual deletion pushforwards agree. The paired event has mass 1 versus 0. -/
theorem actual_marginal_collision :
    (∀ C ∈ mu.support ∪ nu.support, C.Nodup ∧ C.toFinset = {0,1,2,3}) ∧
    (∀ C, 0 ≤ mu C ∧ 0 ≤ nu C) ∧
    (Finsupp.mapDomain (fun _ : Cycle ℕ => ()) mu) () = 1 ∧
    (Finsupp.mapDomain (fun _ : Cycle ℕ => ()) nu) () = 1 ∧
    Disjoint mu.support nu.support ∧
    (∀ i ∈ ({0,1,2,3} : Finset ℕ),
      Finsupp.mapDomain (delete i) mu = Finsupp.mapDomain (delete i) nu) ∧
    (Finsupp.mapDomain (pairedEvent ∘ J02) mu) true = 1 ∧
    (Finsupp.mapDomain (pairedEvent ∘ J02) nu) true = 0 := by
  have h12 : X1 ≠ X2 := by decide
  have h13 : X1 ≠ Y1 := by decide
  have h14 : X1 ≠ Y2 := by decide
  have h23 : X2 ≠ Y1 := by decide
  have h24 : X2 ≠ Y2 := by decide
  have h34 : Y1 ≠ Y2 := by decide
  have sm : mu.support = {X1,X2} := by
    ext C
    by_cases h1 : C = X1 <;> by_cases h2 : C = X2 <;>
      simp [Finsupp.mem_support_iff, mu, h1, h2, eq_comm, h12, h34,
        Finsupp.single_apply]
  have sn : nu.support = {Y1,Y2} := by
    ext C
    by_cases h1 : C = Y1 <;> by_cases h2 : C = Y2 <;>
      simp [Finsupp.mem_support_iff, nu, h1, h2, eq_comm, h12, h34,
        Finsupp.single_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C h
    rw [sm, sn] at h
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with (rfl | rfl) | (rfl | rfl) <;> decide
  · intro C
    constructor <;> apply add_nonneg <;> simp only [Finsupp.single_apply] <;>
      split_ifs <;> norm_num
  · norm_num [mu, Finsupp.mapDomain_add]
  · norm_num [nu, Finsupp.mapDomain_add]
  · rw [sm, sn]
    simp [Finset.disjoint_left, h13, h14, h23, h24]
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · have a : delete 0 X1 = delete 0 Y2 := by decide
      have b : delete 0 X2 = delete 0 Y1 := by decide
      simp only [mu, nu, Finsupp.mapDomain_add, Finsupp.mapDomain_single, a, b]
      exact add_comm _ _
    · have a : delete 1 X1 = delete 1 Y2 := by decide
      have b : delete 1 X2 = delete 1 Y1 := by decide
      simp only [mu, nu, Finsupp.mapDomain_add, Finsupp.mapDomain_single, a, b]
      exact add_comm _ _
    · have a : delete 2 X1 = delete 2 Y1 := by decide
      have b : delete 2 X2 = delete 2 Y2 := by decide
      simp only [mu, nu, Finsupp.mapDomain_add, Finsupp.mapDomain_single, a, b]
    · have a : delete 3 X1 = delete 3 Y1 := by decide
      have b : delete 3 X2 = delete 3 Y2 := by decide
      simp only [mu, nu, Finsupp.mapDomain_add, Finsupp.mapDomain_single, a, b]
  · have a : pairedEvent (J02 X1) = true := by decide
    have b : pairedEvent (J02 X2) = true := by decide
    norm_num [mu, Finsupp.mapDomain_add, Function.comp_apply, a, b]
  · have a : pairedEvent (J02 Y1) = false := by decide
    have b : pairedEvent (J02 Y2) = false := by decide
    norm_num [nu, Finsupp.mapDomain_add, Function.comp_apply, a, b]

#check actual_marginal_collision
#print axioms actual_marginal_collision
end D5.S3.Combinatorics.CircularWords.FourCycleMarginalCollision
