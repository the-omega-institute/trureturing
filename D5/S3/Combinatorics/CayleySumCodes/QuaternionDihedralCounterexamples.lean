/- GID: D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples
   generality: I
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.claim; result=D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.result; claim=D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples.claim
   digest: The actual Q8 matching refutes singleton-nonsquare total-code necessity. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Basic

set_option autoImplicit false


namespace D5.S3.Combinatorics.CayleySumCodes.QuaternionDihedralCounterexamples

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

abbrev Q8 := QuaternionGroup 2
def q8Central : Q8 := QuaternionGroup.a 2
def q8Connection : Set Q8 := {1, q8Central}
private theorem q8_normal : NormalSubset q8Connection := by
  unfold NormalSubset q8Connection q8Central
  decide

private theorem quaternion_result :
    squares (⊤ : Subgroup Q8) = q8Connection ∧
    (Subgroup.center Q8 : Set Q8) = q8Connection ∧
    IsTotalPerfectCode (sumGraph q8Connection q8_normal) (⊤ : Subgroup Q8) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [squares, Set.mem_setOf_eq, SetLike.mem_coe, Subgroup.mem_top, true_and]
    revert x
    unfold q8Connection q8Central
    decide +kernel
  · ext x
    change x ∈ Subgroup.center Q8 ↔ x ∈ q8Connection
    rw [Subgroup.mem_center_iff]
    revert x
    unfold q8Connection q8Central
    decide +kernel
  · change ∀ g : Q8, ∃! h : Q8, h ∈ (⊤ : Subgroup Q8) ∧
      g ≠ h ∧ g * h ∈ q8Connection
    simp only [Subgroup.mem_top, true_and, q8Connection, q8Central,
      Set.mem_insert_iff, Set.mem_singleton_iff, ExistsUnique]
    decide +kernel

theorem whole_transversal_squares {G : Type*} [Group G]
    (hz : (Subgroup.center G : Set G) ⊆ squares (⊤ : Subgroup G))
    (T : Set G) (hn : NormalSubset T)
    (hc : Subgroup.IsComplement T (⊤ : Set G)) :
    T ⊆ squares (⊤ : Subgroup G) := by
  obtain ⟨z, he⟩ := Subgroup.isComplement_univ_right.mp hc
  have hzC : z ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro a
    have hzT : z ∈ T := he.symm ▸ Set.mem_singleton z
    have hh := hn a z hzT
    rw [he] at hh
    have hh' := congrArg (fun x : G => x * a) (Set.mem_singleton_iff.mp hh)
    simpa [mul_assoc] using hh'
  intro y hy
  rw [he] at hy
  exact (Set.mem_singleton_iff.mp hy).symm ▸ hz hzC

private theorem quaternion_old_necessity_fails (T : Set Q8) (hn : NormalSubset T)
    (hc : Subgroup.IsComplement T (⊤ : Set Q8)) :
    T ⊆ squares (⊤ : Subgroup Q8) := by
  apply whole_transversal_squares ?_ T hn hc
  rw [quaternion_result.1, quaternion_result.2.1]

/-- The singleton-nonsquare necessity of Z Lemma4.1/A Lemma2.3,
restricted to the complete actual Q8 group. -/
def claim : Prop :=
  ∀ (K : Subgroup Q8) (Y : Set Q8) (hn : NormalSubset Y),
    IsTotalPerfectCode (sumGraph Y hn) K →
      ∃ T : Set Q8, NormalSubset T ∧ Subgroup.IsComplement T (K : Set Q8) ∧
        ∃ z ∈ T, z ∈ K ∧ z ∉ squares K

/-- The source's actual matching refutes the old necessary condition. -/
theorem result : Not claim := by
  intro hc
  obtain ⟨T, hn, ht, z, hzT, _, hzs⟩ :=
    hc ⊤ q8Connection q8_normal quaternion_result.2.2
  exact hzs (quaternion_old_necessity_fails T hn ht hzT)

#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.QuaternionDihedralCounterexamples
