/- GID: D5/S3/Combinatorics/CayleySumCodes/DihedralOldNecessityCounterexample
   generality: I
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/DihedralOldNecessityCounterexample
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/CayleySumCodes/DihedralOldNecessityCounterexample.claim; result=D5/S3/Combinatorics/CayleySumCodes/DihedralOldNecessityCounterexample.result; claim=D5/S3/Combinatorics/CayleySumCodes/DihedralOldNecessityCounterexample.claim
   digest: The actual D8 matching refutes singleton-nonsquare total-code necessity. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Prod

set_option autoImplicit false

import D5.S3.Combinatorics.CayleySumCodes.QuaternionDihedralCounterexamples

namespace D5.S3.Combinatorics.CayleySumCodes.DihedralOldNecessityCounterexample

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

abbrev D8 := DihedralGroup 4
def d8Central : D8 := DihedralGroup.r 2
def d8Connection : Set D8 := {1, d8Central}
private theorem d8_normal : NormalSubset d8Connection := by decide

private theorem dihedral_result :
    squares (⊤ : Subgroup D8) = d8Connection ∧
    (Subgroup.center D8 : Set D8) = d8Connection ∧
    IsTotalPerfectCode (sumGraph d8Connection d8_normal) (⊤ : Subgroup D8) := by
  refine ⟨Set.ext (by decide), Set.ext (by decide), ?_⟩
  decide

open D5.S3.Combinatorics.CayleySumCodes.QuaternionDihedralCounterexamples

private theorem dihedral_old_necessity_fails (T : Set D8) (hn : NormalSubset T)
    (hc : Subgroup.IsComplement T (⊤ : Set D8)) :
    T ⊆ squares (⊤ : Subgroup D8) := by
  apply whole_transversal_squares ?_ T hn hc
  rw [dihedral_result.1, dihedral_result.2.1]

/-- The singleton-nonsquare necessity of Z Lemma4.1/A Lemma2.3,
restricted to the complete actual D8 group. -/
def claim : Prop :=
  ∀ (K : Subgroup D8) (Y : Set D8) (hn : NormalSubset Y),
    IsTotalPerfectCode (sumGraph Y hn) K →
      ∃ T : Set D8, NormalSubset T ∧ Subgroup.IsComplement T (K : Set D8) ∧
        ∃ z ∈ T, z ∈ K ∧ z ∉ squares K

/-- The source's actual matching refutes the old necessary condition. -/
theorem result : Not claim := by
  intro hc
  obtain ⟨T, hn, ht, z, hzT, _, hzs⟩ :=
    hc ⊤ d8Connection d8_normal dihedral_result.2.2
  exact hzs (dihedral_old_necessity_fails T hn ht hzT)

#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.DihedralOldNecessityCounterexample
