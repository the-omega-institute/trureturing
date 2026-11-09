/- GID: D5/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples
   generality: S
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/QuaternionDihedralCounterexamples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual Q8, D8 and proper Q8-times-C3 missing-case counterexamples. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Prod

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.QuaternionDihedralCounterexamples

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

abbrev Q8 := QuaternionGroup 2
abbrev D8 := DihedralGroup 4

/-- The central involution -1 in the actual quaternion group. -/
def q8Central : Q8 := QuaternionGroup.a 2

/-- The half-turn a squared in the actual dihedral group of order eight. -/
def d8Central : D8 := DihedralGroup.r 2

def q8Connection : Set Q8 := {1, q8Central}
def d8Connection : Set D8 := {1, d8Central}

private theorem q8_normal : NormalSubset q8Connection := by decide
private theorem d8_normal : NormalSubset d8Connection := by decide

/-- Q8 has square set and center exactly {1,-1}, and its graph with this
connection set is a perfect matching on all eight group vertices. -/
theorem quaternion_result :
    squares (⊤ : Subgroup Q8) = q8Connection ∧
    (Subgroup.center Q8 : Set Q8) = q8Connection ∧
    IsTotalPerfectCode (sumGraph q8Connection q8_normal) (⊤ : Subgroup Q8) := by
  refine ⟨Set.ext (by decide), Set.ext (by decide), ?_⟩
  decide

/-- The same missing-case phenomenon in D8, with center and square set
{1,a squared} and the actual sum graph a perfect matching. -/
theorem dihedral_result :
    squares (⊤ : Subgroup D8) = d8Connection ∧
    (Subgroup.center D8 : Set D8) = d8Connection ∧
    IsTotalPerfectCode (sumGraph d8Connection d8_normal) (⊤ : Subgroup D8) := by
  refine ⟨Set.ext (by decide), Set.ext (by decide), ?_⟩
  decide

private theorem whole_transversal_squares {G : Type*} [Group G]
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

/-- Every normal transversal of Q8 in itself consists of squares. Thus the
old singleton-nonsquare necessity fails for this actual matching graph. -/
theorem quaternion_old_necessity_fails (T : Set Q8) (hn : NormalSubset T)
    (hc : Subgroup.IsComplement T (⊤ : Set Q8)) :
    T ⊆ squares (⊤ : Subgroup Q8) := by
  apply whole_transversal_squares ?_ T hn hc
  rw [quaternion_result.1, quaternion_result.2.1]

/-- D8 also has no normal-transversal nonsquare witness in itself. -/
theorem dihedral_old_necessity_fails (T : Set D8) (hn : NormalSubset T)
    (hc : Subgroup.IsComplement T (⊤ : Set D8)) :
    T ⊆ squares (⊤ : Subgroup D8) := by
  apply whole_transversal_squares ?_ T hn hc
  rw [dihedral_result.1, dihedral_result.2.1]

abbrev C3 := Multiplicative (ZMod 3)
abbrev ProductGroup := Q8 × C3

/-- The genuine proper normal subgroup Q8 times the identity in C3. -/
def productSubgroup : Subgroup ProductGroup := (⊤ : Subgroup Q8).prod (⊥ : Subgroup C3)

def productConnection : Set ProductGroup :=
  {(1, 1), (q8Central, 1), (1, Multiplicative.ofAdd 1), (1, Multiplicative.ofAdd 2)}

private theorem product_normal : NormalSubset productConnection := by decide

/-- The third source counterexample is a proper normal subgroup, not only
the degenerate H=G case: it has the required total perfect-code graph. -/
theorem product_result : productSubgroup.Normal ∧ productSubgroup ≠ ⊤ ∧
    IsTotalPerfectCode (sumGraph productConnection product_normal) productSubgroup := by
  refine ⟨by infer_instance, ?_, ?_⟩
  · intro he
    have hn : ((1, Multiplicative.ofAdd 1) : ProductGroup) ∉ productSubgroup := by decide
    apply hn
    rw [he]
    trivial
  · decide

#print axioms quaternion_result
#print axioms dihedral_result
#print axioms quaternion_old_necessity_fails
#print axioms dihedral_old_necessity_fails
#print axioms product_result

end D5.S3.Combinatorics.CayleySumCodes.QuaternionDihedralCounterexamples
