/- GID: D5/S3/Combinatorics/CayleySumCodes/ProperQuaternionOldNecessityCounterexample
   generality: I
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/ProperQuaternionOldNecessityCounterexample
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/CayleySumCodes/ProperQuaternionOldNecessityCounterexample.claim; result=D5/S3/Combinatorics/CayleySumCodes/ProperQuaternionOldNecessityCounterexample.result; claim=D5/S3/Combinatorics/CayleySumCodes/ProperQuaternionOldNecessityCounterexample.claim
   digest: The actual proper Q8-times-C3 example refutes the old normal-subgroup necessity. -/

import D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Subgroup.Basic

import D5.S3.Combinatorics.CayleySumCodes.QuaternionDihedralCounterexamples

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.ProperQuaternionOldNecessityCounterexample

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion

abbrev C3 := Multiplicative (ZMod 3)
open QuaternionDihedralCounterexamples
abbrev ProductGroup := Q8 × C3

/-- The genuine proper normal subgroup Q8 times the identity in C3. -/
def productSubgroup : Subgroup ProductGroup := (⊤ : Subgroup Q8).prod (⊥ : Subgroup C3)

def productConnection : Set ProductGroup :=
  {(1, 1), (QuaternionDihedralCounterexamples.q8Central, 1), (1, Multiplicative.ofAdd 1), (1, Multiplicative.ofAdd 2)}

private theorem product_normal : NormalSubset productConnection := by
  unfold NormalSubset productConnection
  decide

/-- The third source counterexample is a proper normal subgroup, not only
the degenerate H=G case: it has the required total perfect-code graph. -/
private theorem product_result : productSubgroup.Normal ∧ productSubgroup ≠ ⊤ ∧
    IsTotalPerfectCode (sumGraph productConnection product_normal) productSubgroup := by
  refine ⟨?_, ?_, ?_⟩
  · change ((⊤ : Subgroup Q8).prod (⊥ : Subgroup C3)).Normal
    infer_instance
  · intro he
    have hn : ((1, Multiplicative.ofAdd 1) : ProductGroup) ∉ productSubgroup := by
      simp only [productSubgroup, Subgroup.mem_prod, Subgroup.mem_top,
        Subgroup.mem_bot, true_and]
      decide
    apply hn
    rw [he]
    trivial
  · change ∀ g : ProductGroup, ∃! h : ProductGroup, h ∈ productSubgroup ∧
      g ≠ h ∧ g * h ∈ productConnection
    simp only [ExistsUnique, productSubgroup, Subgroup.mem_prod, Subgroup.mem_top,
      Subgroup.mem_bot, true_and, productConnection, Set.mem_insert_iff, Set.mem_singleton_iff]
    decide +kernel

/-- The old necessity, even when restricted to proper normal subgroups
of the complete actual product group. -/
def claim : Prop :=
  ∀ (K : Subgroup ProductGroup), K.Normal → K ≠ ⊤ →
    ∀ (Y : Set ProductGroup) (hn : NormalSubset Y),
      IsTotalPerfectCode (sumGraph Y hn) K →
        ∃ T : Set ProductGroup, NormalSubset T ∧ Subgroup.IsComplement T (K : Set ProductGroup) ∧
          ∃ z ∈ T, z ∈ K ∧ z ∉ squares K

private theorem central_internal_square : ∀ z : ProductGroup,
    z ∈ Subgroup.center ProductGroup → z ∈ productSubgroup →
      z ∈ squares productSubgroup := by
  simp only [Subgroup.mem_center_iff, squares, Set.mem_setOf_eq]
  simp only [productSubgroup, Subgroup.mem_prod, Subgroup.mem_top,
    Subgroup.mem_bot, true_and]
  decide +kernel

/-- The proper-normal source example refutes the old necessity as well. -/
theorem result : Not claim := by
  intro hc
  obtain ⟨T, hn, ht, z, hzT, hzH, hzs⟩ := hc productSubgroup
    product_result.1 product_result.2.1 productConnection product_normal product_result.2.2
  obtain ⟨t, ht1, hu⟩ := Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp ht 1
  have hcentral : z ∈ Subgroup.center ProductGroup := by
    apply Subgroup.mem_center_iff.mpr
    intro a
    have hm : a * z * a⁻¹ ∈ productSubgroup :=
      Subgroup.Normal.conj_mem product_result.1 z hzH a
    have he : a * z * a⁻¹ = z := congrArg Subtype.val
      ((hu ⟨a * z * a⁻¹, hn a z hzT⟩ (by simpa using productSubgroup.inv_mem hm)).trans
       (hu ⟨z, hzT⟩ (by simpa using productSubgroup.inv_mem hzH)).symm)
    have hh := congrArg (fun u : ProductGroup => u * a) he
    simpa [mul_assoc] using hh
  exact hzs (central_internal_square z hcentral hzH)

#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.ProperQuaternionOldNecessityCounterexample
