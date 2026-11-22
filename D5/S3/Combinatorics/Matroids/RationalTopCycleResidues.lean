/- GID: D5/S3/Combinatorics/Matroids/RationalTopCycleResidues
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/RationalTopCycleResidues
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Rational top cycles lift all coefficient residue cycles of an ordered matroid. -/

module

public import D5.S3.Combinatorics.Matroids.RationalJointCircuitImage
import Mathlib.Combinatorics.Colex

/-! Lift rational coefficient residues using normalized integral top cycles. -/

@[expose] public section

namespace D5.S3.Combinatorics.Matroids.RationalTopCycleResidues

open Finset
open scoped Matroid
open D5.S3.Combinatorics.Matroids.OrderedCycleFactorization
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)
set_option autoImplicit false

variable {V A : Type*} [Fintype V] [LinearOrder V] [AddCommGroup A]

private theorem residues_ext {M : Matroid V} {z : Finset V → A}
    (support : ∀ F : Finset V, ¬ M.IsBase (F : Set V) → z F = 0)
    (cycle : ∀ R : Finset V, ∑ x ∈ univ \ R, insertionSign R x • z (insert x R) = 0)
    (passive : ∀ F, PassiveBase M F → z F = 0) :
    z = 0 := by
  classical
  by_contra hne
  let bad := univ.filter fun F : Finset V => z F ≠ 0
  have hb : bad.Nonempty := by
    obtain ⟨F, hF⟩ : ∃ F, z F ≠ 0 := not_forall.mp (fun h => hne (funext h))
    exact ⟨F, mem_filter.mpr ⟨mem_univ _, hF⟩⟩
  obtain ⟨F, hF, hmax⟩ := exists_max_image bad toColex hb
  have hFne := (mem_filter.mp hF).2
  have hbase : M.IsBase (F : Set V) := by
    by_contra h
    exact hFne (support F h)
  have hp : ¬ ∀ a ∈ F, ∃ x ∉ F, x < a ∧
      M.IsBase (↑(insert x (F.erase a)) : Set V) :=
    fun h => hFne (passive F ⟨hbase, h⟩)
  push Not at hp
  obtain ⟨a, ha, hactive⟩ := hp
  let R := F.erase a
  have haR : a ∉ R := notMem_erase _ _
  have heq : insert a R = F := insert_erase ha
  have hsingle := cycle R
  rw [sum_eq_single a] at hsingle
  · rw [heq] at hsingle
    have hsign : insertionSign R a * insertionSign R a = 1 := sign_sq _
    have hzero := congrArg (fun v : A => insertionSign R a • v) hsingle
    simp only [← mul_smul, hsign, one_smul, smul_zero] at hzero
    exact hFne hzero
  · intro x hx hxa
    have hterm : z (insert x R) = 0 := by
      by_cases hxB : M.IsBase (↑(insert x R) : Set V)
      · have hxR := (mem_sdiff.mp hx).2
        have hxF : x ∉ F := fun h => hxR (mem_erase.mpr ⟨hxa, h⟩)
        have hax : a < x := lt_of_le_of_ne
          (le_of_not_gt fun h => hactive x hxF h hxB) hxa.symm
        have hlt : toColex F < toColex (insert x R) := by
          rw [← heq]
          exact (Colex.insert_lt_insert haR hxR).2 hax
        by_contra hxne
        exact (not_le_of_gt hlt) (hmax _ (mem_filter.mpr ⟨mem_univ _, hxne⟩))
      · exact support _ hxB
    rw [hterm, smul_zero]
  · exact fun h => (h (mem_sdiff.mpr ⟨mem_univ _, haR⟩)).elim

open D5.S3.Combinatorics.Matroids.RationalJointCircuitImage
open D5.S3.Combinatorics.Matroids.JointCircuitGramCertificate
open D5.S3.Combinatorics.Matroids.CircuitPairInnerProduct
  (rationalTopCycles castChain mem_rationalTopCycles_iff)

/-- Every residue cycle supported on bases lifts to a rational top cycle. -/
theorem rational_cycle_residues_lift (M : Matroid V) (r : Finset V → RationalResidue)
    (hbase : ∀ F : Finset V, ¬ M.IsBase (F : Set V) → r F = 0)
    (hcycle : ∀ R : Finset V, ∑ x ∈ univ \ R, insertionSign R x • r (insert x R) = 0) :
    ∃ q : rationalTopCycles M, ∀ F, rationalResidue (q.val F) = r F := by
  classical
  have hs : Function.Surjective rationalResidue := QuotientAddGroup.mk'_surjective _
  choose lift hlift using fun B : Passive M => hs (r B.val)
  let q : rationalTopCycles M := ∑ B : Passive M, lift B •
    (⟨castChain (normalizedCycle B).val, mem_rationalTopCycles_iff.mpr
      (normalizedCycle B).prop⟩ : rationalTopCycles M)
  have hq (D : Passive M) : q.val D.val = lift D := by
    simp [q, Finset.sum_apply, castChain, normalizedCycle_coord]
  let z : Finset V → RationalResidue := fun F => rationalResidue (q.val F) - r F
  have hz : z = 0 := residues_ext (M := M)
    (fun F hF => by simp only [z, q.prop.1 _ hF, hbase _ hF, map_zero, sub_zero])
    (fun R => by
      simp only [z, smul_sub, sum_sub_distrib, hcycle, sub_zero, ← map_zsmul, ← map_sum]
      rw [show (∑ x ∈ univ \ R, insertionSign R x • q.val (insert x R)) = 0 by
        simpa only [zsmul_eq_mul] using q.prop.2 R, map_zero])
    (fun F hF => by
      let D : Passive M := ⟨F, hF⟩
      change rationalResidue (q.val D.val) - r D.val = 0
      rw [hq, hlift, sub_self])
  refine ⟨q, fun F => sub_eq_zero.mp ?_⟩
  exact congrFun hz F

end D5.S3.Combinatorics.Matroids.RationalTopCycleResidues
