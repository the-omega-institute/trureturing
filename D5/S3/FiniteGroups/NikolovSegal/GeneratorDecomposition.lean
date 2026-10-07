/- GID: D5/S3/FiniteGroups/NikolovSegal/GeneratorDecomposition
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/GeneratorDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-group generator decomposition follows from explicit minimal-normal absorption. -/

import D5.S3.FiniteGroups.NikolovSegal.OrderedPowerProducts
import D5.S3.FiniteGroups.NikolovSegal.BoundedTupleLift
import D5.S3.FiniteGroups.NikolovSegal.FiniteNormalInduction

set_option autoImplicit false

/-!
The finite-group induction in Nikolov--Segal (2011), p. 504, Proposition 3,
conditional only on the explicitly named large-minimal-normal absorption input.
The input is not proved here. In the paper it comes from Proposition 2 and the
classification of minimal normal subgroups. None of Propositions 1, 2 or 4, or
the restricted Burnside theorem, is asserted as an available theorem.
-/

namespace NikolovSegal

universe u

/-- The precise remaining input for Case 1: a minimal nontrivial normal subgroup
outside the bounded-section class absorbs on the LEFT into the SAME exact `m`
ordered qth-power factors. `m` is fixed before quantifying over all finite groups;
it does not depend on order, rank, or the individual group. This is an explicit
proposition parameter, not an asserted axiom or a generator-split assumption. -/
def LargeMinimalNormalAbsorption (q m k : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (N : Subgroup G),
    Minimal (fun M : Subgroup G => M.Normal ∧ M ≠ ⊥) N →
    ¬alpha N ≤ k →
    ∀ (a : N) (x : G), x ∈ orderedPowerProducts G q m →
      (a : G) * x ∈ orderedPowerProducts G q m

/-- Complete order induction for the paper's generator decomposition, under
the remaining explicit absorption premise. Repeats and identity padding are
allowed. Both tuples have length `d`, including the empty tuple when `d = 0`. -/
theorem generator_decomposition_of_absorption
    (q m k : ℕ) (hk : 4 ≤ k) (hAbs : LargeMinimalNormalAbsorption.{u} q m k)
    (G : Type u) [Group G] [Finite G] (d : ℕ) (hd : Group.rank G ≤ d) :
    ∃ x y : Fin d → G,
      Subgroup.closure (Set.range x ∪ Set.range y) = ⊤ ∧
      (∀ i, x i ∈ orderedPowerProducts G q m) ∧
      alpha (Subgroup.closure (Set.range y)) ≤ k := by
  classical
  suffices h : ∀ n : ℕ, ∀ (H : Type u) [Group H] [Finite H],
      Nat.card H = n → Group.rank H ≤ d →
      ∃ x y : Fin d → H,
        Subgroup.closure (Set.range x ∪ Set.range y) = ⊤ ∧
        (∀ i, x i ∈ orderedPowerProducts H q m) ∧
        alpha (Subgroup.closure (Set.range y)) ≤ k by
    exact h (Nat.card G) G rfl hd
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H _ _ hcard hrank
    by_cases htriv : Subsingleton H
    · let := htriv
      refine ⟨fun _ => 1, fun _ => 1, Subsingleton.elim _ _, ?_, ?_⟩
      · intro i
        exact one_mem_orderedPowerProducts q m
      · exact alpha_le_four_of_subsingleton.trans hk
    · let : Nontrivial H := not_subsingleton_iff_nontrivial.mp htriv
      obtain ⟨N, hmin⟩ := exists_minimal_normal (G := H)
      let : N.Normal := hmin.prop.1
      let p := QuotientGroup.mk' N
      have hp : Function.Surjective p := QuotientGroup.mk'_surjective N
      have hsmall : Nat.card (H ⧸ N) < n :=
        (card_quotient_lt N hmin.prop.2).trans_eq hcard
      have hqrank : Group.rank (H ⧸ N) ≤ d :=
        (Group.rank_le_of_surjective p hp).trans hrank
      obtain ⟨xq, yq, hgenq, hxq, hyq⟩ :=
        ih (Nat.card (H ⧸ N)) hsmall (H ⧸ N) rfl hqrank
      choose x hx hpx using fun i => lift_orderedPowerProducts p hp (hxq i)
      obtain ⟨y, hpy, hy⟩ := exists_bounded_tuple_lift p hp hk yq hyq
      have hquot := lift_tuple_generation N x y xq yq hpx hpy hgenq
      by_cases hN : alpha N ≤ k
      · obtain ⟨a, ha⟩ := D5.S3.FiniteGroups.GaschutzFixed.gaschutz_fixed N (Set.range x) y
          (D5.S3.FiniteGroups.GaschutzFixed.tuple_generation_iff_rank_le.mpr hrank) hquot
        refine ⟨x, fun i => (a i : H) * y i, ha, hx, ?_⟩
        let Y := Subgroup.closure (Set.range yq)
        have hker : alpha p.ker ≤ k := by
          apply (alpha_le_of_subgroup_le ?_).trans hN
          intro g hg
          exact (QuotientGroup.eq_one_iff g).mp (MonoidHom.mem_ker.mp hg)
        have hT : alpha (Y.comap p) ≤ k := alpha_preimage_le p Y hk hker hyq
        apply (alpha_le_of_subgroup_le ?_).trans hT
        apply (Subgroup.closure_le (Y.comap p)).2
        rintro _ ⟨i, rfl⟩
        change p ((a i : H) * y i) ∈ Y
        have hpa : p (a i : H) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (a i).property
        rw [map_mul, hpa, one_mul, hpy i]
        exact Subgroup.subset_closure ⟨i, rfl⟩
      · have hquot' : N ⊔ Subgroup.closure (Set.range y ∪ Set.range x) = ⊤ := by
          simpa only [Set.union_comm] using hquot
        obtain ⟨a, ha⟩ := D5.S3.FiniteGroups.GaschutzFixed.gaschutz_fixed N (Set.range y) x
          (D5.S3.FiniteGroups.GaschutzFixed.tuple_generation_iff_rank_le.mpr hrank) hquot'
        refine ⟨fun i => (a i : H) * x i, y, ?_, ?_, hy⟩
        · simpa only [Set.union_comm] using ha
        · intro i
          exact hAbs H N hmin hN (a i) (x i) (hx i)

end NikolovSegal
