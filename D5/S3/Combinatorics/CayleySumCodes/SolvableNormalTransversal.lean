/- GID: D5/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleySumCodes/SolvableNormalTransversal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite solvable groups whose every subgroup has a normal transversal are abelian. -/

import D5.S3.Combinatorics.CayleySumCodes.NormalTransversal
import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Group.Subgroup.Finite

set_option autoImplicit false

namespace D5.S3.Combinatorics.CayleySumCodes.SolvableNormalTransversal

open D5.S3.Combinatorics.CayleySumCodes.TotalPerfectCriterion
open D5.S3.Combinatorics.CayleySumCodes.NormalTransversal

universe u

variable {G : Type u} [Group G]

/-- Every subgroup of an intermediate subgroup inherits the actual normal
transversal property. No normality or subnormality is imposed on M. -/
theorem all_restrict (h : ∀ H : Subgroup G, NLT H) (M : Subgroup G) :
    ∀ L : Subgroup M, NLT L := by
  intro L
  have hm : L.map M.subtype ≤ M := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hr := NormalTransversal.restrict (L.map M.subtype) M hm (h _)
  have he : (L.map M.subtype).subgroupOf M = L :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective L
  exact he ▸ hr

/-- The all-NLT property descends through every actual surjective group
homomorphism. Applied to a normal-subgroup quotient, it gives all-NLT in
that quotient, without asserting inheritance of either kind of code. -/
theorem all_map {K : Type*} [Group K] (f : G →* K) (hf : Function.Surjective f)
    (h : ∀ H : Subgroup G, NLT H) : ∀ L : Subgroup K, NLT L := by
  intro L
  have hk : f.ker ≤ L.comap f := by
    intro x hx
    change f x ∈ L
    rw [show f x = 1 from hx]
    exact L.one_mem
  have hr := NormalTransversal.map f hf (L.comap f) hk (h _)
  have he : (L.comap f).map f = L := Subgroup.map_comap_eq_self_of_surjective hf L
  exact he ▸ hr

/-- Conjugation cannot move a normal-transversal representative when the
quotient is abelian: the two representatives remain in the same left coset.
Thus every member of that specified transversal is central in the full group. -/
theorem central_transversal (H : Subgroup G) [H.Normal]
    [IsMulCommutative (G ⧸ H)] (T : Set G)
    (hn : NormalSubset T) (hc : Subgroup.IsComplement T (H : Set G)) :
    ∀ t ∈ T, ∀ a : G, a * t = t * a := by
  intro t ht a
  obtain ⟨s, hs, hu⟩ :=
    Subgroup.isComplement_iff_existsUnique_inv_mul_mem.mp hc t
  have ht' : (⟨t, ht⟩ : T) = s := hu ⟨t, ht⟩ (by simp)
  have heq : (QuotientGroup.mk' H) (a * t * a⁻¹) = (QuotientGroup.mk' H) t := by
    simp only [map_mul, map_inv]
    rw [mul_comm' ((QuotientGroup.mk' H) a) ((QuotientGroup.mk' H) t)]
    simp [mul_assoc]
  have hm : (a * t * a⁻¹)⁻¹ * t ∈ H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' H) ((a * t * a⁻¹)⁻¹ * t) = 1
    rw [map_mul, map_inv, heq]
    simp
  have he : a * t * a⁻¹ = t :=
    congrArg Subtype.val ((hu ⟨a * t * a⁻¹, hn a t ht⟩ hm).trans ht'.symm)
  have he' := congrArg (fun x : G => x * a) he
  simpa [mul_assoc] using he'

private theorem commutative_of_central_transversal (H : Subgroup G)
    (hab : ∀ x y : H, x * y = y * x) (T : Set G)
    (hc : Subgroup.IsComplement T (H : Set G))
    (hz : ∀ t ∈ T, ∀ a : G, a * t = t * a) :
    ∀ x y : G, x * y = y * x := by
  intro x y
  obtain ⟨⟨t, h⟩, rfl⟩ := hc.2 x
  obtain ⟨⟨s, k⟩, rfl⟩ := hc.2 y
  have hh : h.1 * k.1 = k.1 * h.1 := congrArg Subtype.val (hab h k)
  calc
    (t.1 * h.1) * (s.1 * k.1) = (t.1 * s.1) * (h.1 * k.1) := by
      simp only [mul_assoc]
      rw [← mul_assoc h.1 s.1 k.1, hz s.1 s.2 h.1, mul_assoc]
    _ = (s.1 * t.1) * (k.1 * h.1) := by rw [hz s.1 s.2 t.1, hh]
    _ = (s.1 * k.1) * (t.1 * h.1) := by
      simp only [mul_assoc]
      rw [← mul_assoc t.1 k.1 h.1, ← hz t.1 t.2 k.1, mul_assoc]

private theorem finite_induction (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card G = n → (∀ H : Subgroup G, NLT H) →
      ∀ x y : G, x * y = y * x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ hcard hAll
    classical
    by_cases htriv : Subsingleton G
    · exact fun _ _ => htriv.elim _ _
    · letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp htriv
      let D := commutator G
      have hlt : Nat.card D < n := by
        rw [← hcard]
        simpa only [Subgroup.card_top] using
          Subgroup.card_lt_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial G)
      have hd : ∀ x y : D, x * y = y * x :=
        ih (Nat.card D) hlt D rfl (all_restrict hAll D)
      obtain ⟨T, hn, hc⟩ := hAll D
      exact commutative_of_central_transversal D hd T hc (central_transversal D T hn hc)

/-- The full finite solvable-group implication, including the trivial group.
All subgroup transversals are hypotheses; solvability and finite cardinality
are used in the strict derived-subgroup order induction, not encoded in a
target-bearing witness package. -/
theorem result [Finite G] [Group.IsSolvable G]
    (h : ∀ H : Subgroup G, NLT H) : ∀ x y : G, x * y = y * x :=
  finite_induction (Nat.card G) G rfl h

#print axioms all_restrict
#print axioms all_map
#print axioms central_transversal
#print axioms result

end D5.S3.Combinatorics.CayleySumCodes.SolvableNormalTransversal
