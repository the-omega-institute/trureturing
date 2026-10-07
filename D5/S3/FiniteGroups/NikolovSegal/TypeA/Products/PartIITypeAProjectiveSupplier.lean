/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeAProjectiveSupplier
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIITypeAProjectiveSupplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Products.PartIITypeAUniformProduct
import D5.S3.FiniteGroups.NikolovSegal.PartIIA1ScalarSupply
import D5.S3.FiniteGroups.NikolovSegal.PartIIPSL3ScalarSupply

/-! Genuine complete untwisted type-A FAMILY scalar supply. All finite
fields, all matrix ranks, arbitrary bare quotient automorphisms and the
original positive e|q are included above ONE uniform group-card cutoff.
A1/A2 and the new all-rank A>=3 proof are actually consumed. No exhaustion
of arbitrary finite simple groups is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
namespace NikolovSegal.PartIITypeAProjectiveSupplier
open Matrix PartIITypeAUniformProduct
universe u

/-- ONE M(q),C(q) BEFORE every field/rank/bare beta/divisor tuple, with
ONE global correction BEFORE all targets in the actual PSLn. No family
classification, class width, scalar or twisted PRODUCT premise remains. -/
theorem actual_uniform_PSLn_scalar_product (q : ℕ) (hq : 0<q) :
    ∃ M C : ℕ, 0<M ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F], ∀ n : ℕ,
      C<Nat.card (ProjectiveSpecialLinearGroup (Fin n) F) →
      ∀ beta : Fin M → MulAut (ProjectiveSpecialLinearGroup (Fin n) F),
      ∀ e : Fin M → ℕ, PartIIScalarProductInput q M beta e := by
  obtain ⟨P,CP,hP,hhigh⟩ := actual_uniform_bare_PSLn_scalar_product_by_group_card q hq
  obtain ⟨A,CA,hA,hA1⟩ := PartIIA1RootSupply.uniform_PSL2_scalar_products q hq
  obtain ⟨B,CB,hB,hA2⟩ := PartIIPSL3ScalarSupply.actual_PSL3_uniform_scalar_product q hq
  let cutoff := max 1 (max CP (max CA (CB^9)))
  refine ⟨P+(A+B),cutoff,by omega,?_⟩
  intro F _ _ _ n hcard beta e
  have hCP : CP<Nat.card (ProjectiveSpecialLinearGroup (Fin n) F) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hcard
  have hCA : CA<Nat.card (ProjectiveSpecialLinearGroup (Fin n) F) :=
    lt_of_le_of_lt ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hcard
  have hCB : CB^9<Nat.card (ProjectiveSpecialLinearGroup (Fin n) F) :=
    lt_of_le_of_lt ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) hcard
  by_cases hn : 4≤n
  · obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
    exact scalar_product_append beta e (hhigh F k hCP
      (fun i => beta (i.castAdd (A+B))) (fun i => e (i.castAdd (A+B))))
  · have hcases : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · have hc : Nat.card (ProjectiveSpecialLinearGroup (Fin 0) F)≤1 := by
        have hs : Nat.card (SpecialLinearGroup (Fin 0) F)=1 := Nat.card_unique
        exact (Nat.card_le_card_of_surjective
          (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 0) F)))
          (QuotientGroup.mk'_surjective _)).trans_eq hs
      have hone : 1<Nat.card (ProjectiveSpecialLinearGroup (Fin 0) F) :=
        lt_of_le_of_lt (le_max_left _ _) hcard
      omega
    · have hc : Nat.card (ProjectiveSpecialLinearGroup (Fin 1) F)≤1 := by
        have hs : Nat.card (SpecialLinearGroup (Fin 1) F)=1 := Nat.card_unique
        exact (Nat.card_le_card_of_surjective
          (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 1) F)))
          (QuotientGroup.mk'_surjective _)).trans_eq hs
      have hone : 1<Nat.card (ProjectiveSpecialLinearGroup (Fin 1) F) :=
        lt_of_le_of_lt (le_max_left _ _) hcard
      omega
    · revert beta e
      rw [show P+(A+B)=A+(P+B) by omega]
      intro e beta
      exact scalar_product_append beta e (hA1 F hCA
        (fun i => beta (i.castAdd (P+B))) (fun i => e (i.castAdd (P+B))))
    · have hfield : CB<Fintype.card F := by
        by_contra hh
        have hc := (actual_PSLn_card_upper_bound F 3).trans
          (Nat.pow_le_pow_left (by omega : Fintype.card F≤CB) 9)
        exact (not_lt_of_ge hc) hCB
      revert beta e
      rw [show P+(A+B)=B+(P+A) by omega]
      intro e beta
      exact scalar_product_append beta e (hA2 F hfield
        (fun i => beta (i.castAdd (P+A))) (fun i => e (i.castAdd (P+A))))
end NikolovSegal.PartIITypeAProjectiveSupplier
