/- GID: D5/S3/Combinatorics/MinimalForts/RootedProduct
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MinimalForts/RootedProduct
   mirror-E: none(waiver:counting-bijection-proof)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Sum]
   utility: none
   digest: Root-containing minimal-fort choices multiply across disjoint base graphs. -/

import D5.S3.Combinatorics.MinimalForts.DisjointSum
import D5.S3.Combinatorics.MinimalForts.UniversalRoot
import Mathlib.Data.Finset.Prod

/-! Domination and exclusion of contained forts both factor over disjoint components. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MinimalForts.RootedProduct

open D5.S3.Combinatorics.GeneralizedPetersen.ZeroForcingThreeFinite
open D5.S3.Combinatorics.MinimalForts.UniversalRoot
open D5.S3.Combinatorics.MinimalForts.DisjointSum
open D5.S3.Combinatorics.Graph.Domination.TrapezohedralMinimalDomination

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]

private theorem minimalDominating_sum_iff (S : Finset V) (T : Finset W) :
    MinimalDominating (G ⊕g H) (S.disjSum T : Set (V ⊕ W)) ↔
      MinimalDominating G (S : Set V) ∧ MinimalDominating H (T : Set W) := by
  simp only [minimalDominating_iff_private, ClosedPrivate, SimpleGraph.IsDominating,
    Sum.forall, Sum.exists, Finset.mem_coe, Finset.inl_mem_disjSum,
    Finset.inr_mem_disjSum, SimpleGraph.sum_adj, Sum.inl.injEq, Sum.inr.injEq,
    reduceCtorEq, false_or, or_false, false_and, and_false, true_implies,
    not_false_eq_true, forall_true_left, and_true, true_and]
  aesop

private theorem fort_free_sum_iff (S : Finset V) (T : Finset W) :
    (∀ U ⊆ S.disjSum T, ¬ IsFort (G ⊕g H) U) ↔
      (∀ U ⊆ S, ¬ IsFort G U) ∧ (∀ U ⊆ T, ¬ IsFort H U) := by
  constructor
  · intro h
    constructor
    · intro U hU hf
      apply h (U.disjSum ∅) (Finset.disjSum_mono hU (Finset.empty_subset T))
      exact (fort_sum_iff G H _ _).mpr ⟨Or.inl hf.1, hf.2, by simp⟩
    · intro U hU hf
      apply h ((∅ : Finset V).disjSum U) (Finset.disjSum_mono (Finset.empty_subset S) hU)
      exact (fort_sum_iff G H _ _).mpr ⟨Or.inr hf.1, by simp, hf.2⟩
  · rintro ⟨hS, hT⟩ U hU hf
    have hparts := Finset.subset_disjSum.mp hU
    have hfparts := (fort_sum_iff G H U.toLeft U.toRight).mp
      (U.toLeft_disjSum_toRight.symm ▸ hf)
    rcases hfparts.1 with hl | hr
    · exact hS _ hparts.1 ⟨hl, hfparts.2.1⟩
    · exact hT _ hparts.2 ⟨hr, hfparts.2.2⟩

private theorem no_isolated_sum (hG : ∀ v, ∃ w, G.Adj v w)
    (hH : ∀ v, ∃ w, H.Adj v w) : ∀ v, ∃ w, (G ⊕g H).Adj v w := by
  intro v
  cases v with
  | inl v => obtain ⟨w, hw⟩ := hG v; exact ⟨.inl w, hw⟩
  | inr v => obtain ⟨w, hw⟩ := hH v; exact ⟨.inr w, hw⟩

private theorem rooted_sum_iff (hG : ∀ v, ∃ w, G.Adj v w)
    (hH : ∀ v, ∃ w, H.Adj v w) (S : Finset V) (T : Finset W) :
    MinimalFort (cone (G ⊕g H)) (rootSet (S.disjSum T)) ↔
      MinimalFort (cone G) (rootSet S) ∧ MinimalFort (cone H) (rootSet T) := by
  rw [minimalFort_rootSet_iff (G ⊕g H) (no_isolated_sum G H hG hH),
    minimalFort_rootSet_iff G hG, minimalFort_rootSet_iff H hH,
    minimalDominating_sum_iff G H, fort_free_sum_iff G H]
  tauto

/-- The full root-containing classes have the exact product cardinality. -/
theorem rootedChoices_sum_count (hG : ∀ v, ∃ w, G.Adj v w)
    (hH : ∀ v, ∃ w, H.Adj v w) :
    (rootedChoices (G ⊕g H)).card = (rootedChoices G).card * (rootedChoices H).card := by
  classical
  let f : Finset V × Finset W → Finset (V ⊕ W) := fun a => a.1.disjSum a.2
  have hi : Function.Injective f := by
    rintro ⟨S, T⟩ ⟨S', T'⟩ h
    exact Prod.ext (Finset.disjSum_inj.mp h).1 (Finset.disjSum_inj.mp h).2
  have he : rootedChoices (G ⊕g H) =
      ((rootedChoices G).product (rootedChoices H)).image f := by
    ext F
    simp only [rootedChoices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.product_eq_sprod, Finset.mem_product]
    constructor
    · intro hf
      refine ⟨(F.toLeft, F.toRight), ?_, F.toLeft_disjSum_toRight⟩
      exact (rooted_sum_iff G H hG hH _ _).mp (F.toLeft_disjSum_toRight.symm ▸ hf)
    · rintro ⟨⟨S, T⟩, ⟨hS, hT⟩, rfl⟩
      exact (rooted_sum_iff G H hG hH S T).mpr ⟨hS, hT⟩
  rw [he, Finset.card_image_of_injective _ hi, Finset.product_eq_sprod, Finset.card_product]

end D5.S3.Combinatorics.MinimalForts.RootedProduct
