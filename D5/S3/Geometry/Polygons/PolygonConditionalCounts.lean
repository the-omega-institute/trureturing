/- GID: D5/S3/Geometry/Polygons/PolygonConditionalCounts
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonConditionalCounts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Catalan and inclusion-exclusion counts of whole conditioned polygon fibres. -/

import D5.S3.Geometry.Polygons.PolygonEarContraction
import D5.S3.Geometry.Polygons.PolygonCatalanSupplier
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Nat.Choose.Sum

/-! Counts on all actual maximal noncrossing original internal chord sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
namespace D5.S3.Geometry.Polygons.PolygonConditionalCounts
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual PolygonEarContraction

variable {n : ℕ} [NeZero n]

def allEquiv :
    {T : Finset (Sym2 (ZMod n)) // IsTriangulation T} ≃
      {T : Finset (Sym2 (ZMod n)) // ClusterAlgebras.IsTriangulation T} where
  toFun T := ⟨T.val, ⟨T.property.isDiagonal, T.property.noncrossing, T.property.maximal⟩⟩
  invFun T := ⟨T.val, ⟨T.property.isDiagonal, T.property.noncrossing, T.property.maximal⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem all_card (hn : 3 ≤ n) :
    Nat.card {T : Finset (Sym2 (ZMod n)) // IsTriangulation T} = catalan (n - 2) := by
  have h : ENat.card {T : Finset (Sym2 (ZMod n)) // IsTriangulation T} =
      (catalan (n - 2) : ℕ∞) := by
    rw [ENat.card_congr (allEquiv (n := n))]
    exact ClusterAlgebras.TypeA.encard_setOf_isTriangulation hn
  rw [ENat.card_eq_coe_natCard] at h
  exact_mod_cast h

/-- Containing-event count for every compatible collection of original ears. -/
theorem forced_card (hn : 14 ≤ n) (P : Finset (ZMod n)) (hP : Compatible P) :
    Nat.card {T : Finset (Sym2 (ZMod n)) // IsTriangulation T ∧ P ⊆ EarCenters T} =
      catalan (n - P.card - 2) := by
  have hbound := compatible_card_bound (by omega) P hP
  have hs : 6 ≤ n - P.card := by omega
  letI : NeZero (n - P.card) := ⟨by omega⟩
  rw [Nat.card_congr (forcedEquiv P hs hP)]
  exact all_card (by omega)

/-- Integer form of the ordinary conditioned Catalan formula; subtraction in indices is natural. -/
def Npq (n p q : ℕ) : ℤ :=
  ∑ j ∈ range (q + 1), (-1 : ℤ) ^ j * (q.choose j : ℤ) * catalan (n - p - j - 2)

private abbrev Forced (P : Finset (ZMod n)) :=
  {T : Finset (Sym2 (ZMod n)) // IsTriangulation T ∧ P ⊆ EarCenters T}

private noncomputable instance forcedFintype (P : Finset (ZMod n)) : Fintype (Forced P) :=
  Fintype.ofFinite _

private noncomputable def event (P : Finset (ZMod n)) (i : ZMod n) : Finset (Forced P) :=
  univ.filter (fun T => i ∈ EarCenters T.val)

private lemma mem_inf_iff {α ι : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ι) (f : ι → Finset α) (x : α) :
    x ∈ s.inf f ↔ ∀ i ∈ s, x ∈ f i := by
  simpa only [Finset.le_eq_subset, singleton_subset_iff] using
    (Finset.le_inf_iff (s := s) (f := f) (a := ({x} : Finset α)))

private noncomputable def intersectionEquiv (P S : Finset (ZMod n)) :
    {T : Forced P // T ∈ S.inf (event P)} ≃ Forced (P ∪ S) where
  toFun T := ⟨T.val.val, T.val.property.1, by
    intro i hi
    rcases mem_union.mp hi with hi | hi
    · exact T.val.property.2 hi
    · have h := (mem_inf_iff S (event P) T.val).mp T.property i hi
      simpa only [event, mem_filter, mem_univ, true_and] using h⟩
  invFun T := ⟨⟨T.val, T.property.1, fun _ hi => T.property.2 (mem_union_left _ hi)⟩, by
    apply (mem_inf_iff _ _ _).mpr
    intro i hi
    simp only [event, mem_filter, mem_univ, true_and]
    exact T.property.2 (mem_union_right _ hi)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def forbiddenEquiv (P Q : Finset (ZMod n)) :
    {T : Forced P // T ∈ Q.inf (fun i => (event P i)ᶜ)} ≃ ConditionFiber P Q ∅ ∅ where
  toFun T := ⟨T.val.val, T.val.property.1, T.val.property.2, by
    apply disjoint_left.mpr
    intro i hi hmem
    have h := (mem_inf_iff Q (fun i => (event P i)ᶜ) T.val).mp T.property i hi
    have h' : i ∉ EarCenters T.val.val := by
      simpa only [mem_compl, event, mem_filter, mem_univ, true_and] using h
    exact h' hmem,
    by simp⟩
  invFun T := ⟨⟨T.val, T.property.1, T.property.2.1⟩, by
    apply (mem_inf_iff _ _ _).mpr
    intro i hi
    simp only [mem_compl, event, mem_filter, mem_univ, true_and]
    exact fun h => disjoint_left.mp T.property.2.2.1 hi h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact count of every completion with P forced and Q forbidden, at arbitrary cyclic placements. -/
theorem conditional_card (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hdis : Disjoint P Q) (hK : Compatible (P ∪ Q)) :
    (Nat.card (ConditionFiber P Q ∅ ∅) : ℤ) = Npq n P.card Q.card := by
  classical
  have hleft : ((Q.inf (fun i => (event P i)ᶜ)).card : ℤ) =
      (Nat.card (ConditionFiber P Q ∅ ∅) : ℤ) := by
    have he := Nat.card_congr (forbiddenEquiv P Q)
    rw [Nat.card_eq_fintype_card, Fintype.card_coe] at he
    exact_mod_cast he
  have hterm (S : Finset (ZMod n)) (hS : S ⊆ Q) :
      ((S.inf (event P)).card : ℤ) = (catalan (n - P.card - S.card - 2) : ℤ) := by
    have hc : Compatible (P ∪ S) := by
      intro i hi j hj hij
      exact hK (mem_union.mp hi |>.elim (mem_union_left _) (fun h => mem_union_right _ (hS h)))
        (mem_union.mp hj |>.elim (mem_union_left _) (fun h => mem_union_right _ (hS h))) hij
    have hdis' : Disjoint P S := hdis.mono_right hS
    have hcount := forced_card hn (P ∪ S) hc
    have he := Nat.card_congr (intersectionEquiv P S)
    rw [Nat.card_eq_fintype_card, Fintype.card_coe] at he
    rw [he, hcount, card_union_of_disjoint hdis', Nat.sub_add_eq]
  have h := Finset.inclusion_exclusion_card_inf_compl Q (event P)
  rw [hleft] at h
  calc
    (Nat.card (ConditionFiber P Q ∅ ∅) : ℤ) =
        ∑ S ∈ Q.powerset, (-1 : ℤ) ^ S.card * catalan (n - P.card - S.card - 2) := by
      rw [h]
      apply sum_congr rfl
      intro S hS
      rw [hterm S (mem_powerset.mp hS)]
    _ = Npq n P.card Q.card := by
      have hsum := Finset.sum_powerset_apply_card (x := Q)
        (fun j : ℕ => (-1 : ℤ) ^ j * (catalan (n - P.card - j - 2) : ℤ))
      simpa only [Npq, nsmul_eq_mul, mul_assoc, mul_left_comm] using hsum

end D5.S3.Geometry.Polygons.PolygonConditionalCounts
