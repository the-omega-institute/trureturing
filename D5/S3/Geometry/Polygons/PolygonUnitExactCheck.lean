import D5.S3.Geometry.Polygons.PolygonStrictNormalization
import D5.S3.Geometry.Polygons.PolygonConditionalCounts
import D5.S3.Geometry.Polygons.PolygonConditionedFan
import Mathlib.Data.Real.Basic
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

open Finset
open D5.S3.Geometry.Polygons.PolygonEarSlide.Carrier
open D5.S3.Geometry.Polygons.PolygonEarSlide.Actual
open D5.S3.Geometry.Polygons.PolygonEarContraction
open D5.S3.Geometry.Polygons.PolygonConditionalCounts
open D5.S3.Geometry.Polygons.PolygonConditionedFan

namespace FibCountPositivityProbe6ae6

theorem compatibility_bridge {n : ℕ} [NeZero n] (P Q : Finset (ZMod n)) :
    (↑(P ∪ Q) : Set (ZMod n)).Pairwise
      (fun i j => ¬Cross (ear i) (ear j)) ↔ Compatible (P ∪ Q) := by
  constructor
  · intro hc i hi j hj hij
    exact hc hi hj hij
  · intro hc i hi j hj hij
    exact hc hi hj hij

theorem source_count_positive {n : ℕ} [NeZero n] (hn : 14 ≤ n)
    (P Q : Finset (ZMod n)) (hd : Disjoint P Q)
    (hc : (↑(P ∪ Q) : Set (ZMod n)).Pairwise
      (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : (P.card = 2 ∧ Q.card = 2) ∨ (P.card = 3 ∧ Q.card = 3) ∨
      (P.card = 2 ∧ Q.card = 4) ∨ (P.card = 4 ∧ Q.card = 2)) :
    ((Nat.card (ConditionFiber P Q ∅ ∅) : ℤ) = Npq n P.card Q.card ∧
      0 < Npq n P.card Q.card ∧ Nonempty (ConditionFiber P Q ∅ ∅)) ∧
    ((Nat.card (ConditionFiber Q P ∅ ∅) : ℤ) = Npq n Q.card P.card ∧
      0 < Npq n Q.card P.card ∧ Nonempty (ConditionFiber Q P ∅ ∅)) := by
  have hk := (compatibility_bridge P Q).mp hc
  have hc' : (↑(Q ∪ P) : Set (ZMod n)).Pairwise
      (fun i j => ¬Cross (ear i) (ear j)) := by
    simpa only [Finset.union_comm] using hc
  have hcases' : (Q.card = 2 ∧ P.card = 2) ∨ (Q.card = 3 ∧ P.card = 3) ∨
      (Q.card = 2 ∧ P.card = 4) ∨ (Q.card = 4 ∧ P.card = 2) := by
    rcases hcases with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
    · exact Or.inl ⟨hq, hp⟩
    · exact Or.inr (Or.inl ⟨hq, hp⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hq, hp⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hq, hp⟩))
  have hpq := conditional_card hn P Q hd hk
  have hqp := conditional_card hn Q P hd.symm ((compatibility_bridge Q P).mp hc')
  have fpq := source_conditioned_witnesses hn P Q hd hc hcases
  have fqp := source_conditioned_witnesses hn Q P hd.symm hc' hcases'
  have ppq : (0 : ℤ) < Nat.card (ConditionFiber P Q ∅ ∅) := by
    exact_mod_cast fpq.2.1
  have pqp : (0 : ℤ) < Nat.card (ConditionFiber Q P ∅ ∅) := by
    exact_mod_cast fqp.2.1
  exact ⟨⟨hpq, hpq ▸ ppq, fpq.1⟩, ⟨hqp, hqp ▸ pqp, fqp.1⟩⟩

theorem real_denominators {n : ℕ} [NeZero n] (hn : 14 ≤ n)
    (P Q : Finset (ZMod n)) (hd : Disjoint P Q)
    (hc : (↑(P ∪ Q) : Set (ZMod n)).Pairwise
      (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : (P.card = 2 ∧ Q.card = 2) ∨ (P.card = 3 ∧ Q.card = 3) ∨
      (P.card = 2 ∧ Q.card = 4) ∨ (P.card = 4 ∧ Q.card = 2)) :
    ((Nat.card (ConditionFiber P Q ∅ ∅) : ℝ) = (Npq n P.card Q.card : ℝ) ∧
      0 < (Nat.card (ConditionFiber P Q ∅ ∅) : ℝ) ∧
      0 < (Npq n P.card Q.card : ℝ) ∧ (Npq n P.card Q.card : ℝ) ≠ 0) ∧
    ((Nat.card (ConditionFiber Q P ∅ ∅) : ℝ) = (Npq n Q.card P.card : ℝ) ∧
      0 < (Nat.card (ConditionFiber Q P ∅ ∅) : ℝ) ∧
      0 < (Npq n Q.card P.card : ℝ) ∧ (Npq n Q.card P.card : ℝ) ≠ 0) := by
  have h := source_count_positive hn P Q hd hc hcases
  have epq : (Nat.card (ConditionFiber P Q ∅ ∅) : ℝ) =
      (Npq n P.card Q.card : ℝ) := by exact_mod_cast h.1.1
  have eqp : (Nat.card (ConditionFiber Q P ∅ ∅) : ℝ) =
      (Npq n Q.card P.card : ℝ) := by exact_mod_cast h.2.1
  have ppq : (0 : ℝ) < (Npq n P.card Q.card : ℝ) := by exact_mod_cast h.1.2.1
  have pqp : (0 : ℝ) < (Npq n Q.card P.card : ℝ) := by exact_mod_cast h.2.2.1
  exact ⟨⟨epq, epq.symm ▸ ppq, ppq, ne_of_gt ppq⟩,
    ⟨eqp, eqp.symm ▸ pqp, pqp, ne_of_gt pqp⟩⟩

theorem denominator_substitution {n : ℕ} [NeZero n] (hn : 14 ≤ n)
    (P Q : Finset (ZMod n)) (hd : Disjoint P Q)
    (hc : (↑(P ∪ Q) : Set (ZMod n)).Pairwise
      (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : (P.card = 2 ∧ Q.card = 2) ∨ (P.card = 3 ∧ Q.card = 3) ∨
      (P.card = 2 ∧ Q.card = 4) ∨ (P.card = 4 ∧ Q.card = 2))
    (a b : ℝ) :
    a / (Nat.card (ConditionFiber P Q ∅ ∅) : ℝ) +
        b / (Nat.card (ConditionFiber Q P ∅ ∅) : ℝ) =
      a / (Npq n P.card Q.card : ℝ) + b / (Npq n Q.card P.card : ℝ) := by
  have h := real_denominators hn P Q hd hc hcases
  rw [h.1.1, h.2.1]

theorem literal_original_source (n : ℕ) (hn : 14 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∀ P Q : Finset (ZMod n), Disjoint P Q →
      (↑(P ∪ Q) : Set (ZMod n)).Pairwise
        (fun i j => ¬Cross (ear i) (ear j)) →
      ((P.card = 2 ∧ Q.card = 2) ∨ (P.card = 3 ∧ Q.card = 3) ∨
        (P.card = 2 ∧ Q.card = 4) ∨ (P.card = 4 ∧ Q.card = 2)) →
      (((Nat.card (ConditionFiber P Q ∅ ∅) : ℤ) = Npq n P.card Q.card ∧
          0 < Npq n P.card Q.card ∧ Nonempty (ConditionFiber P Q ∅ ∅)) ∧
        ((Nat.card (ConditionFiber Q P ∅ ∅) : ℤ) = Npq n Q.card P.card ∧
          0 < Npq n Q.card P.card ∧ Nonempty (ConditionFiber Q P ∅ ∅))) ∧
      (((Nat.card (ConditionFiber P Q ∅ ∅) : ℝ) = (Npq n P.card Q.card : ℝ) ∧
          0 < (Nat.card (ConditionFiber P Q ∅ ∅) : ℝ) ∧
          0 < (Npq n P.card Q.card : ℝ) ∧ (Npq n P.card Q.card : ℝ) ≠ 0) ∧
        ((Nat.card (ConditionFiber Q P ∅ ∅) : ℝ) = (Npq n Q.card P.card : ℝ) ∧
          0 < (Nat.card (ConditionFiber Q P ∅ ∅) : ℝ) ∧
          0 < (Npq n Q.card P.card : ℝ) ∧ (Npq n Q.card P.card : ℝ) ≠ 0)) := by
  letI : NeZero n := ⟨by omega⟩
  intro P Q hd hc hcases
  exact ⟨source_count_positive hn P Q hd hc hcases,
    real_denominators hn P Q hd hc hcases⟩


end FibCountPositivityProbe6ae6

namespace CanonicalSourceApplication
open Finset
open D5.S3.Geometry.Polygons
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual
open PolygonSimultaneousCompression PolygonConditionalCounts PolygonStrictNormalization
variable {n : ℕ} [NeZero n]
private lemma sourceCases_swap {P Q : Finset (ZMod n)} (h : SourceCases P Q) : SourceCases Q P := by
  rcases h with ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ | ⟨a,b⟩ <;> simp_all [SourceCases]
lemma normalized_whole_le_one (P Q : Finset (ZMod n))
    (hpos : (0 : ℝ) < Nat.card (WholeFiber P Q)) (A : Finset (WholeFiber P Q)) :
    (A.card : ℝ) / Nat.card (WholeFiber P Q) ≤ 1 := by
  apply (div_le_one hpos).mpr
  exact_mod_cast (show A.card ≤ Nat.card (WholeFiber P Q) from by
    simpa only [Nat.card_eq_fintype_card] using A.card_le_univ)

lemma normalized_whole_eq_one (P Q : Finset (ZMod n))
    (hpos : (0 : ℝ) < Nat.card (WholeFiber P Q)) (A : Finset (WholeFiber P Q)) :
    (A.card : ℝ) / Nat.card (WholeFiber P Q) = 1 ↔ A = univ := by
  constructor
  · intro h
    have he : (A.card : ℝ) = Nat.card (WholeFiber P Q) := (div_eq_one_iff_eq hpos.ne').mp h
    apply A.eq_univ_of_card
    have hnat : A.card = Nat.card (WholeFiber P Q) := by exact_mod_cast he
    simpa only [Nat.card_eq_fintype_card] using hnat
  · intro h
    subst A
    simp only [card_univ, Nat.card_eq_fintype_card]
    apply div_self
    simpa only [Nat.card_eq_fintype_card] using hpos.ne'

lemma original_normalized_le
    (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hd : Disjoint P Q)
    (hK : (↑(P ∪ Q) : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : SourceCases P Q)
    (A : Finset (WholeFiber P Q)) (B : Finset (WholeFiber Q P))
    (hc : ∀ T ∈ A, ∀ U ∈ B, ¬Disjoint (EarCenters T.val) (EarCenters U.val)) :
    (A.card : ℝ) / Nat.card (WholeFiber P Q) +
      (B.card : ℝ) / Nat.card (WholeFiber Q P) ≤ 1 := by
  have hposP : (0 : ℝ) < Nat.card (WholeFiber P Q) := by
    exact_mod_cast (PolygonConditionedFan.source_conditioned_witnesses hn P Q hd hK hcases).2.1
  have hposQ : (0 : ℝ) < Nat.card (WholeFiber Q P) := by
    exact_mod_cast (PolygonConditionedFan.source_conditioned_witnesses hn Q P hd.symm
      (by simpa only [union_comm] using hK) (sourceCases_swap hcases)).2.1
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · exact (original_normalized_strict hn P Q hd hK hcases A B hc hA hB).le
    · have he : B = ∅ := not_nonempty_iff_eq_empty.mp hB
      simpa only [he, card_empty, Nat.cast_zero, zero_div, add_zero] using
        normalized_whole_le_one P Q hposP A
  · have he : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    simpa only [he, card_empty, Nat.cast_zero, zero_div, zero_add] using
      normalized_whole_le_one Q P hposQ B

lemma original_normalized_equality
    (hn : 14 ≤ n) (P Q : Finset (ZMod n))
    (hd : Disjoint P Q)
    (hK : (↑(P ∪ Q) : Set (ZMod n)).Pairwise (fun i j => ¬Cross (ear i) (ear j)))
    (hcases : SourceCases P Q)
    (A : Finset (WholeFiber P Q)) (B : Finset (WholeFiber Q P))
    (hc : ∀ T ∈ A, ∀ U ∈ B, ¬Disjoint (EarCenters T.val) (EarCenters U.val)) :
    ((A.card : ℝ) / Nat.card (WholeFiber P Q) +
      (B.card : ℝ) / Nat.card (WholeFiber Q P) = 1) ↔
      (A = ∅ ∧ B = univ) ∨ (B = ∅ ∧ A = univ) := by
  classical
  have hposP : (0 : ℝ) < Nat.card (WholeFiber P Q) := by
    exact_mod_cast (PolygonConditionedFan.source_conditioned_witnesses hn P Q hd hK hcases).2.1
  have hposQ : (0 : ℝ) < Nat.card (WholeFiber Q P) := by
    exact_mod_cast (PolygonConditionedFan.source_conditioned_witnesses hn Q P hd.symm
      (by simpa only [union_comm] using hK) (sourceCases_swap hcases)).2.1
  constructor
  · intro h
    by_cases hA : A.Nonempty
    · by_cases hB : B.Nonempty
      · exact ((original_normalized_strict hn P Q hd hK hcases A B hc hA hB).ne h).elim
      · have he : B = ∅ := not_nonempty_iff_eq_empty.mp hB
        have heA : (A.card : ℝ) / Nat.card (WholeFiber P Q) = 1 := by
          simpa only [he, card_empty, Nat.cast_zero, zero_div, add_zero] using h
        exact Or.inr ⟨he,(normalized_whole_eq_one P Q hposP A).mp heA⟩
    · have he : A = ∅ := not_nonempty_iff_eq_empty.mp hA
      have heB : (B.card : ℝ) / Nat.card (WholeFiber Q P) = 1 := by
        simpa only [he, card_empty, Nat.cast_zero, zero_div, zero_add] using h
      exact Or.inl ⟨he,(normalized_whole_eq_one Q P hposQ B).mp heB⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · simpa only [card_empty, Nat.cast_zero, zero_div, zero_add] using
        (normalized_whole_eq_one Q P hposQ univ).mpr rfl
    · simpa only [card_empty, Nat.cast_zero, zero_div, add_zero] using
        (normalized_whole_eq_one P Q hposP univ).mpr rfl

end CanonicalSourceApplication
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

open Finset
namespace FibFullSourceComposition
open D5.S3.Geometry.Polygons
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual
open PolygonSimultaneousCompression PolygonConditionalCounts

-- Both accepted paths use the same complete literal original carrier.
theorem same_carrier {n : ℕ} [NeZero n] (P Q : Finset (ZMod n)) :
    WholeFiber P Q = ConditionFiber P Q ∅ ∅ := rfl

theorem literal_full_B37_2 (n : ℕ) (hn : 14 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∀ P Q : Finset (ZMod n), Disjoint P Q →
      (↑(P ∪ Q) : Set (ZMod n)).Pairwise
        (fun i j => ¬Cross (ear i) (ear j)) →
      ((P.card = 2 ∧ Q.card = 2) ∨ (P.card = 3 ∧ Q.card = 3) ∨
        (P.card = 2 ∧ Q.card = 4) ∨ (P.card = 4 ∧ Q.card = 2)) →
      (((Nat.card (WholeFiber P Q) : ℤ) = Npq n P.card Q.card ∧ 0 < Npq n P.card Q.card ∧
          Nonempty (WholeFiber P Q)) ∧
        ((Nat.card (WholeFiber Q P) : ℤ) = Npq n Q.card P.card ∧ 0 < Npq n Q.card P.card ∧
          Nonempty (WholeFiber Q P))) ∧
      (((Nat.card (WholeFiber P Q) : ℝ) = (Npq n P.card Q.card : ℝ) ∧
          0 < (Npq n P.card Q.card : ℝ) ∧ (Npq n P.card Q.card : ℝ) ≠ 0) ∧
        ((Nat.card (WholeFiber Q P) : ℝ) = (Npq n Q.card P.card : ℝ) ∧
          0 < (Npq n Q.card P.card : ℝ) ∧ (Npq n Q.card P.card : ℝ) ≠ 0)) ∧
      ∀ (A : Finset (WholeFiber P Q)) (B : Finset (WholeFiber Q P)),
        (∀ T ∈ A, ∀ U ∈ B,
          ¬Disjoint (EarCenters T.val) (EarCenters U.val)) →
        ((A.card : ℝ) / (Npq n P.card Q.card : ℝ) +
          (B.card : ℝ) / (Npq n Q.card P.card : ℝ) ≤ 1) ∧
        (A.Nonempty → B.Nonempty →
          (A.card : ℝ) / (Npq n P.card Q.card : ℝ) +
            (B.card : ℝ) / (Npq n Q.card P.card : ℝ) < 1) ∧
        (((A.card : ℝ) / (Npq n P.card Q.card : ℝ) +
          (B.card : ℝ) / (Npq n Q.card P.card : ℝ) = 1) ↔
          (A = ∅ ∧ B = univ) ∨ (B = ∅ ∧ A = univ)) := by
  letI : NeZero n := ⟨by omega⟩
  intro P Q hd hc hcases
  have hcount := FibCountPositivityProbe6ae6.source_count_positive hn P Q hd hc hcases
  have hreal := FibCountPositivityProbe6ae6.real_denominators hn P Q hd hc hcases
  refine ⟨hcount, ⟨⟨hreal.1.1, hreal.1.2.2⟩, ⟨hreal.2.1, hreal.2.2.2⟩⟩, ?_⟩
  intro A B hcross
  have hle := CanonicalSourceApplication.original_normalized_le hn P Q hd hc hcases A B hcross
  have hlt := D5.S3.Geometry.Polygons.PolygonStrictNormalization.original_normalized_strict hn P Q hd hc hcases A B hcross
  have heq := CanonicalSourceApplication.original_normalized_equality hn P Q hd hc hcases A B hcross
  have epq : (Nat.card (WholeFiber P Q) : ℝ) = (Npq n P.card Q.card : ℝ) := hreal.1.1
  have eqp : (Nat.card (WholeFiber Q P) : ℝ) = (Npq n Q.card P.card : ℝ) := hreal.2.1
  rw [epq, eqp] at hle hlt heq
  exact ⟨hle, hlt, heq⟩

theorem literal_expanded_B37_2 (n : ℕ) (hn : 14 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    ∀ P Q : Finset (ZMod n), Disjoint P Q →
      (↑(P ∪ Q) : Set (ZMod n)).Pairwise
        (fun i j => ¬Cross (ear i) (ear j)) →
      ((P.card = 2 ∧ Q.card = 2) ∨ (P.card = 3 ∧ Q.card = 3) ∨
        (P.card = 2 ∧ Q.card = 4) ∨ (P.card = 4 ∧ Q.card = 2)) →
      (((Nat.card (WholeFiber P Q) : ℤ) = ((∑ j ∈ range (Q.card + 1), (-1 : ℤ) ^ j * (Q.card.choose j : ℤ) * catalan (n - P.card - j - 2)) : ℤ) ∧ 0 < ((∑ j ∈ range (Q.card + 1), (-1 : ℤ) ^ j * (Q.card.choose j : ℤ) * catalan (n - P.card - j - 2)) : ℤ) ∧
          Nonempty (WholeFiber P Q)) ∧
        ((Nat.card (WholeFiber Q P) : ℤ) = ((∑ j ∈ range (P.card + 1), (-1 : ℤ) ^ j * (P.card.choose j : ℤ) * catalan (n - Q.card - j - 2)) : ℤ) ∧ 0 < ((∑ j ∈ range (P.card + 1), (-1 : ℤ) ^ j * (P.card.choose j : ℤ) * catalan (n - Q.card - j - 2)) : ℤ) ∧
          Nonempty (WholeFiber Q P))) ∧
      (((Nat.card (WholeFiber P Q) : ℝ) = (((∑ j ∈ range (Q.card + 1), (-1 : ℤ) ^ j * (Q.card.choose j : ℤ) * catalan (n - P.card - j - 2)) : ℤ) : ℝ) ∧
          0 < (((∑ j ∈ range (Q.card + 1), (-1 : ℤ) ^ j * (Q.card.choose j : ℤ) * catalan (n - P.card - j - 2)) : ℤ) : ℝ) ∧ (((∑ j ∈ range (Q.card + 1), (-1 : ℤ) ^ j * (Q.card.choose j : ℤ) * catalan (n - P.card - j - 2)) : ℤ) : ℝ) ≠ 0) ∧
        ((Nat.card (WholeFiber Q P) : ℝ) = (((∑ j ∈ range (P.card + 1), (-1 : ℤ) ^ j * (P.card.choose j : ℤ) * catalan (n - Q.card - j - 2)) : ℤ) : ℝ) ∧
          0 < (((∑ j ∈ range (P.card + 1), (-1 : ℤ) ^ j * (P.card.choose j : ℤ) * catalan (n - Q.card - j - 2)) : ℤ) : ℝ) ∧ (((∑ j ∈ range (P.card + 1), (-1 : ℤ) ^ j * (P.card.choose j : ℤ) * catalan (n - Q.card - j - 2)) : ℤ) : ℝ) ≠ 0)) ∧
      ∀ (A : Finset (WholeFiber P Q)) (B : Finset (WholeFiber Q P)),
        (∀ T ∈ A, ∀ U ∈ B,
          ¬Disjoint (EarCenters T.val) (EarCenters U.val)) →
        ((A.card : ℝ) / (((∑ j ∈ range (Q.card + 1), (-1 : ℤ) ^ j * (Q.card.choose j : ℤ) * catalan (n - P.card - j - 2)) : ℤ) : ℝ) +
          (B.card : ℝ) / (((∑ j ∈ range (P.card + 1), (-1 : ℤ) ^ j * (P.card.choose j : ℤ) * catalan (n - Q.card - j - 2)) : ℤ) : ℝ) ≤ 1) ∧
        (A.Nonempty → B.Nonempty →
          (A.card : ℝ) / (((∑ j ∈ range (Q.card + 1), (-1 : ℤ) ^ j * (Q.card.choose j : ℤ) * catalan (n - P.card - j - 2)) : ℤ) : ℝ) +
            (B.card : ℝ) / (((∑ j ∈ range (P.card + 1), (-1 : ℤ) ^ j * (P.card.choose j : ℤ) * catalan (n - Q.card - j - 2)) : ℤ) : ℝ) < 1) ∧
        (((A.card : ℝ) / (((∑ j ∈ range (Q.card + 1), (-1 : ℤ) ^ j * (Q.card.choose j : ℤ) * catalan (n - P.card - j - 2)) : ℤ) : ℝ) +
          (B.card : ℝ) / (((∑ j ∈ range (P.card + 1), (-1 : ℤ) ^ j * (P.card.choose j : ℤ) * catalan (n - Q.card - j - 2)) : ℤ) : ℝ) = 1) ↔
          (A = ∅ ∧ B = univ) ∨ (B = ∅ ∧ A = univ)) := by
  simpa only [Npq] using literal_full_B37_2 n hn

end FibFullSourceComposition

namespace FibFullSourceComposition
open Finset
open D5.S3.Geometry.Polygons
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual
open PolygonSimultaneousCompression PolygonConditionalCounts

theorem exact_common_ears {n : ℕ} [NeZero n] (P Q : Finset (ZMod n))
    (T : WholeFiber P Q) (U : WholeFiber Q P) :
    EarCenters T.val ∩ EarCenters U.val =
      (EarCenters T.val ∩ E_K (P ∪ Q)) ∩ (EarCenters U.val ∩ E_K (P ∪ Q)) :=
  common_ears_eq_trace_inter T U

theorem original_identity_both_ways {n : ℕ} [NeZero n]
    (T : {T : Finset (Sym2 (ZMod n)) // IsTriangulation T})
    (U : {T : Finset (Sym2 (ZMod n)) // ClusterAlgebras.IsTriangulation T}) :
    (allEquiv T).val = T.val ∧ (allEquiv.symm U).val = U.val := ⟨rfl, rfl⟩
end FibFullSourceComposition

run_cmd do
  let roots := #[``FibFullSourceComposition.same_carrier,
    ``FibFullSourceComposition.literal_full_B37_2,
    ``FibFullSourceComposition.literal_expanded_B37_2,
    ``FibFullSourceComposition.exact_common_ears,
    ``FibFullSourceComposition.original_identity_both_ways,
    ``FibCountPositivityProbe6ae6.source_count_positive,
    ``FibCountPositivityProbe6ae6.real_denominators,
    ``CanonicalSourceApplication.original_normalized_le,
    ``CanonicalSourceApplication.original_normalized_equality,
    ``D5.S3.Geometry.Polygons.PolygonTraceFlip.actual_flip_trace_injective,
    ``D5.S3.Geometry.Polygons.PolygonTraceFlip.actual_flip_trace_card_le,
    ``D5.S3.Geometry.Polygons.PolygonStrictNormalization.original_normalized_strict,
    ``D5.S3.Geometry.Polygons.PolygonConditionalCounts.allEquiv,
    ``D5.S3.Geometry.Polygons.PolygonConditionalCounts.conditional_card,
    ``D5.S3.Geometry.Polygons.PolygonConditionedFan.ear_injective,
    ``D5.S3.Geometry.Polygons.PolygonConditionedFan.source_conditioned_witnesses,
    ``ClusterAlgebras.TypeA.IsTriangulation.existsUnique_isFlipReplacement,
    ``ClusterAlgebras.TypeA.encard_setOf_isTriangulation]
  let roots := roots ++ #[``ClusterAlgebras.Cross.symm,
    ``ClusterAlgebras.mem_segments,
    ``ClusterAlgebras.TypeA.not_cross_self,
    ``ClusterAlgebras.TypeA.basePos_self,
    ``ClusterAlgebras.TypeA.basePos_self_lt_of_ne,
    ``ClusterAlgebras.TypeA.sbtw_iff_basePos,
    ``ClusterAlgebras.TypeA.bijOn_basePosSeg_isSide,
    ``ClusterAlgebras.TypeA.not_cross_of_isSide,
    ``ClusterAlgebras.TypeA.IsTriangulation.not_cross,
    ``ClusterAlgebras.TypeA.mem_segments_iff_basePosSeg,
    ``ClusterAlgebras.TypeA.isSegment_mk_of_ne,
    ``ClusterAlgebras.TypeA.mem_segments_iff_of_basePos_lt,
    ``ClusterAlgebras.TypeA.IsTriangulation.existsUnique_apex,
    ``ClusterAlgebras.TypeA.quadrilateral_basePos,
    ``ClusterAlgebras.TypeA.quadrilateral_cross,
    ``ClusterAlgebras.TypeA.cross_mk_of_interleave,
    ``ClusterAlgebras.TypeA.quadrilateral_cross_left_of_basePos,
    ``ClusterAlgebras.TypeA.quadrilateral_cross_right_of_basePos,
    ``ClusterAlgebras.TypeA.quadrilateral_cross_left,
    ``ClusterAlgebras.TypeA.quadrilateral_cross_right,
    ``ClusterAlgebras.TypeA.IsDiagonal.exists_sbtw,
    ``ClusterAlgebras.TypeA.mem_segments_flipTriangulation,
    ``ClusterAlgebras.TypeA.IsFlipQuadrilateral.rim_ne,
    ``ClusterAlgebras.TypeA.IsTriangulation.existsUnique_apex_of_mem,
    ``ClusterAlgebras.TypeA.IsFlipQuadrilateral.isFlipReplacement,
    ``ClusterAlgebras.TypeA.IsFlipQuadrilateral.eq_of_isFlipReplacement]
  let mut entries : Array Lean.Json := #[]
  for root in roots do
    let axioms ← Lean.collectAxioms root
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unaccepted transitive axiom {ax} in {root}"
    let info ← Lean.getConstInfo root
    unless (info.value? (allowOpaque := true)).isSome do
      throwError "Missing value for checked root {root}"
    let ty ← Lean.Elab.Command.liftTermElabM do
      Lean.withOptions (fun o => o.setBool `pp.explicit true |>.setBool `pp.fullNames true) do
        return (← Lean.Meta.ppExpr info.type).pretty
    entries := entries.push (Lean.Json.mkObj [
      ("root", Lean.Json.str root.toString),
      ("type", Lean.Json.str ty),
      ("axioms", Lean.Json.arr (axioms.map (fun ax => Lean.Json.str ax.toString)))])
    Lean.logInfo m!"CANONICAL_SOURCE_AXIOM_GUARD {root}: {axioms}"
  let some handoff ← IO.getEnv "FIB_CANONICAL_HANDOFF"
    | throwError "FIB_CANONICAL_HANDOFF required"
  IO.FS.writeFile (System.FilePath.mk handoff / "checked-roots.json")
    (Lean.Json.arr entries).pretty
  Lean.logInfo "CANONICAL_FULL_SOURCE_ACCEPTED selected-target-types-and-B37.2"
