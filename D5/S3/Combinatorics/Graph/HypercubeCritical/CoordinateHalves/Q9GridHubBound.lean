import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9SignedProjection
import Mathlib.Data.Finset.Card

/-! The four-carrier hub bound for the nine-point grid projection. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridHubBound

open Finset
open BalancedCriticalSpectrum (Q)
open Q9SignedProjection (signedRow)

/-- The two lower bounds on side counts and the two edge counts bound the hub carrier.
At equality the two side carriers partition the hub and lie in the corner carrier. -/
theorem hub_card_le_eight {V : Type*} [DecidableEq V] {A B C D : Finset V}
    (hno : ∀ x ∈ A, x ∈ B → x ∉ C)
    (htotal : A.card + 2 * B.card + 2 * C.card + 4 * D.card = 72)
    (hB : 28 ≤ B.card + 2 * D.card) (hC : 28 ≤ C.card + 2 * D.card)
    (hedgeB : (A ∩ B).card + 2 * (C ∩ D).card = 12)
    (hedgeC : (A ∩ C).card + 2 * (B ∩ D).card = 12) :
    A.card ≤ 8 ∧ (A.card = 8 → Disjoint B C ∧ A = B ∪ C ∧ A ⊆ D) := by
  have hdisjoint : Disjoint (A ∩ B) (A ∩ C) := by
    apply disjoint_left.mpr
    intro x hxAB hxAC
    exact hno x (mem_inter.mp hxAB).1 (mem_inter.mp hxAB).2 (mem_inter.mp hxAC).2
  have hsub : (A ∩ B) ∪ (A ∩ C) ⊆ A := union_subset inter_subset_left inter_subset_left
  have hcovered := card_le_card hsub
  have hcardUnion := card_union_of_disjoint hdisjoint
  have hBD := card_le_card (inter_subset_left : B ∩ D ⊆ B)
  have hCD := card_le_card (inter_subset_left : C ∩ D ⊆ C)
  have hbudget : A.card + B.card + C.card ≤ 16 := by omega
  have hcapacity : 24 ≤ A.card + 2 * (B.card + C.card) := by omega
  refine ⟨by omega, ?_⟩
  intro hEight
  have hside : B.card + C.card = 8 := by omega
  have hcover : (A ∩ B) ∪ (A ∩ C) = A := eq_of_subset_of_card_le hsub (by omega)
  have hAB := card_le_card (inter_subset_right : A ∩ B ⊆ B)
  have hAC := card_le_card (inter_subset_right : A ∩ C ⊆ C)
  have hBfull : A ∩ B = B := eq_of_subset_of_card_le inter_subset_right (by omega)
  have hCfull : A ∩ C = C := eq_of_subset_of_card_le inter_subset_right (by omega)
  have hBeq : B ∩ D = B := eq_of_subset_of_card_le inter_subset_left (by omega)
  have hCeq : C ∩ D = C := eq_of_subset_of_card_le inter_subset_left (by omega)
  have hUnion : A = B ∪ C := by simpa only [hBfull, hCfull] using hcover.symm
  refine ⟨by simpa only [hBfull, hCfull] using hdisjoint, hUnion, ?_⟩
  rw [hUnion, ← hBeq, ← hCeq]
  exact union_subset inter_subset_right inter_subset_right

/-- With sign agreement on the hub overlaps, the two signed row equations rule out
equality in the hub bound. The weighted total makes the hub cardinality even. -/
theorem signed_hub_card_le_six {A B C D : Finset (Q 5)} {a b c : Q 5 → ℤ}
    (hno : ∀ x ∈ A, x ∈ B → x ∉ C)
    (htotal : A.card + 2 * B.card + 2 * C.card + 4 * D.card = 72)
    (hB : 28 ≤ B.card + 2 * D.card) (hC : 28 ≤ C.card + 2 * D.card)
    (hedgeB : (A ∩ B).card + 2 * (C ∩ D).card = 12)
    (hedgeC : (A ∩ C).card + 2 * (B ∩ D).card = 12)
    (ha : ∀ x, x ∈ A ↔ a x ≠ 0) (hb : ∀ x, x ∈ B ↔ b x ≠ 0)
    (hc : ∀ x, x ∈ C ↔ c x ≠ 0)
    (hab : ∀ x, a x ≠ 0 → b x ≠ 0 → a x = b x)
    (hac : ∀ x, a x ≠ 0 → c x ≠ 0 → a x = c x)
    (hrowA : ∀ x, signedRow a x = 3 * a x - 2 * b x - 2 * c x)
    (hrowSum : ∀ x, signedRow (fun y => b y + c y) x = 2 * a x - 3 * (b x + c x)) :
    A.card ≤ 6 := by
  obtain ⟨hle, heq⟩ := hub_card_le_eight hno htotal hB hC hedgeB hedgeC
  have hEven : A.card % 2 = 0 := by omega
  have hne : A.card ≠ 8 := by
    intro hEight
    obtain ⟨hdisjoint, hUnion, _⟩ := heq hEight
    have hsum : (fun x => b x + c x) = a := by
      funext x
      have hsupport : a x ≠ 0 ↔ b x ≠ 0 ∨ c x ≠ 0 := by
        simpa only [hUnion, mem_union, hb x, hc x] using (ha x).symm
      by_cases hbzero : b x = 0
      · by_cases hczero : c x = 0
        · have hazero : a x = 0 := by
            by_contra hanz
            exact (hsupport.mp hanz).elim (fun h => h hbzero) (fun h => h hczero)
          simp only [hazero, hbzero, hczero, add_zero]
        · rw [hbzero, zero_add, ← hac x (hsupport.mpr (Or.inr hczero)) hczero]
      · have hczero : c x = 0 := by
          by_contra hcnz
          exact disjoint_left.mp hdisjoint ((hb x).mpr hbzero) ((hc x).mpr hcnz)
        rw [hczero, add_zero, ← hab x (hsupport.mpr (Or.inl hbzero)) hbzero]
    have hnonempty : A.Nonempty := card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := hnonempty
    have hsumAt : b x + c x = a x := congrFun hsum x
    have hleft := hrowA x
    have hright := hrowSum x
    rw [hsum, hsumAt] at hright
    have hzero : a x = 0 := by omega
    exact ((ha x).mp hx) hzero
  omega

#print axioms hub_card_le_eight
#print axioms signed_hub_card_le_six

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9GridHubBound
