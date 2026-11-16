/- GID: D5/S3/Combinatorics/ConstraintRelations/NearUnanimityInterpolation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ConstraintRelations/NearUnanimityInterpolation
   mirror-E: none(waiver:structural-proof)
   anchors: []
   utility: none
   digest: One fixed near-unanimity operation interpolates finite coordinate sets. -/

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Choose

/-! # Finite-coordinate interpolation under a fixed near-unanimity operation -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ConstraintRelations.NearUnanimityInterpolation

universe u v

/-- Preservation by one fixed k-ary near-unanimity operation turns agreement on
all subsets of fewer than k coordinates into agreement on any finite set.
The coordinate types may vary and need not be finite. -/
theorem finite_coordinate_interpolation
    {I : Type u} (X : I → Type v) (k : Nat) (hk : 3 ≤ k)
    (nu : (i : I) → (Fin k → X i) → X i)
    (hnu : ∀ (i : I) (a b : X i) (bad : Fin k),
      nu i (fun j => if j = bad then b else a) = a)
    (R : Set ((i : I) → X i))
    (hclosure : ∀ rows : Fin k → ((i : I) → X i),
      (∀ j, rows j ∈ R) → (fun i => nu i (fun j => rows j i)) ∈ R)
    (theta : (i : I) → X i) (F : Finset I)
    (hlocal : ∀ T : Finset I, T ⊆ F → T.card < k →
      ∃ r : (i : I) → X i, r ∈ R ∧ ∀ i, i ∈ T → r i = theta i) :
    ∃ r : (i : I) → X i, r ∈ R ∧ ∀ i, i ∈ F → r i = theta i := by
  classical
  revert hlocal
  refine Finset.strongInductionOn F ?_
  intro F ih hlocal
  by_cases hsmall : F.card < k
  · exact hlocal F (fun _ h => h) hsmall
  obtain ⟨G, hGF, hGcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hsmall)
  let e : G ≃ Fin k := Finset.equivFinOfCardEq hGcard
  let pick : Fin k → I := fun j => (e.symm j).val
  have hpick (j : Fin k) : pick j ∈ F := hGF (e.symm j).property
  have hinj : Function.Injective pick := by
    intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  have hrows : ∀ j : Fin k, ∃ r : (i : I) → X i, r ∈ R ∧
      ∀ i, i ∈ F.erase (pick j) → r i = theta i := by
    intro j
    apply ih (F.erase (pick j)) (Finset.erase_ssubset (hpick j))
    intro T hTF hT
    exact hlocal T (hTF.trans (Finset.erase_subset _ _)) hT
  choose rows hR hagree using hrows
  refine ⟨fun i => nu i (fun j => rows j i), hclosure rows hR, ?_⟩
  intro i hi
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < (3 : Nat)) hk
  obtain ⟨bad, hbad⟩ : ∃ bad : Fin k, ∀ j : Fin k, j ≠ bad → pick j ≠ i := by
    by_cases hhit : ∃ j : Fin k, pick j = i
    · obtain ⟨bad, hbad⟩ := hhit
      refine ⟨bad, ?_⟩
      intro j hj hji
      exact hj (hinj (hji.trans hbad.symm))
    · exact ⟨⟨0, hkpos⟩, fun j _ hji => hhit ⟨j, hji⟩⟩
  have htuple : (fun j => rows j i) =
      (fun j => if j = bad then rows bad i else theta i) := by
    funext j
    by_cases hj : j = bad
    · subst j
      simp
    · rw [ite_eq_right hj]
      exact hagree j i (Finset.mem_erase.mpr ⟨(hbad j hj).symm, hi⟩)
  change nu i (fun j => rows j i) = theta i
  rw [htuple]
  exact hnu i (theta i) (rows bad i) bad

end D5.S3.Combinatorics.ConstraintRelations.NearUnanimityInterpolation
