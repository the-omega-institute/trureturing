/- GID: D5/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/SpacetimeArithmetic/CumulativeInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer-time cumulative summation is an additive equivalence between
     finitely supported increments and histories with a zero left tail and a
     constant right tail, with adjacent difference as its inverse.
   boundary: Coefficients form any additive commutative group. The spatial
     specialization uses jointly finitely supported integer profiles on
     integer time times three-dimensional integer space.
-/

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.Abel

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.SpacetimeArithmetic.CumulativeInverse

open scoped BigOperators

abbrev Signal (R : Type) [Zero R] := ℤ →₀ R

def TailCondition {R : Type} [Zero R] (C : ℤ → R) : Prop :=
  ∃ ℓ u : ℤ, ∃ B : R,
    (∀ n, n < ℓ → C n = 0) ∧ (∀ n, u ≤ n → C n = B)

abbrev History (R : Type) [Zero R] := {C : ℤ → R // TailCondition (R := R) C}

variable {R : Type} [AddCommGroup R]

instance : Zero (History R) :=
  ⟨⟨fun _ => 0, by
    refine ⟨0, 0, 0, ?_, ?_⟩ <;> simp⟩⟩

instance : Add (History R) :=
  ⟨fun C D => ⟨fun n => C.1 n + D.1 n, by
    rcases C.2 with ⟨ℓ₁, u₁, B₁, hℓ₁, hu₁⟩
    rcases D.2 with ⟨ℓ₂, u₂, B₂, hℓ₂, hu₂⟩
    refine ⟨min ℓ₁ ℓ₂, max u₁ u₂, B₁ + B₂, ?_, ?_⟩
    · intro n hn
      change C.1 n + D.1 n = 0
      rw [hℓ₁ n (lt_of_lt_of_le hn (min_le_left _ _)),
        hℓ₂ n (lt_of_lt_of_le hn (min_le_right _ _)), zero_add]
    · intro n hn
      change C.1 n + D.1 n = B₁ + B₂
      rw [hu₁ n (le_trans (le_max_left _ _) hn), hu₂ n (le_trans (le_max_right _ _) hn)]⟩⟩

instance : Neg (History R) :=
  ⟨fun C => ⟨fun n => -C.1 n, by
    rcases C.2 with ⟨ℓ, u, B, hℓ, hu⟩
    refine ⟨ℓ, u, -B, ?_, ?_⟩
    · intro n hn
      change -C.1 n = 0
      rw [hℓ n hn, neg_zero]
    · intro n hn
      change -C.1 n = -B
      rw [hu n hn]⟩⟩

instance : AddCommGroup (History R) where
  add_assoc C D E := by apply Subtype.ext; funext n; exact add_assoc _ _ _
  zero_add C := by apply Subtype.ext; funext n; exact zero_add _
  add_zero C := by apply Subtype.ext; funext n; exact add_zero _
  add_comm C D := by apply Subtype.ext; funext n; exact add_comm _ _
  neg_add_cancel C := by apply Subtype.ext; funext n; exact neg_add_cancel _
  nsmul := nsmulRec
  zsmul := zsmulRec

def cumulative (c : Signal R) (n : ℤ) : R :=
  ∑ t ∈ c.support.filter (fun t => t ≤ n), c t

lemma cumulative_succ (c : Signal R) (n : ℤ) :
    cumulative c n = cumulative c (n - 1) + c n := by
  by_cases h : c n = 0
  · have hn : n ∉ c.support := by simp [Finsupp.mem_support_iff, h]
    have heq : c.support.filter (fun t => t ≤ n) =
        c.support.filter (fun t => t ≤ n - 1) := by
      ext t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ht, htn⟩
        refine ⟨ht, ?_⟩
        by_contra hnot
        have : t = n := by omega
        exact hn (this ▸ ht)
      · rintro ⟨ht, htn⟩
        exact ⟨ht, by omega⟩
    simp [cumulative, heq, h]
  · have hn : n ∈ c.support := Finsupp.mem_support_iff.mpr h
    have heq : c.support.filter (fun t => t ≤ n) =
        insert n (c.support.filter (fun t => t ≤ n - 1)) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨ht, htn⟩
        by_cases htn' : t = n
        · exact Or.inl htn'
        · right
          refine ⟨ht, ?_⟩
          omega
      · intro ht
        rcases ht with rfl | ⟨ht, htn⟩
        · exact ⟨hn, le_rfl⟩
        · exact ⟨ht, le_trans htn (by omega)⟩
    have hnot : n ∉ c.support.filter (fun t => t ≤ n - 1) := by
      simp only [Finset.mem_filter]
      omega
    simp only [cumulative, heq, Finset.sum_insert hnot]
    exact add_comm _ _

noncomputable def cumulativeHistory (c : Signal R) : History R :=
  ⟨cumulative c, by
    classical
    by_cases hs : c.support.Nonempty
    · let ℓ := c.support.min' hs
      let u := c.support.max' hs + 1
      refine ⟨ℓ, u, ∑ t ∈ c.support, c t, ?_, ?_⟩
      · intro n hn
        have heq : c.support.filter (fun t => t ≤ n) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro t ht htn
          exact (not_lt_of_ge (c.support.min'_le t ht)) (lt_of_le_of_lt htn hn)
        simp [cumulative, heq]
      · intro n hn
        have heq : c.support.filter (fun t => t ≤ n) = c.support := by
          rw [Finset.filter_eq_self]
          intro t ht
          exact le_trans (c.support.le_max' t ht) (by omega)
        simp [cumulative, heq]
    · have hc : c = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
      subst c
      refine ⟨0, 0, 0, ?_, ?_⟩ <;> simp [cumulative]⟩

lemma difference_finite (C : History R) :
    (Function.support (fun n => C.1 n - C.1 (n - 1))).Finite := by
  rcases C.2 with ⟨ℓ, u, B, hℓ, hu⟩
  apply (Finset.Icc ℓ u).finite_toSet.subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_Icc]
  change C.1 n - C.1 (n - 1) ≠ 0 at hn
  constructor
  · by_contra h
    have hnl : n < ℓ := by omega
    exact hn (by rw [hℓ n hnl, hℓ (n - 1) (by omega), sub_self])
  · by_contra h
    have hnu : u < n := by omega
    exact hn (by rw [hu n (by omega), hu (n - 1) (by omega), sub_self])

noncomputable def difference (C : History R) : Signal R :=
  Finsupp.ofSupportFinite (fun n => C.1 n - C.1 (n - 1)) (difference_finite C)

lemma difference_apply (C : History R) (n : ℤ) :
    difference C n = C.1 n - C.1 (n - 1) := rfl

theorem difference_cumulative (c : Signal R) :
    difference (cumulativeHistory c) = c := by
  ext n
  change cumulative c n - cumulative c (n - 1) = c n
  rw [cumulative_succ, add_sub_cancel_left]

private theorem difference_injective : Function.Injective (difference (R := R)) := by
  intro C D h
  rcases C.2 with ⟨ℓC, uC, BC, hℓC, huC⟩
  rcases D.2 with ⟨ℓD, uD, BD, hℓD, huD⟩
  let b : ℤ := min ℓC ℓD - 1
  have hbC : C.1 b = 0 := hℓC b (by dsimp [b]; omega)
  have hbD : D.1 b = 0 := hℓD b (by dsimp [b]; omega)
  have hsame : ∀ k : ℕ, C.1 (b + k) = D.1 (b + k) := by
    intro k
    induction k with
    | zero => simpa using hbC.trans hbD.symm
    | succ k hk =>
      have hstep := congrArg (fun c : Signal R => c (b + (k + 1 : ℕ))) h
      simp only [difference_apply] at hstep
      have hp : b + ((k + 1 : ℕ) : ℤ) - 1 = b + (k : ℤ) := by omega
      rw [hp, hk] at hstep
      exact sub_left_inj.mp hstep
  apply Subtype.ext
  funext n
  by_cases hn : n < b
  · rw [hℓC n (by dsimp [b] at hn; omega), hℓD n (by dsimp [b] at hn; omega)]
  · have heq : b + ((n - b).toNat : ℤ) = n := by omega
    simpa only [heq] using hsame (n - b).toNat

theorem cumulative_difference (C : History R) :
    cumulativeHistory (difference C) = C := by
  apply difference_injective
  exact difference_cumulative (difference C)

private theorem difference_add (C D : History R) :
    difference (C + D) = difference C + difference D := by
  ext n
  change (C.1 n + D.1 n) - (C.1 (n - 1) + D.1 (n - 1)) =
    (C.1 n - C.1 (n - 1)) + (D.1 n - D.1 (n - 1))
  abel

theorem cumulative_add (c d : Signal R) :
    cumulativeHistory (c + d) = cumulativeHistory c + cumulativeHistory d := by
  apply difference_injective
  rw [difference_cumulative, difference_add, difference_cumulative, difference_cumulative]

noncomputable def cumulativeEquiv : Signal R ≃+ History R where
  toFun := cumulativeHistory
  invFun := difference
  left_inv := difference_cumulative
  right_inv := cumulative_difference
  map_add' := cumulative_add

theorem cumulative_inverse_bijective : Function.Bijective (cumulativeHistory (R := R)) :=
  cumulativeEquiv.bijective

abbrev Space := Fin 3 → ℤ

abbrev Spatial := Space →₀ ℤ

abbrev Profile := (ℤ × Space) →₀ ℤ

noncomputable def profileCumulativeEquiv : Profile ≃+ History Spatial :=
  Finsupp.curryAddEquiv.trans cumulativeEquiv

theorem profile_cumulative_apply (c : Profile) (n : ℤ) :
    (profileCumulativeEquiv c).1 n = cumulative c.curry n := rfl

theorem profile_inverse_apply (C : History Spatial) (n : ℤ) (p : Space) :
    profileCumulativeEquiv.symm C (n, p) = C.1 n p - C.1 (n - 1) p := rfl

theorem cumulative_inverse :
    Function.Bijective profileCumulativeEquiv ∧
      (∀ c d : Profile, profileCumulativeEquiv (c + d) =
        profileCumulativeEquiv c + profileCumulativeEquiv d) ∧
      (∀ (C : History Spatial) (n : ℤ) (p : Space),
        profileCumulativeEquiv.symm C (n, p) = C.1 n p - C.1 (n - 1) p) :=
  ⟨profileCumulativeEquiv.bijective, profileCumulativeEquiv.map_add, profile_inverse_apply⟩

end D5.S3.ConceptDynamics.SpacetimeArithmetic.CumulativeInverse

#print axioms D5.S3.ConceptDynamics.SpacetimeArithmetic.CumulativeInverse.difference_cumulative
#print axioms D5.S3.ConceptDynamics.SpacetimeArithmetic.CumulativeInverse.cumulative_difference
#print axioms D5.S3.ConceptDynamics.SpacetimeArithmetic.CumulativeInverse.cumulative_inverse
