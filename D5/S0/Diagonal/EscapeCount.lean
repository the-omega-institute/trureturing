/- GID: D5/S0/Diagonal/EscapeCount
   generality: G
   mirror-B: D5/B/S0/Diagonal/EscapeCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite diagonal listings admit an exact count of those escaped by self-application. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

open scoped BigOperators

universe u v

namespace D5.S0.Diagonal.EscapeCount

variable {A : Type u} {Y : Type v}

/-- Apply the twist to the diagonal entries of a finite self-application listing. -/
def diagonal (f : Y → Y) (g : A → A → Y) : A → Y := fun a => f (g a a)

/-- A listing is escaped when its twisted diagonal is absent from its range. -/
def IsEscaped (f : Y → Y) (g : A → A → Y) : Prop := diagonal f g ∉ Set.range g

/-- A row that lands on the twisted diagonal has a fixed point at its diagonal entry. -/
theorem diagonal_landing_fixed {f : Y → Y} {g : A → A → Y} {a₀ : A} :
    g a₀ = diagonal f g → f (g a₀ a₀) = g a₀ a₀ := by
  intro h
  simpa [diagonal] using (congrFun h a₀).symm

private abbrev Rows (A : Type u) (Y : Type v) :=
  (a : A) → {b : A // b ≠ a} → Y

private def listing_equiv [DecidableEq A] :
    (A → A → Y) ≃ (A → Y) × Rows A Y where
  toFun g := ⟨fun a => g a a, fun a b => g a b⟩
  invFun p a b := if h : b = a then p.1 a else p.2 a ⟨b, h⟩
  left_inv g := by
    funext a b
    by_cases h : b = a <;> simp [h]
  right_inv p := by
    rcases p with ⟨X, R⟩
    apply Prod.ext
    · funext a
      simp
    · funext a b
      simp [b.property]

private abbrev EscapedRows (f : Y → Y) (X : A → Y) (R : Rows A Y) : Prop :=
  ∀ a, ¬(f (X a) = X a ∧ R a = fun b => f (X b.1))

private theorem listing_equiv_escaped_iff [DecidableEq A]
    (f : Y → Y) (X : A → Y) (R : Rows A Y) :
    IsEscaped f (listing_equiv.symm ⟨X, R⟩) ↔ EscapedRows f X R := by
  classical
  change (¬∃ a, listing_equiv.symm ⟨X, R⟩ a =
    diagonal f (listing_equiv.symm ⟨X, R⟩)) ↔ _
  constructor
  · intro hEscaped a hCaptured
    apply hEscaped
    refine ⟨a, ?_⟩
    funext b
    by_cases hba : b = a
    · subst b
      simpa [listing_equiv, diagonal] using hCaptured.1.symm
    · have hOffDiagonal := congrFun hCaptured.2 ⟨b, hba⟩
      simpa [listing_equiv, diagonal, hba] using hOffDiagonal
  · intro hRows hRange
    rcases hRange with ⟨a, ha⟩
    apply hRows a
    constructor
    · simpa [listing_equiv, diagonal] using (congrFun ha a).symm
    · funext b
      have hOffDiagonal := congrFun ha b
      simpa [listing_equiv, diagonal, b.property] using hOffDiagonal

private theorem off_diagonal_card [Fintype A] [Fintype Y] [DecidableEq A] (a : A) :
    Fintype.card ({b : A // b ≠ a} → Y) =
      Fintype.card Y ^ (Fintype.card A - 1) := by
  rw [Fintype.card_fun]
  congr 1
  rw [Fintype.card_subtype_compl]
  simp

private theorem row_choice_card [Fintype A] [Fintype Y] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (X : A → Y) (a : A) :
    Fintype.card
        {r : {b : A // b ≠ a} → Y //
          ¬(f (X a) = X a ∧ r = fun b => f (X b.1))} =
      Fintype.card Y ^ (Fintype.card A - 1) -
        if f (X a) = X a then 1 else 0 := by
  classical
  rw [Fintype.card_subtype_compl]
  rw [off_diagonal_card]
  split_ifs with hFixed
  · simp [hFixed]
  · simp [hFixed]

private theorem fiber_card [Fintype A] [Fintype Y] [DecidableEq A] [DecidableEq Y]
    (f : Y → Y) (X : A → Y) :
    Fintype.card {R : Rows A Y // EscapedRows f X R} =
      ∏ a, (Fintype.card Y ^ (Fintype.card A - 1) -
        if f (X a) = X a then 1 else 0) := by
  classical
  calc
    _ = Fintype.card
        ((a : A) → {r : {b : A // b ≠ a} → Y //
          ¬(f (X a) = X a ∧ r = fun b => f (X b.1))}) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = ∏ a, Fintype.card
        {r : {b : A // b ≠ a} → Y //
          ¬(f (X a) = X a ∧ r = fun b => f (X b.1))} := Fintype.card_pi
    _ = _ := Finset.prod_congr rfl fun a _ => row_choice_card f X a

private theorem sum_row_weights [Fintype A] [Fintype Y] [DecidableEq Y] [Nonempty A]
    (f : Y → Y) :
    (∑ y : Y, (Fintype.card Y ^ (Fintype.card A - 1) -
      if f y = y then 1 else 0)) =
      Fintype.card Y ^ Fintype.card A - Fintype.card {y : Y // f y = y} := by
  classical
  have hIndicatorLe : ∀ y ∈ (Finset.univ : Finset Y),
      (if f y = y then 1 else 0) ≤ Fintype.card Y ^ (Fintype.card A - 1) := by
    intro y _
    split_ifs
    · exact one_le_pow₀ (Fintype.card_pos_iff.mpr ⟨y⟩)
    · exact Nat.zero_le _
  rw [Finset.sum_tsub_distrib Finset.univ hIndicatorLe]
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  rw [Finset.sum_boole]
  rw [← Fintype.card_subtype]
  congr 1
  rw [← pow_succ']
  congr 1
  exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr inferInstance)

/-- The number of listings escaped by a twist is the exact row-wise power of the
number of functions minus the fixed points of the twist. -/
theorem escaped_listing_card [Fintype A] [Fintype Y] (f : Y → Y) :
    Nat.card {g : A → A → Y // IsEscaped f g} =
      (Fintype.card Y ^ Fintype.card A - Nat.card {y : Y // f y = y}) ^
        Fintype.card A := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hA =>
      have hCardA : Fintype.card A = 0 := Fintype.card_eq_zero_iff.mpr hA
      rw [hCardA, pow_zero]
      rw [Nat.card_eq_fintype_card]
      apply Fintype.card_eq_one_iff.mpr
      let g : A → A → Y := fun a => (@IsEmpty.false A hA a).elim
      have hg : IsEscaped f g := by
        intro hRange
        rcases hRange with ⟨a, _⟩
        exact (@IsEmpty.false A hA a).elim
      refine ⟨⟨g, hg⟩, ?_⟩
      intro listing
      apply Subtype.ext
      funext a
      exact (@IsEmpty.false A hA a).elim
  | inr hA =>
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      calc
        Fintype.card {g : A → A → Y // IsEscaped f g} =
            Fintype.card {p : (A → Y) × Rows A Y //
              EscapedRows f p.1 p.2} := by
          apply Fintype.card_congr
          apply listing_equiv.subtypeEquiv
          intro g
          simpa using listing_equiv_escaped_iff f (listing_equiv g).1 (listing_equiv g).2
        _ = Fintype.card
            (Σ X : A → Y, {R : Rows A Y // EscapedRows f X R}) :=
          Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (EscapedRows f))
        _ = ∑ X : A → Y, Fintype.card {R : Rows A Y // EscapedRows f X R} :=
          Fintype.card_sigma
        _ = ∑ X : A → Y, ∏ a, (Fintype.card Y ^ (Fintype.card A - 1) -
            if f (X a) = X a then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro X _
          exact fiber_card f X
        _ = ∏ _a : A, ∑ y : Y, (Fintype.card Y ^ (Fintype.card A - 1) -
            if f y = y then 1 else 0) := by
          symm
          exact Fintype.prod_sum fun (_a : A) (y : Y) =>
            Fintype.card Y ^ (Fintype.card A - 1) - if f y = y then 1 else 0
        _ = (Fintype.card Y ^ Fintype.card A -
            Fintype.card {y : Y // f y = y}) ^ Fintype.card A := by
          rw [sum_row_weights f]
          exact Finset.prod_const _

end D5.S0.Diagonal.EscapeCount
