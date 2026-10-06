/- GID: D5/S3/Geometry/FiniteGeometry/AffinePlaneLines
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGeometry/AffinePlaneLines
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-field affine lines through a point are indexed by slopes and one vertical direction. -/

import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Sum.Basic
import Mathlib.Tactic

namespace D5.S3.Geometry.FiniteGeometry.AffinePlaneLines

open scoped BigOperators

inductive AffineLine (F : Type*) where
  | graph (m b : F)
  | vertical (c : F)
  deriving DecidableEq

instance {F : Type*} [Fintype F] : Fintype (AffineLine F) := by
  classical
  exact Fintype.ofEquiv ((F × F) ⊕ F) {
    toFun := fun data => match data with
      | Sum.inl (m, b) => .graph m b
      | Sum.inr c => .vertical c
    invFun := fun line => match line with
      | .graph m b => Sum.inl (m, b)
      | .vertical c => Sum.inr c
    left_inv := by
      intro data
      cases data with
      | inl pair => cases pair <;> rfl
      | inr c => rfl
    right_inv := by
      intro line
      cases line <;> rfl }

def AffineLine.Mem {F : Type*} [Field F] (p : F × F) : AffineLine F → Prop
  | .graph m b => p.2 = m * p.1 + b
  | .vertical c => p.1 = c

instance {F : Type*} [Field F] : Membership (F × F) (AffineLine F) where
  mem line p := AffineLine.Mem p line

noncomputable instance linesThroughFintype {F : Type*} [Field F] [Fintype F]
    (p : F × F) : Fintype {ℓ : AffineLine F // p ∈ ℓ} :=
  Fintype.ofFinite _

def linesThroughEquiv {F : Type*} [Field F] [Fintype F] (p : F × F) :
    Option F ≃ {ℓ : AffineLine F // p ∈ ℓ} :=
  { toFun := fun slope => match slope with
      | some m => ⟨.graph m (p.2 - m * p.1), by
          change p.2 = m * p.1 + (p.2 - m * p.1)
          ring⟩
      | none => ⟨.vertical p.1, by
          change p.1 = p.1
          rfl⟩
    invFun := fun line => match line.1 with
      | .graph m _ => some m
      | .vertical _ => none
    left_inv := by
      intro slope
      cases slope <;> rfl
    right_inv := by
      rintro ⟨line, hline⟩
      cases line with
      | graph m b =>
          change p.2 = m * p.1 + b at hline
          have hb : p.2 - m * p.1 = b := by
            calc
              p.2 - m * p.1 = (m * p.1 + b) - m * p.1 := by rw [← hline]
              _ = b := by ring
          apply Subtype.ext
          simp [hb]
      | vertical c =>
          change p.1 = c at hline
          have hc : c = p.1 := hline.symm
          apply Subtype.ext
          simp [hc] }

theorem card_affineLines_through {F : Type*} [Field F] [Fintype F]
    (p : F × F) :
    Fintype.card {ℓ : AffineLine F // p ∈ ℓ} = Fintype.card F + 1 := by
  classical
  simpa using (Fintype.card_congr (linesThroughEquiv p)).symm

theorem exists_unique_line_through_distinct_points {F : Type*} [Field F]
    (p q : F × F) (hpq : p ≠ q) :
    ∃! ℓ : AffineLine F, p ∈ ℓ ∧ q ∈ ℓ := by
  by_cases hx : p.1 = q.1
  · have hy : p.2 ≠ q.2 := by
      intro hy
      apply hpq
      exact Prod.ext hx hy
    refine ⟨.vertical p.1, ?_, ?_⟩
    · constructor
      · rfl
      · change q.1 = p.1
        exact hx.symm
    · intro line hline
      cases line with
      | graph m b =>
          rcases hline with ⟨hpl, hql⟩
          exfalso
          change p.2 = m * p.1 + b at hpl
          change q.2 = m * q.1 + b at hql
          rw [← hx] at hql
          apply hy
          exact hpl.trans hql.symm
      | vertical c =>
          rcases hline with ⟨hpl, _⟩
          change p.1 = c at hpl
          apply congrArg AffineLine.vertical hpl.symm
  · have hdx : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    let m : F := (q.2 - p.2) / (q.1 - p.1)
    let b : F := p.2 - m * p.1
    refine ⟨.graph m b, ?_, ?_⟩
    · constructor
      · change p.2 = m * p.1 + b
        simp [b]
      · change q.2 = m * q.1 + b
        dsimp [m, b]
        field_simp [hdx]
        ring
    · intro line hline
      cases line with
      | graph m' b' =>
          rcases hline with ⟨hpl, hql⟩
          change p.2 = m' * p.1 + b' at hpl
          change q.2 = m' * q.1 + b' at hql
          have hm : m' = m := by
            apply (eq_div_iff hdx).2
            calc
              m' * (q.1 - p.1) = (m' * q.1 + b') - (m' * p.1 + b') := by ring
              _ = q.2 - p.2 := by rw [← hql, ← hpl]
          have hb : b' = b := by
            calc
              b' = (m' * p.1 + b') - m' * p.1 := by ring
              _ = p.2 - m' * p.1 := by rw [hpl]
              _ = p.2 - m * p.1 := by rw [hm]
              _ = b := by rfl
          simp [hm, hb]
      | vertical c =>
          rcases hline with ⟨hpl, hql⟩
          exfalso
          change p.1 = c at hpl
          change q.1 = c at hql
          exact (hx (hpl.trans hql.symm)).elim

end D5.S3.Geometry.FiniteGeometry.AffinePlaneLines
