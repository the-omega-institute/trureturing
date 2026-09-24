/- GID: D5/S3/ConceptDynamics/Coding/CountedGroupWindowChain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedGroupWindowChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One constructed group-equivariant chain code carries forward, inverse, and coordinate recovery budgets. -/

import D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.CountedGroupWindowChain

open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
open D5.S3.ConceptDynamics.Coding.BipartiteOverlapConjugacy
open D5.S3.ConceptDynamics.Coding.EquivariantOverlapRecoding
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

universe u
variable {H : Type u} [Group H] [Fintype H]
  [TopologicalSpace H] [IsTopologicalGroup H]

section Elementary
variable {n m : ℕ} (U : GroupMat H n m) (V : GroupMat H m n)

/-- The base edge is determined independently of the input group coordinate. -/
theorem elementary_future (x y : Path (U * V) × H) (i : ℤ)
    (h0 : x.1.val i = y.1.val i) (h1 : x.1.val (i + 1) = y.1.val (i + 1)) :
    ((elementaryHomeomorph U V x).1).val i =
      ((elementaryHomeomorph U V y).1).val i := by
  have join_congr (a a' : Edge V) (b b' : Edge U)
      (h : a.target = b.source) (h' : a'.target = b'.source)
      (ha : a = a') (hb : b = b') : join V U a b h = join V U a' b' h' := by
    subst a'
    subst b'
    rfl
  exact join_congr _ _ _ _
    ((forward (boundary U V) (toAlternating U V x.1)).property i).1
    ((forward (boundary U V) (toAlternating U V y.1)).property i).1
    (congrArg (fun a => (split U V a).2) h0)
    (congrArg (fun a => (split U V a).1) h1)

/-- The inverse uses the preceding and the current output edge. -/
theorem elementary_past (x y : Path (V * U) × H) (i : ℤ)
    (hm : x.1.val (i - 1) = y.1.val (i - 1)) (h0 : x.1.val i = y.1.val i) :
    (((elementaryHomeomorph U V).symm x).1).val i =
      (((elementaryHomeomorph U V).symm y).1).val i := by
  have join_congr (a a' : Edge U) (b b' : Edge V)
      (h : a.target = b.source) (h' : a'.target = b'.source)
      (ha : a = a') (hb : b = b') : join U V a b h = join U V a' b' h' := by
    subst a'
    subst b'
    rfl
  exact join_congr _ _ _ _
    ((backward (boundary U V) (toAlternating V U x.1)).property i).1
    ((backward (boundary U V) (toAlternating V U y.1)).property i).1
    (congrArg (fun a => (split V U a).2) hm)
    (congrArg (fun a => (split V U a).1) h0)

end Elementary

/-- All four finite-observation statements concern this same homeomorphism. -/
structure WindowGroupConjugacy {a b : ℕ}
    (A : GroupMat H a a) (B : GroupMat H b b) (r : ℕ)
    extends GroupConjugacy A B where
  future : ∀ (x y : Path A × H) (i : ℤ),
    (∀ j : ℕ, j ≤ r → x.1.val (i + (j : ℤ)) = y.1.val (i + (j : ℤ))) →
    ((homeomorph x).1).val i = ((homeomorph y).1).val i
  past : ∀ (x y : Path B × H) (i : ℤ),
    (∀ j : ℕ, j ≤ r → x.1.val (i - (j : ℤ)) = y.1.val (i - (j : ℤ))) →
    ((homeomorph.symm x).1).val i = ((homeomorph.symm y).1).val i
  coordinate_future : ∀ (x y : Path A × H), x.2 = y.2 →
    (∀ j : ℕ, j ≤ r → x.1.val (j : ℤ) = y.1.val (j : ℤ)) →
    (homeomorph x).2 = (homeomorph y).2
  coordinate_past : ∀ (x y : Path B × H), x.2 = y.2 →
    (∀ j : ℕ, j ≤ r → x.1.val (-(j : ℤ)) = y.1.val (-(j : ℤ))) →
    (homeomorph.symm x).2 = (homeomorph.symm y).2

variable {a b c : ℕ} {A : GroupMat H a a} {B : GroupMat H b b}
  {C : GroupMat H c c}

/-- Composition adds both recovery windows and both anchored coordinate budgets. -/
def WindowGroupConjugacy.trans {r s : ℕ}
    (f : WindowGroupConjugacy A B r) (g : WindowGroupConjugacy B C s) :
    WindowGroupConjugacy A C (r + s) where
  toGroupConjugacy := f.toGroupConjugacy.trans g.toGroupConjugacy
  future := by
    intro x y i h
    apply g.future
    intro j hj
    apply f.future
    intro l hl
    have hi : (i + (j : ℤ)) + (l : ℤ) = i + ((j + l : ℕ) : ℤ) := by omega
    simpa only [hi] using h (j + l) (by omega)
  past := by
    intro x y i h
    apply f.past
    intro j hj
    apply g.past
    intro l hl
    have hi : (i - (j : ℤ)) - (l : ℤ) = i - ((j + l : ℕ) : ℤ) := by omega
    simpa only [hi] using h (j + l) (by omega)
  coordinate_future := by
    intro x y hc h
    apply g.coordinate_future
    · apply f.coordinate_future x y hc
      intro j hj
      exact h j (by omega)
    · intro j hj
      apply f.future
      intro l hl
      have hi : (j : ℤ) + (l : ℤ) = ((j + l : ℕ) : ℤ) := by omega
      simpa only [hi] using h (j + l) (by omega)
  coordinate_past := by
    intro x y hc h
    apply f.coordinate_past
    · apply g.coordinate_past x y hc
      intro j hj
      exact h j (by omega)
    · intro j hj
      apply g.past
      intro l hl
      have hi : -(j : ℤ) - (l : ℤ) = -((j + l : ℕ) : ℤ) := by omega
      simpa only [hi] using h (j + l) (by omega)

def identity (A : GroupMat H a a) : WindowGroupConjugacy A A 0 where
  toGroupConjugacy := ⟨Homeomorph.refl _, fun _ => rfl, fun _ _ => rfl⟩
  future := by
    intro x y i h
    simpa using h 0 (by omega)
  past := by
    intro x y i h
    simpa using h 0 (by omega)
  coordinate_future := fun _ _ h _ => h
  coordinate_past := fun _ _ h _ => h

/-- This constructor assumes matrices only; the path splitting is counted internally. -/
noncomputable def elementary {n m : ℕ}
    (U : GroupMat H n m) (V : GroupMat H m n) :
    WindowGroupConjugacy (U * V) (V * U) 1 where
  toGroupConjugacy :=
    ⟨elementaryHomeomorph U V, elementary_step U V, elementary_equivariant U V⟩
  future := by
    intro x y i h
    apply elementary_future U V
    · simpa using h 0 (by omega)
    · simpa using h 1 (by omega)
  past := by
    intro x y i h
    apply elementary_past U V
    · simpa using h 1 (by omega)
    · simpa using h 0 (by omega)
  coordinate_future := by
    intro x y hc h
    have h0 : x.1.val 0 = y.1.val 0 := by simpa using h 0 (by omega)
    change x.2 * (split U V (x.1.val 0)).1.label =
      y.2 * (split U V (y.1.val 0)).1.label
    rw [hc, h0]
  coordinate_past := by
    intro x y hc h
    have hm : x.1.val (-1) = y.1.val (-1) := by simpa using h 1 (by omega)
    change x.2 * ((split V U (x.1.val (-1))).2.label)⁻¹ =
      y.2 * ((split V U (y.1.val (-1))).2.label)⁻¹
    rw [hc, hm]

/-- A finite matrix chain supplies one code carrying all four proved finite windows. -/
theorem chain_has_window_group_conjugacy {L : ℕ}
    (ch : ExchangeChain (MonoidAlgebra ℕ H) A B L) :
    Nonempty (WindowGroupConjugacy A B L) := by
  induction ch with
  | nil A => exact ⟨identity A⟩
  | cons U V tail ih =>
      obtain ⟨g⟩ := ih
      simpa only [Nat.add_comm] using
        (⟨(elementary U V).trans g⟩ :
          Nonempty (WindowGroupConjugacy (U * V) _ (1 + _)))

#print axioms elementary_future
#print axioms elementary_past
#print axioms WindowGroupConjugacy.trans
#print axioms chain_has_window_group_conjugacy

end D5.S3.ConceptDynamics.Coding.CountedGroupWindowChain
