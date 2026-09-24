/- GID: D5/S3/ConceptDynamics/Coding/CountedExchangeChain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedExchangeChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite rectangular exchange chain constructs a one-step conjugacy with additive recovery windows. -/

import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.CountedExchangeChain

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

/-- One code, both directions, and an explicit two-sided observation budget. -/
structure WindowConjugacy {n m : ℕ} (A : CountMat n n) (B : CountMat m m) (r : ℕ) where
  homeomorph : Path A ≃ₜ Path B
  intertwines : ∀ x, homeomorph (shift A x) = shift B (homeomorph x)
  future : ∀ (x y : Path A) (i : ℤ),
    (∀ j : ℕ, j ≤ r → x.val (i + (j : ℤ)) = y.val (i + (j : ℤ))) →
    (homeomorph x).val i = (homeomorph y).val i
  past : ∀ (x y : Path B) (i : ℤ),
    (∀ j : ℕ, j ≤ r → x.val (i - (j : ℤ)) = y.val (i - (j : ℤ))) →
    (homeomorph.symm x).val i = (homeomorph.symm y).val i

variable {n m k : ℕ} {A : CountMat n n} {B : CountMat m m} {C : CountMat k k}

/-- Composing actual codes adds, rather than multiplies, their required windows. -/
def WindowConjugacy.trans {r s : ℕ} (f : WindowConjugacy A B r)
    (g : WindowConjugacy B C s) : WindowConjugacy A C (r + s) where
  homeomorph := f.homeomorph.trans g.homeomorph
  intertwines := by
    intro x
    change g.homeomorph (f.homeomorph (shift A x)) =
      shift C (g.homeomorph (f.homeomorph x))
    rw [f.intertwines, g.intertwines]
  future := by
    intro x y i h
    apply g.future
    intro j hj
    apply f.future
    intro l hl
    have hh := h (j + l) (by omega)
    simpa [Nat.cast_add, add_assoc] using hh
  past := by
    intro x y i h
    apply f.past
    intro j hj
    apply g.past
    intro l hl
    have hh := h (j + l) (by omega)
    simpa [Nat.cast_add, sub_sub] using hh

def identity (A : CountMat n n) : WindowConjugacy A A 0 where
  homeomorph := Homeomorph.refl _
  intertwines := fun _ => rfl
  future := by
    intro x y i h
    simpa using h 0 (by omega)
  past := by
    intro x y i h
    simpa using h 0 (by omega)

/-- The elementary witness is the counted-edge construction itself. -/
noncomputable def elementary (U : CountMat n m) (V : CountMat m n) :
    WindowConjugacy (U * V) (V * U) 1 where
  homeomorph := elementaryHomeomorph U V
  intertwines := by
    intro x
    apply Subtype.ext
    rfl
  future := by
    intro x y i h
    have h0 : x.val i = y.val i := by simpa using h 0 (by omega)
    have h1 : x.val (i + 1) = y.val (i + 1) := by simpa using h 1 (by omega)
    have join_congr (a a' : Edge V) (b b' : Edge U)
        (hab : a.target = b.source) (hab' : a'.target = b'.source)
        (ha : a = a') (hb : b = b') : join V U a b hab = join V U a' b' hab' := by
      subst a'
      subst b'
      rfl
    exact join_congr _ _ _ _
      ((forward (boundary U V) (toAlternating U V x)).property i).1
      ((forward (boundary U V) (toAlternating U V y)).property i).1
      (congrArg (fun a => (split U V a).2) h0)
      (congrArg (fun a => (split U V a).1) h1)
  past := by
    intro x y i h
    have hm : x.val (i - 1) = y.val (i - 1) := by simpa using h 1 (by omega)
    have h0 : x.val i = y.val i := by simpa using h 0 (by omega)
    have join_congr (a a' : Edge U) (b b' : Edge V)
        (hab : a.target = b.source) (hab' : a'.target = b'.source)
        (ha : a = a') (hb : b = b') : join U V a b hab = join U V a' b' hab' := by
      subst a'
      subst b'
      rfl
    exact join_congr _ _ _ _
      ((backward (boundary U V) (toAlternating V U x)).property i).1
      ((backward (boundary U V) (toAlternating V U y)).property i).1
      (congrArg (fun a => (split V U a).2) hm)
      (congrArg (fun a => (split V U a).1) h0)

/-- Induction constructs the full homeomorphism for every finite chain and every intermediate size. -/
theorem chain_has_window_conjugacy {L : ℕ} (c : ExchangeChain ℕ A B L) :
    Nonempty (WindowConjugacy A B L) := by
  induction c with
  | nil A => exact ⟨identity A⟩
  | cons U V tail ih =>
      obtain ⟨g⟩ := ih
      simpa [Nat.add_comm] using
        (⟨(elementary U V).trans g⟩ : Nonempty (WindowConjugacy (U * V) _ (1 + _)))

#print axioms WindowConjugacy.trans
#print axioms chain_has_window_conjugacy

end D5.S3.ConceptDynamics.Coding.CountedExchangeChain
