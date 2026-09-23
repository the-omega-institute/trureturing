/- GID: D5/S3/ConceptDynamics/Coding/CountedExchangeChain
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/CountedExchangeChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
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
  intertwines := elementary_shift U V
  future := by
    intro x y i h
    apply elementary_window U V
    · simpa using h 0 (by omega)
    · simpa using h 1 (by omega)
  past := by
    intro x y i h
    apply elementary_inverse_window U V
    · simpa using h 1 (by omega)
    · simpa using h 0 (by omega)

/-- Induction constructs the full homeomorphism for every finite chain and every intermediate size. -/
theorem chain_has_window_conjugacy {L : ℕ} (c : ExchangeChain ℕ A B L) :
    Nonempty (WindowConjugacy A B L) := by
  induction c with
  | nil A => exact ⟨identity A⟩
  | cons U V tail ih =>
      obtain ⟨g⟩ := ih
      simpa [Nat.add_comm] using
        (⟨(elementary U V).trans g⟩ : Nonempty (WindowConjugacy (U * V) _ (1 + _)))

/-- A concrete choice from the recursively built nonempty code type. -/
noncomputable def chainCode {L : ℕ} (c : ExchangeChain ℕ A B L) :
    WindowConjugacy A B L := Classical.choice (chain_has_window_conjugacy c)

theorem chain_code_intertwines {L : ℕ} (c : ExchangeChain ℕ A B L) (x : Path A) :
    (chainCode c).homeomorph (shift A x) = shift B ((chainCode c).homeomorph x) :=
  (chainCode c).intertwines x

/-- Every finite output interval has an explicitly enlarged input interval. -/
theorem chain_full_window {L : ℕ} (c : ExchangeChain ℕ A B L)
    (x y : Path A) (a b : ℤ)
    (h : ∀ i : ℤ, a ≤ i → i ≤ b + (L : ℤ) → x.val i = y.val i) :
    ∀ i : ℤ, a ≤ i → i ≤ b →
      ((chainCode c).homeomorph x).val i = ((chainCode c).homeomorph y).val i := by
  intro i hai hib
  apply (chainCode c).future
  intro j hj
  apply h
  · omega
  · omega

/-- The inverse has the corresponding past interval, for the same constructed code. -/
theorem chain_full_inverse_window {L : ℕ} (c : ExchangeChain ℕ A B L)
    (x y : Path B) (a b : ℤ)
    (h : ∀ i : ℤ, a - (L : ℤ) ≤ i → i ≤ b → x.val i = y.val i) :
    ∀ i : ℤ, a ≤ i → i ≤ b →
      ((chainCode c).homeomorph.symm x).val i = ((chainCode c).homeomorph.symm y).val i := by
  intro i hai hib
  apply (chainCode c).past
  intro j hj
  apply h
  · omega
  · omega

#print axioms WindowConjugacy.trans
#print axioms chain_has_window_conjugacy
#print axioms chain_code_intertwines
#print axioms chain_full_window
#print axioms chain_full_inverse_window

end D5.S3.ConceptDynamics.Coding.CountedExchangeChain
