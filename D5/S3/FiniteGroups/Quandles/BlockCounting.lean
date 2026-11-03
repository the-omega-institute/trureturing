/- GID: D5/S3/FiniteGroups/Quandles/BlockCounting
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Quandles/BlockCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete counting of good involutions by independent finite central-label blocks. -/

import D5.S3.FiniteGroups.Quandles.CentralLabels
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

namespace D5.S3.FiniteGroups.Quandles.BlockCounting

open CentralLabels

variable {G B Z : Type*} [Group G] {C : B → Type*}

/-- A conjugacy partition and an enumeration of the actual center, whose
central twisted inversions preserve the indicated blocks. No counts are assumed. -/
structure Data (G B Z : Type*) [Group G] (C : B → Type*) where
  code : G → Sigma C
  repr : Sigma C → G
  code_repr : ∀ c, code (repr c) = c
  code_conj : ∀ g x, code (g * x * g⁻¹) = code x
  repr_conj : ∀ x, ∃ g, g * repr (code x) * g⁻¹ = x
  center : Z ≃ Subgroup.center G
  dest : ∀ b, C b → Z → C b
  code_twist : ∀ x z,
    code ((center z : G) * x⁻¹) = ⟨(code x).1, dest (code x).1 (code x).2 z⟩

/-- All local assignments, not assignments modulo an equivalence relation.
The label equality on a paired class is what counts a two-cycle's weight once. -/
def Local (d : ∀ b, C b → Z → C b) (b : B) :=
  {f : C b → Z // ∀ i, f (d b i (f i)) = f i}

private theorem label_repr (D : Data G B Z C) (z : Label G) (x : G) :
    z.val x = z.val (D.repr (D.code x)) := by
  obtain ⟨g, hg⟩ := D.repr_conj x
  rw [← hg, z.property.1]

/-- The complete global-to-local bijection. Completeness uses both directions
of the conjugacy partition and surjectivity of the enumeration of the center. -/
def labelBlockEquiv (D : Data G B Z C) : Label G ≃ (∀ b, Local D.dest b) where
  toFun z b := by
    let f : C b → Z := fun i => D.center.symm (z.val (D.repr ⟨b, i⟩))
    refine ⟨f, ?_⟩
    intro i
    apply D.center.injective
    simp only [f, Equiv.apply_symm_apply]
    have hz := z.property.2 (D.repr ⟨b, i⟩)
    have ht := label_repr D z ((z.val (D.repr ⟨b, i⟩) : G) * (D.repr ⟨b, i⟩)⁻¹)
    have hcode := D.code_twist (D.repr ⟨b, i⟩) (f i)
    simp only [D.code_repr, f, Equiv.apply_symm_apply] at hcode
    rw [hcode] at ht
    exact ht.symm.trans hz
  invFun f := by
    let z : G → Subgroup.center G := fun x => D.center ((f (D.code x).1).val (D.code x).2)
    refine ⟨z, ?_, ?_⟩
    · intro g x
      simp only [z, D.code_conj]
    · intro x
      change D.center ((f (D.code ((D.center ((f (D.code x).1).val (D.code x).2) : G)
        * x⁻¹))).1).val (D.code ((D.center ((f (D.code x).1).val (D.code x).2) : G)
        * x⁻¹)).2) = _
      simp only [D.code_twist]
      exact congrArg D.center ((f (D.code x).1).property (D.code x).2)
  left_inv z := by
    apply Subtype.ext
    funext x
    change D.center (D.center.symm (z.val (D.repr (D.code x)))) = z.val x
    rw [Equiv.apply_symm_apply]
    exact (label_repr D z x).symm
  right_inv f := by
    funext b
    apply Subtype.ext
    funext i
    change D.center.symm (D.center ((f (D.code (D.repr ⟨b,i⟩)).1).val
      (D.code (D.repr ⟨b,i⟩)).2)) = (f b).val i
    simp only [D.code_repr, Equiv.symm_apply_apply]

/-- Finite block factorization, including zero-count and empty-block cases. -/
theorem good_card [Fintype B] (D : Data G B Z C) :
    Nat.card (Good G) = ∏ b, Nat.card (Local D.dest b) := by
  rw [Nat.card_congr (goodLabelEquiv.trans (labelBlockEquiv D)), Nat.card_pi]

/-- The same factorization for the repository's original subquandle interface. -/
theorem whole_good_card [Fintype G] [DecidableEq G] [Fintype B] (D : Data G B Z C) :
    Nat.card (D5.S0.Certificates.Groups.TaGoodInvolutionBoundRefutation.Good
      (Finset.univ : Finset G) (by intro x hx y hy; exact Finset.mem_univ _)) =
      ∏ b, Nat.card (Local D.dest b) := by
  rw [← Nat.card_congr (wholeGoodEquiv (G := G))]
  exact good_card D

/-- The supplied partition really enumerates the native conjugacy-class quotient. -/
def classEquiv (D : Data G B Z C) : ConjClasses G ≃ Sigma C where
  toFun := Quotient.lift D.code (by
    intro x y h
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    exact (D.code_conj g x).symm)
  invFun := fun c => ConjClasses.mk (D.repr c)
  left_inv c := by
    induction c using Quotient.inductionOn with
    | _ x =>
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      exact isConj_iff.mpr (D.repr_conj x)
  right_inv c := D.code_repr c

end D5.S3.FiniteGroups.Quandles.BlockCounting
