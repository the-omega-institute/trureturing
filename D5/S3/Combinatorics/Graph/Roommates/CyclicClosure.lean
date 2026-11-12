/- GID: D5/S3/Combinatorics/Graph/Roommates/CyclicClosure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Roommates/CyclicClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Card]
   utility: none
   digest: Every certified word closes into a stable labelled cyclic profile after six sites. -/

import D5.S3.Combinatorics.Graph.Roommates.CyclicBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace D5.S3.Combinatorics.Graph.Roommates.CyclicClosure
open OpenCertificates CyclicBridge PaddedCompletion

variable {m : ℕ} {w : Word m} {d : Fin m → ℤ}

private def exterior (d : Fin m → ℤ) (i : Fin m) : Prop :=
  d i ≠ 0 ∧ ((i.val : ℤ) + d i < 0 ∨ (m : ℤ) ≤ i.val + d i)

private def inside (d : Fin m → ℤ) (i : Fin m) (h : ¬exterior d i) : Fin m :=
  ⟨((i.val : ℤ) + d i).toNat, by
    have hi := i.isLt
    simp only [exterior, not_and_or, not_or] at h
    rcases h with h | ⟨h,h'⟩ <;> omega⟩

private theorem inside_coord (i : Fin m) (h : ¬exterior d i) :
    ((inside d i h).val : ℤ) = i.val + d i := by
  have hi := i.isLt
  simp only [exterior, not_and_or, not_or] at h
  rcases h with h | ⟨h,h'⟩ <;> simp only [inside] <;> omega

private def joinPartner (hw : Certificate w d) : Fin m ⊕ Fin 6 → Fin m ⊕ Fin 6
  | .inl i => if h : exterior d i then .inr (closingRequest d hw.bounded ⟨i,h⟩)
      else .inl (inside d i h)
  | .inr b => match BufferLayout.partner (closingRequest d hw.bounded) (.inr b) with
      | .inl a => .inl a.val
      | .inr c => .inr c

private theorem joinPartner_involutive (hw : Certificate w d) :
    Function.Involutive (joinPartner hw) := by
  let r := closingRequest d hw.bounded
  have hc := closing_request_completion hw
  intro x
  cases x with
  | inl i =>
    by_cases h : exterior d i
    · have he : ∃ a : ClosingRequester d, r a = r ⟨i,h⟩ := ⟨⟨i,h⟩,rfl⟩
      have hh : Classical.choose he = (⟨i,h⟩ : ClosingRequester d) := hc.1 (Classical.choose_spec he)
      simp only [joinPartner, dif_pos h, BufferLayout.partner, dif_pos he, hh]
    · let j := inside d i h
      have hj := inside_coord i h
      have hdj : d j = -d i := by
        by_cases hz : d i = 0
        · have he : j = i := Fin.ext (by dsimp [j] at hj; omega)
          simpa [he, hz]
        · exact hw.reciprocal i j hz hj.symm
      have hn : ¬exterior d j := by
        have hi := i.isLt
        dsimp [exterior]
        omega
      have he : inside d j hn = i := by
        apply Fin.ext
        have ht := inside_coord j hn
        omega
      simp only [joinPartner, dif_neg h, dif_neg hn, he]
  | inr b =>
    by_cases h : ∃ a : ClosingRequester d, r a = b
    · let a := Classical.choose h
      have ha : r a = b := Classical.choose_spec h
      have he := a.property
      simp only [joinPartner, BufferLayout.partner, dif_pos h, dif_pos he]
      exact congrArg Sum.inr ha
    · have hfree : ¬∃ a : ClosingRequester d,
          r a = BufferLayout.mate (BufferLayout.flags r) b := by
        intro ⟨a,ha⟩
        have he := hc.2.1 (.inr b)
        simp only [BufferLayout.partner, dif_neg h, dif_pos (show ∃ a', r a' =
          BufferLayout.mate (BufferLayout.flags r) b from ⟨a,ha⟩)] at he
        cases he
      have he := hc.2.1 (.inr b)
      simp only [BufferLayout.partner, dif_neg h, dif_neg hfree, Sum.inr.injEq] at he
      simpa only [joinPartner, BufferLayout.partner, dif_neg h, dif_neg hfree] using congrArg Sum.inr he

/-- The full cycle partner map, retaining old interior pairs and fulfilling all requests. -/
def matching (hw : Certificate w d) : SourceModel.Matching (Fin (m + 1 + 5)) := by
  let e : (Fin m ⊕ Fin 6) ≃ Fin (m + 1 + 5) := finSumFinEquiv
  let f := joinPartner hw
  have hf := joinPartner_involutive hw
  let g := fun i => e (f (e.symm i))
  have hg : Function.Involutive g := by
    intro i
    simp only [g, Equiv.symm_apply_apply, hf, Equiv.apply_symm_apply]
  exact ⟨Equiv.ofInvolutive g hg, hg⟩

#print axioms matching
end D5.S3.Combinatorics.Graph.Roommates.CyclicClosure
