import D5.S3.Combinatorics.CircularWords.CyclicInsertionGap
import Mathlib.SetTheory.Cardinal.Finite

/-!
The finite fiber of actual oriented nodup cycles.  `gapCircle B x j` puts `x`
immediately before `B[j]`; in particular `j = 0` is the cyclic cut gap.
The carrier consists of cycles themselves, with no chosen root in its elements.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.SingleDeletionFiberCount

open CircularDeletionTransport CyclicInsertionGap

universe u
variable {α : Type u} [DecidableEq α]

/-- All cyclic slots give exactly the legal original cycles over a fixed residual.
The existing unique-gap theorem supplies completeness; the anchor only proves
injectivity of the displayed parametrization, without adding roots to the fiber. -/
noncomputable def insertionEquiv {A : Finset α} {x : α} (hx : x ∈ A)
    {B : List α} (hB : B.Nodup) (hB0 : B ≠ []) (sB : B.toFinset = A.erase x) :
    Fin B.length ≃
      {C : Cycle α // C.Nodup ∧ C.toFinset = A ∧ delete x C = (B : Cycle α)} := by
  have hxB : x ∉ B := by
    intro h
    have : x ∈ A.erase x := sB ▸ List.mem_toFinset.mpr h
    exact (Finset.mem_erase.mp this).1 rfl
  have hinj : Function.Injective (gapCircle B x) := by
    intro j k h
    have hn : (x :: B.rotate j.val).Nodup :=
      List.nodup_cons.mpr ⟨by simpa using hxB, List.nodup_rotate.mpr hB⟩
    have he : B.rotate j.val = B.rotate k.val := anchored_coe_injective hn h
    apply Fin.ext
    simpa only [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt k.isLt]
      using hB.rotate_congr hB0 j.val k.val he
  have hgap (j : Fin B.length) :
      (gapCircle B x j).Nodup ∧ x ∈ gapCircle B x j ∧
        delete x (gapCircle B x j) = (B : Cycle α) :=
    (gapCircle_fiber hB hB0 hxB _).mpr
      ⟨j, rfl, fun k hk => hinj hk.symm⟩
  have sgap (j : Fin B.length) : (gapCircle B x j).toFinset = A := by
    have hr : (B.rotate j.val).toFinset = B.toFinset := by
      ext y
      simp only [List.mem_toFinset, List.mem_rotate]
    change (x :: B.rotate j.val).toFinset = A
    rw [List.toFinset_cons, hr, sB, Finset.insert_erase hx]
  let f : Fin B.length →
      {C : Cycle α // C.Nodup ∧ C.toFinset = A ∧ delete x C = (B : Cycle α)} :=
    fun j => ⟨gapCircle B x j, (hgap j).1, sgap j, (hgap j).2.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro j k h
    exact hinj (congrArg Subtype.val h)
  · rintro ⟨C, hC, sC, hd⟩
    have hCx : x ∈ C := by
      induction C using Quotient.inductionOn with
      | _ L =>
        apply Cycle.mem_coe_iff.mpr
        apply List.mem_toFinset.mp
        exact sC.symm ▸ hx
    obtain ⟨j, hj, _⟩ := (gapCircle_fiber hB hB0 hxB C).mp ⟨hC, hCx, hd⟩
    exact ⟨j, Subtype.ext hj.symm⟩

/-- Every legal one-deletion residual has exactly `A.card - 1` legal original
oriented cycles.  No finiteness assumption on the ambient label type is needed. -/
theorem deletion_fiber_card {A : Finset α} (hA : 3 ≤ A.card)
    {x : α} (hx : x ∈ A) {B : Cycle α} (hB : B.Nodup)
    (sB : B.toFinset = A.erase x) :
    Nat.card {C : Cycle α // C.Nodup ∧ C.toFinset = A ∧ delete x C = B} =
      A.card - 1 := by
  induction B using Quotient.inductionOn with
  | _ L =>
    have hn : L.Nodup := Cycle.nodup_coe_iff.mp hB
    have hs : L.toFinset = A.erase x := sB
    have hlen : L.length = A.card - 1 := by
      rw [← List.toFinset_card_of_nodup hn, hs, Finset.card_erase_of_mem hx]
    have hL0 : L ≠ [] := by
      intro he
      simp only [he, List.length_nil] at hlen
      omega
    exact (Nat.card_eq_of_equiv_fin (insertionEquiv hx hn hL0 hs).symm).trans hlen

end D5.S3.Combinatorics.CircularWords.SingleDeletionFiberCount
