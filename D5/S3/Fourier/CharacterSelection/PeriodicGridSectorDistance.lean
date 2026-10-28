/- GID: D5/S3/Fourier/CharacterSelection/PeriodicGridSectorDistance
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/PeriodicGridSectorDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact Hamming distance from every flat rectangular grid label to each holonomy sector. -/

import D5.S3.Fourier.CharacterSelection.PeriodicGridHolonomy
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Prod

/-! Hamming support bounds and exact changes of flat holonomy sector. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.PeriodicGridSectorDistance

open Finset PeriodicGridHolonomy

/-- Count the horizontal and vertical labeled coordinates separately. -/
def edgeDistance {M N : ℕ} (y z : EdgeLabel M N) : ℕ :=
  hammingDist (fun ij : Fin M × Fin N => y.horizontal ij.1 ij.2)
    (fun ij => z.horizontal ij.1 ij.2) +
  hammingDist (fun ij : Fin M × Fin N => y.vertical ij.1 ij.2)
    (fun ij => z.vertical ij.1 ij.2)

private theorem row_disagreement_embedding {I J A : Type*} [Fintype J]
    [AddCommMonoid A] (f g : I → J → A)
    (hs : ∀ i, (∑ j, f i j) ≠ ∑ j, g i j) :
    Nonempty (I ↪ {ij : I × J // f ij.1 ij.2 ≠ g ij.1 ij.2}) := by
  classical
  have hd : ∀ i, ∃ j, f i j ≠ g i j := by
    intro i
    by_contra h
    push Not at h
    exact hs i (Finset.sum_congr rfl (fun j _ => h j))
  choose c hc using hd
  exact ⟨{
    toFun := fun i => ⟨(i, c i), hc i⟩
    inj' := by
      intro i k hik
      exact congrArg (fun q => q.val.1) hik }⟩

private theorem row_disagreement_bound {I J A : Type*} [Fintype I] [Fintype J]
    [AddCommMonoid A] [DecidableEq A] (f g : I → J → A)
    (hs : ∀ i, (∑ j, f i j) ≠ ∑ j, g i j) :
    Fintype.card I ≤ hammingDist (fun ij : I × J => f ij.1 ij.2)
      (fun ij => g ij.1 ij.2) := by
  classical
  obtain ⟨e⟩ := row_disagreement_embedding f g hs
  simpa only [Fintype.card_subtype, hammingDist] using Fintype.card_le_of_embedding e

private theorem seam_support_distance {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq J] (q : J) (x : I → J → ZMod 2) (a b : ZMod 2) :
    hammingDist (fun ij : I × J => x ij.1 ij.2 + if ij.2 = q then a else 0)
      (fun ij => x ij.1 ij.2 + if ij.2 = q then b else 0) =
      if a = b then 0 else Fintype.card I := by
  classical
  by_cases hab : a = b
  · simp [hab]
  · rw [ite_eq_right hab, hammingDist]
    have heq :
        ({ij : I × J | x ij.1 ij.2 + (if ij.2 = q then a else 0) ≠
          x ij.1 ij.2 + (if ij.2 = q then b else 0)} : Finset (I × J)) =
        (univ : Finset I) ×ˢ {q} := by
      ext ⟨i, j⟩
      by_cases hj : j = q
      · subst j
        simp [hab, Prod.mk.injEq]
      · simp [hj, Ne.symm hj, hab, Prod.mk.injEq]
    rw [heq, card_product]
    simp

private theorem combined_distance {M N : ℕ} [NeZero M] [NeZero N]
    (x : Fin M → Fin N → ZMod 2) (a b h v : ZMod 2) :
    edgeDistance (combinedLabel x a b) (combinedLabel x h v) =
      (if a = h then 0 else M) + (if b = v then 0 else N) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by have hm := NeZero.pos M; omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have hn := NeZero.pos N; omega⟩
  have hh : hammingDist
      (fun ij : Fin (m + 1) × Fin (n + 1) => (combinedLabel x a b).horizontal ij.1 ij.2)
      (fun ij => (combinedLabel x h v).horizontal ij.1 ij.2) =
      if a = h then 0 else m + 1 := by
    simpa [combinedLabel, seam, Fin.ext_iff, Nat.add_right_cancel_iff] using
      seam_support_distance (Fin.last n) (gradient x).horizontal a h
  have hv : hammingDist
      (fun ij : Fin (m + 1) × Fin (n + 1) => (combinedLabel x a b).vertical ij.1 ij.2)
      (fun ij => (combinedLabel x h v).vertical ij.1 ij.2) =
      if b = v then 0 else n + 1 := by
    have ht := seam_support_distance (Fin.last m)
      (fun j i => (gradient x).vertical i j) b v
    simp only [hammingDist] at ht ⊢
    have he :
        Fintype.card {ij : Fin (n + 1) × Fin (m + 1) //
          (gradient x).vertical ij.2 ij.1 + (if ij.2 = Fin.last m then b else 0) ≠
          (gradient x).vertical ij.2 ij.1 + (if ij.2 = Fin.last m then v else 0)} =
        Fintype.card {ij : Fin (m + 1) × Fin (n + 1) //
          (combinedLabel x a b).vertical ij.1 ij.2 ≠
          (combinedLabel x h v).vertical ij.1 ij.2} := by
      apply Fintype.card_congr
      apply Equiv.subtypeEquiv (Equiv.prodComm _ _)
      intro ij
      simp [combinedLabel, seam, Fin.ext_iff, Nat.add_right_cancel_iff]
    simp only [Fintype.card_subtype] at he
    simpa only [Fintype.card_fin] using he.symm.trans ht
  exact congrArg₂ (· + ·) hh hv

/-- The minimum is attained for every target pair, and bounds every flat label in that sector. -/
theorem flat_sector_distance {M N : ℕ} [NeZero M] [NeZero N]
    (y : EdgeLabel M N) (hy : Flat y) (h v : ZMod 2) :
    let d := (if rowHolonomy y 0 = h then 0 else M) +
      (if columnHolonomy y 0 = v then 0 else N)
    (∃ z : EdgeLabel M N, Flat z ∧ rowHolonomy z 0 = h ∧
      columnHolonomy z 0 = v ∧ edgeDistance y z = d) ∧
    ∀ z : EdgeLabel M N, Flat z → rowHolonomy z 0 = h →
      columnHolonomy z 0 = v → d ≤ edgeDistance y z := by
  classical
  dsimp only
  constructor
  · let c := flatLabelEquiv (M := M) (N := N) ⟨y, hy⟩
    let z := (holonomySectorEquiv (M := M) (N := N) h v).symm c.1
    refine ⟨z.1, z.2.1, z.2.2.1, z.2.2.2, ?_⟩
    have heq : combinedLabel c.1.1 (rowHolonomy y 0) (columnHolonomy y 0) = y :=
      congrArg Subtype.val ((flatLabelEquiv (M := M) (N := N)).symm_apply_apply ⟨y, hy⟩)
    change edgeDistance y (combinedLabel c.1.1 h v) = _
    calc
      edgeDistance y (combinedLabel c.1.1 h v) =
          edgeDistance (combinedLabel c.1.1 (rowHolonomy y 0) (columnHolonomy y 0))
            (combinedLabel c.1.1 h v) := congrArg (fun w => edgeDistance w _) heq.symm
      _ = _ := combined_distance c.1.1 _ _ h v
  · intro z hz hh hv
    have hrow : (if rowHolonomy y 0 = h then 0 else M) ≤
        hammingDist (fun ij : Fin M × Fin N => y.horizontal ij.1 ij.2)
          (fun ij => z.horizontal ij.1 ij.2) := by
      split_ifs with hsame
      · exact Nat.zero_le _
      · simpa only [Fintype.card_fin] using row_disagreement_bound y.horizontal z.horizontal
          (fun i he => hsame (by
            change rowHolonomy y i = rowHolonomy z i at he
            rw [(flat_holonomy_constant y hy).1 i,
              (flat_holonomy_constant z hz).1 i, hh] at he
            exact he))
    have hcolumn : (if columnHolonomy y 0 = v then 0 else N) ≤
        hammingDist (fun ij : Fin M × Fin N => y.vertical ij.1 ij.2)
          (fun ij => z.vertical ij.1 ij.2) := by
      split_ifs with hsame
      · exact Nat.zero_le _
      · have hb := row_disagreement_bound (fun j i => y.vertical i j)
          (fun j i => z.vertical i j) (fun j he => hsame (by
            change columnHolonomy y j = columnHolonomy z j at he
            rw [(flat_holonomy_constant y hy).2 j,
              (flat_holonomy_constant z hz).2 j, hv] at he
            exact he))
        have he := Fintype.card_congr
          (Equiv.subtypeEquiv (Equiv.prodComm (Fin N) (Fin M))
            (fun ij => Iff.rfl) :
            {ij : Fin N × Fin M // y.vertical ij.2 ij.1 ≠ z.vertical ij.2 ij.1} ≃
            {ij : Fin M × Fin N // y.vertical ij.1 ij.2 ≠ z.vertical ij.1 ij.2})
        simp only [Fintype.card_subtype] at he
        simpa only [Fintype.card_fin, hammingDist, he] using hb
    exact Nat.add_le_add hrow hcolumn

#print axioms flat_sector_distance

end D5.S3.Fourier.CharacterSelection.PeriodicGridSectorDistance
