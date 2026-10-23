/- GID: D5/S3/Combinatorics/EdgeLabeling/CubicARGraphEvents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/CubicARGraphEvents
   mirror-E: none(waiver:counting-component-of-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bounds free-triple bad events in the marked cubic-labeling sample space. -/

import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphArithmetic
import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting
import D5.S3.Combinatorics.EdgeLabeling.CubicARGraphMarkedEvents

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.EdgeLabeling.CubicARGraphEvents

open Finset
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphArithmetic
open D5.S3.Combinatorics.EdgeLabeling.CubicARGraphMarkedEvents

private def sortedFreeLabels (m : ℕ) (hm : 6 ≤ m) (r : additivePairs m) : Fin 3 → Fin m :=
  fun i => ⟨![r.val.1 - 1, r.val.2 - 1, r.val.1 + r.val.2 - 1] i, by
    have hr := (mem_additivePairs hm).mp r.property
    change 3 ≤ r.val.1 ∧ r.val.1 < r.val.2 ∧ r.val.1 + r.val.2 ≤ m at hr
    fin_cases i <;> simp <;> omega⟩

private lemma sortedFreeLabels_injective (m : ℕ) (hm : 6 ≤ m) (r : additivePairs m) :
    Function.Injective (sortedFreeLabels m hm r) := by
  have hr := (mem_additivePairs hm).mp r.property
  change 3 ≤ r.val.1 ∧ r.val.1 < r.val.2 ∧ r.val.1 + r.val.2 ≤ m at hr
  intro i j hij
  have h := congrArg Fin.val hij
  fin_cases i <;> fin_cases j <;> simp [sortedFreeLabels] at h ⊢ <;> omega

private lemma sortedFreeLabels_free (m : ℕ) (hm : 6 ≤ m) (r : additivePairs m)
    (i : Fin 3) : 2 ≤ (sortedFreeLabels m hm r i).val := by
  have hr := (mem_additivePairs hm).mp r.property
  change 3 ≤ r.val.1 ∧ r.val.1 < r.val.2 ∧ r.val.1 + r.val.2 ≤ m at hr
  fin_cases i <;> simp [sortedFreeLabels] <;> omega

private noncomputable def triplePerm (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Equiv.Perm (Fin 3) := by
  have hinj : Function.Injective (![i, j, k] : Fin 3 → Fin 3) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢ <;> aesop
  exact Equiv.ofBijective _ ⟨hinj, Finite.surjective_of_injective hinj⟩

private lemma cover_sorted (m : ℕ) (hm : 6 ≤ m) (x : Fin 3 → Fin m)
    (hx : ∀ i, 2 ≤ (x i).val) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hlt : (x i).val < (x j).val)
    (hadd : (x i).val + 1 + ((x j).val + 1) = (x k).val + 1) :
    ∃ (r : additivePairs m) (σ : Equiv.Perm (Fin 3)),
      ∀ a, x a = sortedFreeLabels m hm r (σ a) := by
  let r : additivePairs m := ⟨((x i).val + 1, (x j).val + 1),
    (mem_additivePairs hm).mpr ⟨by have := hx i; omega, by omega,
      by have := (x k).isLt; omega⟩⟩
  let τ := triplePerm i j k hij hik hjk
  have heq : ∀ a, x (τ a) = sortedFreeLabels m hm r a := by
    intro a
    apply Fin.ext
    have hτ : ∀ a, τ a = (![i, j, k] : Fin 3 → Fin 3) a := fun _ => rfl
    rw [hτ]
    change (x (![i, j, k] a)).val =
      ![(x i).val + 1 - 1, (x j).val + 1 - 1,
        (x i).val + 1 + ((x j).val + 1) - 1] a
    fin_cases a <;> simp <;> omega
  refine ⟨r, τ.symm, ?_⟩
  intro a
  simpa using heq (τ.symm a)

private lemma bad_free_labels_covered (m : ℕ) (hm : 6 ≤ m) (x : Fin 3 → Fin m)
    (hx : ∀ i, 2 ≤ (x i).val) (hinj : Function.Injective x)
    (hbad : (x 0).val + 1 + ((x 1).val + 1) = (x 2).val + 1 ∨
      (x 0).val + 1 + ((x 2).val + 1) = (x 1).val + 1 ∨
      (x 1).val + 1 + ((x 2).val + 1) = (x 0).val + 1) :
    ∃ (r : additivePairs m) (σ : Equiv.Perm (Fin 3)),
      ∀ a, x a = sortedFreeLabels m hm r (σ a) := by
  have hne : ∀ i j : Fin 3, i ≠ j → (x i).val ≠ (x j).val := by
    intro i j hij he
    exact hij (hinj (Fin.ext he))
  rcases hbad with hbad | hbad | hbad
  · rcases lt_or_gt_of_ne (hne 0 1 (by decide)) with hlt | hlt
    · exact cover_sorted m hm x hx 0 1 2 (by decide) (by decide) (by decide) hlt hbad
    · apply cover_sorted m hm x hx 1 0 2 (by decide) (by decide) (by decide) hlt
      omega
  · rcases lt_or_gt_of_ne (hne 0 2 (by decide)) with hlt | hlt
    · exact cover_sorted m hm x hx 0 2 1 (by decide) (by decide) (by decide) hlt hbad
    · apply cover_sorted m hm x hx 2 0 1 (by decide) (by decide) (by decide) hlt
      omega
  · rcases lt_or_gt_of_ne (hne 1 2 (by decide)) with hlt | hlt
    · exact cover_sorted m hm x hx 1 2 0 (by decide) (by decide) (by decide) hlt hbad
    · apply cover_sorted m hm x hx 2 1 0 (by decide) (by decide) (by decide) hlt
      omega

open Classical in
private lemma card_marked_free_constraints {E : Type} [Fintype E] [DecidableEq E]
    (m : ℕ) (hm : 6 ≤ m) (hm2 : 2 ≤ m) (p q : E) (hpq : p ≠ q)
    (t : Fin 3 → E) (ht : Function.Injective t)
    (htp : ∀ i, t i ≠ p) (htq : ∀ i, t i ≠ q)
    (r : additivePairs m) (σ : Equiv.Perm (Fin 3)) (hcard : Fintype.card E = m) :
    (univ.filter (fun e : MarkedLabeling E m hm2 p q =>
      ∀ i, e.val (t i) = sortedFreeLabels m hm r (σ i))).card = (m - 5).factorial := by
  classical
  let d : Fin 5 → E := ![p, q, t 0, t 1, t 2]
  let l : Fin 5 → Fin m := ![⟨0, by omega⟩, ⟨1, hm2⟩,
    sortedFreeLabels m hm r (σ 0), sortedFreeLabels m hm r (σ 1),
    sortedFreeLabels m hm r (σ 2)]
  have ht01 : t 0 ≠ t 1 := ht.ne (by decide)
  have ht02 : t 0 ≠ t 2 := ht.ne (by decide)
  have ht12 : t 1 ≠ t 2 := ht.ne (by decide)
  have ht0p := htp 0
  have ht1p := htp 1
  have ht2p := htp 2
  have ht0q := htq 0
  have ht1q := htq 1
  have ht2q := htq 2
  have hd : Function.Injective d := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [d, hpq, Ne.symm hpq, ht01, Ne.symm ht01, ht02, Ne.symm ht02,
        ht12, Ne.symm ht12, ht0p, Ne.symm ht0p, ht1p, Ne.symm ht1p,
        ht2p, Ne.symm ht2p, ht0q, Ne.symm ht0q, ht1q, Ne.symm ht1q,
        ht2q, Ne.symm ht2q] at hij ⊢
  have hl : Function.Injective l := by
    have hx := (sortedFreeLabels_injective m hm r).comp σ.injective
    have hn : ∀ i j : Fin 3, i ≠ j →
        (sortedFreeLabels m hm r (σ i)).val ≠ (sortedFreeLabels m hm r (σ j)).val := by
      intro i j hij he
      exact hij (hx (Fin.ext he))
    have h0 := sortedFreeLabels_free m hm r (σ 0)
    have h1 := sortedFreeLabels_free m hm r (σ 1)
    have h2 := sortedFreeLabels_free m hm r (σ 2)
    have hn01 := hn 0 1 (by decide)
    have hn02 := hn 0 2 (by decide)
    have hn12 := hn 1 2 (by decide)
    intro i j hij
    have he := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp [l] at he ⊢ <;> omega
  let eventEquiv : {e : MarkedLabeling E m hm2 p q //
      ∀ i, e.val (t i) = sortedFreeLabels m hm r (σ i)} ≃
      {e : E ≃ Fin m // ∀ i, e (d i) = l i} :=
    { toFun := fun e => ⟨e.val.val, by
        intro i
        fin_cases i
        · simpa [d, l] using e.val.property.1
        · simpa [d, l] using e.val.property.2
        · simpa [d, l] using e.property 0
        · simpa [d, l] using e.property 1
        · simpa [d, l] using e.property 2⟩
      invFun := fun e => ⟨⟨e.val, ⟨by simpa [d, l] using e.property 0,
        by simpa [d, l] using e.property 1⟩⟩, by
        intro i
        fin_cases i
        · simpa [d, l] using e.property 2
        · simpa [d, l] using e.property 3
        · simpa [d, l] using e.property 4⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr eventEquiv]
  rw [← Nat.card_eq_fintype_card]
  have h := D5.S3.Combinatorics.EdgeLabeling.CubicARGraphCounting.nat_card_equiv_constraints
    d l hd hl (by simpa using hcard)
  simpa [hcard] using h

open Classical in
/-- Three free distinct edges form a bad event in at most six times the additive-pair
count times the number of extensions of five fixed labels. -/
theorem card_bad_free_triple {E : Type} [Fintype E] [DecidableEq E]
    (m : ℕ) (hm : 6 ≤ m) (hm2 : 2 ≤ m) (p q : E) (hpq : p ≠ q)
    (t : Fin 3 → E) (ht : Function.Injective t)
    (htp : ∀ i, t i ≠ p) (htq : ∀ i, t i ≠ q) (hcard : Fintype.card E = m) :
    Fintype.card {e : MarkedLabeling E m hm2 p q //
      AdditiveTriple (markLabel e) (t 0) (t 1) (t 2)} ≤
        6 * (additivePairs m).card * (m - 5).factorial := by
  classical
  let bad := univ.filter (fun e : MarkedLabeling E m hm2 p q =>
    AdditiveTriple (markLabel e) (t 0) (t 1) (t 2))
  let events : (additivePairs m × Equiv.Perm (Fin 3)) →
      Finset (MarkedLabeling E m hm2 p q) := fun j =>
    univ.filter (fun e => ∀ i, e.val (t i) = sortedFreeLabels m hm j.1 (j.2 i))
  have hsub : bad ⊆ univ.biUnion events := by
    intro e he
    have hb := (mem_filter.mp he).2
    let x : Fin 3 → Fin m := fun i => e.val (t i)
    have hx : ∀ i, 2 ≤ (x i).val := by
      intro i
      have h0 : (x i).val ≠ 0 := by
        intro hzero
        apply htp i
        apply e.val.injective
        apply Fin.ext
        simpa [x, e.property.1] using hzero
      have h1 : (x i).val ≠ 1 := by
        intro hone
        apply htq i
        apply e.val.injective
        apply Fin.ext
        simpa [x, e.property.2] using hone
      omega
    obtain ⟨r, σ, heq⟩ := bad_free_labels_covered m hm x hx
      (e.val.injective.comp ht) (by simpa [x, AdditiveTriple, markLabel] using hb)
    exact mem_biUnion.mpr ⟨(r, σ), mem_univ _, mem_filter.mpr ⟨mem_univ _, heq⟩⟩
  rw [Fintype.card_subtype]
  change bad.card ≤ _
  calc
    bad.card ≤ (univ.biUnion events).card := card_le_card hsub
    _ ≤ ∑ j, (events j).card := card_biUnion_le
    _ = ∑ _j : additivePairs m × Equiv.Perm (Fin 3), (m - 5).factorial := by
      apply sum_congr rfl
      intro j hj
      exact card_marked_free_constraints m hm hm2 p q hpq t ht htp htq j.1 j.2 hcard
    _ = 6 * (additivePairs m).card * (m - 5).factorial := by
      simp [Fintype.card_prod, Fintype.card_perm, show Nat.factorial 3 = 6 by decide,
        mul_comm, mul_left_comm, mul_assoc]

end D5.S3.Combinatorics.EdgeLabeling.CubicARGraphEvents
