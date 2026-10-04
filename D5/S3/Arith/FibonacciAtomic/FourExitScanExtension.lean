/- GID: D5/S3/Arith/FibonacciAtomic/FourExitScanExtension
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordinary actual slot scans extend arbitrary retained-family recipes with exact gain. -/

import D5.S3.Arith.FibonacciAtomic.FourExitRawEndpointSpectrum
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FourExitScanExtension

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition ActualJointResponseCostCore
open FourExitRawEndpointSpectrum
open scoped Classical

/-- A recipe on any retained set of slots extends to all slots. Each added
slot's four exceptional rows incur exactly one nonleaf response. -/
theorem ordinary_scan_completion (k : Nat) (_hk : 1 ≤ k)
    (e : Fin (4 * k + 1) ≃ Unit ⊕ (Fin k × Fin 4)) (J : Finset (Fin k))
    (r : Recipe (fun i => family k (e i))
      (Finset.univ.filter (fun i => match e i with
        | .inl _ => True
        | .inr p => p.1 ∈ J))) :
    ∃ R : Recipe (fun i => family k (e i)) Finset.univ,
      (∀ i, (match e i with | .inl _ => True | .inr p => p.1 ∈ J) →
        gain R i = gain r i) ∧
      (∀ (j : Fin k), j ∉ J → ∀ b : Fin 4,
        gain R (e.symm (.inr (j, b))) = 1) := by
  classical
  let F := fun i => family k (e i)
  let S := fun M : Finset (Fin k) => Finset.univ.filter (fun i => match e i with
    | .inl _ => True
    | .inr p => p.1 ∈ M)
  let q := fun (t : Fin 3) (j : Fin k) => List.replicate j.val true ++ false ::
    (match t.val with
      | 0 => [false, false, false, true]
      | 1 => [false, true, true]
      | _ => [true, false, true])
  let a := fun (t : Fin 3) (j : Fin k) =>
    (⟨vector F (q t j), q t j, rfl⟩ : actualVectors F)
  have slot_eval (n : Nat) : ∀ (f : Fin n → Source) (v : Source)
      (j : Fin n) (u : Address),
      readout (List.replicate j.val true ++ false :: u) (comb n f v) =
        readout u (f j) := by
    induction n with
    | zero => exact fun _ _ j => Fin.elim0 j
    | succ n ih =>
      intro f v j u
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        change readout (List.replicate (j.val + 1) true ++ false :: u)
          (.mul (f 0) (comb n (fun x => f x.succ) v)) = _
        simp only [List.replicate_succ, List.cons_append, readout]
        exact ih (fun x => f x.succ) v j u
  have profile (t : Fin 3) (j : Fin k) (i : Fin (4 * k + 1)) :
      (a t j).val i = match e i with
      | .inl _ => .alpha
      | .inr (l, b) => if l = j then
          (match t.val, b.val with
            | _, 0 => .absent
            | 0, 1 => .branch
            | 1, 1 => .branch
            | 1, 2 => .branch
            | 2, 3 => .branch
            | _, _ => .alpha)
        else .alpha := by
    dsimp only [a, vector, F, q]
    cases he : e i with
    | inl u =>
      simp only [family, slot_eval]
      fin_cases t <;> rfl
    | inr p =>
      rcases p with ⟨l, b⟩
      simp only [family, slot_eval]
      by_cases h : l = j
      · subst l
        simp only [ite_true]
        fin_cases t <;> fin_cases b <;> rfl
      · simp only [if_neg h, if_neg (Ne.symm h)]
        fin_cases t <;> rfl
  have cast_gain {U V : Finset (Fin (4 * k + 1))} (h : U = V)
      (p : Recipe F U) (i : Fin (4 * k + 1)) :
      gain (h ▸ p) i = gain p i := by cases h; rfl
  have add_slot (M : Finset (Fin k)) (j : Fin k) (hj : j ∉ M)
      (p : Recipe F (S M)) :
      ∃ P : Recipe F (S (insert j M)), ∀ i ∈ S (insert j M),
        gain P i = if (∃ b, e i = .inr (j, b)) then 1 else gain p i := by
    let D := fun t : Nat => Finset.univ.filter (fun i => match e i with
      | .inl _ => True
      | .inr (l, b) => l ∈ M ∨ (l = j ∧ t ≤ b.val))
    let x := fun b : Fin 4 => e.symm (.inr (j, b))
    have d0 : D 0 = S (insert j M) := by
      ext i
      cases he : e i with
      | inl u => simp [D, S, he]
      | inr v => rcases v with ⟨l,b⟩; simp [D, S, he, or_comm]
    have d4 : D 4 = S M := by
      ext i
      cases he : e i with
      | inl u => simp [D, S, he]
      | inr v =>
        rcases v with ⟨l,b⟩
        have hb : ¬ 4 ≤ b.val := Nat.not_le.mpr b.isLt
        simp [D, S, he, hb]
    have children :
        (∀ y, survivors (D 0) (a 0 j).val y =
          match y with
          | .alpha => D 2 | .beta => ∅ | .branch => {x 1} | .absent => {x 0}) ∧
        (∀ y, survivors (D 2) (a 1 j).val y =
          match y with
          | .alpha => D 3 | .branch => {x 2} | _ => ∅) ∧
        (∀ y, survivors (D 3) (a 2 j).val y =
          match y with
          | .alpha => D 4 | .branch => {x 3} | _ => ∅) := by
      have hx (i : Fin (4 * k + 1)) (b : Fin 4) :
          i = x b ↔ e i = .inr (j,b) := by
        constructor
        · intro h; subst i; simp [x]
        · intro h
          apply e.injective
          simpa [x] using h
      repeat' constructor
      all_goals
        intro y
        ext i
        simp only [survivors, Finset.mem_filter, profile]
        cases he : e i with
        | inl u => cases y <;> simp [D, survivors, he, hx]
        | inr v =>
          rcases v with ⟨l,b⟩
          by_cases h : l = j
          · subst l
            fin_cases b <;> cases y <;> simp [D, survivors, he, hx, hj]
          · fin_cases b <;> cases y <;> simp [D, survivors, he, hx, h, hj]
    have split_ok (t : Fin 3) (d : Nat) (b : Fin 4)
        (hdb : d ≤ b.val) (hresp : (a t j).val (x b) ≠ .alpha) :
        2 ≤ ((D d).image (a t j).val).card := by
      apply Finset.one_lt_card.mpr
      refine ⟨.alpha, ?_, (a t j).val (x b), ?_, Ne.symm hresp⟩
      · apply Finset.mem_image.mpr
        refine ⟨e.symm (.inl ()), ?_, ?_⟩
        · simp [D]
        · simp [profile]
      · apply Finset.mem_image.mpr
        exact ⟨x b, by simp [D, x, hdb], rfl⟩
    let p4 : Recipe F (D 4) := d4.symm ▸ p
    let p3 : Recipe F (D 3) := .split (D 3) (a 2 j)
      (split_ok 2 3 3 (by decide) (by simp [profile, x])) (fun y hy => by
        cases y with
        | alpha => exact (children.2.2 .alpha).symm ▸ p4
        | branch => exact (children.2.2 .branch).symm ▸ Recipe.singleton (x 3)
        | beta => exfalso; simpa only [children.2.2 .beta, Finset.not_nonempty_empty] using hy
        | absent => exfalso; simpa only [children.2.2 .absent, Finset.not_nonempty_empty] using hy)
    let p2 : Recipe F (D 2) := .split (D 2) (a 1 j)
      (split_ok 1 2 2 (by decide) (by simp [profile, x])) (fun y hy => by
        cases y with
        | alpha => exact (children.2.1 .alpha).symm ▸ p3
        | branch => exact (children.2.1 .branch).symm ▸ Recipe.singleton (x 2)
        | beta => exfalso; simpa only [children.2.1 .beta, Finset.not_nonempty_empty] using hy
        | absent => exfalso; simpa only [children.2.1 .absent, Finset.not_nonempty_empty] using hy)
    let p0 : Recipe F (D 0) := .split (D 0) (a 0 j)
      (split_ok 0 0 0 (by decide) (by simp [profile, x])) (fun y hy => by
        cases y with
        | alpha => exact (children.1 .alpha).symm ▸ p2
        | branch => exact (children.1 .branch).symm ▸ Recipe.singleton (x 1)
        | absent => exact (children.1 .absent).symm ▸ Recipe.singleton (x 0)
        | beta => exfalso; simpa only [children.1 .beta, Finset.not_nonempty_empty] using hy)
    have split_gain (U : Finset (Fin (4 * k + 1))) (v : actualVectors F)
        (hv : 2 ≤ (U.image v.val).card)
        (next : ∀ y, (survivors U v.val y).Nonempty → Recipe F (survivors U v.val y))
        (i : Fin (4 * k + 1)) (hi : i ∈ U) (y : Reply) (hy : v.val i = y) :
        gain (.split U v hv next) i = chi y +
          gain (next y ⟨i, by simp [survivors, hi, hy]⟩) i := by
      subst y
      simp only [gain, dif_pos hi]
    have g3 (i : Fin (4 * k + 1)) (hi : i ∈ D 3) :
        gain p3 i = match (a 2 j).val i with
        | .alpha => gain p i | .branch => 1 | _ => 0 := by
      cases hy : (a 2 j).val i with
      | alpha =>
        rw [show gain p3 i = _ from split_gain _ _ _ _ i hi .alpha hy]
        simp [p3, p4, chi, cast_gain]
      | branch =>
        rw [show gain p3 i = _ from split_gain _ _ _ _ i hi .branch hy]
        simp [p3, chi, cast_gain, gain]
      | beta =>
        have mem : i ∈ survivors (D 3) (a 2 j).val .beta := by simp [survivors, hi, hy]
        exfalso
        simpa [children.2.2 .beta] using mem
      | absent =>
        have mem : i ∈ survivors (D 3) (a 2 j).val .absent := by simp [survivors, hi, hy]
        exfalso
        simpa [children.2.2 .absent] using mem
    have g2 (i : Fin (4 * k + 1)) (hi : i ∈ D 2) :
        gain p2 i = match (a 1 j).val i with
        | .alpha => gain p3 i | .branch => 1 | _ => 0 := by
      cases hy : (a 1 j).val i with
      | alpha =>
        rw [show gain p2 i = _ from split_gain _ _ _ _ i hi .alpha hy]
        simp [p2, chi, cast_gain]
      | branch =>
        rw [show gain p2 i = _ from split_gain _ _ _ _ i hi .branch hy]
        simp [p2, chi, cast_gain, gain]
      | beta =>
        have mem : i ∈ survivors (D 2) (a 1 j).val .beta := by simp [survivors, hi, hy]
        exfalso
        simpa [children.2.1 .beta] using mem
      | absent =>
        have mem : i ∈ survivors (D 2) (a 1 j).val .absent := by simp [survivors, hi, hy]
        exfalso
        simpa [children.2.1 .absent] using mem
    have g0 (i : Fin (4 * k + 1)) (hi : i ∈ D 0) :
        gain p0 i = match (a 0 j).val i with
        | .alpha => gain p2 i | .branch | .absent => 1 | .beta => 0 := by
      cases hy : (a 0 j).val i with
      | alpha =>
        rw [show gain p0 i = _ from split_gain _ _ _ _ i hi .alpha hy]
        simp [p0, chi, cast_gain]
      | branch =>
        rw [show gain p0 i = _ from split_gain _ _ _ _ i hi .branch hy]
        simp [p0, chi, cast_gain, gain]
      | absent =>
        rw [show gain p0 i = _ from split_gain _ _ _ _ i hi .absent hy]
        simp [p0, chi, cast_gain, gain]
      | beta =>
        have mem : i ∈ survivors (D 0) (a 0 j).val .beta := by simp [survivors, hi, hy]
        exfalso
        simpa [children.1 .beta] using mem
    refine ⟨d0 ▸ p0, ?_⟩
    intro i hi
    rw [cast_gain]
    have hi0 : i ∈ D 0 := d0.symm ▸ hi
    rw [g0 i hi0]
    cases he : e i with
    | inl u =>
      have hi2 : i ∈ D 2 := by simp [D, he]
      have hi3 : i ∈ D 3 := by simp [D, he]
      simp [profile, he, g2 i hi2, g3 i hi3]
    | inr v =>
      rcases v with ⟨l,b⟩
      by_cases h : l = j
      · subst l
        fin_cases b
        · simp [profile, he]
        · simp [profile, he]
        · have hi2 : i ∈ D 2 := by simp [D, he]
          simp [profile, he, g2 i hi2]
        · have hi2 : i ∈ D 2 := by simp [D, he]
          have hi3 : i ∈ D 3 := by simp [D, he]
          simp [profile, he, g2 i hi2, g3 i hi3]
      · have hl : l ∈ M := by simpa [D, he, h] using hi0
        have hi2 : i ∈ D 2 := by simp [D, he, hl]
        have hi3 : i ∈ D 3 := by simp [D, he, hl]
        simp [profile, he, h, g2 i hi2, g3 i hi3]
  have extend (T : Finset (Fin k)) (hT : Disjoint J T) :
      ∃ R : Recipe F (S (J ∪ T)),
        (∀ i ∈ S J, gain R i = gain r i) ∧
        (∀ j ∈ T, ∀ b : Fin 4, gain R (e.symm (.inr (j,b))) = 1) := by
    revert hT
    induction T using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.union_empty]
      exact ⟨r, fun _ _ => rfl, by simp⟩
    | @insert j T hj ih =>
      intro hT
      have hjJ : j ∉ J := (Finset.disjoint_insert_right.mp hT).1
      obtain ⟨P,hP,hPT⟩ := ih (Finset.disjoint_insert_right.mp hT).2
      have hjM : j ∉ J ∪ T := by simp [hjJ, hj]
      obtain ⟨Q,hQ⟩ := add_slot (J ∪ T) j hjM P
      have sets : S (insert j (J ∪ T)) = S (J ∪ insert j T) := by
        rw [Finset.union_insert]
      refine ⟨sets ▸ Q, ?_, ?_⟩
      · intro i hi
        rw [cast_gain, hQ i]
        · have no : ¬ ∃ b, e i = .inr (j,b) := by
            rintro ⟨b,hb⟩
            have : j ∈ J := by simpa [S, hb] using hi
            exact hjJ this
          rw [if_neg no]
          exact hP i hi
        · cases he : e i with
          | inl u => simp [S, he]
          | inr v =>
            have : v.1 ∈ J := by simpa [S, he] using hi
            simp [S, he, this]
      · intro l hl b
        rw [cast_gain, hQ (e.symm (.inr (l,b)))]
        · rcases Finset.mem_insert.mp hl with h | h
          · subst l; simp
          · have hlj : l ≠ j := fun heq => hj (heq ▸ h)
            simp only [Equiv.apply_symm_apply, Sum.inr.injEq, Prod.mk.injEq]
            rw [if_neg (by simp [hlj])]
            exact hPT l h b
        · rcases Finset.mem_insert.mp hl with h | h
          · subst l; simp [S]
          · simp [S, h]
  obtain ⟨R,hR,hother⟩ := extend (Finset.univ \ J) Finset.disjoint_sdiff
  have full : S (J ∪ (Finset.univ \ J)) = Finset.univ := by
    ext i
    cases he : e i <;> simp [S, he]
  refine ⟨full ▸ R, ?_, ?_⟩
  · intro i hi
    rw [cast_gain]
    exact hR i (by simpa [S] using hi)
  · intro j hj b
    rw [cast_gain]
    exact hother j (by simp [hj]) b

end D5.S3.Arith.FibonacciAtomic.FourExitScanExtension
