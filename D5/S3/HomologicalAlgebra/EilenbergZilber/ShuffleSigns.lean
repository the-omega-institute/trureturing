/- GID: D5/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/EilenbergZilber/ShuffleSigns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inversion counts and signs under shuffle step insertion. -/

/-
Copyright (c) 2026 Jeffrey Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeffrey Li

Source: LeanPool/EilenbergZilber, revision 8bbde3a6de815108d41922c9362ebbe38422663a.
Original source: jeffrey-dot-li/lean-homology, revision
40c5aae235b0f499ebfc1e68ce574a62b531203c; author release
fd0147a1ffe4f3c14c247574e148893d7cdf8cf6 (LeanPool PR 588).
Modifications: receiving namespace and imports, module boundaries, exposure of
consumed private interfaces, canonical identifier spellings, and omission of unused
companion, reflexive binding, and frontal material.
-/

module

public import D5.S3.HomologicalAlgebra.EilenbergZilber.ShuffleInsertion

@[expose] public section

noncomputable section

namespace D5.S3.HomologicalAlgebra.EilenbergZilber

namespace Shuffle

/-! ##### Helper lemmas for `sign_insertLeftStep`

The proof reduces to an inversion-count identity: inserting a left step at
position `j` adds exactly `t - j` to the inversion count, where
`t = insertLeftIndex ν j`. We split the `invCount` sum at `t` using
`Fin.sum_univ_succAbove`, match the non-inserted terms against `invCount ν`,
and compute the contribution of the inserted step directly. -/

/-- The inserted step is a left step: the first coordinate increases from `j`
to `succAbove j (ν.1 t).1 > j` at the insertion vertex. -/
lemma insertLeftStep_isLeftStep_at {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2))
    (ht : (insertLeftIndex ν j).val < p + 1 + q) :
    isLeftStep (insertLeftStep ν j) ⟨(insertLeftIndex ν j).val, ht⟩ := by
  -- Unfold to: j < j.succAbove (ν.1 ⟨t, ...⟩).fst
  unfold isLeftStep; simp +decide only [insertLeftStep, insertLeftStepFun, Fin.castSucc_mk,
      OrderHom.coe_mk, lt_self_iff_false, ↓reduceDIte, Fin.succ_mk, add_lt_iff_neg_left,
      Nat.add_eq_left, add_tsub_cancel_right, Fin.val_fin_lt]
  have hfst : ¬ (ν.1 ⟨(insertLeftIndex ν j).val, by omega⟩).1.val < j.val := by
    intro h
    have := (insertLeftIndex_iff ν j ⟨(insertLeftIndex ν j).val, by omega⟩).mp h
    simp at this
  -- succAbove j fst = fst.succ when fst ≥ j, so j < fst + 1
  simp only [Fin.succAbove]
  split
  · exfalso; simp [Fin.lt_def] at *; omega
  · simp [Fin.lt_def, Fin.val_succ] at *; omega

/-- The second coordinate at the insertion point equals `t - j`. -/
private lemma insertLeftStep_snd_at {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    ((insertLeftStep ν j).1 ⟨(insertLeftIndex ν j).val, by omega⟩).2.val =
    (insertLeftIndex ν j).val - j.val := by
  simp +decide [insertLeftStep, insertLeftStepFun]

/-- The `invCount` term at the insertion point contributes `t - j`:
`if isLeftStep μ t then μ(t).snd else 0 = t - j`. -/
private lemma insertLeftStep_invCount_term_at {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2))
    (ht : (insertLeftIndex ν j).val < p + 1 + q) :
    (if ((insertLeftStep ν j).1 (Fin.castSucc ⟨(insertLeftIndex ν j).val, ht⟩)).1 <
        ((insertLeftStep ν j).1 (Fin.succ ⟨(insertLeftIndex ν j).val, ht⟩)).1
     then ((insertLeftStep ν j).1 (Fin.castSucc ⟨(insertLeftIndex ν j).val, ht⟩)).2.val
     else 0) =
    (insertLeftIndex ν j).val - j.val := by
  split_ifs with h
  · exact insertLeftStep_snd_at ν j
  · exact absurd (insertLeftStep_isLeftStep_at ν j ht) h

/-- Each non-inserted step of `insertLeftStep ν j` has the same `invCount`
contribution as the corresponding step of `ν`. For step `i` of `ν`, the
matching step in the new shuffle is `i` if `i < t`, or `i + 1` if `i ≥ t`
(where `t = insertLeftIndex ν j`).

**Proof sketch** (three cases by position of `i` relative to `t`):
- **i+1 < t** (both endpoints in 'before' region): `insertLeftStepFun` applies
  `succAbove j` to both fst coords. `Fin.succAbove_lt_succAbove_iff` shows
  the fst comparison is preserved. The snd coord is unchanged.
- **i < t ≤ i+1** (castSucc in 'before', succ at insertion point): The new
  fst comparison is `succAbove(j, ν(i).fst) < j`. Since `ν(i).fst < j`
  (by `insertLeftIndex_iff`), `succAbove = castSucc`, so the condition
  reduces to `ν(i).fst < j`. The original condition `ν(i).fst < ν(i+1).fst`
  is equivalent since `ν(i).fst < j ≤ ν(i+1).fst`. Snd is unchanged.
- **i ≥ t** (both endpoints in 'after' region): `insertLeftStepFun` shifts
  by -1, mapping back to indices `i` and `i+1` of ν. Same argument via
  `succAbove` preserving ordering. Snd unchanged.

The main difficulty is Fin proof-irrelevance: `split_ifs` creates many
branches where `⟨i.val, proof₁⟩` and `i.castSucc` need to be identified.
Use `congr 3; ext; simp [Fin.val_castSucc]` to close the `.2.val` goals,
and `Fin.succAbove_lt_succAbove_iff` + `convert` for the condition goals.
`Fin.lt_def` loops with `simp` — avoid it or use `- Fin.lt_def`. -/
private lemma insertLeftStep_invCount_term_skip {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2))
    (i : Fin (p + q)) :
    let t := (insertLeftIndex ν j).val
    let r : Fin (p + 1 + q) :=
      if i.val < t then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
    (if ((insertLeftStep ν j).1 r.castSucc).1 <
        ((insertLeftStep ν j).1 r.succ).1
     then ((insertLeftStep ν j).1 r.castSucc).2.val
     else 0) =
    (if (ν.1 (Fin.castSucc i)).1 < (ν.1 (Fin.succ i)).1
     then (ν.1 (Fin.castSucc i)).2.val
     else 0) := by
  set t := (insertLeftIndex ν j).val
  by_cases h1 : i.val + 1 < t
  · -- Case 1: i+1 < t (both endpoints in 'before' region)
    simp only [show i.val < t from by omega]
    simp only [ite_true, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
    have hcs_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 + q)).castSucc.val = i.val := by
      simp [Fin.val_mk]
    have hsu_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 + q)).succ.val = i.val + 1 := by
      simp [Fin.val_mk]
    split_ifs <;> try omega
    all_goals simp only at *
    -- Goal 1: .2 values match (Fin proof-irrelevance)
    · rfl
    -- Goal 2: contradiction (succAbove preserves ordering)
    · exfalso; rename_i h_sa h_not
      exact h_not (Fin.succAbove_lt_succAbove_iff.mp (by
        exact h_sa))
    -- Goal 3: contradiction (same)
    · exfalso; rename_i h_sa h_orig
      apply h_sa
      exact Fin.succAbove_lt_succAbove_iff.mpr (by
        exact h_orig)
  · by_cases h2 : i.val < t
    · -- Case 2: i < t ≤ i+1 (castSucc before, succ at insertion point)
      simp only [h2]
      simp only [ite_true, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
      have hcs_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 +
          q)).castSucc.val = i.val := by
        simp [Fin.val_mk]
      have hsu_val : (⟨↑i, (by omega : ↑i < p + 1 + q)⟩ : Fin (p + 1 +
          q)).succ.val = i.val + 1 := by
        simp [Fin.val_mk]
      split_ifs <;> try omega
      all_goals simp only at *
      · rfl
      · exfalso; rename_i h_sa h_not
        simp only [hcs_val, hsu_val] at *
        apply h_not
        -- (↑ν i.castSucc).1.val < j.val since i < t, and (↑ν i.succ).1.val ≥ j.val since ¬(i+1 < t)
        have heq1 : (⟨i.val, (by omega : i.val < p + q + 1)⟩ : Fin (p + q + 1)) = i.castSucc := by
          ext; simp
        have heq2 : (⟨i.val + 1, (by omega : i.val + 1 < p + q + 1)⟩ : Fin (p + q +
            1)) = i.succ := by
          ext; simp [Fin.val_succ]
        have h_cs_lt := (insertLeftIndex_iff ν j ⟨i.val, by omega⟩).mpr (by simp; omega)
        have h_su_ge := mt (insertLeftIndex_iff ν j ⟨i.val + 1, by omega⟩).mp (by simp; omega)
        rw [heq1] at h_cs_lt; rw [heq2] at h_su_ge
        push Not at h_su_ge
        exact Fin.lt_def.mpr (by omega)
      · exfalso; rename_i h_sa h_orig
        simp only [hcs_val, hsu_val] at *
        apply h_sa
        rw [Fin.succAbove_lt_iff_castSucc_lt]
        have heq1 : (⟨i.val, (by omega : i.val < p + q + 1)⟩ : Fin (p + q + 1)) = i.castSucc := by
          ext; simp
        have h_cs_lt := (insertLeftIndex_iff ν j ⟨i.val, by omega⟩).mpr (by simp; omega)
        rw [heq1] at h_cs_lt
        exact Fin.mk_lt_mk.mpr h_cs_lt
    · -- Case 3: i ≥ t (both endpoints in 'after' region)
      simp only [show ¬(i.val < t) from h2]
      simp only [ite_false, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
      have hcs_val : (⟨↑i + 1, (by omega : ↑i + 1 < p + 1 + q)⟩ : Fin (p + 1 +
          q)).castSucc.val = i.val + 1 := by
        simp [Fin.val_mk]
      have hsu_val : (⟨↑i + 1, (by omega : ↑i + 1 < p + 1 + q)⟩ : Fin (p + 1 +
          q)).succ.val = i.val + 2 := by
        simp [Fin.val_mk]
      split_ifs <;> try omega
      all_goals simp only at *
      · rfl
      · exfalso; rename_i h_sa h_not
        apply h_not
        exact Fin.succAbove_lt_succAbove_iff.mp (by
          exact h_sa)
      · exfalso; rename_i h_sa h_orig
        apply h_sa
        exact Fin.succAbove_lt_succAbove_iff.mpr (by
          exact h_orig)

/-- **Key inversion-count identity** (additive form, avoiding ℕ subtraction):
`invCount(insertLeftStep ν j) + j = invCount(ν) + insertLeftIndex(ν, j)`.

Proof sketch: split the invCount sum for the new shuffle at the insertion
index `t`. The term at `t` contributes `t - j`
(by `insertLeftStep_invCount_term_at`). Each remaining step `r ≠ t` bijects
with a step of `ν` having the same contribution
(by `insertLeftStep_invCount_term_skip`). -/
private lemma invCount_insertLeftStep_add {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    (insertLeftStep ν j).invCount + j.val =
    ν.invCount + (insertLeftIndex ν j).val := by
  set μ := insertLeftStep ν j
  have hge : j.val ≤ (insertLeftIndex ν j).val := insertLeftIndex_ge ν j
  have hle : (insertLeftIndex ν j).val ≤ j.val + q := insertLeftIndex_le ν j
  -- Key: rewrite p+1+q as (p+q)+1 to use Fin.sum_univ_succAbove
  -- This is valid because p + 1 + q = (p + q) + 1 definitionally in Lean's kernel?
  -- No — but we can cast via finCongr.
  -- The insertion index as a Fin ((p+q)+1), if in range
  -- Since t ≤ j + q ≤ (p+1) + q = p + 1 + q, and p + 1 + q = (p + q) + 1,
  -- we have t ≤ (p+q) + 1. But we need t < (p+q) + 1, i.e., t ≤ p + q.
  -- When t = (p+q)+1, the insertion is at the very end.
  -- Actually, Fin.sum_univ_succAbove splits Fin (n+1) at ANY element of Fin (n+1),
  -- so we just need t < p + 1 + q. This might not hold when t = p+q+1 = p+1+q.
  -- Use Finset approach instead: extract element from univ, biject rest.
  simp only [invCount]
  -- Use Finset.sum_erase_add to extract one element
  by_cases ht_in : (insertLeftIndex ν j).val < p + 1 + q
  · -- Main case: t is a valid step index
    set t : Fin (p + 1 + q) := ⟨(insertLeftIndex ν j).val, ht_in⟩
    -- Extract term at t: ∑ = f(t) + (∑ over univ \ {t})
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    -- f(t) = t - j by insertLeftStep_invCount_term_at
    rw [insertLeftStep_invCount_term_at ν j ht_in]
    -- Biject remaining terms with invCount(ν) via skip map
    have hskip := insertLeftStep_invCount_term_skip ν j
    suffices h : ∑ x ∈ Finset.univ.erase t,
        (if (μ.1 x.castSucc).1 < (μ.1 x.succ).1 then (μ.1 x.castSucc).2.val else 0) =
      ∑ r : Fin (p + q),
        (if (ν.1 r.castSucc).1 < (ν.1 r.succ).1 then (ν.1 r.castSucc).2.val else 0) by omega
    -- φ(i) = if i.val < t then ⟨i, _⟩ else ⟨i+1, _⟩
    let φ : Fin (p + q) → Fin (p + 1 + q) :=
      fun i => if h : i.val < (insertLeftIndex ν j).val
        then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
    apply (Finset.sum_nbij φ _ _ _ _).symm
    · -- maps into erase t
      intro i _; simp only [Finset.mem_erase, Finset.mem_univ, and_true, φ]
      intro heq
      have : (if h : i.val < (insertLeftIndex ν j).val then (⟨i.val, by omega⟩ : Fin (p+1+q))
        else ⟨i.val + 1, by omega⟩).val = t.val := congr_arg Fin.val heq
      have ht_val : t.val = (insertLeftIndex ν j).val := rfl
      split_ifs at this with h <;> simp at this <;> omega
    · -- injective
      intro a _ b _ hab
      have : (φ a).val = (φ b).val := congr_arg Fin.val hab
      simp only [φ] at this
      ext
      split_ifs at this with ha hb <;> simp at this <;> omega
    · -- surjective onto erase t
      intro r hr
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
          Set.mem_singleton_iff, true_and] at hr
      have hr_ne : r.val ≠ (insertLeftIndex ν j).val := fun h => hr (Fin.ext h)
      by_cases hrlt : r.val < (insertLeftIndex ν j).val
      · exact ⟨⟨r.val, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val, by omega⟩ = r
          simp only [φ, hrlt, dite_true];⟩
      · exact ⟨⟨r.val - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val - 1, by omega⟩ = r
          simp only [φ]; split_ifs with h; · exfalso; omega
          · exact Fin.ext (by simp; omega)⟩
    · -- pointwise equality: fν(i) = fμ(φ(i))
      intro i _; exact (hskip i).symm
  · -- Boundary case: t = p + 1 + q (insertion at the very end, j = p+1)
    have hfmu : (if (μ.1 (Fin.castSucc ⟨p + q, by omega⟩)).1 < (μ.1 (Fin.succ ⟨p + q, by omega⟩)).1
      then (μ.1 (Fin.castSucc ⟨p + q, by omega⟩)).2.val else 0) = q := by
      have ht_eq : (insertLeftIndex ν j).val = p + 1 + q := by omega
      simp only [μ, insertLeftStep, insertLeftStepFun, OrderHom.coe_mk]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all <;> try omega
      -- Remaining: "before" branch for castSucc, "at" branch for succ
      · have hlast : ν.1 ⟨p + q, by omega⟩ = (Fin.last p, Fin.last q) := by
          have : (⟨p + q, (by omega : p + q < p + q + 1)⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
            Fin.ext (by simp [Fin.last])
          rw [this]; exact Shuffle.apply_last ν
        simp only [hlast, Fin.last]
      · exfalso; simp at h2; omega
      · have heq : (⟨p + q, (by omega : p + q < p + q + 1)⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
          Fin.ext (by simp [Fin.last])
        have h := Shuffle.apply_last ν; rw [← heq] at h
        change (ν.1 ⟨p + q, _⟩).2.val = q
        rw [show (ν.1 ⟨p + q, _⟩).2 = (Fin.last q) from congr_arg Prod.snd h]
        simp [Fin.last]
      · exfalso
        have heq : (⟨p + q, (by omega : p + q < p + q + 1)⟩ : Fin (p + q + 1)) = Fin.last (p + q) :=
          Fin.ext (by simp [Fin.last])
        have hlast' := Shuffle.apply_last ν; rw [← heq] at hlast'
        simp only [hlast', Fin.last] at h5
        rw [Fin.le_def, Fin.val_castSucc] at h5
        omega
    set s : Fin (p + 1 + q) := ⟨p + q, by omega⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), hfmu]
    have hskip := insertLeftStep_invCount_term_skip ν j
    suffices h : ∑ x ∈ Finset.univ.erase s,
        (if (μ.1 x.castSucc).1 < (μ.1 x.succ).1 then (μ.1 x.castSucc).2.val else 0) =
      ∑ r : Fin (p + q),
        (if (ν.1 r.castSucc).1 < (ν.1 r.succ).1 then (ν.1 r.castSucc).2.val else 0) by omega
    let φ : Fin (p + q) → Fin (p + 1 + q) :=
      fun i => if h : i.val < (insertLeftIndex ν j).val
        then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩
    apply (Finset.sum_nbij φ _ _ _ _).symm
    · -- maps into erase s
      intro i _; simp only [Finset.mem_erase, Finset.mem_univ, and_true, φ]
      intro heq
      have : (if h : i.val < (insertLeftIndex ν j).val then (⟨i.val, by omega⟩ : Fin (p+1+q))
        else ⟨i.val + 1, by omega⟩).val = s.val := congr_arg Fin.val heq
      have hs_val : s.val = p + q := rfl
      split_ifs at this with h <;> simp at this <;> omega
    · -- injective
      intro a _ b _ hab
      have : (φ a).val = (φ b).val := congr_arg Fin.val hab
      simp only [φ] at this
      ext
      split_ifs at this with ha hb <;> simp at this <;> omega
    · -- surjective onto erase s
      intro r hr
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
          Set.mem_singleton_iff, true_and] at hr
      have hr_ne : r.val ≠ p + q := fun h => hr (Fin.ext h)
      by_cases hrlt : r.val < (insertLeftIndex ν j).val
      · exact ⟨⟨r.val, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val, by omega⟩ = r
          simp only [φ, hrlt, dite_true]⟩
      · exact ⟨⟨r.val - 1, by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), by
          show φ ⟨r.val - 1, by omega⟩ = r
          simp only [φ]; split_ifs with h; · exfalso; omega
          · exact Fin.ext (by simp; omega)⟩
    · -- pointwise equality
      intro i _; exact (hskip i).symm

/-- Sign relation for left insertion:
`(insertLeftStep ν j).sign * (-1)^(insertLeftIndex ν j) = (-1)^j * ν.sign`.

Derived from `invCount_insertLeftStep_add` via exponent arithmetic:
the identity `invCount(μ) + j = invCount(ν) + t` gives
`(-1)^(invCount(μ) + j) = (-1)^(invCount(ν) + t)`, hence
`sign(μ) * (-1)^j = sign(ν) * (-1)^t`, and multiplying both sides
by `(-1)^(j+t)` (using `(-1)^(2k) = 1`) yields the result. -/
lemma sign_insertLeftStep {p q : ℕ}
    (ν : Shuffle p q) (j : Fin (p + 2)) :
    (insertLeftStep ν j).sign * (-1 : ℤ) ^ (insertLeftIndex ν j).val =
    (-1 : ℤ) ^ j.val * ν.sign := by
  simp only [sign, ← pow_add]
  have h := invCount_insertLeftStep_add ν j
  have hge := insertLeftIndex_ge ν j
  rw [show (insertLeftStep ν j).invCount + (insertLeftIndex ν j).val =
    (j.val + ν.invCount) + 2 * ((insertLeftIndex ν j).val - j.val) from by omega]
  rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]



/-- Right insertion index equals left insertion index on the swapped shuffle. -/
private lemma insertRightIndex_eq_swap {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightIndex ν k).val = (insertLeftIndex (ν.swap) k).val := by
  simp only [insertRightIndex, insertLeftIndex]
  have : (Finset.univ.filter fun r : Fin (q + p + 1) =>
      ((ν.swap).1 r).1.val < k.val) =
    (Finset.univ.filter fun r : Fin (p + q + 1) =>
      (ν.1 r).2.val < k.val).map (Fin.castOrderIso (by omega)).toEquiv.toEmbedding := by
    ext x
    simp only [Finset.mem_filter_univ, Finset.mem_map]
    simp only [swap_apply_fst]
    exact ⟨fun h => ⟨_, h, Fin.ext rfl⟩, by rintro ⟨a, ha, rfl⟩; exact ha⟩
  rw [this, Finset.card_map]


/-- Right insertion is left insertion on the swapped shuffle. -/
lemma insertRightStep_eq_swap {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightStep ν k).swap = insertLeftStep (ν.swap) k := by
  have hidx := insertRightIndex_eq_swap ν k
  apply Subtype.ext; ext r
  all_goals
    simp only [insertRightStep, insertLeftStep, insertRightStepFun, insertLeftStepFun]
    -- Replace the left index of `ν.swap` by the right index of `ν` before unfolding `swap`:
    -- once `swap` is unfolded inside the index's `Finset.filter`, simp cannot rewrite there
    -- because the filter's `DecidablePred` instance depends on the predicate.
    simp only [← hidx]
    simp only [swap, OrderHom.coe_mk, Fin.castOrderIso, Prod.swap, RelIso.coe_fn_mk,
      Equiv.coe_fn_mk, Fin.val_cast]
    split_ifs <;> simp_all only [Fin.cast]


/-- Sign relation for right insertion:
`(insertRightStep ν k).sign * (-1)^(insertRightIndex ν k) =
 (-1)^p * (-1)^k * ν.sign`. -/
lemma sign_insertRightStep {p q : ℕ}
    (ν : Shuffle p q) (k : Fin (q + 2)) :
    (insertRightStep ν k).sign * (-1 : ℤ) ^ (insertRightIndex ν k).val =
    (-1 : ℤ) ^ p * ((-1 : ℤ) ^ k.val * ν.sign) := by
  have h1 := sign_eq_negOnePow_mul_swap_sign (insertRightStep ν k)
  have h2 := insertRightStep_eq_swap ν k
  have h3 := insertRightIndex_eq_swap ν k
  have h4 := sign_insertLeftStep (ν.swap) k
  have h5 := sign_eq_negOnePow_mul_swap_sign ν
  rw [h1, h2, h3, h5]
  -- LHS: (-1)^(p*(q+1)) * sign * (-1)^idx
  -- RHS: (-1)^p * ((-1)^k * ((-1)^(p*q) * swap_sign))
  -- Use h4: sign * (-1)^idx = (-1)^k * swap_sign
  -- Then LHS = (-1)^(p*(q+1)) * (-1)^k * swap_sign
  -- RHS = (-1)^(p + p*q) * (-1)^k * swap_sign, and p*(q+1) = p + p*q
  calc (-1 : ℤ) ^ (p * (q + 1)) *
      (insertLeftStep (ν.swap) k).sign * (-1) ^ (insertLeftIndex (ν.swap) k).val
      = (-1) ^ (p * (q + 1)) *
        ((insertLeftStep (ν.swap) k).sign * (-1) ^ (insertLeftIndex (ν.swap) k).val) := by ring
    _ = (-1) ^ (p * (q + 1)) * ((-1) ^ k.val * (ν.swap).sign) := by rw [h4]
    _ = (-1) ^ p * ((-1) ^ k.val * ((-1) ^ (p * q) * (ν.swap).sign)) := by
        rw [show p * (q + 1) = p * q + p from by ring, pow_add]; ring


end Shuffle

end D5.S3.HomologicalAlgebra.EilenbergZilber
