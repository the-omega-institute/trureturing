/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreExtremum
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreExtremum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Signed frozen deletion preserves both signs of full-grid extrema. -/

/- Finite proofs adapted from Chakshu Gupta, https://github.com/ChakshuGupta13/lab,
commit 0bf8c67f7f5a2e8d44fb88c19fb80337221bbc11,
math/gupta2026degseq/lean/OrigamiCone/OrigamiCone/.
SequelEdContractExtremum.lean: bfd29f90788f3c03a8467d2b850bea239a4d8213.
CC BY 4.0; see docs/reports/miura-suppliers/lab-NOTICE.txt and lab-LICENSE.txt.
Namespaces, imports and selected declaration boundaries are adapted.
Retire these transplants when equivalent suppliers exist in pinned mathlib. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCoreCellExpand
public import D5.S3.Combinatorics.Geometry.MiuraStripRigidity

/-! Finite signed contraction and its exact full-grid invariants. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraCoreExtremum

open MiuraHeightEnvelope MiuraCoreColumns MiuraCoreFrozenSlope MiuraCoreContract MiuraCoreCellExpand

noncomputable section

open MiuraHeightEnvelope MiuraStripRigidity

variable {m n : ℕ}

lemma adj_of_row_col_diff {N : ℕ} {p q : Cell m N}
    (hrow : p.1 = q.1) (hcol : ((p.2.val : ℤ) - q.2.val).natAbs = 1) : adj p q := by
  have hrowV : p.1.val = q.1.val := by rw [hrow]
  unfold adj gdist
  omega

lemma cellExpand_adj_same_branch (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n)
    (p q : Cell m (n - 1)) (hadj : adj p q)
    (hbr : (p.2.val < j.val ∧ q.2.val < j.val) ∨ (¬ p.2.val < j.val ∧ ¬ q.2.val < j.val)) :
    adj (cellExpand j p hj0 hj1) (cellExpand j q hj0 hj1) := by
  rcases hbr with ⟨hpL, hqL⟩ | ⟨hpR, hqR⟩
  · rw [cellExpand_left _ _ hj0 hj1 hpL, cellExpand_left _ _ hj0 hj1 hqL]
    unfold adj gdist at hadj ⊢
    push_cast at hadj ⊢
    exact hadj
  · rw [cellExpand_right _ _ hj0 hj1 hpR, cellExpand_right _ _ hj0 hj1 hqR]
    unfold adj gdist at hadj ⊢
    push_cast at hadj ⊢
    convert hadj using 3
    omega

lemma cellExpand_adj_frozenCell (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n)
    (p : Cell m (n - 1)) (hpb : p.2.val + 1 = j.val ∨ p.2.val = j.val) :
    adj (cellExpand j p hj0 hj1) (p.1, j) := by
  rcases hpb with hL | hR
  · have hpL : p.2.val < j.val := by omega
    rw [cellExpand_left _ _ hj0 hj1 hpL]
    refine adj_of_row_col_diff rfl ?_
    simp only [Fin.val_mk]
    omega
  · have hpR : ¬ p.2.val < j.val := by omega
    rw [cellExpand_right _ _ hj0 hj1 hpR]
    refine adj_of_row_col_diff rfl ?_
    simp only [Fin.val_mk]
    omega

theorem contractAt_isSLM_of_h_max (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p : Cell m (n - 1))
    (hmax : IsStrictLocalMax h (cellExpand j p hfrz.1 hfrz.2.1)) :
    IsStrictLocalMax (contractAt h hm j hfrz) p := by
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  intro q hqadj
  rcases adj_row_or_col hqadj with ⟨hp1eq, hb⟩ | ⟨hp2eq, ha⟩
  ·
    by_cases hbr : (p.2.val < j.val ∧ q.2.val < j.val) ∨ (¬ p.2.val < j.val ∧ ¬ q.2.val < j.val)
    ·
      have hdiff := contractAt_diff_same_branch h hm j ⟨hj0, hj1, hsym⟩ p q hbr
      have hexp_adj := cellExpand_adj_same_branch j hj0 hj1 p q hqadj hbr
      have hval := hmax _ hexp_adj
      linarith
    ·
      push Not at hbr
      obtain ⟨hnAA, hnBB⟩ := hbr
      by_cases hpL : p.2.val < j.val
      ·
        have hqR : ¬ q.2.val < j.val := by
          have := hnAA hpL; omega
        have hqeq : q.2.val = p.2.val + 1 := by
          have hnat : ((p.2.val : ℤ) - q.2.val).natAbs = 1 := hb; omega
        have hpv : p.2.val + 1 = j.val := by omega
        have hqv : q.2.val = j.val := by omega
        have hdiff := contractAt_diff_seam_LtoR h hh hm j ⟨hj0, hj1, hsym⟩ p q hp1eq hpv hqv
        have hexp_adj := cellExpand_adj_frozenCell j hj0 hj1 p (Or.inl hpv)
        have hval := hmax (p.1, j) hexp_adj
        linarith
      ·
        push Not at hpL
        have hqL : q.2.val < j.val := hnBB hpL
        have hpvv : p.2.val = q.2.val + 1 := by
          have hnat : ((p.2.val : ℤ) - q.2.val).natAbs = 1 := hb; omega
        have hpv : p.2.val = j.val := by omega
        have hqv : q.2.val + 1 = j.val := by omega
        have hdiff := contractAt_diff_seam_RtoL h hh hm j ⟨hj0, hj1, hsym⟩ p q hp1eq hpv hqv
        have hexp_adj := cellExpand_adj_frozenCell j hj0 hj1 p (Or.inr hpv)
        have hval := hmax (p.1, j) hexp_adj
        linarith
  ·
    have hp2v : p.2.val = q.2.val := by rw [hp2eq]
    have hbr : (p.2.val < j.val ∧ q.2.val < j.val) ∨ (¬ p.2.val < j.val ∧ ¬ q.2.val < j.val) := by
      by_cases hpL : p.2.val < j.val
      · exact Or.inl ⟨hpL, hp2v ▸ hpL⟩
      · exact Or.inr ⟨hpL, hp2v ▸ hpL⟩
    have hdiff := contractAt_diff_same_branch h hm j ⟨hj0, hj1, hsym⟩ p q hbr
    have hexp_adj := cellExpand_adj_same_branch j hj0 hj1 p q hqadj hbr
    have hval := hmax _ hexp_adj
    linarith

theorem contractAt_isSLm_of_h_min (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p : Cell m (n - 1))
    (hmin : IsStrictLocalMin h (cellExpand j p hfrz.1 hfrz.2.1)) :
    IsStrictLocalMin (contractAt h hm j hfrz) p := by
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  intro q hqadj
  rcases adj_row_or_col hqadj with ⟨hp1eq, hb⟩ | ⟨hp2eq, ha⟩
  · by_cases hbr : (p.2.val < j.val ∧ q.2.val < j.val) ∨ (¬ p.2.val < j.val ∧ ¬ q.2.val < j.val)
    · have hdiff := contractAt_diff_same_branch h hm j ⟨hj0, hj1, hsym⟩ p q hbr
      have hexp_adj := cellExpand_adj_same_branch j hj0 hj1 p q hqadj hbr
      have hval := hmin _ hexp_adj
      linarith
    · push Not at hbr
      obtain ⟨hnAA, hnBB⟩ := hbr
      by_cases hpL : p.2.val < j.val
      · have hqR : ¬ q.2.val < j.val := by
          have := hnAA hpL; omega
        have hqeq : q.2.val = p.2.val + 1 := by
          have hnat : ((p.2.val : ℤ) - q.2.val).natAbs = 1 := hb; omega
        have hpv : p.2.val + 1 = j.val := by omega
        have hqv : q.2.val = j.val := by omega
        have hdiff := contractAt_diff_seam_LtoR h hh hm j ⟨hj0, hj1, hsym⟩ p q hp1eq hpv hqv
        have hexp_adj := cellExpand_adj_frozenCell j hj0 hj1 p (Or.inl hpv)
        have hval := hmin (p.1, j) hexp_adj
        linarith
      · push Not at hpL
        have hqL : q.2.val < j.val := hnBB hpL
        have hpvv : p.2.val = q.2.val + 1 := by
          have hnat : ((p.2.val : ℤ) - q.2.val).natAbs = 1 := hb; omega
        have hpv : p.2.val = j.val := by omega
        have hqv : q.2.val + 1 = j.val := by omega
        have hdiff := contractAt_diff_seam_RtoL h hh hm j ⟨hj0, hj1, hsym⟩ p q hp1eq hpv hqv
        have hexp_adj := cellExpand_adj_frozenCell j hj0 hj1 p (Or.inr hpv)
        have hval := hmin (p.1, j) hexp_adj
        linarith
  · have hp2v : p.2.val = q.2.val := by rw [hp2eq]
    have hbr : (p.2.val < j.val ∧ q.2.val < j.val) ∨ (¬ p.2.val < j.val ∧ ¬ q.2.val < j.val) := by
      by_cases hpL : p.2.val < j.val
      · exact Or.inl ⟨hpL, hp2v ▸ hpL⟩
      · exact Or.inr ⟨hpL, hp2v ▸ hpL⟩
    have hdiff := contractAt_diff_same_branch h hm j ⟨hj0, hj1, hsym⟩ p q hbr
    have hexp_adj := cellExpand_adj_same_branch j hj0 hj1 p q hqadj hbr
    have hval := hmin _ hexp_adj
    linarith

theorem contractAt_isSLE_of_h_extremum (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p : Cell m (n - 1))
    (hext : IsStrictLocalExtremum h (cellExpand j p hfrz.1 hfrz.2.1)) :
    IsStrictLocalExtremum (contractAt h hm j hfrz) p := by
  rcases hext with hmax | hmin
  · exact Or.inl (contractAt_isSLM_of_h_max h hh hm j hfrz p hmax)
  · exact Or.inr (contractAt_isSLm_of_h_min h hh hm j hfrz p hmin)

lemma adj_cellExpand_of_not_frozen (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n)
    (p : Cell m (n - 1)) (u : Cell m n)
    (hadj : adj (cellExpand j p hj0 hj1) u) (hufrz : u.2 ≠ j) :
    ∃ q : Cell m (n - 1), cellExpand j q hj0 hj1 = u ∧ adj p q ∧
    ((p.2.val < j.val ∧ q.2.val < j.val) ∨ (¬ p.2.val < j.val ∧ ¬ q.2.val < j.val)) := by
  obtain ⟨q, hq⟩ := cellExpand_surjOn j hj0 hj1 u hufrz
  refine ⟨q, hq, ?_, ?_⟩
  · rw [← hq] at hadj
    by_cases hpL : p.2.val < j.val
    · by_cases hqL : q.2.val < j.val
      · rw [cellExpand_left _ _ hj0 hj1 hpL, cellExpand_left _ _ hj0 hj1 hqL] at hadj
        unfold adj gdist at hadj ⊢
        push_cast at hadj ⊢
        exact hadj
      · exfalso
        push Not at hqL
        have hqR : ¬ q.2.val < j.val := by omega
        rw [cellExpand_left _ _ hj0 hj1 hpL, cellExpand_right _ _ hj0 hj1 hqR] at hadj
        unfold adj gdist at hadj
        simp only [Prod.fst, Prod.snd, Fin.val_mk] at hadj
        have h_col : ((p.2.val : ℤ) - (q.2.val + 1)).natAbs ≥ 2 := by
          have hle : (p.2.val : ℤ) - (q.2.val + 1) ≤ -2 := by push_cast; omega
          omega
        omega
    · push Not at hpL
      have hpR : ¬ p.2.val < j.val := by omega
      by_cases hqL : q.2.val < j.val
      · exfalso
        rw [cellExpand_right _ _ hj0 hj1 hpR, cellExpand_left _ _ hj0 hj1 hqL] at hadj
        unfold adj gdist at hadj
        simp only [Prod.fst, Prod.snd, Fin.val_mk] at hadj
        have h_col : ((p.2.val + 1 : ℤ) - q.2.val).natAbs ≥ 2 := by
          have hge : (p.2.val + 1 : ℤ) - q.2.val ≥ 2 := by push_cast; omega
          omega
        omega
      · push Not at hqL
        have hqR : ¬ q.2.val < j.val := by omega
        rw [cellExpand_right _ _ hj0 hj1 hpR, cellExpand_right _ _ hj0 hj1 hqR] at hadj
        unfold adj gdist at hadj ⊢
        push_cast at hadj ⊢
        convert hadj using 3
        omega
  · rw [← hq] at hadj
    by_cases hpL : p.2.val < j.val
    · by_cases hqL : q.2.val < j.val
      · exact Or.inl ⟨hpL, hqL⟩
      · exfalso
        push Not at hqL
        have hqR : ¬ q.2.val < j.val := by omega
        rw [cellExpand_left _ _ hj0 hj1 hpL, cellExpand_right _ _ hj0 hj1 hqR] at hadj
        unfold adj gdist at hadj
        simp only [Prod.fst, Prod.snd, Fin.val_mk] at hadj
        have h_col : ((p.2.val : ℤ) - (q.2.val + 1)).natAbs ≥ 2 := by
          have hle : (p.2.val : ℤ) - (q.2.val + 1) ≤ -2 := by push_cast; omega
          omega
        omega
    · push Not at hpL
      have hpR : ¬ p.2.val < j.val := by omega
      by_cases hqL : q.2.val < j.val
      · exfalso
        rw [cellExpand_right _ _ hj0 hj1 hpR, cellExpand_left _ _ hj0 hj1 hqL] at hadj
        unfold adj gdist at hadj
        simp only [Prod.fst, Prod.snd, Fin.val_mk] at hadj
        have h_col : ((p.2.val + 1 : ℤ) - q.2.val).natAbs ≥ 2 := by
          have hge : (p.2.val + 1 : ℤ) - q.2.val ≥ 2 := by push_cast; omega
          omega
        omega
      · push Not at hqL
        have hqR : ¬ q.2.val < j.val := by omega
        exact Or.inr ⟨hpR, hqR⟩

theorem h_max_of_contractAt_isSLM (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p : Cell m (n - 1))
    (hmax : IsStrictLocalMax (contractAt h hm j hfrz) p) :
    IsStrictLocalMax h (cellExpand j p hfrz.1 hfrz.2.1) := by
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  intro u hadj
  by_cases hufrz : u.2 = j
  · have hcellne : (cellExpand j p hj0 hj1).2 ≠ j := cellExpand_ne_j j p hj0 hj1
    rcases adj_row_or_col hadj with ⟨hrow_eq, hcol⟩ | ⟨hcol_eq, _⟩
    · have hcellp1 : (cellExpand j p hj0 hj1).1 = p.1 := by
        by_cases hpL : p.2.val < j.val
        · rw [cellExpand_left _ _ hj0 hj1 hpL]
        · rw [cellExpand_right _ _ hj0 hj1 (by omega : ¬ p.2.val < j.val)]
      have hu1 : u.1 = p.1 := hcellp1 ▸ hrow_eq.symm
      have hueq : u = (p.1, j) := Prod.ext hu1 hufrz
      by_cases hpL : p.2.val < j.val
      · have hcellp2v : (cellExpand j p hj0 hj1).2.val = p.2.val := by
          rw [cellExpand_left _ _ hj0 hj1 hpL]
        have hpv : p.2.val + 1 = j.val := by
          have hcolShow := hcol
          rw [hufrz, hcellp2v] at hcolShow
          have h_p_lt : (p.2.val : ℤ) < j.val := by push_cast; omega
          have : (p.2.val : ℤ) - j.val < 0 := by omega
          omega
        let q : Cell m (n - 1) := (p.1, ⟨j.val, by omega⟩)
        have hp1q : p.1 = q.1 := rfl
        have hqv : q.2.val = j.val := rfl
        have hqadj : adj p q := by
          refine adj_of_row_col_diff rfl ?_
          show ((p.2.val : ℤ) - j.val).natAbs = 1
          push_cast; omega
        have hdiff := contractAt_diff_seam_LtoR h hh hm j ⟨hj0, hj1, hsym⟩ p q hp1q hpv hqv
        have hval := hmax q hqadj
        rw [hueq]
        linarith
      · push Not at hpL
        have hpR : ¬ p.2.val < j.val := by omega
        have hcellp2v : (cellExpand j p hj0 hj1).2.val = p.2.val + 1 := by
          rw [cellExpand_right _ _ hj0 hj1 hpR]
        have hpv : p.2.val = j.val := by
          have hcolShow := hcol
          rw [hufrz, hcellp2v] at hcolShow
          have h_p_ge : (p.2.val : ℤ) ≥ j.val := by push_cast; omega
          have : (p.2.val + 1 : ℤ) - j.val > 0 := by omega
          omega
        let q : Cell m (n - 1) := (p.1, ⟨j.val - 1, by omega⟩)
        have hp1q : p.1 = q.1 := rfl
        have hqv : q.2.val + 1 = j.val := by
          show j.val - 1 + 1 = j.val
          omega
        have hqadj : adj p q := by
          refine adj_of_row_col_diff rfl ?_
          show ((p.2.val : ℤ) - (j.val - 1 : ℕ)).natAbs = 1
          push_cast; omega
        have hdiff := contractAt_diff_seam_RtoL h hh hm j ⟨hj0, hj1, hsym⟩ p q hp1q hpv hqv
        have hval := hmax q hqadj
        rw [hueq]
        linarith
    · exfalso
      apply hcellne
      rw [hcol_eq, hufrz]
  · obtain ⟨q, hqEq, hqadj, hbr⟩ := adj_cellExpand_of_not_frozen j hj0 hj1 p u hadj hufrz
    have hdiff := contractAt_diff_same_branch h hm j ⟨hj0, hj1, hsym⟩ p q hbr
    have hval := hmax q hqadj
    rw [← hqEq]
    linarith

theorem h_min_of_contractAt_isSLm (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p : Cell m (n - 1))
    (hmin : IsStrictLocalMin (contractAt h hm j hfrz) p) :
    IsStrictLocalMin h (cellExpand j p hfrz.1 hfrz.2.1) := by
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  intro u hadj
  by_cases hufrz : u.2 = j
  · have hcellne : (cellExpand j p hj0 hj1).2 ≠ j := cellExpand_ne_j j p hj0 hj1
    rcases adj_row_or_col hadj with ⟨hrow_eq, hcol⟩ | ⟨hcol_eq, _⟩
    · have hcellp1 : (cellExpand j p hj0 hj1).1 = p.1 := by
        by_cases hpL : p.2.val < j.val
        · rw [cellExpand_left _ _ hj0 hj1 hpL]
        · rw [cellExpand_right _ _ hj0 hj1 (by omega : ¬ p.2.val < j.val)]
      have hu1 : u.1 = p.1 := hcellp1 ▸ hrow_eq.symm
      have hueq : u = (p.1, j) := Prod.ext hu1 hufrz
      by_cases hpL : p.2.val < j.val
      · have hcellp2v : (cellExpand j p hj0 hj1).2.val = p.2.val := by
          rw [cellExpand_left _ _ hj0 hj1 hpL]
        have hpv : p.2.val + 1 = j.val := by
          have hcolShow := hcol
          rw [hufrz, hcellp2v] at hcolShow
          have h_p_lt : (p.2.val : ℤ) < j.val := by push_cast; omega
          have : (p.2.val : ℤ) - j.val < 0 := by omega
          omega
        let q : Cell m (n - 1) := (p.1, ⟨j.val, by omega⟩)
        have hp1q : p.1 = q.1 := rfl
        have hqv : q.2.val = j.val := rfl
        have hqadj : adj p q := by
          refine adj_of_row_col_diff rfl ?_
          show ((p.2.val : ℤ) - j.val).natAbs = 1
          push_cast; omega
        have hdiff := contractAt_diff_seam_LtoR h hh hm j ⟨hj0, hj1, hsym⟩ p q hp1q hpv hqv
        have hval := hmin q hqadj
        rw [hueq]
        linarith
      · push Not at hpL
        have hpR : ¬ p.2.val < j.val := by omega
        have hcellp2v : (cellExpand j p hj0 hj1).2.val = p.2.val + 1 := by
          rw [cellExpand_right _ _ hj0 hj1 hpR]
        have hpv : p.2.val = j.val := by
          have hcolShow := hcol
          rw [hufrz, hcellp2v] at hcolShow
          have h_p_ge : (p.2.val : ℤ) ≥ j.val := by push_cast; omega
          have : (p.2.val + 1 : ℤ) - j.val > 0 := by omega
          omega
        let q : Cell m (n - 1) := (p.1, ⟨j.val - 1, by omega⟩)
        have hp1q : p.1 = q.1 := rfl
        have hqv : q.2.val + 1 = j.val := by
          show j.val - 1 + 1 = j.val
          omega
        have hqadj : adj p q := by
          refine adj_of_row_col_diff rfl ?_
          show ((p.2.val : ℤ) - (j.val - 1 : ℕ)).natAbs = 1
          push_cast; omega
        have hdiff := contractAt_diff_seam_RtoL h hh hm j ⟨hj0, hj1, hsym⟩ p q hp1q hpv hqv
        have hval := hmin q hqadj
        rw [hueq]
        linarith
    · exfalso
      apply hcellne
      rw [hcol_eq, hufrz]
  · obtain ⟨q, hqEq, hqadj, hbr⟩ := adj_cellExpand_of_not_frozen j hj0 hj1 p u hadj hufrz
    have hdiff := contractAt_diff_same_branch h hm j ⟨hj0, hj1, hsym⟩ p q hbr
    have hval := hmin q hqadj
    rw [← hqEq]
    linarith

theorem h_extremum_of_contractAt_isSLE (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p : Cell m (n - 1))
    (hext : IsStrictLocalExtremum (contractAt h hm j hfrz) p) :
    IsStrictLocalExtremum h (cellExpand j p hfrz.1 hfrz.2.1) := by
  rcases hext with hmax | hmin
  · exact Or.inl (h_max_of_contractAt_isSLM h hh hm j hfrz p hmax)
  · exact Or.inr (h_min_of_contractAt_isSLm h hh hm j hfrz p hmin)

theorem contractAt_isSLE_iff (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p : Cell m (n - 1)) :
    IsStrictLocalExtremum (contractAt h hm j hfrz) p ↔
    IsStrictLocalExtremum h (cellExpand j p hfrz.1 hfrz.2.1) :=
  ⟨h_extremum_of_contractAt_isSLE h hh hm j hfrz p,
   contractAt_isSLE_of_h_extremum h hh hm j hfrz p⟩

end

end D5.S3.Combinatorics.Geometry.MiuraCoreExtremum
