/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreCellExpand
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreCellExpand
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Surviving cells and edge differences are tracked through frozen deletion. -/

/- Finite proofs adapted from Chakshu Gupta, https://github.com/ChakshuGupta13/lab,
commit 0bf8c67f7f5a2e8d44fb88c19fb80337221bbc11,
math/gupta2026degseq/lean/OrigamiCone/OrigamiCone/.
SequelEdCellExpand.lean: 74d588f431b314dd5b542c6e710a5d20deb31d8b.
CC BY 4.0; see docs/reports/miura-suppliers/lab-NOTICE.txt and lab-LICENSE.txt.
Namespaces, imports and selected declaration boundaries are adapted.
Retire these transplants when equivalent suppliers exist in pinned mathlib. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCoreContract

/-! Finite signed contraction and its exact full-grid invariants. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraCoreCellExpand

open MiuraHeightEnvelope MiuraCoreColumns MiuraCoreFrozenSlope MiuraCoreContract

noncomputable section

open MiuraHeightEnvelope

variable {m n : ℕ}

theorem frozenColumn_no_extremum (h : Cell m n → ℤ) (j : Fin n) (hfrz : frozenColumn h j) :
    ∀ i : Fin m, ¬ IsStrictLocalExtremum h (i, j) := by
  intro i hext
  exact frozenColumn_not_active h j hfrz ⟨i, hext⟩

def cellExpand (j : Fin n) (p : Cell m (n - 1)) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) :
    Cell m n :=
  if p.2.val < j.val then
    (p.1, ⟨p.2.val, by have := p.2.isLt; omega⟩)
  else
    (p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩)

theorem cellExpand_left (j : Fin n) (p : Cell m (n - 1)) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n)
    (hp : p.2.val < j.val) :
    cellExpand j p hj0 hj1 = (p.1, ⟨p.2.val, by have := p.2.isLt; omega⟩) := by
  unfold cellExpand; simp [hp]

theorem cellExpand_right (j : Fin n) (p : Cell m (n - 1)) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n)
    (hp : ¬ p.2.val < j.val) :
    cellExpand j p hj0 hj1 = (p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩) := by
  unfold cellExpand; simp [hp]

theorem cellExpand_ne_j (j : Fin n) (p : Cell m (n - 1)) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) :
    (cellExpand j p hj0 hj1).2 ≠ j := by
  intro hc
  have hval := congrArg Fin.val hc
  unfold cellExpand at hval
  by_cases hlt : p.2.val < j.val
  · simp [hlt] at hval; omega
  · simp [hlt] at hval; omega

theorem cellExpand_injective (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n) :
    Function.Injective (cellExpand (m := m) j · hj0 hj1) := by
  intro p q hpq
  have hval1 := congrArg Prod.fst hpq
  have hval2 := congrArg Prod.snd hpq
  have hval2v : (cellExpand j p hj0 hj1).2.val = (cellExpand j q hj0 hj1).2.val :=
    congrArg Fin.val hval2
  unfold cellExpand at hval1 hval2v
  by_cases hlp : p.2.val < j.val
  · by_cases hlq : q.2.val < j.val
    · simp [hlp, hlq] at hval1 hval2v
      exact Prod.ext hval1 (Fin.ext hval2v)
    · simp [hlp, hlq] at hval1 hval2v
      omega
  · by_cases hlq : q.2.val < j.val
    · simp [hlp, hlq] at hval1 hval2v
      omega
    · simp [hlp, hlq] at hval1 hval2v
      exact Prod.ext hval1 (Fin.ext (by omega))

theorem contractAt_isCanonicalHeight (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (hcanon : IsCanonicalHeight h) :
    IsCanonicalHeight (contractAt h hm j hfrz) := by
  refine ⟨contractAt_isHeight h hh hm j hfrz, ?_⟩
  intro p hp1 hp2
  have hj0 : 0 < j.val := hfrz.1
  have hval : contractAt h hm j hfrz p
      = h (p.1, ⟨p.2.val, by have := p.2.isLt; have hj1 := hfrz.2.1; omega⟩) := by
    apply contractAt_left h hm j hfrz p
    rw [hp2]; exact hj0
  rw [hval]
  exact hcanon.2 _ hp1 (by simp [hp2])

theorem cellExpand_surjOn (j : Fin n) (hj0 : 0 < j.val) (hj1 : j.val + 1 < n)
    (q : Cell m n) (hqj : q.2 ≠ j) :
    ∃ p : Cell m (n - 1), cellExpand j p hj0 hj1 = q := by
  by_cases hlt : q.2.val < j.val
  · refine ⟨(q.1, ⟨q.2.val, by have := q.2.isLt; omega⟩), ?_⟩
    unfold cellExpand
    simp [hlt]
  · have hqjval : q.2.val ≠ j.val := fun h => hqj (Fin.ext h)
    have hgt : q.2.val > j.val := by omega
    refine ⟨(q.1, ⟨q.2.val - 1, by have := q.2.isLt; omega⟩), ?_⟩
    have hpge : ¬ q.2.val - 1 < j.val := by omega
    unfold cellExpand
    simp only [hpge, if_false]
    exact Prod.ext rfl (Fin.ext (by simp only [Fin.val_mk]; omega))

theorem frozenSlope_eq_right (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (i : Fin m) :
    h (i, ⟨j.val + 1, hfrz.2.1⟩) - h (i, j) = frozenSlope h hm j hfrz := by
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  have hL := frozenSlope_eq h hh hm j ⟨hj0, hj1, hsym⟩ i
  have hs := hsym i
  linarith

theorem contractAt_diff_same_branch (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p q : Cell m (n - 1))
    (hbr : (p.2.val < j.val ∧ q.2.val < j.val) ∨ (¬ p.2.val < j.val ∧ ¬ q.2.val < j.val)) :
    contractAt h hm j hfrz q - contractAt h hm j hfrz p
      = h (cellExpand j q hfrz.1 hfrz.2.1) - h (cellExpand j p hfrz.1 hfrz.2.1) := by
  obtain ⟨hj0, hj1, _⟩ := hfrz
  rcases hbr with ⟨hpL, hqL⟩ | ⟨hpR, hqR⟩
  · rw [contractAt_left _ _ _ _ p hpL, contractAt_left _ _ _ _ q hqL]
    rw [cellExpand_left _ _ hj0 hj1 hpL, cellExpand_left _ _ hj0 hj1 hqL]
  · rw [contractAt_right _ _ _ _ p hpR, contractAt_right _ _ _ _ q hqR]
    rw [cellExpand_right _ _ hj0 hj1 hpR, cellExpand_right _ _ hj0 hj1 hqR]
    ring

theorem contractAt_diff_seam_LtoR (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j)
    (p q : Cell m (n - 1)) (hp1 : p.1 = q.1)
    (hpv : p.2.val + 1 = j.val) (hqv : q.2.val = j.val) :
    contractAt h hm j hfrz q - contractAt h hm j hfrz p
      = h (p.1, j) - h (cellExpand j p hfrz.1 hfrz.2.1) := by
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  have hpL : p.2.val < j.val := by omega
  have hqR : ¬ q.2.val < j.val := by omega
  rw [contractAt_left _ _ _ _ p hpL, contractAt_right _ _ _ _ q hqR]
  rw [cellExpand_left _ _ hj0 hj1 hpL]
  have hqFin : (⟨q.2.val + 1, by have := q.2.isLt; omega⟩ : Fin n) = ⟨j.val + 1, hj1⟩ := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  have hpFin : (⟨p.2.val, by have := p.2.isLt; omega⟩ : Fin n)
      = ⟨j.val - 1, by omega⟩ := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  rw [hqFin, hpFin, ← hp1]
  have hR := frozenSlope_eq_right h hh hm j ⟨hj0, hj1, hsym⟩ p.1
  linarith

theorem contractAt_diff_seam_RtoL (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j)
    (p q : Cell m (n - 1)) (hp1 : p.1 = q.1)
    (hpv : p.2.val = j.val) (hqv : q.2.val + 1 = j.val) :
    contractAt h hm j hfrz q - contractAt h hm j hfrz p
      = h (p.1, j) - h (cellExpand j p hfrz.1 hfrz.2.1) := by
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  have hpR : ¬ p.2.val < j.val := by omega
  have hqL : q.2.val < j.val := by omega
  rw [contractAt_right _ _ _ _ p hpR, contractAt_left _ _ _ _ q hqL]
  rw [cellExpand_right _ _ hj0 hj1 hpR]
  have hqFin : (⟨q.2.val, by have := q.2.isLt; omega⟩ : Fin n)
      = ⟨j.val - 1, by omega⟩ := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  have hpFin : (⟨p.2.val + 1, by have := p.2.isLt; omega⟩ : Fin n)
      = ⟨j.val + 1, hj1⟩ := by
    apply Fin.ext; simp only [Fin.val_mk]; omega
  rw [hqFin, hpFin, ← hp1]
  have hL := frozenSlope_eq h hh hm j ⟨hj0, hj1, hsym⟩ p.1
  linarith

end

end D5.S3.Combinatorics.Geometry.MiuraCoreCellExpand
