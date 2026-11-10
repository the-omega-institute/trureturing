/- GID: D5/S3/Combinatorics/Geometry/MiuraCoreContract
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraCoreContract
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Signed deletion of a frozen column preserves every unit grid edge. -/

/- Finite proofs adapted from Chakshu Gupta, https://github.com/ChakshuGupta13/lab,
commit 0bf8c67f7f5a2e8d44fb88c19fb80337221bbc11,
math/gupta2026degseq/lean/OrigamiCone/OrigamiCone/.
SequelEdContractAt.lean: af9295c3fda473676d972e5058cc57233dd340a8.
CC BY 4.0; see docs/reports/miura-suppliers/lab-NOTICE.txt and lab-LICENSE.txt.
Namespaces, imports and selected declaration boundaries are adapted.
Retire these transplants when equivalent suppliers exist in pinned mathlib. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraCoreFrozenSlope

/-! Finite signed contraction and its exact full-grid invariants. -/

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraCoreContract

open MiuraHeightEnvelope MiuraCoreColumns MiuraCoreFrozenSlope

noncomputable section

open MiuraHeightEnvelope

variable {m n : ℕ}

noncomputable def frozenSlope (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) : ℤ :=
  h (⟨0, hm⟩, j) - h (⟨0, hm⟩, ⟨j.val - 1, by
    obtain ⟨hj0, _, _⟩ := hfrz; omega⟩)

theorem frozenSlope_eq (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (i : Fin m) :
    h (i, j) - h (i, ⟨j.val - 1, by obtain ⟨hj0, _, _⟩ := hfrz; omega⟩)
      = frozenSlope h hm j hfrz := by
  unfold frozenSlope
  have := frozenColumn_dL_eq_row0 h hh hm j hfrz i
  linarith

theorem frozenSlope_pm (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) :
    frozenSlope h hm j hfrz = 1 ∨ frozenSlope h hm j hfrz = -1 := by
  unfold frozenSlope
  obtain ⟨hj0, hj1, _⟩ := hfrz
  set jL : Fin n := ⟨j.val - 1, by omega⟩ with hjLdef
  have hadj : adj ((⟨0, hm⟩, j) : Cell m n) (⟨0, hm⟩, jL) := by
    unfold adj gdist; simp only [hjLdef, Fin.val_mk]; omega
  have hvv := hh _ _ hadj
  rcases abs_cases (h (⟨0, hm⟩, j) - h (⟨0, hm⟩, jL)) with ⟨he, _⟩ | ⟨he, _⟩ <;>
    first | (left; omega) | (right; omega)

noncomputable def contractAt (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) : Cell m (n - 1) → ℤ :=
  let k := frozenSlope h hm j hfrz
  fun p =>
    if p.2.val < j.val then
      h (p.1, ⟨p.2.val, by
        have := p.2.isLt
        obtain ⟨hj0, hj1, _⟩ := hfrz
        omega⟩)
    else
      h (p.1, ⟨p.2.val + 1, by
        have := p.2.isLt
        obtain ⟨hj0, hj1, _⟩ := hfrz
        omega⟩) - k

theorem contractAt_left (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p : Cell m (n - 1))
    (hp : p.2.val < j.val) :
    contractAt h hm j hfrz p = h (p.1, ⟨p.2.val, by
      have := p.2.isLt; obtain ⟨_, hj1, _⟩ := hfrz; omega⟩) := by
  unfold contractAt
  simp only [hp, ite_true]

theorem contractAt_right (h : Cell m n → ℤ) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p : Cell m (n - 1))
    (hp : ¬ p.2.val < j.val) :
    contractAt h hm j hfrz p = h (p.1, ⟨p.2.val + 1, by
      have := p.2.isLt; obtain ⟨_, hj1, _⟩ := hfrz; omega⟩)
        - frozenSlope h hm j hfrz := by
  unfold contractAt
  simp only [hp, ite_false]

theorem contractAt_isHeight_vertical (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p q : Cell m (n - 1))
    (hp2v : p.2.val = q.2.val) (hadj : adj p q) :
    |contractAt h hm j hfrz p - contractAt h hm j hfrz q| = 1 := by
  obtain ⟨hj0, hj1, _⟩ := hfrz
  unfold adj gdist at hadj
  have hsum : ((p.1.val : ℤ) - q.1.val).natAbs + ((p.2.val : ℤ) - q.2.val).natAbs = 1 := by
    exact_mod_cast hadj
  have hrowabs : ((p.1.val : ℤ) - q.1.val).natAbs = 1 := by omega
  by_cases hlt : p.2.val < j.val
  · have hlt' : q.2.val < j.val := by omega
    rw [contractAt_left _ _ _ _ p hlt, contractAt_left _ _ _ _ q hlt']
    have hadj_orig : adj ((p.1, ⟨p.2.val, by have := p.2.isLt; omega⟩) : Cell m n)
        (q.1, ⟨q.2.val, by have := q.2.isLt; omega⟩) := by
      unfold adj gdist; simp only [Fin.val_mk]; omega
    exact hh _ _ hadj_orig
  · have hlt' : ¬ q.2.val < j.val := by omega
    rw [contractAt_right _ _ _ _ p hlt, contractAt_right _ _ _ _ q hlt']
    have hadj_orig : adj ((p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩) : Cell m n)
        (q.1, ⟨q.2.val + 1, by have := q.2.isLt; omega⟩) := by
      unfold adj gdist; simp only [Fin.val_mk]; omega
    have hh_val := hh _ _ hadj_orig
    have hcancel : (h (p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩)
        - frozenSlope h hm j ⟨hj0, hj1, ‹_›⟩)
        - (h (q.1, ⟨q.2.val + 1, by have := q.2.isLt; omega⟩)
            - frozenSlope h hm j ⟨hj0, hj1, ‹_›⟩)
      = h (p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩)
        - h (q.1, ⟨q.2.val + 1, by have := q.2.isLt; omega⟩) := by ring
    rw [hcancel]
    exact hh_val

theorem contractAt_isHeight_horizontal_bothLeft
    (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p q : Cell m (n - 1))
    (hp1v : p.1.val = q.1.val) (hlt_p : p.2.val < j.val) (hlt_q : q.2.val < j.val)
    (hadj : adj p q) :
    |contractAt h hm j hfrz p - contractAt h hm j hfrz q| = 1 := by
  obtain ⟨hj0, hj1, _⟩ := hfrz
  unfold adj gdist at hadj
  have hsum : ((p.1.val : ℤ) - q.1.val).natAbs + ((p.2.val : ℤ) - q.2.val).natAbs = 1 := by
    exact_mod_cast hadj
  rw [contractAt_left _ _ _ _ p hlt_p, contractAt_left _ _ _ _ q hlt_q]
  have hadj_orig : adj ((p.1, ⟨p.2.val, by have := p.2.isLt; omega⟩) : Cell m n)
      (q.1, ⟨q.2.val, by have := q.2.isLt; omega⟩) := by
    unfold adj gdist; simp only [Fin.val_mk]; omega
  exact hh _ _ hadj_orig

theorem contractAt_isHeight_horizontal_bothRight
    (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p q : Cell m (n - 1))
    (hp1v : p.1.val = q.1.val) (hlt_p : ¬ p.2.val < j.val) (hlt_q : ¬ q.2.val < j.val)
    (hadj : adj p q) :
    |contractAt h hm j hfrz p - contractAt h hm j hfrz q| = 1 := by
  obtain ⟨hj0, hj1, _⟩ := hfrz
  unfold adj gdist at hadj
  have hsum : ((p.1.val : ℤ) - q.1.val).natAbs + ((p.2.val : ℤ) - q.2.val).natAbs = 1 := by
    exact_mod_cast hadj
  rw [contractAt_right _ _ _ _ p hlt_p, contractAt_right _ _ _ _ q hlt_q]
  have hadj_orig : adj ((p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩) : Cell m n)
      (q.1, ⟨q.2.val + 1, by have := q.2.isLt; omega⟩) := by
    unfold adj gdist; simp only [Fin.val_mk]; omega
  have hh_val := hh _ _ hadj_orig
  have hcancel : (h (p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩)
      - frozenSlope h hm j ⟨hj0, hj1, ‹_›⟩)
      - (h (q.1, ⟨q.2.val + 1, by have := q.2.isLt; omega⟩)
          - frozenSlope h hm j ⟨hj0, hj1, ‹_›⟩)
    = h (p.1, ⟨p.2.val + 1, by have := p.2.isLt; omega⟩)
      - h (q.1, ⟨q.2.val + 1, by have := q.2.isLt; omega⟩) := by ring
  rw [hcancel]
  exact hh_val

theorem contractAt_isHeight_horizontal_boundary_pLqR
    (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p q : Cell m (n - 1))
    (hp1eq : p.1 = q.1) (hlt_p : p.2.val < j.val) (hlt_q : ¬ q.2.val < j.val)
    (hadj : adj p q) :
    |contractAt h hm j hfrz p - contractAt h hm j hfrz q| = 1 := by
  obtain ⟨hj0, hj1, hsym⟩ := hfrz
  unfold adj gdist at hadj
  have hp1v : p.1.val = q.1.val := congrArg Fin.val hp1eq
  have hsum : ((p.1.val : ℤ) - q.1.val).natAbs + ((p.2.val : ℤ) - q.2.val).natAbs = 1 := by
    exact_mod_cast hadj
  have hcolabs : ((p.2.val : ℤ) - q.2.val).natAbs = 1 := by omega
  have hq2eqj : q.2.val = j.val := by
    have := Int.natAbs_eq_iff.mp hcolabs; omega
  have hp2eqj : p.2.val = j.val - 1 := by omega
  set k : ℤ := frozenSlope h hm j ⟨hj0, hj1, hsym⟩ with hkdef
  have hsl := frozenSlope_eq h hh hm j ⟨hj0, hj1, hsym⟩ q.1
  have hsy := hsym q.1
  rw [contractAt_left _ _ _ _ p hlt_p, contractAt_right _ _ _ _ q hlt_q]
  have hp2fin : (⟨p.2.val, by have := p.2.isLt; omega⟩ : Fin n)
      = ⟨j.val - 1, by omega⟩ := Fin.ext (by simp [hp2eqj])
  have hq2fin : (⟨q.2.val + 1, by have := q.2.isLt; omega⟩ : Fin n)
      = ⟨j.val + 1, hj1⟩ := Fin.ext (by simp [hq2eqj])
  rw [hp2fin, hq2fin, hp1eq]
  have hval : h (q.1, ⟨j.val - 1, by omega⟩)
      - (h (q.1, ⟨j.val + 1, hj1⟩) - k) = -k := by
    have hsl_norm : h (q.1, j) - h (q.1, ⟨j.val - 1, by omega⟩) = k := hsl
    linarith
  rw [hval]
  have hk_pm : k = 1 ∨ k = -1 := frozenSlope_pm h hh hm j ⟨hj0, hj1, hsym⟩
  rcases hk_pm with hk1 | hk1
  · show |(-k : ℤ)| = 1; rw [hk1]; decide
  · show |(-k : ℤ)| = 1; rw [hk1]; decide

theorem contractAt_isHeight_horizontal_boundary_pRqL
    (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p q : Cell m (n - 1))
    (hp1eq : p.1 = q.1) (hlt_p : ¬ p.2.val < j.val) (hlt_q : q.2.val < j.val)
    (hadj : adj p q) :
    |contractAt h hm j hfrz p - contractAt h hm j hfrz q| = 1 := by
  have hadj' : adj q p := by unfold adj gdist at hadj ⊢; omega
  have :=
    contractAt_isHeight_horizontal_boundary_pLqR h hh hm j hfrz q p
      hp1eq.symm hlt_q hlt_p hadj'
  rw [abs_sub_comm]; exact this

theorem contractAt_isHeight_horizontal (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) (p q : Cell m (n - 1))
    (hp1eq : p.1 = q.1) (hadj : adj p q) :
    |contractAt h hm j hfrz p - contractAt h hm j hfrz q| = 1 := by
  have hp1v : p.1.val = q.1.val := congrArg Fin.val hp1eq
  by_cases hlt_p : p.2.val < j.val
  · by_cases hlt_q : q.2.val < j.val
    · exact contractAt_isHeight_horizontal_bothLeft h hh hm j hfrz p q hp1v hlt_p hlt_q hadj
    · exact contractAt_isHeight_horizontal_boundary_pLqR h hh hm j hfrz p q hp1eq hlt_p hlt_q hadj
  · by_cases hlt_q : q.2.val < j.val
    · exact contractAt_isHeight_horizontal_boundary_pRqL h hh hm j hfrz p q hp1eq hlt_p hlt_q hadj
    · exact contractAt_isHeight_horizontal_bothRight h hh hm j hfrz p q hp1v hlt_p hlt_q hadj

theorem contractAt_isHeight (h : Cell m n → ℤ) (hh : IsHeight h) (hm : 0 < m)
    (j : Fin n) (hfrz : frozenColumn h j) :
    IsHeight (contractAt h hm j hfrz) := by
  intro p q hpq
  have hadj_copy := hpq
  unfold adj gdist at hpq
  have hsum : ((p.1.val : ℤ) - q.1.val).natAbs + ((p.2.val : ℤ) - q.2.val).natAbs = 1 := by
    exact_mod_cast hpq
  rcases Nat.eq_zero_or_pos ((p.1.val : ℤ) - q.1.val).natAbs with hr0 | _
  · have hp1v : p.1.val = q.1.val := by
      have : (p.1.val : ℤ) - q.1.val = 0 := by
        have := Int.natAbs_eq_zero.mp hr0; omega
      have h1 := p.1.isLt; have h2 := q.1.isLt; omega
    have hp1eq : p.1 = q.1 := Fin.ext hp1v
    exact contractAt_isHeight_horizontal h hh hm j hfrz p q hp1eq hadj_copy
  · have hp2v : p.2.val = q.2.val := by
      have hcabs : ((p.2.val : ℤ) - q.2.val).natAbs = 0 := by omega
      have : (p.2.val : ℤ) - q.2.val = 0 := by
        have := Int.natAbs_eq_zero.mp hcabs; omega
      have h1 := p.2.isLt; have h2 := q.2.isLt; omega
    exact contractAt_isHeight_vertical h hh hm j hfrz p q hp2v hadj_copy

end

end D5.S3.Combinatorics.Geometry.MiuraCoreContract
