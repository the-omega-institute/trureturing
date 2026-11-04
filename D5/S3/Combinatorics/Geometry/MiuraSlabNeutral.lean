/- GID: D5/S3/Combinatorics/Geometry/MiuraSlabNeutral
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/MiuraSlabNeutral
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: An occupied internal interval with equal cut slopes has both extrema. -/

module

public import D5.S3.Combinatorics.Geometry.MiuraSlabExtrema

/-! Both signs of neutral-strip forcing, on the same actual ambient array. -/

@[expose] public section

namespace D5.S3.Combinatorics.Geometry.MiuraSlabNeutral

open MiuraHeightEnvelope MiuraStripRigidity MiuraSlabExtrema

variable {m n : ℕ}

/-- A row is occupied when it contains an ambient minimum or maximum. -/
def RowOccupied (h : Cell m n → ℤ) (i : Fin m) : Prop :=
  ∃ j, IsStrictLocalMin h (i, j) ∨ IsStrictLocalMax h (i, j)

/-- Both cuts of an internal row interval have the same downward slope.
The quantifiers range over the actual full-width cuts of the given array. -/
def EqualRowCuts (h : Cell m n → ℤ) (I : Interval m) (s : ℤ) : Prop :=
  ∃ (ht : 0 < I.first.val) (hb : I.last.val + 1 < m),
    (∀ j : Fin n, h (I.first, j) = h (⟨I.first.val - 1, by omega⟩, j) + s) ∧
    (∀ j : Fin n, h (⟨I.last.val + 1, hb⟩, j) = h (I.last, j) + s)

private theorem increasing_interval_maximum {h : Cell m n → ℤ} (hh : IsHeight h)
    (I : Interval m) (hc : EqualRowCuts h I 1)
    (ho : ∃ i, I.Contains i ∧ RowOccupied h i) :
    ∃ v : Cell m n, I.Contains v.1 ∧ IsStrictLocalMax h v := by
  obtain ⟨ht, hb, htop, _⟩ := hc
  let p := I.first.val
  let r := I.last.val + 2 - p
  have hp : 0 < p := ht
  have hr : 1 ≤ r := by have := I.ordered; simp only [Fin.le_def] at this; dsimp [r, p]; omega
  have hpr : p + r ≤ m := by have := I.ordered; simp only [Fin.le_def] at this; dsimp [r, p]; omega
  have hstrip : ∀ (v : Cell r n) (u : Cell m n),
      adj (stripMap p r hpr v) u → u.1.val < p →
      h u = h (stripMap p r hpr v) - 1 := by
    intro v u hadj hlow
    have hdist := hadj
    simp only [adj, gdist, stripMap, Fin.val_mk] at hdist
    have hu : u.1.val = p - 1 := by omega
    have hv : v.1.val = 0 := by omega
    have hj : u.2 = v.2 := by
      apply Fin.ext
      omega
    have hrow : u.1 = (⟨I.first.val - 1, by omega⟩ : Fin m) := Fin.ext hu
    have hrowv : (stripMap p r hpr v).1 = I.first := by
      apply Fin.ext
      simp only [stripMap, Fin.val_mk]
      dsimp [p]
      omega
    have he := htop v.2
    have hvcell : stripMap p r hpr v = (I.first, v.2) := Prod.ext hrowv rfl
    have hucell : u = ((⟨I.first.val - 1, by omega⟩ : Fin m), v.2) :=
      Prod.ext hrow hj
    rw [hvcell, hucell]
    omega
  have hocc : ∃ v : Cell r n, v.1.val + 1 < r ∧
      (IsStrictLocalMax h (stripMap p r hpr v) ∨
       IsStrictLocalMin h (stripMap p r hpr v)) := by
    obtain ⟨i, hi, j, hj⟩ := ho
    have hi' : p ≤ i.val ∧ i.val ≤ I.last.val := hi
    let v : Cell r n := (⟨i.val - p, by dsimp [r]; omega⟩, j)
    have hv : stripMap p r hpr v = (i, j) := by
      apply Prod.ext
      · apply Fin.ext
        simp only [stripMap, v, Fin.val_mk]
        omega
      · rfl
    refine ⟨v, ?_, ?_⟩
    · dsimp [v, r]
      omega
    · rw [hv]
      exact hj.symm
  obtain ⟨v, hv, hmax⟩ := occupied_internal_strip_has_maximum hh p r hp hr hpr hstrip hocc
  refine ⟨stripMap p r hpr v, ?_, hmax⟩
  change I.first.val ≤ p + v.1.val ∧ p + v.1.val ≤ I.last.val
  dsimp [p, r] at *
  omega

private def revCell (v : Cell m n) : Cell m n := (v.1.rev, v.2)

private theorem revCell_involutive (v : Cell m n) : revCell (revCell v) = v := by
  simp [revCell]

private theorem revCell_adj (v u : Cell m n) : adj (revCell v) (revCell u) ↔ adj v u := by
  simp only [adj, gdist, revCell, Fin.val_rev]
  have := v.1.isLt
  have := u.1.isLt
  omega

private theorem increasing_interval_minimum {h : Cell m n → ℤ} (hh : IsHeight h)
    (I : Interval m) (hc : EqualRowCuts h I 1)
    (ho : ∃ i, I.Contains i ∧ RowOccupied h i) :
    ∃ v : Cell m n, I.Contains v.1 ∧ IsStrictLocalMin h v := by
  obtain ⟨ht, hb, htop, hbottom⟩ := hc
  let g : Cell m n → ℤ := fun v => -h (revCell v)
  let J : Interval m := ⟨I.last.rev, I.first.rev, by
    simp only [Fin.le_def, Fin.val_rev]
    have := I.ordered
    simp only [Fin.le_def] at this
    omega⟩
  have hg : IsHeight g := by
    intro v u hadj
    have he := hh (revCell v) (revCell u) ((revCell_adj v u).mpr hadj)
    simpa only [g, neg_sub_neg, abs_sub_comm] using he
  have htJ : 0 < J.first.val := by dsimp [J]; omega
  have hbJ : J.last.val + 1 < m := by
    dsimp [J]
    have := I.first.isLt
    omega
  have hcJ : EqualRowCuts g J 1 := by
    refine ⟨htJ, hbJ, ?_, ?_⟩
    · intro j
      have he := hbottom j
      have hfirst : revCell (J.first, j) = (I.last, j) := by simp [revCell, J]
      have hprev : revCell ((⟨J.first.val - 1, by omega⟩ : Fin m), j) =
          ((⟨I.last.val + 1, hb⟩ : Fin m), j) := by
        apply Prod.ext
        · apply Fin.ext
          simp only [revCell, J, Fin.val_rev]
          have := I.last.isLt
          omega
        · rfl
      change -h (revCell (J.first, j)) = -h (revCell (⟨J.first.val - 1, _⟩, j)) + 1
      rw [hfirst, hprev]
      omega
    · intro j
      have he := htop j
      have hlast : revCell (J.last, j) = (I.first, j) := by simp [revCell, J]
      have hnext : revCell ((⟨J.last.val + 1, hbJ⟩ : Fin m), j) =
          ((⟨I.first.val - 1, by omega⟩ : Fin m), j) := by
        apply Prod.ext
        · apply Fin.ext
          simp only [revCell, J, Fin.val_rev]
          have := I.first.isLt
          omega
        · rfl
      change -h (revCell (⟨J.last.val + 1, _⟩, j)) = -h (revCell (J.last, j)) + 1
      rw [hnext, hlast]
      omega
  have hoJ : ∃ i, J.Contains i ∧ RowOccupied g i := by
    obtain ⟨i, hi, j, hj⟩ := ho
    refine ⟨i.rev, ?_, j, ?_⟩
    · change I.last.rev ≤ i.rev ∧ i.rev ≤ I.first.rev
      simp only [Fin.le_def, Fin.val_rev]
      change I.first.val ≤ i.val ∧ i.val ≤ I.last.val at hi
      have := i.isLt
      have := I.first.isLt
      have := I.last.isLt
      omega
    · rcases hj with hmin | hmax
      · right
        intro u hu
        have he := hmin (revCell u) (by
          simpa only [revCell, Fin.rev_rev] using (revCell_adj (i.rev, j) u).mpr hu)
        dsimp [g, revCell] at *
        simp only [Fin.rev_rev] at *
        omega
      · left
        intro u hu
        have he := hmax (revCell u) (by
          simpa only [revCell, Fin.rev_rev] using (revCell_adj (i.rev, j) u).mpr hu)
        dsimp [g, revCell] at *
        simp only [Fin.rev_rev] at *
        omega
  obtain ⟨v, hv, hmax⟩ := increasing_interval_maximum hg J hcJ hoJ
  refine ⟨revCell v, ?_, ?_⟩
  · change I.first.val ≤ m - (v.1.val + 1) ∧ m - (v.1.val + 1) ≤ I.last.val
    change I.last.rev ≤ v.1 ∧ v.1 ≤ I.first.rev at hv
    simp only [Fin.le_def, Fin.val_rev] at hv
    have := v.1.isLt
    have := I.first.isLt
    have := I.last.isLt
    omega
  · intro u hu
    have he := hmax (revCell u) (by
      rw [← revCell_involutive v]
      exact (revCell_adj (revCell v) u).mpr hu)
    dsimp [g] at he
    rw [revCell_involutive] at he
    omega

/-- A nonempty occupied internal row interval between equal signed cuts has
an ambient minimum and an ambient maximum. Both signs are covered. -/
theorem neutral_row_has_both {h : Cell m n → ℤ} (hh : IsHeight h)
    (I : Interval m) (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hc : EqualRowCuts h I s)
    (ho : ∃ i, I.Contains i ∧ RowOccupied h i) :
    (∃ v : Cell m n, I.Contains v.1 ∧ IsStrictLocalMin h v) ∧
    (∃ v : Cell m n, I.Contains v.1 ∧ IsStrictLocalMax h v) := by
  rcases hs with rfl | rfl
  · exact ⟨increasing_interval_minimum hh I hc ho, increasing_interval_maximum hh I hc ho⟩
  · let g : Cell m n → ℤ := fun v => -h v
    have hg : IsHeight g := by
      intro v u hadj
      have he := hh v u hadj
      simpa only [g, neg_sub_neg, abs_sub_comm] using he
    obtain ⟨ht, hb, htop, hbottom⟩ := hc
    have hc' : EqualRowCuts g I 1 := by
      refine ⟨ht, hb, ?_, ?_⟩ <;> intro j
      · have := htop j; dsimp [g]; omega
      · have := hbottom j; dsimp [g]; omega
    have ho' : ∃ i, I.Contains i ∧ RowOccupied g i := by
      obtain ⟨i, hi, j, hj⟩ := ho
      refine ⟨i, hi, j, ?_⟩
      rcases hj with hmin | hmax
      · right; intro u hu; have := hmin u hu; dsimp [g]; omega
      · left; intro u hu; have := hmax u hu; dsimp [g]; omega
    obtain ⟨v, hv, hmin⟩ := increasing_interval_minimum hg I hc' ho'
    obtain ⟨w, hw, hmax⟩ := increasing_interval_maximum hg I hc' ho'
    constructor
    · refine ⟨w, hw, ?_⟩
      intro u hu; have := hmax u hu; dsimp [g] at this; omega
    · refine ⟨v, hv, ?_⟩
      intro u hu; have := hmin u hu; dsimp [g] at this; omega

end D5.S3.Combinatorics.Geometry.MiuraSlabNeutral
