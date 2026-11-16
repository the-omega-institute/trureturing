/- GID: D5/S1/Dynamics/Symbolic/KhetanSixCellResidue
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: Abstract residue propagation for the six-cell Nivat boundary. -/

import Mathlib

/-! This file isolates the residue propagation mechanism behind the six-cell
Nivat boundary. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanSixCellResidue

/-! The Boolean core used by the column argument. -/

private lemma xor_middle {p q s c : Prop}
    (hp : Xor p q ↔ c) (hs : Xor q s ↔ c) : p ↔ s := by
  by_cases hc : c
  · have hp' := hp.mpr hc
    have hs' := hs.mpr hc
    by_cases pp : p <;> by_cases qq : q <;> by_cases ss : s <;> simp_all [Xor]
  · have hp' : ¬ Xor p q := by
      intro h
      exact hc (hp.mp h)
    have hs' : ¬ Xor q s := by
      intro h
      exact hc (hs.mp h)
    by_cases pp : p <;> by_cases qq : q <;> by_cases ss : s <;> simp_all [Xor]

private lemma xor_cancel_left {p q p' q' c : Prop}
    (hpp : p ↔ p') (hp : Xor p q ↔ c) (hp' : Xor p' q' ↔ c) : q ↔ q' := by
  have hpp' : p = p' := propext hpp
  subst p'
  by_cases hc : c
  · have h₁ := hp.mpr hc
    have h₂ := hp'.mpr hc
    by_cases pp : p <;> by_cases qq : q <;> by_cases qq' : q' <;> simp_all [Xor]
  · have h₁ : ¬ Xor p q := by
      intro h
      exact hc (hp.mp h)
    have h₂ : ¬ Xor p q' := by
      intro h
      exact hc (hp'.mp h)
    by_cases pp : p <;> by_cases qq : q <;> by_cases qq' : q' <;> simp_all [Xor]

private lemma xor_cancel_right {p q p' q' c : Prop}
    (hqq : q ↔ q') (hp : Xor p q ↔ c) (hp' : Xor p' q' ↔ c) : p ↔ p' := by
  have hqq' : q = q' := propext hqq
  subst q'
  by_cases hc : c
  · have h₁ := hp.mpr hc
    have h₂ := hp'.mpr hc
    by_cases pp : p <;> by_cases pp' : p' <;> by_cases qq : q <;> simp_all [Xor]
  · have h₁ : ¬ Xor p q := by
      intro h
      exact hc (hp.mp h)
    have h₂ : ¬ Xor p' q := by
      intro h
      exact hc (hp'.mp h)
    by_cases pp : p <;> by_cases pp' : p' <;> by_cases qq : q <;> simp_all [Xor]

private def PeriodicColumn (T : ℤ → ℤ → Prop) (x : ℤ) : Prop :=
  ∀ y : ℤ, T x (y + 3) ↔ T x y

private def EmptyColumn (T : ℤ → ℤ → Prop) (x : ℤ) : Prop :=
  ∀ y : ℤ, ¬ T x y

/-! If the two adjacent-column partitions use different residue classes, the
middle column is empty. This is the local obstruction that starts propagation. -/
private lemma empty_of_residue_change
    (T : ℤ → ℤ → Prop) (r : ℤ → ℤ) (k : ℤ)
    (hpart : ∀ x y : ℤ,
      Xor (T (x - 1) y) (T x y) ↔ y % 3 = r x % 3)
    (hdisj : ∀ x y : ℤ, ¬ (T (x - 1) y ∧ T x y))
    (hchange : r k % 3 ≠ r (k + 1) % 3) :
    EmptyColumn T k := by
  intro y hy
  have hxork : Xor (T (k - 1) y) (T k y) := by
    exact Or.inr ⟨hy, fun hleft => hdisj k y ⟨hleft, hy⟩⟩
  have hleft := (hpart k y).mp hxork
  have hy' : T ((k + 1) - 1) y := by
    simpa only [Int.add_sub_cancel] using hy
  have hxork1 : Xor (T ((k + 1) - 1) y) (T (k + 1) y) := by
    exact Or.inl ⟨hy', fun hright => hdisj (k + 1) y ⟨hy', hright⟩⟩
  have hright := (hpart (k + 1) y).mp hxork1
  exact hchange (hleft.symm.trans hright)

/-! A 3-periodic column propagates one step to either side through the XOR
column equations. -/
private lemma periodic_step_right
    (T : ℤ → ℤ → Prop) (r : ℤ → ℤ) (x : ℤ)
    (hpart : ∀ x y : ℤ,
      Xor (T (x - 1) y) (T x y) ↔ y % 3 = r x % 3)
    (hper : PeriodicColumn T x) :
    PeriodicColumn T (x + 1) := by
  intro y
  have hshift : (y + 3) % 3 = y % 3 := by omega
  have h₁ : Xor (T x (y + 3)) (T (x + 1) (y + 3)) ↔
      (y + 3) % 3 = r (x + 1) % 3 := by
    convert hpart (x + 1) (y + 3) using 1 <;> ring
  have h₂ : Xor (T x y) (T (x + 1) y) ↔ y % 3 = r (x + 1) % 3 := by
    convert hpart (x + 1) y using 1 <;> ring
  rw [hshift] at h₁
  have hx : Xor (T x (y + 3)) (T (x + 1) (y + 3)) ↔
      Xor (T x y) (T (x + 1) y) := h₁.trans h₂.symm
  exact xor_cancel_left (hper y) hx (Iff.rfl)

private lemma periodic_step_left
    (T : ℤ → ℤ → Prop) (r : ℤ → ℤ) (x : ℤ)
    (hpart : ∀ x y : ℤ,
      Xor (T (x - 1) y) (T x y) ↔ y % 3 = r x % 3)
    (hper : PeriodicColumn T x) :
    PeriodicColumn T (x - 1) := by
  intro y
  have hshift : (y + 3) % 3 = y % 3 := by omega
  have h₁ : Xor (T (x - 1) (y + 3)) (T x (y + 3)) ↔
      (y + 3) % 3 = r x % 3 := by
    simpa only using hpart x (y + 3)
  have h₂ : Xor (T (x - 1) y) (T x y) ↔ y % 3 = r x % 3 := hpart x y
  rw [hshift] at h₁
  have hx : Xor (T (x - 1) (y + 3)) (T x (y + 3)) ↔
      Xor (T (x - 1) y) (T x y) := h₁.trans h₂.symm
  exact xor_cancel_right (hper y) hx (Iff.rfl)

/-! The abstract dichotomy. The only input is the exact residue partition of
 each adjacent pair of columns; the one-dimensional Newman/Fourier theorem is
 deliberately a separate dependency. -/
theorem three_residue_column_dichotomy
    (T : ℤ → ℤ → Prop) (r : ℤ → ℤ)
    (hpart : ∀ x y : ℤ,
      Xor (T (x - 1) y) (T x y) ↔ y % 3 = r x % 3)
    (hdisj : ∀ x y : ℤ, ¬ (T (x - 1) y ∧ T x y)) :
    (∀ x y : ℤ, T (x + 2) y ↔ T x y) ∨
      (∀ x y : ℤ, T x (y + 3) ↔ T x y) := by
  by_cases hconst : ∀ x : ℤ, r x % 3 = r (x + 1) % 3
  · left
    intro x y
    have h₁ : Xor (T x y) (T (x + 1) y) ↔ y % 3 = r (x + 1) % 3 := by
      convert hpart (x + 1) y using 1 <;> ring
    have h₂ : Xor (T (x + 1) y) (T (x + 2) y) ↔ y % 3 = r (x + 2) % 3 := by
      convert hpart (x + 2) y using 1 <;> ring
    have hr : r (x + 2) % 3 = r (x + 1) % 3 := by
      convert (hconst (x + 1)).symm using 1 <;> ring
    rw [hr] at h₂
    exact (xor_middle h₁ h₂).symm
  · right
    obtain ⟨k, hk⟩ := not_forall.mp hconst
    have hzero : EmptyColumn T k := empty_of_residue_change T r k hpart hdisj hk
    have hper_offset : ∀ n : ℤ, PeriodicColumn T (k + n) := by
      intro n
      induction n using Int.induction_on with
      | zero =>
          have hz : PeriodicColumn T k := by
            intro y
            constructor <;> intro hy
            · exact (hzero (y + 3) hy).elim
            · exact (hzero y hy).elim
          simpa only [add_zero] using hz
      | succ n ih =>
          simpa [add_assoc, add_comm, add_left_comm] using
            periodic_step_right T r (k + n) hpart ih
      | pred n ih =>
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
            periodic_step_left T r (k - n) hpart ih
    have hper : ∀ x : ℤ, PeriodicColumn T x := by
      intro x
      simpa [sub_add_cancel] using hper_offset (x - k)
    intro x y
    exact hper x y

end D5.S1.Dynamics.Symbolic.KhetanSixCellResidue
