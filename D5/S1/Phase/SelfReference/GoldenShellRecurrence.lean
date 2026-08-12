/- GID: D5/S1/Phase/SelfReference/GoldenShellRecurrence
   generality: G
   mirror-B: D5/B/S1/Phase/SelfReference/GoldenShellRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden shell function s(n)=⌊(n+1)/φ⌋ satisfies the Hofstadter G self-referential recurrence s(n)=n−s(s(n−1)) for all n≥1 (equivalently the additive core s(m+1)+s(s(m))=m+1), so the Beatty golden shift and the classical Hofstadter G sequence (OEIS A005206) are the same function. Proved for all n by floor arithmetic and the irrationality of the golden slope, upgrading the observation's n≤10⁵ numerical check to a theorem. -/

import Mathlib

open Real

namespace D5.S1.Phase.SelfReference.GoldenShellRecurrence

/-- The **golden shell function** `s(n) = ⌊(n+1)/φ⌋`, the Zeckendorf/Beatty golden shift
(slope `1/φ ≈ 0.618`), which coincides with the classical Hofstadter G sequence (OEIS A005206). -/
noncomputable def g (n : ℕ) : ℕ := ⌊((n : ℝ) + 1) * goldenRatio⁻¹⌋₊

/-- Additive core of the recurrence: `s(m+1) + s(s(m)) = m+1`. -/
theorem golden_shell_core (m : ℕ) : g (m + 1) + g (g m) = m + 1 := by
  have hφpos : (0:ℝ) < goldenRatio := goldenRatio_pos
  have h1ltφ : (1:ℝ) < goldenRatio := one_lt_goldenRatio
  set τ := goldenRatio⁻¹ with hτ
  have hτpos : 0 < τ := inv_pos.mpr hφpos
  have hτlt1 : τ < 1 := inv_lt_one_of_one_lt₀ h1ltφ
  have hφsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have hτφ1 : τ * goldenRatio = 1 := inv_mul_cancel₀ (ne_of_gt hφpos)
  -- τ = φ - 1, hence the two golden relations
  have hτv : τ = goldenRatio - 1 := by
    have h : τ * goldenRatio = (goldenRatio - 1) * goldenRatio := by nlinarith [hτφ1, hφsq]
    exact mul_right_cancel₀ (ne_of_gt hφpos) h
  have hτsq : τ ^ 2 = 1 - τ := by rw [hτv]; linear_combination hφsq
  have h1τ : 1 + τ = goldenRatio := by rw [hτv]; ring
  clear_value τ
  have hτ1τ : τ * (1 + τ) = 1 := by rw [h1τ]; exact hτφ1
  -- the base real value x = (m+1)τ and its floor A = g m
  set x : ℝ := ((m : ℝ) + 1) * τ with hx
  have hxpos : 0 ≤ x := by positivity
  have hgm : g m = ⌊x⌋₊ := by simp [g, hτ, hx]
  set A : ℕ := ⌊x⌋₊ with hA
  have hAle : (A : ℝ) ≤ x := Nat.floor_le hxpos
  have hltA : x < (A : ℝ) + 1 := Nat.lt_floor_add_one x
  have hxm : x < (m : ℝ) + 1 := by rw [hx]; nlinarith [hτlt1, hτpos]
  have hAm : A ≤ m := by
    have hAr : (A : ℝ) < (m : ℝ) + 1 := lt_of_le_of_lt hAle hxm
    have hAlt : A < m + 1 := by exact_mod_cast hAr
    omega
  -- fractional part f = x - A ∈ [0,1)
  set f : ℝ := x - (A : ℝ) with hf
  have hf0 : 0 ≤ f := by rw [hf]; linarith
  have hf1 : f < 1 := by rw [hf]; linarith
  -- irrationality: (m+2)τ ≠ A+1, so f ≠ τ^2
  have hτirr : Irrational τ := by rw [hτ, inv_goldenRatio]; exact goldenConj_irrational.neg
  have hne : ((m : ℝ) + 2) * τ ≠ ((A : ℝ) + 1) := by
    have hirr : Irrational (((m + 2 : ℕ) : ℝ) * τ) := hτirr.natCast_mul (by omega)
    have := hirr.ne_nat (A + 1)
    push_cast at this ⊢
    intro hc; exact this (by linarith [hc])
  have hfne : f ≠ τ ^ 2 := by
    intro hc
    apply hne
    -- (m+2)τ = x + τ = A + f + τ = A + τ^2 + τ = A + 1
    have : ((m : ℝ) + 2) * τ = x + τ := by rw [hx]; ring
    rw [this]
    have hxaf : x = (A : ℝ) + f := by rw [hf]; ring
    rw [hxaf, hc]; linarith [hτsq]
  -- g(m+1) = ⌊x + τ⌋₊  and  g(gm)=g A = ⌊(A+1)τ⌋₊
  have hgm1 : g (m + 1) = ⌊x + τ⌋₊ := by
    simp only [g, ← hτ]; congr 1; rw [hx]; push_cast; ring
  have hgA : g A = ⌊((A : ℝ) + 1) * τ⌋₊ := by simp only [g, hτ]
  -- algebraic form of (A+1)τ
  have hAτ : ((A : ℝ) + 1) * τ = ((m : ℝ) + 1 - (A : ℝ)) + (τ - f * (1 + τ)) := by
    have hxaf : x = (A : ℝ) + f := by rw [hf]; ring
    -- A τ = (m+1) - x - f τ  from  x τ = (m+1)τ^2 = (m+1)(1-τ)
    have hxτ : x * τ = ((m : ℝ) + 1) * (1 - τ) := by rw [hx]; nlinarith [hτsq]
    nlinarith [hxτ, hxaf, hτsq]
  clear hφpos h1ltφ hφsq hτφ1 hτv h1τ hτirr hne
  clear_value x f A
  rw [hgm1, hgm, hgA]
  -- case split on f vs τ^2
  rcases lt_or_gt_of_ne hfne with hlt | hgt
  · -- f < τ^2 : g(m+1)=A, g A = m+1-A
    have e1 : ⌊x + τ⌋₊ = A := by
      rw [Nat.floor_eq_iff (by linarith [hxpos, hτpos])]
      constructor
      · have hxaf : x = (A : ℝ) + f := by rw [hf]; ring
        rw [hxaf]; linarith
      · have hxaf : x = (A : ℝ) + f := by rw [hf]; ring
        have : f + τ < 1 := by nlinarith [hlt, hτsq]
        rw [hxaf]; linarith
    have e2 : ⌊((A : ℝ) + 1) * τ⌋₊ = m + 1 - A := by
      rw [Nat.floor_eq_iff (mul_nonneg (by positivity) hτpos.le), hAτ]
      have hRpos : 0 ≤ τ - f * (1 + τ) := by
        have : f * (1 + τ) ≤ τ := by
          have h1τpos : 0 < 1 + τ := by linarith
          nlinarith [hlt, hτsq, hτ1τ]
        linarith
      have hRlt1 : τ - f * (1 + τ) < 1 := by nlinarith [hf0, hτlt1, hτpos]
      have hcast : ((m + 1 - A : ℕ) : ℝ) = (m : ℝ) + 1 - (A : ℝ) := by
        push_cast [Nat.cast_sub (by omega : A ≤ m + 1)]; ring
      rw [hcast]; constructor <;> linarith
    rw [e1, e2]; omega
  · -- f > τ^2 : g(m+1)=A+1, g A = m-A
    have e1 : ⌊x + τ⌋₊ = A + 1 := by
      rw [Nat.floor_eq_iff (by linarith [hxpos, hτpos])]
      have hxaf : x = (A : ℝ) + f := by rw [hf]; ring
      have hge : 1 ≤ f + τ := by nlinarith [hgt, hτsq]
      constructor
      · rw [hxaf]; push_cast; linarith
      · rw [hxaf]; push_cast; nlinarith [hf1, hτlt1]
    have e2 : ⌊((A : ℝ) + 1) * τ⌋₊ = m - A := by
      rw [Nat.floor_eq_iff (mul_nonneg (by positivity) hτpos.le), hAτ]
      have hRneg : τ - f * (1 + τ) < 0 := by
        have : τ < f * (1 + τ) := by
          have h1τpos : 0 < 1 + τ := by linarith
          nlinarith [hgt, hτsq, hτ1τ]
        linarith
      have hRge : (-1 : ℝ) ≤ τ - f * (1 + τ) := by
        have : f * (1 + τ) ≤ 1 + τ := by nlinarith [hf1, hτpos]
        nlinarith [this, hτpos]
      have hcast : ((m - A : ℕ) : ℝ) = (m : ℝ) - (A : ℝ) := by
        push_cast [Nat.cast_sub hAm]; ring
      rw [hcast]; constructor <;> linarith
    rw [e1, e2]
    omega

/-- **Golden shell Hofstadter recurrence (observation 6.157, part 一).** The golden shell function
`s(n) = ⌊(n+1)/φ⌋` satisfies the Hofstadter G self-referential recurrence `s(n) = n − s(s(n−1))`
for every `n ≥ 1` — i.e. the ledger's Beatty golden shift and Douglas Hofstadter's self-referential
G tree are one and the same function. Only this identity (part 一) is recorded; the separate MIU
`I mod 3 ∈ {1,2}` invariant of part 二 is not covered. -/
theorem golden_shell_recurrence (n : ℕ) (hn : 1 ≤ n) :
    g n = n - g (g (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := golden_shell_core m
  simp only [Nat.add_sub_cancel]
  omega

end D5.S1.Phase.SelfReference.GoldenShellRecurrence
