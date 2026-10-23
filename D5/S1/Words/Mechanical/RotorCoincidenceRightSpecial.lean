/- GID: D5/S1/Words/Mechanical/RotorCoincidenceRightSpecial
   generality: I
   mirror-B: D5/B/S1/Words/Mechanical/RotorCoincidenceRightSpecial
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The unique right-special rotor factor is the reversed prefix after the initial zero. -/
import D5.S1.Words.Mechanical.MechanicalRightSpecial

/-! Right-special factors of the separator encoding of an irrational cutting sequence. -/

namespace D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial

noncomputable def cutting (σ : ℝ) (m : ℕ) : ℕ := by
  classical
  exact if ∃ k : ℕ, 1 ≤ k ∧ m = ⌊(k : ℝ) * σ⌋₊ + k then 3 else 1

noncomputable def rotor (σ : ℝ) (m : ℕ) : ℕ :=
  if m = 0 then 0 else if m % 2 = 1 then 2 else cutting σ (m / 2)

def IsFactor (R : ℕ → ℕ) (w : List ℕ) : Prop :=
  ∃ i, ∀ t : ℕ, ∀ h : t < w.length, R (i + t) = w[t]

def IsRightSpecial (R : ℕ → ℕ) (w : List ℕ) : Prop :=
  ∃ a b : ℕ, a ≠ b ∧ IsFactor R (w ++ [a]) ∧ IsFactor R (w ++ [b])

def claim : Prop :=
  ∀ σ : ℝ, Irrational σ → 1 < σ → ∀ n : ℕ, 2 ≤ n →
    ∀ w : List ℕ, w.length = n - 1 →
      (IsRightSpecial (rotor σ) w ↔
        w = (List.ofFn (fun t : Fin (n - 1) => rotor σ (t + 1))).reverse)

private theorem beatty_jump {d : ℝ} (hd : 1 < d) (hi : Irrational d)
    (m : ℕ) :
    (∃ k : ℕ, 1 ≤ k ∧ m = ⌊(k : ℝ) * d⌋₊) ↔
      ⌊((m : ℝ) + 1) / d⌋ - ⌊(m : ℝ) / d⌋ = (1 : ℤ) := by
  have hd0 : 0 < d := by linarith
  have hstep : 1 / d < 1 := (div_lt_one hd0).mpr hd
  have hdiff : ((m : ℝ) + 1) / d = (m : ℝ) / d + 1 / d := by ring
  constructor
  · rintro ⟨k, hk, hm⟩
    have hk0 : 0 ≤ (k : ℝ) * d := mul_nonneg (Nat.cast_nonneg _) hd0.le
    have hlo := Nat.floor_le hk0
    have hhi := Nat.lt_floor_add_one ((k : ℝ) * d)
    rw [← hm] at hlo hhi
    have hstrict : (m : ℝ) < (k : ℝ) * d := by
      refine lt_of_le_of_ne hlo ?_
      intro heq
      exact (hi.natCast_mul (by omega : k ≠ 0)).ne_int m (by simpa using heq.symm)
    have hx : (m : ℝ) / d < k := (div_lt_iff₀ hd0).mpr hstrict
    have hy : (k : ℝ) < ((m : ℝ) + 1) / d := (lt_div_iff₀ hd0).mpr hhi
    have hfx : ⌊(m : ℝ) / d⌋ = (k : ℤ) - 1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    have hfy : ⌊((m : ℝ) + 1) / d⌋ = (k : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · exact hy.le
      · push_cast
        linarith
    rw [hfx, hfy]
    omega
  · intro h
    let z : ℤ := ⌊((m : ℝ) + 1) / d⌋
    have hz : 0 < z := by
      have hx0 : 0 ≤ ⌊(m : ℝ) / d⌋ :=
        Int.floor_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) hd0.le)
      dsimp [z]
      omega
    let k := z.toNat
    have hkz : (k : ℤ) = z := Int.toNat_of_nonneg hz.le
    have hk : 1 ≤ k := by omega
    have hy : (k : ℝ) * d ≤ (m : ℝ) + 1 := by
      apply (le_div_iff₀ hd0).mp
      have hf := Int.floor_le (((m : ℝ) + 1) / d)
      have hkreal : (k : ℝ) = (z : ℝ) := by exact_mod_cast hkz
      rw [hkreal]
      exact hf
    have hx : (m : ℝ) < (k : ℝ) * d := by
      apply (div_lt_iff₀ hd0).mp
      have hf := Int.lt_floor_add_one ((m : ℝ) / d)
      have hh : ⌊(m : ℝ) / d⌋ + 1 = (k : ℤ) := by dsimp [z] at hkz; omega
      rw [← Int.cast_one, ← Int.cast_add, hh, Int.cast_natCast] at hf
      exact hf
    have hy' : (k : ℝ) * d < (m : ℝ) + 1 := by
      refine lt_of_le_of_ne hy ?_
      intro heq
      exact (hi.natCast_mul (by omega : k ≠ 0)).ne_int (m + 1) (by
        push_cast
        exact heq)
    refine ⟨k, hk, (Nat.floor_eq_iff (by positivity)).mpr ⟨hx.le, hy'⟩ |>.symm⟩

private theorem cutting_mechanical {σ : ℝ} (hσ : Irrational σ) (hσ1 : 1 < σ)
    (j : ℕ) :
    cutting σ (j + 1) =
      if lowerMechanicalWord (1 / (σ + 1)) (1 / (σ + 1)) j then 3 else 1 := by
  classical
  have hi : Irrational (σ + 1) := by simpa using hσ.add_ratCast 1
  have he : (∃ k : ℕ, 1 ≤ k ∧ j + 1 = ⌊(k : ℝ) * σ⌋₊ + k) ↔
      lowerMechanicalWord (1 / (σ + 1)) (1 / (σ + 1)) j = true := by
    rw [lowerMechanicalWord_eq_true_iff]
    have hj := beatty_jump (by linarith : 1 < σ + 1) hi (j + 1)
    have hfloor (k : ℕ) : ⌊(k : ℝ) * (σ + 1)⌋₊ = ⌊(k : ℝ) * σ⌋₊ + k := by
      rw [mul_add, mul_one, Nat.floor_add_natCast (by positivity)]
    simp_rw [hfloor] at hj
    have hl : lowerMechanicalLetter (1 / (σ + 1)) (1 / (σ + 1)) j =
        ⌊(((j + 1 : ℕ) : ℝ) + 1) / (σ + 1)⌋ - ⌊((j + 1 : ℕ) : ℝ) / (σ + 1)⌋ := by
      unfold lowerMechanicalLetter
      congr 1 <;> congr 1 <;> push_cast <;> ring
    rw [hl]
    exact hj
  simp only [cutting, he]

private theorem mechanical_reverse_prefix_special {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hα : Irrational α) (m : ℕ) :
    MechanicalRightSpecial.IsLowerMechanicalRightSpecial α α m
      (lowerMechanicalFactor α α m 0).reverse := by
  sorry

private theorem rotor_special_unique {σ : ℝ} (hσ : Irrational σ) (hσ1 : 1 < σ)
    (hcut : ∀ j : ℕ, cutting σ (j + 1) =
      if lowerMechanicalWord (1 / (σ + 1)) (1 / (σ + 1)) j then 3 else 1)
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∀ u v : List ℕ, u.length = ℓ → v.length = ℓ →
      IsRightSpecial (rotor σ) u → IsRightSpecial (rotor σ) v → u = v := by
  sorry

private theorem rotor_reverse_prefix_special {σ : ℝ}
    (hσ : Irrational σ) (hσ1 : 1 < σ)
    (hcut : ∀ j : ℕ, cutting σ (j + 1) =
      if lowerMechanicalWord (1 / (σ + 1)) (1 / (σ + 1)) j then 3 else 1)
    (hrev : ∀ m : ℕ,
      MechanicalRightSpecial.IsLowerMechanicalRightSpecial
        (1 / (σ + 1)) (1 / (σ + 1)) m
        (lowerMechanicalFactor (1 / (σ + 1)) (1 / (σ + 1)) m 0).reverse)
    (ℓ : ℕ) (hℓ : 0 < ℓ) :
    IsRightSpecial (rotor σ)
      (List.ofFn (fun t : Fin ℓ => rotor σ (t + 1))).reverse := by
  sorry

theorem result : claim := by
  intro σ hσ hσ1 n hn w hw
  have hα0 : 0 < 1 / (σ + 1) := one_div_pos.mpr (by linarith)
  have hα1 : 1 / (σ + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hα : Irrational (1 / (σ + 1)) := by
    simpa using (hσ.add_ratCast 1).inv
  have hc := cutting_mechanical hσ hσ1
  have hr := mechanical_reverse_prefix_special hα0 hα1 hα
  have hs := rotor_reverse_prefix_special hσ hσ1 hc hr (n - 1) (by omega)
  constructor
  · intro h
    exact rotor_special_unique hσ hσ1 hc (n - 1) (by omega) w _ hw
      (by simp) h hs
  · rintro rfl
    exact hs

end D5.S1.Words.Mechanical.RotorCoincidenceRightSpecial
