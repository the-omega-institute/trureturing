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

private theorem cutting_mechanical {σ : ℝ} (hσ : Irrational σ) (hσ1 : 1 < σ)
    (j : ℕ) :
    cutting σ (j + 1) =
      if lowerMechanicalWord (1 / (σ + 1)) (1 / (σ + 1)) j then 3 else 1 := by
  sorry

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
