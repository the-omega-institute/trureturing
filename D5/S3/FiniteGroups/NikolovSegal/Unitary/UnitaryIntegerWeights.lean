/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryIntegerWeights
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryIntegerWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryExponentAvoidance

namespace NikolovSegal.UnitaryField

def positiveWeight (d : ℕ) (i : Fin d) : ℤ := i.val + 1
def weightSum (d : ℕ) : ℤ := ∑ i : Fin d, positiveWeight d i

theorem positiveWeight_bounds {d : ℕ} (i : Fin d) :
    1 ≤ positiveWeight d i ∧ positiveWeight d i ≤ d := by
  have h : (i.val : ℤ) < d := by exact_mod_cast i.isLt
  simp only [positiveWeight]
  omega

theorem weightSum_bounds (d : ℕ) : (d : ℤ) ≤ weightSum d ∧ weightSum d ≤ (d : ℤ)^2 := by
  constructor
  · calc
      (d : ℤ) = ∑ _i : Fin d, (1 : ℤ) := by simp
      _ ≤ weightSum d := Finset.sum_le_sum fun i _ => (positiveWeight_bounds i).1
  · calc
      weightSum d ≤ ∑ _i : Fin d, (d : ℤ) :=
        Finset.sum_le_sum fun i _ => (positiveWeight_bounds i).2
      _ = (d : ℤ)^2 := by simp [pow_two]

/- All even blocks of at least two pairs: distinct nonzero weights with total zero.
The final weight is the negative sum of the preceding positive weights. -/
def evenWeight (m : ℕ) : Fin (m + 2) → ℤ :=
  Fin.lastCases (-weightSum (m + 1)) (positiveWeight (m + 1))

theorem evenWeight_sum (m : ℕ) : ∑ i, evenWeight m i = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp [evenWeight, weightSum]

theorem evenWeight_nonzero (m : ℕ) (i : Fin (m + 2)) : evenWeight m i ≠ 0 := by
  have hS := (weightSum_bounds (m + 1)).1
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [evenWeight, Fin.lastCases_last]
    omega
  · simp only [evenWeight, Fin.lastCases_castSucc]
    have h := (positiveWeight_bounds j).1
    omega

theorem evenWeight_injective (m : ℕ) : Function.Injective (evenWeight m) := by
  intro i j
  have hS := (weightSum_bounds (m + 1)).1
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · simp only [evenWeight, Fin.lastCases_last, Fin.lastCases_castSucc]
    have h := (positiveWeight_bounds j).1
    omega
  · simp only [evenWeight, Fin.lastCases_last, Fin.lastCases_castSucc]
    have h := (positiveWeight_bounds i).1
    omega
  · simp only [evenWeight, Fin.lastCases_castSucc, positiveWeight]
    intro h
    have hval : i.val = j.val := by omega
    exact congrArg Fin.castSucc (Fin.ext hval)

theorem evenWeight_bound (m : ℕ) (i : Fin (m + 2)) :
    |evenWeight m i| ≤ ((m + 2 : ℕ) : ℤ)^2 := by
  have hS := weightSum_bounds (m + 1)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [evenWeight, Fin.lastCases_last, abs_neg]
    rw [abs_of_nonneg (by omega)]
    push_cast at hS ⊢
    nlinarith
  · simp only [evenWeight, Fin.lastCases_castSucc]
    have h := positiveWeight_bounds j
    rw [abs_of_nonneg (by omega)]
    push_cast at h ⊢
    nlinarith

def pairedExponent {d : ℕ} (Q : ℕ) (a : Fin d → ℤ) : (Fin d ⊕ Fin d) → ℤ
  | .inl i => a i
  | .inr i => -(Q : ℤ) * a i

def oddExponent {d : ℕ} (Q : ℕ) (a : Fin d → ℤ) : Option (Fin d ⊕ Fin d) → ℤ
  | none => ((Q : ℤ) - 1) * (∑ i, a i)
  | some i => pairedExponent Q a i

theorem mixed_weight_nonzero (Q B : ℕ) (hQ : B < Q) (x y : ℤ)
    (hx : |x| ≤ B) (hy : y ≠ 0) : x + (Q : ℤ) * y ≠ 0 := by
  intro h
  have hypos : 1 ≤ |y| := by have := abs_pos.mpr hy; omega
  have hQz : (B : ℤ) < Q := by exact_mod_cast hQ
  have hQ0 : 0 ≤ (Q : ℤ) := by positivity
  have he : x = -(Q : ℤ) * y := by linarith
  rw [he, abs_mul, abs_neg, abs_of_nonneg hQ0] at hx
  nlinarith

theorem pairedExponent_injective {d : ℕ} (Q B : ℕ) (hQ : B < Q)
    (a : Fin d → ℤ) (ha : Function.Injective a) (hn : ∀ i, a i ≠ 0)
    (hb : ∀ i, |a i| ≤ B) : Function.Injective (pairedExponent Q a) := by
  intro i j h
  have hQ0 : (Q : ℤ) ≠ 0 := by omega
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (ha h)
    | inr j =>
      have hh := mixed_weight_nonzero Q B hQ (a i) (a j) (hb i) (hn j)
      simp only [pairedExponent] at h
      exfalso; apply hh; linarith
  | inr i =>
    cases j with
    | inl j =>
      have hh := mixed_weight_nonzero Q B hQ (a j) (a i) (hb j) (hn i)
      simp only [pairedExponent] at h
      exfalso; apply hh; linarith
    | inr j =>
      simp only [pairedExponent] at h
      exact congrArg Sum.inr (ha (mul_left_cancel₀ (neg_ne_zero.mpr hQ0) h))

theorem odd_positiveExponent_injective {d : ℕ} (hd : 0 < d) (Q : ℕ) (hQ : 2 < Q) :
    Function.Injective (oddExponent Q (positiveWeight d)) := by
  have hS := weightSum_bounds d
  have hQz : (2 : ℤ) < Q := by exact_mod_cast hQ
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hp : Function.Injective (positiveWeight d) := by
    intro i j h
    apply Fin.ext
    simp only [positiveWeight] at h
    omega
  have hpair : Function.Injective (pairedExponent Q (positiveWeight d)) := by
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hp h)
      | inr j =>
        have h₁ := positiveWeight_bounds i; have h₂ := positiveWeight_bounds j
        change positiveWeight d i = -(Q : ℤ) * positiveWeight d j at h
        exfalso; nlinarith
    | inr i =>
      cases j with
      | inl j =>
        have h₁ := positiveWeight_bounds i; have h₂ := positiveWeight_bounds j
        change -(Q : ℤ) * positiveWeight d i = positiveWeight d j at h
        exfalso; nlinarith
      | inr j =>
        change -(Q : ℤ) * positiveWeight d i = -(Q : ℤ) * positiveWeight d j at h
        exact congrArg Sum.inr (hp (mul_left_cancel₀ (by omega : -(Q : ℤ) ≠ 0) h))
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some j =>
      cases j with
      | inl j =>
        have hj := positiveWeight_bounds j
        change ((Q : ℤ) - 1) * weightSum d = positiveWeight d j at h
        exfalso; nlinarith
      | inr j =>
        have hj := positiveWeight_bounds j
        change ((Q : ℤ) - 1) * weightSum d = -(Q : ℤ) * positiveWeight d j at h
        exfalso; nlinarith
  | some i =>
    cases j with
    | none =>
      cases i with
      | inl i =>
        have hi := positiveWeight_bounds i
        change positiveWeight d i = ((Q : ℤ) - 1) * weightSum d at h
        exfalso; nlinarith
      | inr i =>
        have hi := positiveWeight_bounds i
        change -(Q : ℤ) * positiveWeight d i = ((Q : ℤ) - 1) * weightSum d at h
        exfalso; nlinarith
    | some j => exact congrArg Option.some (hpair h)

end NikolovSegal.UnitaryField
