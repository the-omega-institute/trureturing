/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235281DiagonalRecurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235281DiagonalRecurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The seven-lag recurrence for Hardin's square arrays. -/

/-
result: proof_shape: content
escape_witness: coefficient_from_width_three determines the complementary-profile
  coefficient at every width from the width-three coefficient by transposition.
admission_basis: open-problem-resolution (#34242)
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence

/-! Hardin's diagonal recurrence for literal constant-stress arrays. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235281DiagonalRecurrence
open D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence hiding flip
open scoped BigOperators
noncomputable section

/-- Any cell of a row fixes the entire row once all adjacent sums are fixed. -/
private theorem cell_injective {k : ℕ} (p : Profile k) (i : Fin (k + 1)) :
    Function.Injective (fun r : Fiber p => r.1 i) := by
  intro r s hi
  let same (j : Fin (k + 1)) : Prop := r.1 j = s.1 j
  have adj (j : Fin k) : same j.castSucc = same j.succ := by
    have hr := r.2 j
    have hs := s.2 j
    unfold edge at hr hs
    apply propext
    change r.1 j.castSucc = s.1 j.castSucc ↔ r.1 j.succ = s.1 j.succ
    constructor <;> intro h <;> apply Fin.ext
    · have hv := congrArg Fin.val h
      omega
    · have hv := congrArg Fin.val h
      omega
  have hi' : same i := hi
  apply Subtype.ext
  funext j
  change same j
  rw [fin_constant same adj j, ← fin_constant same adj i]
  exact hi'

private def firstAtEdge {k : ℕ} {p : Profile k} (j : Fin k) (r : Fiber p) :
    Fin ((p j).val + 1) :=
  ⟨(r.1 j.castSucc).val, by
    have hr := r.2 j
    unfold edge at hr
    omega⟩

private theorem firstAtEdge_injective {k : ℕ} {p : Profile k} (j : Fin k) :
    Function.Injective (firstAtEdge (p := p) j) := by
  intro r s h
  apply cell_injective p j.castSucc
  have hv := congrArg (fun x : Fin ((p j).val + 1) => x.val) h
  exact Fin.ext hv

private theorem fiber_bound_edge {k : ℕ} (p : Profile k) (j : Fin k) :
    b p ≤ (p j).val + 1 := by
  have h := Nat.card_le_card_of_injective _ (firstAtEdge_injective (p := p) j)
  simpa only [b, Nat.card_fin] using h

private def constProfile (k : ℕ) (c : Fin 3) : Profile k := fun _ => c

@[simp] private theorem flip_constProfile (k : ℕ) (c : Fin 3) :
    HardinA235289Recurrence.flip (constProfile k c) = constProfile k c.rev := rfl

@[simp] private theorem flip_flip {k : ℕ} (p : Profile k) : HardinA235289Recurrence.flip (HardinA235289Recurrence.flip p) = p := by
  funext j
  simp [HardinA235289Recurrence.flip]

private def constantRow (k : ℕ) (c : Fin 3) (x : Fin (c.val + 1)) :
    Fiber (constProfile k c) :=
  ⟨fun i => ⟨if i.val % 2 = 0 then x.val else c.val - x.val, by
      have hc := c.isLt
      have hx := x.isLt
      split <;> omega⟩,
   fun j => by
    simp only [edge, constProfile, Fin.val_castSucc, Fin.val_succ]
    by_cases h : j.val % 2 = 0
    · have h' : (j.val + 1) % 2 ≠ 0 := by omega
      have hx := x.isLt
      simp only [h, h', ite_true, ite_false]
      omega
    · have h' : (j.val + 1) % 2 = 0 := by omega
      have hx := x.isLt
      simp only [h, h', ite_true, ite_false]
      omega⟩

private theorem fiber_const {k : ℕ} (c : Fin 3) : b (constProfile (k + 1) c) = c.val + 1 := by
  let f : Fiber (constProfile (k + 1) c) → Fin (c.val + 1) := firstAtEdge 0
  have hf : Function.Injective f := firstAtEdge_injective 0
  have hs : Function.Surjective f := by
    intro x
    exact ⟨constantRow _ c x, Fin.ext rfl⟩
  change Nat.card (Fiber (constProfile (k + 1) c)) = _
  rw [Nat.card_congr (Equiv.ofBijective f ⟨hf, hs⟩), Nat.card_fin]

private def IsConstant {k : ℕ} (p : Profile k) : Prop := ∃ c, p = constProfile k c

private theorem isConstant_flip {k : ℕ} (p : Profile k) :
    IsConstant (HardinA235289Recurrence.flip p) ↔ IsConstant p := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.rev, by simpa only [flip_flip, flip_constProfile] using congrArg HardinA235289Recurrence.flip hc⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c.rev, flip_constProfile _ _⟩

private theorem nonconstant_pair {k : ℕ} (p : Profile (k + 1)) (hp : ¬IsConstant p) :
    b p = 0 ∨ b (HardinA235289Recurrence.flip p) = 0 ∨
    (b p = 1 ∧ b (HardinA235289Recurrence.flip p) = 1) ∨
    (b p = 1 ∧ b (HardinA235289Recurrence.flip p) = 2) ∨
    (b p = 2 ∧ b (HardinA235289Recurrence.flip p) = 1) := by
  have hsum : b p + b (HardinA235289Recurrence.flip p) ≤ 3 := by
    by_contra! h
    apply hp
    refine ⟨p 0, ?_⟩
    have forces (j : Fin (k + 1)) : (p j).val + 1 = b p := by
      have h1 := fiber_bound_edge p j
      have h2 := fiber_bound_edge (HardinA235289Recurrence.flip p) j
      have hj := (p j).isLt
      simp only [HardinA235289Recurrence.flip, Fin.val_rev] at h2
      omega
    funext j
    apply Fin.ext
    have hj := forces j
    have h0 := forces 0
    change (p j).val = (p 0).val
    omega
  omega

private def weights (a d : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => a
  | n + 2 => a * d * weights a d n

private theorem profileCount_weights {k : ℕ} (p : Profile k) (h : ℕ) :
    (profileCount p h : ℤ) = weights (b p) (b (HardinA235289Recurrence.flip p)) h := by
  induction h using Nat.twoStepInduction with
  | zero => simp [profileCount, weights]
  | one =>
    simp [profileCount, weights]
    rfl
  | more h ih _ =>
    rw [profileCount_two_step]
    simp only [Nat.cast_mul, weights, ih]

private def W (n : ℕ) : ℤ := weights 1 3 (n + 2) + weights 3 1 (n + 2)
private def U (n : ℕ) : ℤ := (2 : ℤ) ^ (n + 2) + W n
private def V (n : ℕ) : ℤ := weights 1 2 (n + 2) + weights 2 1 (n + 2)

open scoped Classical

private def constPart {k : ℕ} (p : Profile k) (h : ℕ) : ℤ :=
  if IsConstant p then (profileCount p h : ℤ) else 0

private def oneOne {k : ℕ} (p : Profile k) : ℤ :=
  if ¬IsConstant p ∧ b p = 1 ∧ b (HardinA235289Recurrence.flip p) = 1 then 1 else 0

private def oneTwo {k : ℕ} (p : Profile k) : ℤ :=
  if ¬IsConstant p ∧ b p = 1 ∧ b (HardinA235289Recurrence.flip p) = 2 then 1 else 0

private def twoOne {k : ℕ} (p : Profile k) : ℤ :=
  if ¬IsConstant p ∧ b p = 2 ∧ b (HardinA235289Recurrence.flip p) = 1 then 1 else 0

private def C (k : ℕ) : ℤ := ∑ p : Profile (k + 1), oneOne p
private def D (k : ℕ) : ℤ := ∑ p : Profile (k + 1), oneTwo p

private theorem profile_contribution {k : ℕ} (p : Profile (k + 1)) (n : ℕ) :
    (profileCount p (n + 2) : ℤ) =
      constPart p (n + 2) + oneOne p + oneTwo p * weights 1 2 (n + 2) +
        twoOne p * weights 2 1 (n + 2) := by
  by_cases hp : IsConstant p
  · simp [constPart, oneOne, oneTwo, twoOne, hp]
  · rcases nonconstant_pair p hp with ha | hd | ⟨ha, hd⟩ | ⟨ha, hd⟩ | ⟨ha, hd⟩
    · simp [constPart, oneOne, oneTwo, twoOne, hp, ha, profileCount_two_step]
    · simp [constPart, oneOne, oneTwo, twoOne, hp, hd, profileCount_two_step]
    · simp [constPart, oneOne, oneTwo, twoOne, hp, ha, hd, profileCount_eq_pow p 1 ha hd]
    · simp [constPart, oneOne, oneTwo, twoOne, hp, ha, hd, profileCount_weights]
    · simp [constPart, oneOne, oneTwo, twoOne, hp, ha, hd, profileCount_weights]

private def flipEquiv (k : ℕ) : Profile k ≃ Profile k :=
  ⟨HardinA235289Recurrence.flip, HardinA235289Recurrence.flip, flip_flip, flip_flip⟩

private theorem sum_twoOne (k : ℕ) : ∑ p : Profile (k + 1), twoOne p = D k := by
  unfold D
  apply Fintype.sum_equiv (flipEquiv (k + 1))
  intro p
  change twoOne p = oneTwo (HardinA235289Recurrence.flip p)
  simp only [twoOne, oneTwo, isConstant_flip, flip_flip, and_comm]

private theorem constProfile_injective (k : ℕ) :
    Function.Injective (constProfile (k + 1)) := by
  intro c d h
  exact congrFun h 0

private theorem sum_constPart (n k : ℕ) :
    ∑ p : Profile (k + 1), constPart p (n + 2) = U n := by
  let s := Finset.univ.image (constProfile (k + 1))
  have hsupport (p : Profile (k + 1)) : p ∈ s ↔ IsConstant p := by
    simp [s, IsConstant, eq_comm]
  calc
    _ = ∑ p ∈ s, constPart p (n + 2) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro p _ hp
      have hnc : ¬IsConstant p := fun hc => hp ((hsupport p).mpr hc)
      simp [constPart, hnc]
    _ = ∑ c : Fin 3, constPart (constProfile (k + 1) c) (n + 2) := by
      exact Finset.sum_image (fun _ _ _ _ h => constProfile_injective k h)
    _ = U n := by
      simp only [Fin.sum_univ_three, constPart, show ∀ c : Fin 3,
        IsConstant (constProfile (k + 1) c) from fun c => ⟨c, rfl⟩, ite_true]
      have hzero : (profileCount (constProfile (k + 1) 0) (n + 2) : ℤ) =
          weights 1 3 (n + 2) := by
        rw [profileCount_weights, flip_constProfile, fiber_const, fiber_const]
        rfl
      have htwo : (profileCount (constProfile (k + 1) 2) (n + 2) : ℤ) =
          weights 3 1 (n + 2) := by
        rw [profileCount_weights, flip_constProfile, fiber_const, fiber_const]
        rfl
      have hmid : (profileCount (constProfile (k + 1) 1) (n + 2) : ℤ) =
          (2 : ℤ) ^ (n + 2) := by
        rw [profileCount_eq_pow _ 2 (fiber_const 1) (by rw [flip_constProfile, fiber_const]; rfl)]
        push_cast
        rfl
      rw [hzero, hmid, htwo]
      unfold U W
      ring

private theorem T_decompose (n k : ℕ) :
    T (n + 1) (k + 1) = 2 * (U n + C k + D k * V n) := by
  rw [literal_sum, ← Finset.mul_sum]
  apply congrArg (fun x : ℤ => 2 * x)
  simp_rw [profile_contribution]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, sum_constPart, sum_twoOne]
  change U n + C k + D k * weights 1 2 (n + 2) + D k * weights 2 1 (n + 2) = _
  unfold V
  ring

/-- A width-two array has just one edge per row, so all its profiles are constant. -/
private theorem width_two_const (p : Profile 1) : IsConstant p := by
  refine ⟨p 0, ?_⟩
  funext j
  rw [Subsingleton.elim j (0 : Fin 1)]
  rfl

private theorem T_width_two (n : ℕ) : T (n + 1) 1 = 2 * U n := by
  have hC : C 0 = 0 := by simp [C, oneOne, width_two_const]
  have hD : D 0 = 0 := by simp [D, oneTwo, width_two_const]
  change T (n + 1) (0 + 1) = 2 * U n
  rw [T_decompose, hC, hD, zero_mul, add_zero, add_zero]

private theorem V_zero : V 0 = 4 := by
  norm_num [V, weights]

private theorem V_one : V 1 = 6 := by
  norm_num [V, weights]

private theorem T_from_width_two (n k : ℕ) :
    T (n + 1) (k + 1) = 2 * (U n + U k - U 0 + D k * (V n - 4)) := by
  have h := T_transpose (0 + 1) (k + 1)
  rw [T_decompose 0 k, T_width_two, V_zero] at h
  rw [T_decompose]
  linear_combination h

/-- Comparing a width with width three determines its coefficient up to one common factor. -/
private theorem coefficient_from_width_three (k : ℕ) :
    2 * D k = D 1 * (V k - 4) := by
  have h := T_transpose (1 + 1) (k + 1)
  rw [T_from_width_two 1 k, T_from_width_two k 1, V_one] at h
  have hscaled : 2 * (2 * D k) = 2 * (D 1 * (V k - 4)) := by
    linear_combination h
  omega

private def powerTwo (n : ℕ) : ℤ := (2 : ℤ) ^ (n + 2)

private theorem diagonal_formula (n : ℕ) :
    T (n + 1) (n + 1) = 4 * powerTwo n + 4 * W n +
      D 1 * (V n)^2 - 8 * D 1 * V n + (16 * D 1 - 2 * U 0) := by
  rw [T_from_width_two]
  unfold U powerTwo
  linear_combination (V n - 4) * coefficient_from_width_three n

private theorem powerTwo_step (n : ℕ) : powerTwo (n + 2) = 4 * powerTwo n := by
  unfold powerTwo
  rw [pow_add]
  norm_num
  ring

private theorem W_step (n : ℕ) : W (n + 2) = 3 * W n := by
  unfold W
  change 1 * 3 * weights 1 3 (n + 2) + 3 * 1 * weights 3 1 (n + 2) = _
  ring

private theorem V_step (n : ℕ) : V (n + 2) = 2 * V n := by
  unfold V
  change 1 * 2 * weights 1 2 (n + 2) + 2 * 1 * weights 2 1 (n + 2) = _
  ring

private theorem V_sq_step (n : ℕ) : (V (n + 2))^2 = 4 * (V n)^2 := by
  rw [V_step]
  ring

private def Seven (f : ℕ → ℤ) (n : ℕ) : Prop :=
  f (n + 7) = f (n + 6) + 9 * f (n + 5) - 9 * f (n + 4) - 26 * f (n + 3) +
    26 * f (n + 2) + 24 * f (n + 1) - 24 * f n

/-- Each quadratic factor of the characteristic polynomial implies the recurrence. -/
private theorem seven_of_two_step (f : ℕ → ℤ) (c : ℤ) (hc : c = 2 ∨ c = 3 ∨ c = 4)
    (step : ∀ n, f (n + 2) = c * f n) (n : ℕ) : Seven f n := by
  unfold Seven
  have h0 : f (n + 2) = c * f n := step n
  have h1 : f (n + 3) = c * f (n + 1) := step (n + 1)
  have h2 : f (n + 4) = c * f (n + 2) := step (n + 2)
  have h3 : f (n + 5) = c * f (n + 3) := step (n + 3)
  have h4 : f (n + 6) = c * f (n + 4) := step (n + 4)
  have h5 : f (n + 7) = c * f (n + 5) := step (n + 5)
  rw [h5, h4, h3, h2, h1, h0]
  rcases hc with h | h | h <;> subst c <;> ring

private theorem shifted_diagonal_seven (n : ℕ) :
    Seven (fun n => T (n + 1) (n + 1)) n := by
  have hp := seven_of_two_step powerTwo 4 (Or.inr (Or.inr rfl)) powerTwo_step n
  have hw := seven_of_two_step W 3 (Or.inr (Or.inl rfl)) W_step n
  have hv := seven_of_two_step V 2 (Or.inl rfl) V_step n
  have hq := seven_of_two_step (fun n => (V n)^2) 4 (Or.inr (Or.inr rfl)) V_sq_step n
  unfold Seven at hp hw hv hq ⊢
  dsimp only at hq ⊢
  simp only [diagonal_formula]
  linear_combination 4 * hp + 4 * hw + D 1 * hq - 8 * D 1 * hv

/-- The seven-lag recurrence for the literal square counts in OEIS A235281. -/
theorem result (m : ℕ) (hm : 1 ≤ m) :
    T (m + 7) (m + 7) = T (m + 6) (m + 6) + 9 * T (m + 5) (m + 5) -
      9 * T (m + 4) (m + 4) - 26 * T (m + 3) (m + 3) +
      26 * T (m + 2) (m + 2) + 24 * T (m + 1) (m + 1) - 24 * T m m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  simpa only [Seven, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    shifted_diagonal_seven n

end

end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235281DiagonalRecurrence
