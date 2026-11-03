/- GID: D5/S1/Dynamics/Shadowing/ProgressionTwoShadowing
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/ProgressionTwoShadowing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Infinite two-branch tracing in the quadratic progression-avoidance subshift. -/

import D5.S1.Dynamics.Shadowing.ProgressionSubshift
import D5.S1.Dynamics.Shadowing.QuadraticRotationHitting

/-! Two explicit whole configurations repair the diagonal splice. The same pair
works for every natural time; only its initial diameter is controlled. -/

open Set Function SymbolicDynamics.FullShift

namespace D5.S1.Dynamics.Shadowing

def quadraticProgressionLength (p : ℕ) : ℕ := p ^ 2 + 3

/-- Delete precisely the selected coordinates, preserving every other symbol. -/
noncomputable def eraseCoordinates (c : ℕ → ReturnBit) (E : Set ℕ) : ℕ → ReturnBit := by
  classical
  exact fun k => if k ∈ E then returnZero else c k

/-- Separated quarter masks cannot occur at two phases less than one eighth
apart, including across the integer boundary. -/
theorem quarter_masks_separated (u v : ℝ) (hu : Int.fract u ∈ Icc (1 / 8 : ℝ) (3 / 8))
    (hv : Int.fract v ∈ Icc (5 / 8 : ℝ) (7 / 8)) : 1 / 8 ≤ |v - u| := by
  by_contra! h
  have hlo := (abs_lt.mp h).1
  have hhi := (abs_lt.mp h).2
  have hfu := Int.fract_add_floor u
  have hfv := Int.fract_add_floor v
  have hlow : (-1 : ℝ) < ((⌊v⌋ - ⌊u⌋ : ℤ) : ℝ) := by push_cast; linarith [hu.1, hv.2]
  have hhigh : (((⌊v⌋ - ⌊u⌋ : ℤ) : ℝ)) < 0 := by push_cast; linarith [hu.2, hv.1]
  have hlow' : (-1 : ℤ) < ⌊v⌋ - ⌊u⌋ := by exact_mod_cast hlow
  have hhigh' : ⌊v⌋ - ⌊u⌋ < (0 : ℤ) := by exact_mod_cast hhigh
  omega

/-- The two deletion masks repair every infinite pseudo-orbit, after the
accuracy-dependent control has been fixed. Both branches are genuine points. -/
theorem quadratic_progression_neighborhood_two_shadowing :
    NeighborhoodTwoShadowing (progressionShift quadraticProgressionLength) := by
  apply neighborhood_two_of_pair
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  let R := r + 1
  have hR : (1 / 2 : ℝ) ^ (R + 1) < ε :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : r ≤ R + 1)).trans_lt hr
  let M := 32 * (R + 1)
  let α : ℝ := Real.sqrt 2 / M
  let P := 256 * M * (M + 3)
  let D := max R (P ^ 3 + 2 * P)
  have hM : 0 < M := by dsimp [M]; omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hα : 0 < α := by dsimp [α]; positivity
  have hαsmall : (R : ℝ) * α < 1 / 8 := by
    have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    have hs2 : Real.sqrt 2 < 2 := by nlinarith
    dsimp [α, M]
    push_cast
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 32 * ((R : ℝ) + 1))).2
    nlinarith [mul_lt_mul_of_pos_left hs2 (show (0 : ℝ) < (R : ℝ) + 1 by positivity)]
  refine ⟨(1 / 2 : ℝ) ^ D, by positivity, fun z hz => ?_⟩
  let c := diagonalSplice (fun i => (z i).1)
  have hover : ∀ i j, j ≤ D + 1 → c (i + j) = (z i).1 j := by
    apply diagonal_splice_overlap
    intro i j hj
    simpa only [progressionShift, shift_apply, Nat.add_comm] using
      PiNat.apply_eq_of_dist_lt (hz i) hj
  have hsmall : ∀ s p : ℕ, 0 < p → p ≤ P →
      ∃ j < quadraticProgressionLength p, c (s + j * p) = returnZero := by
    intro s p hp hpP
    obtain ⟨j, hj, hzero⟩ := (z s).2 0 p hp
    have hjspan : j * p ≤ D + 1 := by
      have hj' : j ≤ p ^ 2 + 2 := by change j < p ^ 2 + 3 at hj; omega
      have hpow := Nat.pow_le_pow_left hpP 2
      have hmul := Nat.mul_le_mul (show j ≤ P ^ 2 + 2 by omega) hpP
      calc
        j * p ≤ (P ^ 2 + 2) * P := hmul
        _ = P ^ 3 + 2 * P := by ring
        _ ≤ D := le_max_right _ _
        _ ≤ D + 1 := Nat.le_succ _
    refine ⟨j, hj, ?_⟩
    rw [hover s (j * p) hjspan]
    simpa using hzero
  let E₀ : Set ℕ := {k | Int.fract ((k : ℝ) * α) ∈ Icc (1 / 8 : ℝ) (3 / 8)}
  let E₁ : Set ℕ := {k | Int.fract ((k : ℝ) * α) ∈ Icc (5 / 8 : ℝ) (7 / 8)}
  have hinitial : ∀ k ≤ R, k ∉ E₀ ∧ k ∉ E₁ := by
    intro k hk
    have hkr : (k : ℝ) ≤ R := by exact_mod_cast hk
    have hphase : (k : ℝ) * α < 1 / 8 :=
      (mul_le_mul_of_nonneg_right hkr hα.le).trans_lt hαsmall
    have hfrac : Int.fract ((k : ℝ) * α) = (k : ℝ) * α :=
      Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩
    constructor <;> intro h
    · change Int.fract _ ∈ Icc _ _ at h
      rw [hfrac] at h
      linarith [h.1]
    · change Int.fract _ ∈ Icc _ _ at h
      rw [hfrac] at h
      linarith [h.1]
  have hwindow : ∀ i, (∀ j ≤ R, i + j ∉ E₀) ∨ (∀ j ≤ R, i + j ∉ E₁) := by
    intro i
    by_cases h : ∀ j ≤ R, i + j ∉ E₀
    · exact Or.inl h
    · right
      push Not at h
      obtain ⟨j, hj, hjE⟩ := h
      intro k hk hkE
      have hsep := quarter_masks_separated _ _ hjE hkE
      have hjr : (j : ℝ) ≤ R := by exact_mod_cast hj
      have hkr : (k : ℝ) ≤ R := by exact_mod_cast hk
      have hclose : |((i + k : ℕ) : ℝ) * α - ((i + j : ℕ) : ℝ) * α| < 1 / 8 := by
        rw [abs_lt]
        push_cast
        constructor <;> nlinarith [mul_le_mul_of_nonneg_right hjr hα.le,
          mul_le_mul_of_nonneg_right hkr hα.le]
      linarith
  have hhit (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 3 / 4) (s p : ℕ) (hp : 0 < p)
      (hpP : P < p) : ∃ j < quadraticProgressionLength p,
        Int.fract (((s + j * p : ℕ) : ℝ) * α) ∈ Icc a (a + 1 / 4) := by
    obtain ⟨j, hj, hjhit⟩ := sqrt_two_scaled_quarter_hitting M p hM hp ((s : ℝ) * α) a ha ha'
    refine ⟨j, ?_, ?_⟩
    · change j < p ^ 2 + 3
      change j ≤ P * p at hj
      nlinarith
    · have heq : (((s + j * p : ℕ) : ℝ) * α) =
          (s : ℝ) * α + (j : ℝ) * p * (Real.sqrt 2 / M) := by
        dsimp [α]
        push_cast
        ring
      simpa only [heq] using hjhit
  classical
  let a := eraseCoordinates c E₀
  let b := eraseCoordinates c E₁
  have hlegal (E : Set ℕ) (hit : ∀ s p, 0 < p → P < p →
      ∃ j < quadraticProgressionLength p, s + j * p ∈ E) :
      ProgressionLegal quadraticProgressionLength (eraseCoordinates c E) := by
    intro s p hp
    by_cases hpP : p ≤ P
    · obtain ⟨j, hj, hzero⟩ := hsmall s p hp hpP
      exact ⟨j, hj, by simp [eraseCoordinates, hzero]⟩
    · obtain ⟨j, hj, hE⟩ := hit s p hp (by omega)
      exact ⟨j, hj, by simp [eraseCoordinates, hE]⟩
  let A : ProgressionPoint quadraticProgressionLength := ⟨a, hlegal E₀ (by
    intro s p hp hpP
    simpa only [E₀, mem_ofPred_eq, show (1 / 8 : ℝ) + 1 / 4 = 3 / 8 by norm_num] using
      hhit (1 / 8) (by norm_num) (by norm_num) s p hp hpP)⟩
  let B : ProgressionPoint quadraticProgressionLength := ⟨b, hlegal E₁ (by
    intro s p hp hpP
    simpa only [E₁, mem_ofPred_eq, show (5 / 8 : ℝ) + 1 / 4 = 7 / 8 by norm_num] using
      hhit (5 / 8) (by norm_num) (by norm_num) s p hp hpP)⟩
  refine ⟨A, B, ?_, fun i => ?_⟩
  · apply lt_of_le_of_lt _ hR
    change dist a b ≤ _
    apply PiNat.mem_cylinder_iff_dist_le.mp
    intro j hj
    have hinit := hinitial j (by omega)
    simp [a, b, eraseCoordinates, hinit]
  · rcases hwindow i with h | h
    · left
      apply lt_of_le_of_lt _ hR
      change dist (((progressionShift quadraticProgressionLength)^[i] A).1) (z i).1 ≤ _
      apply PiNat.mem_cylinder_iff_dist_le.mp
      intro j hj
      rw [progression_shift_iterate]
      change a (i + j) = _
      rw [show a (i + j) = c (i + j) by simp [a, eraseCoordinates, h j (by omega)]]
      exact hover i j (by have := le_max_left R (P ^ 3 + 2 * P); dsimp [D]; omega)
    · right
      apply lt_of_le_of_lt _ hR
      change dist (((progressionShift quadraticProgressionLength)^[i] B).1) (z i).1 ≤ _
      apply PiNat.mem_cylinder_iff_dist_le.mp
      intro j hj
      rw [progression_shift_iterate]
      change b (i + j) = _
      rw [show b (i + j) = c (i + j) by simp [b, eraseCoordinates, h j (by omega)]]
      exact hover i j (by have := le_max_left R (P ^ 3 + 2 * P); dsimp [D]; omega)

end D5.S1.Dynamics.Shadowing
