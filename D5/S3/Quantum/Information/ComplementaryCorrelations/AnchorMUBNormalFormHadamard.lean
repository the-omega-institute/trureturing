/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Flat qubit and qutrit unitaries reduce to the standard Hadamard and Fourier matrices. -/

import D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMeasurement
import D5.S3.Quantum.Tomography.MUB.ComplexHadamardTwoSided

/-! Dephasing in orders two and three for the two actual measurement matrices. -/

noncomputable section

namespace AnchorMeasurement

open Matrix
open scoped BigOperators Matrix
open D5.S3.Quantum.Tomography.MUB.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUB.ComplexHadamardTwoSided
open D5.S3.Quantum.FiniteDimensional
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

namespace MUBNormalForm

theorem phase_mul_star {z : ℂ} (h : Complex.normSq z = 1) :
    z * star z = 1 := by
  rw [Complex.star_def, Complex.mul_conj, h, Complex.ofReal_one]

private theorem star_mul_phase {z : ℂ} (h : Complex.normSq z = 1) :
    star z * z = 1 := by
  rw [mul_comm, phase_mul_star h]

/-- The phases make both the distinguished row and the distinguished column one. -/
def dephaseAt {n : Type*} (H : Mat n) (o : n) : Mat n :=
  fun i j => star (H i o) * H i j * (H o o * star (H o j))

theorem dephaseAt_hadamard {n : Type*} [Fintype n] [DecidableEq n]
    {H : Mat n} (hH : IsComplexHadamard H) (o : n) :
    IsComplexHadamard (dephaseAt H o) := by
  let r : n → ℂ := fun i => star (H i o)
  let c : n → ℂ := fun j => H o o * star (H o j)
  have hflat (i j : n) : Complex.normSq (H i j) = 1 := hH.1 i j
  have hr (i : n) : Complex.normSq (r i) = 1 := by
    simp [r, Complex.normSq_conj, hflat]
  have hc (j : n) : Complex.normSq (c j) = 1 := by
    simp [c, Complex.normSq_mul, Complex.normSq_conj, hflat]
  constructor
  · intro i j
    change Complex.normSq (r i * H i j * c j) = 1
    simp [Complex.normSq_mul, hr, hc, hflat]
  · ext i j
    have hterm (k : n) :
        dephaseAt H o i k * star (dephaseAt H o j k) =
          (r i * star (r j)) * (H i k * star (H j k)) := by
      change (r i * H i k * c k) * star (r j * H j k * c k) = _
      calc
        _ = (r i * star (r j)) * (H i k * star (H j k)) * (c k * star (c k)) := by
          simp only [star_mul]
          ring
        _ = _ := by rw [phase_mul_star (hc k), mul_one]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hterm, ← Finset.mul_sum]
    change (r i * star (r j)) * (H * Hᴴ) i j = _
    rw [hH.2]
    by_cases hij : i = j
    · subst j
      rw [phase_mul_star (hr i), one_mul]
    · simp [hij, smul_eq_mul]

theorem dephaseAt_row {n : Type*} {H : Mat n} (hH : EntrywiseUnit H)
    (o j : n) : dephaseAt H o o j = 1 := by
  change star (H o o) * H o j * (H o o * star (H o j)) = 1
  calc
    _ = (star (H o o) * H o o) * (H o j * star (H o j)) := by ring
    _ = 1 := by rw [star_mul_phase (hH o o), phase_mul_star (hH o j), mul_one]

theorem dephaseAt_col {n : Type*} {H : Mat n} (hH : EntrywiseUnit H)
    (o i : n) : dephaseAt H o i o = 1 := by
  change (star (H i o) * H i o) * (H o o * star (H o o)) = 1
  rw [star_mul_phase (hH i o), phase_mul_star (hH o o), mul_one]

theorem hadamardEquivalent_dephaseAt {n : Type*} {H : Mat n}
    (hH : EntrywiseUnit H) (o : n) : HadamardEquivalent H (dephaseAt H o) := by
  refine ⟨Equiv.refl n, Equiv.refl n, (fun i => star (H i o)),
    (fun j => H o o * star (H o j)), ?_, ?_, fun _ _ => rfl⟩
  · intro i
    simpa only [Complex.star_def, Complex.normSq_conj] using hH i o
  · intro j
    rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj, hH o o, hH o j, mul_one]

private theorem rowSum_zero {n : Type*} [Fintype n] [DecidableEq n]
    {H : Mat n} (hH : IsComplexHadamard H) {o i : n} (hi : i ≠ o)
    (hrow : ∀ j, H o j = 1) : ∑ j, H i j = 0 := by
  have h := congrArg (fun M : Mat n => M i o) hH.2
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, hrow, Matrix.one_apply, hi] using h

private theorem colSum_zero {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Mat n} (hH : IsComplexHadamard H) {o j : n} (hj : o ≠ j)
    (hcol : ∀ i, H i o = 1) : ∑ i, H i j = 0 := by
  have h := congrArg (fun M : Mat n => M o j) (conjTranspose_mul_self_eq_card_smul H hH)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, Matrix.one_apply, hj] using h

private theorem sqrt_mul_self_cast (m : ℕ) :
    (↑(Real.sqrt (m : ℝ)) : ℂ) * ↑(Real.sqrt (m : ℝ)) = (m : ℂ) := by
  exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))

abbrev scaled {n : Type*} (m : ℕ) (H : Mat n) : Mat n :=
  (↑(Real.sqrt (m : ℝ)) : ℂ) • H

private theorem scaled_isComplexHadamard {n : Type*} [Fintype n] [DecidableEq n]
    (m : ℕ) (hm : Fintype.card n = m) (hm0 : m ≠ 0) (U : Matrix.unitaryGroup n ℂ)
    (hU : ∀ i j, Complex.normSq ((U : Mat n) i j) = (m : ℝ)⁻¹) :
    IsComplexHadamard (scaled m (U : Mat n)) := by
  constructor
  · intro i j
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    simp only [scaled, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, hU,
      Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg m)]
    exact mul_inv_cancel₀ hmR
  · have hs : star (↑(Real.sqrt (m : ℝ)) : ℂ) = ↑(Real.sqrt (m : ℝ)) :=
      Complex.conj_ofReal _
    change scaled m (U : Mat n) * (scaled m (U : Mat n))ᴴ = _
    unfold scaled
    have hunitary : (U : Mat n) * (U : Mat n)ᴴ = 1 := Unitary.coe_mul_star_self U
    rw [Matrix.conjTranspose_smul, hs, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, sqrt_mul_self_cast, hunitary, hm]

private theorem scaled_cancel_equiv {n : Type*} (m : ℕ) (hm : m ≠ 0)
    {H K : Mat n} (h : HadamardEquivalent (scaled m H) (scaled m K)) :
    HadamardEquivalent H K := by
  obtain ⟨p, q, a, b, ha, hb, h⟩ := h
  have hs : (↑(Real.sqrt (m : ℝ)) : ℂ) ≠ 0 := by
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
    exact_mod_cast (Real.sqrt_pos.2 hmR).ne'
  refine ⟨p, q, a, b, ha, hb, fun i j => mul_left_cancel₀ hs ?_⟩
  calc
    _ = (scaled m K) i j := rfl
    _ = a i * (scaled m H) (p i) (q j) * b j := h i j
    _ = _ := by simp only [scaled, Matrix.smul_apply, smul_eq_mul]; ring

private theorem scaled_aliceR_entry (i j : Alice) :
    scaled 2 (aliceR : Mat Alice) i j = if i = 1 ∧ j = 1 then -1 else 1 := by
  let t : ℂ := ↑(Real.sqrt 2 / 2 : ℝ)
  have hmatrix : (aliceR : Mat Alice) = !![t, t; t, -t] := by
    change D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard = _
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard,
        D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2,
        pauliMatrix, qubitX, qubitZ, t]
  have hscale : (↑(Real.sqrt 2) : ℂ) * t = 1 := by
    have hr : Real.sqrt 2 * (Real.sqrt 2 / 2) = 1 := by
      rw [← mul_div_assoc, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    change (↑(Real.sqrt 2) : ℂ) * (↑(Real.sqrt 2 / 2 : ℝ) : ℂ) = 1
    exact_mod_cast hr
  rw [hmatrix]
  fin_cases i <;> fin_cases j <;>
    norm_num [scaled, Matrix.smul_apply, smul_eq_mul, Nat.cast_ofNat, hscale, mul_neg]

/-- Dephased binary complex Hadamards are the pinned scaled Hadamard matrix. -/
theorem dephased_hadamard_two {H : Mat Alice} (hH : IsComplexHadamard H)
    (hrow : ∀ j, H 0 j = 1) (hcol : ∀ i, H i 0 = 1) :
    H = scaled 2 (aliceR : Mat Alice) := by
  have hs := rowSum_zero hH (i := 1) (by decide) hrow
  rw [Fin.sum_univ_two, hcol] at hs
  have h11 : H 1 1 = -1 := by linear_combination hs
  ext i j
  rw [scaled_aliceR_entry]
  fin_cases i <;> fin_cases j <;> norm_num [hrow, hcol, h11]

theorem hadamard_two {H : Mat Alice} (hH : IsComplexHadamard H) :
    HadamardEquivalent H (scaled 2 (aliceR : Mat Alice)) := by
  have h := hadamardEquivalent_dephaseAt hH.1 0
  rw [dephased_hadamard_two (dephaseAt_hadamard hH 0)
    (dephaseAt_row hH.1 0) (dephaseAt_col hH.1 0)] at h
  exact h

private abbrev χ : AddChar Bob ℂ := ZMod.stdAddChar
private abbrev ω : ℂ := χ (-1)
private abbrev ω' : ℂ := χ 1

private theorem sum_bob (f : Bob → ℂ) : (∑ i, f i) = f 0 + f 1 + f 2 := by
  calc
    (∑ i, f i) = ∑ i : Fin 3, f ((ZMod.finEquiv 3).toEquiv i) :=
      ((ZMod.finEquiv 3).toEquiv.sum_comp f).symm
    _ = _ := by rw [Fin.sum_univ_three]; rfl

private theorem phase_pair_mul : ω * ω' = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

private theorem phase_pair_sum : 1 + ω + ω' = 0 := by
  have hne : ω ≠ 1 := by
    intro h
    have he : χ (-1) = χ 0 := h.trans (χ.map_zero_eq_one).symm
    exact (by decide : (-1 : Bob) ≠ 0) (ZMod.injective_stdAddChar he)
  have hsq : ω * ω = ω' := by
    rw [← AddChar.map_add_eq_mul, show (-1 : Bob) + -1 = 1 by decide]
  have hprod : (ω - 1) * (1 + ω + ω') = 0 := by
    calc
      _ = (ω * ω - ω') + (ω * ω' - 1) := by ring
      _ = 0 := by rw [hsq, phase_pair_mul]; ring
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

private theorem unit_pair_eq_pinned {x y : ℂ} (hx : Complex.normSq x = 1)
    (hy : Complex.normSq y = 1) (h : 1 + x + y = 0) :
    (x = ω ∧ y = ω') ∨ (x = ω' ∧ y = ω) := by
  have hstar := congrArg (starRingEnd ℂ) h
  change star (1 + x + y) = star (0 : ℂ) at hstar
  simp only [star_add, star_one, star_zero] at hstar
  have hxy : x * y = 1 := by
    have he : x * y + y + x = 0 := by
      calc
        _ = x * y * (1 + star x + star y) := by
          calc
            _ = x * y + y * (x * star x) + x * (y * star y) := by
              rw [phase_mul_star hx, phase_mul_star hy, mul_one, mul_one]
            _ = _ := by ring
        _ = 0 := by rw [hstar, mul_zero]
    linear_combination he - h
  have hpoly : (x - ω) * (x - ω') = 0 := by
    calc
      _ = x * (1 + x + y) - (x * y - ω * ω') - x * (1 + ω + ω') := by ring
      _ = 0 := by rw [h, hxy, phase_pair_mul, phase_pair_sum]; ring
  rcases mul_eq_zero.mp hpoly with h₁ | h₂
  · have hx' := sub_eq_zero.mp h₁
    exact Or.inl ⟨hx', by rw [hx'] at h; linear_combination h - phase_pair_sum⟩
  · have hx' := sub_eq_zero.mp h₂
    exact Or.inr ⟨hx', by rw [hx'] at h; linear_combination h - phase_pair_sum⟩

private theorem scaled_bobR_entry (i j : Bob) :
    scaled 3 (bobR : Mat Bob) i j = χ (-(i * j)) := by
  have hs : (↑(Real.sqrt 3) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne'
  change (↑(Real.sqrt 3) : ℂ) * (χ (-(i * j)) / ↑(Real.sqrt 3)) = _
  rw [mul_comm, div_mul_cancel₀ _ hs]

private theorem bob_phase_distinct : ω ≠ ω' := by
  intro h
  exact (by decide : (-1 : Bob) ≠ 1) (ZMod.injective_stdAddChar h)

private theorem bob_cases (i : Bob) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The only dephased ternary complex Hadamards differ from the pinned
Fourier matrix by the swap of its two noninitial rows. -/
theorem dephased_hadamard_three {H : Mat Bob} (hH : IsComplexHadamard H)
    (hrow : ∀ j, H 0 j = 1) (hcol : ∀ i, H i 0 = 1) :
    H = scaled 3 (bobR : Mat Bob) ∨
      H = (scaled 3 (bobR : Mat Bob)).submatrix (Equiv.swap (1 : Bob) 2) id := by
  have row (i : Bob) (hi : i ≠ 0) :
      (H i 1 = ω ∧ H i 2 = ω') ∨ (H i 1 = ω' ∧ H i 2 = ω) := by
    apply unit_pair_eq_pinned (hH.1 i 1) (hH.1 i 2)
    simpa only [sum_bob, hcol] using rowSum_zero hH hi hrow
  have col : 1 + H 1 1 + H 2 1 = 0 := by
    simpa only [sum_bob, hrow] using colSum_zero hH (by decide : (0 : Bob) ≠ 1) hcol
  have different : H 1 1 ≠ H 2 1 := by
    intro he
    rcases row 1 (by decide) with ha | ha
    · have he' : 1 + ω + ω = 0 := by simpa only [← he, ha.1] using col
      exact bob_phase_distinct (by linear_combination he' - phase_pair_sum)
    · have he' : 1 + ω' + ω' = 0 := by simpa only [← he, ha.1] using col
      exact bob_phase_distinct (by linear_combination phase_pair_sum - he')
  rcases row 1 (by decide) with ⟨h11, h12⟩ | ⟨h11, h12⟩
  · obtain ⟨h21, h22⟩ := (row 2 (by decide)).resolve_left
      (fun h => different (h11.trans h.1.symm))
    left
    ext i j
    rw [scaled_bobR_entry]
    rcases bob_cases i with rfl | rfl | rfl <;>
      rcases bob_cases j with rfl | rfl | rfl <;>
      simp [hrow, hcol, h11, h12, h21, h22] <;>
      congr 1
  · obtain ⟨h21, h22⟩ := (row 2 (by decide)).resolve_right
      (fun h => different (h11.trans h.1.symm))
    right
    ext i j
    change H i j = scaled 3 (bobR : Mat Bob) (Equiv.swap (1 : Bob) 2 i) j
    rw [scaled_bobR_entry]
    rcases bob_cases i with rfl | rfl | rfl <;>
      rcases bob_cases j with rfl | rfl | rfl <;>
      simp [Equiv.swap_apply_def, show (0 : Bob) ≠ 1 by decide,
        show (0 : Bob) ≠ 2 by decide,
        hrow, hcol, h11, h12, h21, h22] <;>
      congr 1

theorem hadamard_three {H : Mat Bob} (hH : IsComplexHadamard H) :
    HadamardEquivalent H (scaled 3 (bobR : Mat Bob)) := by
  have h := hadamardEquivalent_dephaseAt hH.1 0
  rcases dephased_hadamard_three (dephaseAt_hadamard hH 0)
    (dephaseAt_row hH.1 0) (dephaseAt_col hH.1 0) with hsame | hswap
  · simpa only [hsame] using h
  · apply hadamardEquivalent_trans h
    rw [hswap]
    apply hadamardEquivalent_symm
    exact ⟨Equiv.swap 1 2, Equiv.refl Bob, (fun _ => 1), (fun _ => 1),
      (fun _ => Complex.normSq_one), (fun _ => Complex.normSq_one),
      fun _ _ => by simp⟩

theorem flat_two_equivalent (U : Matrix.unitaryGroup Alice ℂ)
    (hU : ∀ i j, Complex.normSq ((U : Mat Alice) i j) = (1 / 2 : ℝ)) :
    HadamardEquivalent (U : Mat Alice) (aliceR : Mat Alice) := by
  apply scaled_cancel_equiv 2 (by decide)
  apply hadamard_two
  exact scaled_isComplexHadamard 2 (by simp) (by decide) U
    (by simpa only [one_div, Nat.cast_ofNat] using hU)

theorem flat_three_equivalent (U : Matrix.unitaryGroup Bob ℂ)
    (hU : ∀ i j, Complex.normSq ((U : Mat Bob) i j) = (1 / 3 : ℝ)) :
    HadamardEquivalent (U : Mat Bob) (bobR : Mat Bob) := by
  apply scaled_cancel_equiv 3 (by decide)
  apply hadamard_three
  exact scaled_isComplexHadamard 3 (ZMod.card 3) (by decide) U
    (by simpa only [one_div, Nat.cast_ofNat] using hU)

private theorem flat_of_scaled_entry {n : Type*} {m : ℕ} {H : Mat n}
    {i j : n} (h : Complex.normSq (scaled m H i j) = 1) :
    Complex.normSq (H i j) = (m : ℝ)⁻¹ := by
  have hm : (m : ℝ) * Complex.normSq (H i j) = 1 := by
    simpa only [scaled, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg m)] using h
  have hm0 : (m : ℝ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hm
    exact zero_ne_one hm
  apply mul_left_cancel₀ hm0
  rw [hm, mul_inv_cancel₀ hm0]

end MUBNormalForm
end AnchorMeasurement
