/- GID: D5/S3/Quantum/Recovery/LocalCompression/QutritDiagonalReset
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/QutritDiagonalReset
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bell comparison for diagonal resets with arbitrary qutrit CPTP decoders. -/

import D5.S3.Quantum.Recovery.LocalCompression.QutritPure
import D5.S3.Quantum.Matrix.CartesianVariance

/-! Matched Bell coordinates for a plane-preserving qutrit encoder and an arbitrary decoder. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open UnitaryReconstruction.LiuWildChoiObstruction (normalizedChoi normalizedChoi_entry pairMatrix)
open D5.S3.Quantum.Recovery.LocalCompression.QutritPure

namespace D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset

open private source_entry encoder_apply decoder_apply
  from D5.S3.Quantum.Recovery.LocalCompression.QutritPure

/-- Preserve the upper two-by-two block, erase the cross block, and reset level 2
to the diagonal memory state with probabilities `t` and `1 - t`. -/
def DiagonalReset (E : QuantumChannel Qutrit Qubit) (t : ℝ) : Prop :=
  0 ≤ t ∧ t ≤ 1 ∧ ∀ X : Matrix Qutrit Qutrit ℂ,
    CStarMatrix.ofMatrix.symm (E.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      !![X 0 0 + (t : ℂ) * X 2 2, X 0 1;
         X 1 0, X 1 1 + (1 - (t : ℂ)) * X 2 2]

/-- Three times the real compression of the Bell-state difference to the kets `|ii⟩`. -/
def matchedBlock (C : QuantumChannel Qutrit Qutrit) : Matrix Qutrit Qutrit ℝ :=
  fun i j => 3 * (pairMatrix source (i, i) (j, j) -
    pairMatrix (normalizedChoi C) (i, i) (j, j)).re

/-- The matched block at attenuation amplitude `x` with level 1 attenuated. -/
def modelBlock (x : ℝ) : Matrix Qutrit Qutrit ℝ :=
  !![0, 1 - x, 1; 1 - x, 1 - x ^ 2, 1; 1, 1, x ^ 2]

private def read (D : QuantumChannel Qubit Qutrit) (i j : Qubit) (u v : Qutrit) : ℂ :=
  D.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i j 1)) u v

/-- The decoder's probability of matching the memory level at the output. -/
def matchedProbability (D : QuantumChannel Qubit Qutrit) (i : Qubit) : ℝ :=
  (read D i i i.castSucc i.castSucc).re

private def discardedProbability (D : QuantumChannel Qubit Qutrit) (i : Qubit) : ℝ :=
  (read D i i 2 2).re

private def decoderChoi (D : QuantumChannel Qubit Qutrit) :
    Matrix (Qubit × Qutrit) (Qubit × Qutrit) ℂ :=
  (2 : ℂ) • pairMatrix (normalizedChoi D)

private theorem decoderChoi_entry (D : QuantumChannel Qubit Qutrit)
    (i j : Qubit) (u v : Qutrit) :
    decoderChoi D (i, u) (j, v) = read D i j u v := by
  rw [decoderChoi, Matrix.smul_apply, smul_eq_mul, normalizedChoi_entry]
  norm_num [read, Fintype.card_fin]
  ring

private theorem decoderChoi_psd (D : QuantumChannel Qubit Qutrit) :
    (decoderChoi D).PosSemidef :=
  (density_posSemidef (normalizedChoi D)).smul (by norm_num)

private theorem read_nonneg (D : QuantumChannel Qubit Qutrit) (i : Qubit) (u : Qutrit) :
    0 ≤ (read D i i u u).re := by
  rw [← decoderChoi_entry]
  exact (Complex.nonneg_iff.mp ((decoderChoi_psd D).diag_nonneg (i := (i, u)))).1

private theorem read_sum (D : QuantumChannel Qubit Qutrit) (i : Qubit) :
    ∑ u : Qutrit, (read D i i u u).re = 1 := by
  rw [← Complex.re_sum]
  change (D.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single i i 1))).trace.re = 1
  rw [D.trace_preserving]
  change (Matrix.single i i (1 : ℂ)).trace.re = 1
  simp

private theorem probability_bounds (D : QuantumChannel Qubit Qutrit) (i : Qubit) :
    0 ≤ matchedProbability D i ∧
      discardedProbability D i ≤ 1 - matchedProbability D i ∧ matchedProbability D i ≤ 1 := by
  have h := read_sum D i
  rw [Fin.sum_univ_three] at h
  refine ⟨read_nonneg D i _, ?_, ?_⟩
  · fin_cases i
    · change discardedProbability D 0 ≤ 1 - matchedProbability D 0
      change (read D 0 0 0 0).re + (read D 0 0 1 1).re + (read D 0 0 2 2).re = 1 at h
      change (read D 0 0 2 2).re ≤ 1 - (read D 0 0 0 0).re
      linarith [read_nonneg D 0 1]
    · change discardedProbability D 1 ≤ 1 - matchedProbability D 1
      change (read D 1 1 0 0).re + (read D 1 1 1 1).re + (read D 1 1 2 2).re = 1 at h
      change (read D 1 1 2 2).re ≤ 1 - (read D 1 1 1 1).re
      linarith [read_nonneg D 1 0]
  · fin_cases i
    · change (read D 0 0 0 0).re ≤ 1
      change (read D 0 0 0 0).re + (read D 0 0 1 1).re + (read D 0 0 2 2).re = 1 at h
      linarith [read_nonneg D 0 1, read_nonneg D 0 2]
    · change (read D 1 1 1 1).re ≤ 1
      change (read D 1 1 0 0).re + (read D 1 1 1 1).re + (read D 1 1 2 2).re = 1 at h
      linarith [read_nonneg D 1 0, read_nonneg D 1 2]

private theorem re_entry_le {n : Type*} [Finite n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (i j : n) :
    (A i j).re ≤ Real.sqrt (A i i).re * Real.sqrt (A j j).re := by
  classical
  let _ := Fintype.ofFinite n
  have hi := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := i))).1
  have hj := (Complex.nonneg_iff.mp (hA.diag_nonneg (i := j))).1
  have hroot := mul_nonneg (Real.sqrt_nonneg (A i i).re) (Real.sqrt_nonneg (A j j).re)
  by_cases h : 0 ≤ (A i j).re
  · apply (sq_le_sq₀ h hroot).mp
    rw [mul_pow, Real.sq_sqrt hi, Real.sq_sqrt hj]
    simpa only [pow_two] using (Complex.re_sq_le_normSq _).trans
      (D5.S3.Quantum.Matrix.CartesianVariance.psd_entry_bound hA i j)
  · exact (le_of_not_ge h).trans hroot

private theorem coherence_bound (D : QuantumChannel Qubit Qutrit) :
    (read D 0 1 0 1).re ≤ Real.sqrt (matchedProbability D 0) *
      Real.sqrt (matchedProbability D 1) := by
  simpa only [decoderChoi_entry, matchedProbability, Fin.castSucc_zero, Fin.castSucc_one]
    using re_entry_le (decoderChoi_psd D) (0, 0) (1, 1)

private theorem matchedBlock_symm (C : QuantumChannel Qutrit Qutrit) (i j : Qutrit) :
    matchedBlock C i j = matchedBlock C j i := by
  have hs := (density_posSemidef source).isHermitian.apply (i, i) (j, j)
  have hc := (density_posSemidef (normalizedChoi C)).isHermitian.apply (i, i) (j, j)
  have hs' := congrArg Complex.re hs
  have hc' := congrArg Complex.re hc
  simp only [Complex.star_def, Complex.conj_re] at hs' hc'
  change (pairMatrix source (j, j) (i, i)).re =
    (pairMatrix source (i, i) (j, j)).re at hs'
  change (pairMatrix (normalizedChoi C) (j, j) (i, i)).re =
    (pairMatrix (normalizedChoi C) (i, i) (j, j)).re at hc'
  simp only [matchedBlock, Complex.sub_re, hs', hc']

private theorem comp_entry (E : QuantumChannel Qutrit Qubit)
    (D : QuantumChannel Qubit Qutrit) (i j : Qutrit) :
    matchedBlock (D.comp E) i j = 1 -
      (D.toCompletelyPositiveMap (E.toCompletelyPositiveMap
        (CStarMatrix.ofMatrix (Matrix.single i j 1))) i j).re := by
  unfold matchedBlock
  rw [show pairMatrix source (i, i) (j, j) = (1 / 3 : ℂ) by simpa using source_entry i i j j,
    normalizedChoi_entry, QuantumChannel.comp_apply]
  norm_num [Fintype.card_fin, Complex.sub_re, Complex.mul_re, Complex.inv_re, Complex.inv_im]
  ring

private theorem matchedBlock_entries (E : QuantumChannel Qutrit Qubit)
    (D : QuantumChannel Qubit Qutrit) {t : ℝ} (hE : DiagonalReset E t) :
    let a := 1 - (read D 0 1 0 1).re
    let b := 1 - (t * discardedProbability D 0 + (1 - t) * discardedProbability D 1)
    matchedBlock (D.comp E) =
      !![1 - matchedProbability D 0, a, 1;
         a, 1 - matchedProbability D 1, 1;
         1, 1, b] := by
  dsimp only
  have action (i j : Qutrit) := hE.2.2 (Matrix.single i j 1)
  have h00 : E.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single 0 0 1)) =
      CStarMatrix.ofMatrix (Matrix.single 0 0 1) := by
    apply CStarMatrix.ofMatrix.symm.injective
    rw [action]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single]
  have h01 : E.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single 0 1 1)) =
      CStarMatrix.ofMatrix (Matrix.single 0 1 1) := by
    apply CStarMatrix.ofMatrix.symm.injective
    rw [action]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single]
  have h11 : E.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single 1 1 1)) =
      CStarMatrix.ofMatrix (Matrix.single 1 1 1) := by
    apply CStarMatrix.ofMatrix.symm.injective
    rw [action]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single]
  have h02 : E.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single 0 2 1)) = 0 := by
    apply CStarMatrix.ofMatrix.symm.injective
    rw [action]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single]
  have h12 : E.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single 1 2 1)) = 0 := by
    apply CStarMatrix.ofMatrix.symm.injective
    rw [action]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.single]
  have h22 : E.toCompletelyPositiveMap (CStarMatrix.ofMatrix (Matrix.single 2 2 1)) =
       (t : ℂ) • CStarMatrix.ofMatrix (Matrix.single 0 0 1) +
       (1 - (t : ℂ)) • CStarMatrix.ofMatrix (Matrix.single 1 1 1) := by
    apply CStarMatrix.ofMatrix.symm.injective
    rw [action]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.single, smul_eq_mul]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · change matchedBlock (D.comp E) 0 0 = 1 - matchedProbability D 0
    rw [comp_entry, h00]; rfl
  · change matchedBlock (D.comp E) 0 1 = 1 - (read D 0 1 0 1).re
    rw [comp_entry, h01]; rfl
  · change matchedBlock (D.comp E) 0 2 = 1
    simp [comp_entry, h02]
  · change matchedBlock (D.comp E) 1 0 = 1 - (read D 0 1 0 1).re
    rw [matchedBlock_symm, comp_entry, h01]; rfl
  · change matchedBlock (D.comp E) 1 1 = 1 - matchedProbability D 1
    rw [comp_entry, h11]; rfl
  · change matchedBlock (D.comp E) 1 2 = 1
    simp [comp_entry, h12]
  · change matchedBlock (D.comp E) 2 0 = 1
    rw [matchedBlock_symm]; simp [comp_entry, h02]
  · change matchedBlock (D.comp E) 2 1 = 1
    rw [matchedBlock_symm]; simp [comp_entry, h12]
  · change matchedBlock (D.comp E) 2 2 = _
    rw [comp_entry, h22, map_add, map_smul, map_smul]
    change 1 - ((t : ℂ) * read D 0 0 2 2 + (1 - (t : ℂ)) * read D 1 1 2 2).re =
      1 - (t * discardedProbability D 0 + (1 - t) * discardedProbability D 1)
    simp [discardedProbability, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im]

/-- The minimum matched probability determines the model's attenuation amplitude. -/
def amplitude (D : QuantumChannel Qubit Qutrit) : ℝ :=
  Real.sqrt (min (matchedProbability D 0) (matchedProbability D 1))

/-- Put the less reliably matched memory level in position 1. -/
def matchedOrder (D : QuantumChannel Qubit Qutrit) : Qutrit ≃ Qutrit :=
  if matchedProbability D 1 ≤ matchedProbability D 0 then Equiv.refl _
  else Equiv.swap 0 1

private theorem comparison (E : QuantumChannel Qutrit Qubit)
    (D : QuantumChannel Qubit Qutrit) {t : ℝ} (hE : DiagonalReset E t) (i j : Qutrit) :
    modelBlock (amplitude D) i j ≤
      matchedBlock (D.comp E) (matchedOrder D i) (matchedOrder D j) := by
  obtain ⟨hp0, hr0, he0⟩ := probability_bounds D 0
  obtain ⟨hp1, hr1, he1⟩ := probability_bounds D 1
  have hx : amplitude D ^ 2 = min (matchedProbability D 0) (matchedProbability D 1) :=
    Real.sq_sqrt (le_min hp0 hp1)
  have hr (k : Qubit) : discardedProbability D k ≤ 1 - amplitude D ^ 2 := by
    rw [hx]
    fin_cases k
    · change discardedProbability D 0 ≤ _
      linarith [min_le_left (matchedProbability D 0) (matchedProbability D 1)]
    · change discardedProbability D 1 ≤ _
      linarith [min_le_right (matchedProbability D 0) (matchedProbability D 1)]
  have hlast : t * discardedProbability D 0 + (1 - t) * discardedProbability D 1 ≤
      1 - amplitude D ^ 2 := by
    have h := add_le_add (mul_le_mul_of_nonneg_left (hr 0) hE.1)
      (mul_le_mul_of_nonneg_left (hr 1) (sub_nonneg.mpr hE.2.1))
    linarith
  rw [matchedBlock_entries E D hE]
  by_cases h : matchedProbability D 1 ≤ matchedProbability D 0
  · have hcoh := (coherence_bound D).trans
      (mul_le_of_le_one_left (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr he0))
    rw [min_eq_right h] at hx
    have ha : amplitude D = Real.sqrt (matchedProbability D 1) := by
      simp [amplitude, min_eq_right h]
    rw [← ha] at hcoh
    fin_cases i <;> fin_cases j <;> simp [matchedOrder, h, modelBlock] <;> linarith
  · have h' := le_of_lt (lt_of_not_ge h)
    have hcoh := (coherence_bound D).trans
      (mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr he1))
    rw [min_eq_left h'] at hx
    have ha : amplitude D = Real.sqrt (matchedProbability D 0) := by
      simp [amplitude, min_eq_left h']
    rw [← ha] at hcoh
    fin_cases i <;> fin_cases j <;>
      norm_num [matchedOrder, h, modelBlock, Equiv.swap_apply_def] <;> linarith

private theorem attenuating_block (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1) :
    matchedBlock ((decoder x y h).comp encoder) = modelBlock x := by
  have hE : DiagonalReset encoder 0 := by
    refine ⟨le_rfl, zero_le_one, fun X => ?_⟩
    rw [encoder_apply]
    simp
  rw [matchedBlock_entries _ _ hE]
  have hread (i j : Qubit) (u v : Qutrit) :=
    show read (decoder x y h) i j u v =
      (!![Matrix.single i j (1 : ℂ) 0 0, Matrix.single i j (1 : ℂ) 0 1 * (x : ℂ), 0;
          (x : ℂ) * Matrix.single i j (1 : ℂ) 1 0, (x : ℂ) ^ 2 * Matrix.single i j (1 : ℂ) 1 1, 0;
          0, 0, (y : ℂ) ^ 2 * Matrix.single i j (1 : ℂ) 1 1] : Matrix Qutrit Qutrit ℂ) u v from
      congrArg (fun M : Matrix Qutrit Qutrit ℂ => M u v) (decoder_apply x y h (Matrix.single i j 1))
  simp only [matchedProbability, discardedProbability, Fin.castSucc_zero, Fin.castSucc_one, hread]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modelBlock, Matrix.single, Complex.mul_re, pow_two]
  nlinarith

/-- The matched block of every allowed encoder and decoder dominates the block
realized by an explicit attenuating decoder at the smaller matched amplitude. -/
theorem diagonal_reset_bell_comparison (E : QuantumChannel Qutrit Qubit)
    (D : QuantumChannel Qubit Qutrit) (t : ℝ) (hE : DiagonalReset E t) :
    ∃ (x y : ℝ) (h : x ^ 2 + y ^ 2 = 1),
      x = amplitude D ∧ 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧
      matchedBlock ((decoder x y h).comp encoder) = modelBlock x ∧
      ∀ i j, modelBlock x i j ≤ matchedBlock (D.comp E) (matchedOrder D i) (matchedOrder D j) := by
  have hx0 : 0 ≤ amplitude D := Real.sqrt_nonneg _
  have hx1 : amplitude D ≤ 1 :=
    Real.sqrt_le_one.mpr ((min_le_left _ _).trans (probability_bounds D 0).2.2)
  let y := Real.sqrt (1 - amplitude D ^ 2)
  have hy : y ^ 2 = 1 - amplitude D ^ 2 := Real.sq_sqrt (by nlinarith)
  have h : amplitude D ^ 2 + y ^ 2 = 1 := by linarith
  exact ⟨amplitude D, y, h, rfl, hx0, hx1, Real.sqrt_nonneg _, attenuating_block _ _ h,
    comparison E D hE⟩

end D5.S3.Quantum.Recovery.LocalCompression.QutritDiagonalReset
