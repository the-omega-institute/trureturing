import D5.S3.Quantum.Semigroups.WuCubicTracialEndpoint
import Mathlib.Analysis.SpecificLimits.Basic

/-! Quartic sharpness of the tracial deficit along a transverse two-mode family. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Filter
open scoped Matrix ComplexOrder MatrixOrder Topology

namespace D5.S3.Quantum.Semigroups.WuCubicTracialSharpness

open WuCubicDirectedOccupationCap (Mat frameVector frameWeight lowering)
open WuCubicOperatorBridge (G)
open WuCubicAngularCertificate (normalizedDeficit physicalFrame)
open WuCubicOperatorNormalization (normalizedEmbedded operatorDeficit operatorDeficit_eq_scaled)
open WuCubicSpectralVariance (entropyGap thermalLambda thermalMassCoefficient)
open WuCubicHotOuter (mass spread squareDeficit squareEnergy)
open WuCubicTracialEndpoint (normalizedDeficit_tracial_quartic)
open WuRepeatedMiddleCubic (alpha oneModeDeficit)
open D5.S3.TotalVariation.Pinsker (binary_pinsker)

open private occupationBasis inFrame inFrame_entry lowering_amplitudes from
  D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
open private levelsAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer
open private entropy_center symmetricEnergy source_split edgeDeficit pairEntropy entropyPart from
  D5.S3.Quantum.Semigroups.WuCubicHotOuter
open private h gamma c e bias gibbsLow gibbsHigh cutA cutB entropyPair from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private scaled_diagonal from
  D5.S3.Quantum.Semigroups.WuCubicOperatorNormalization
open private rootValue rootScale rootRatio from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge

noncomputable section

private def transverseScale : ℝ := 1 / Real.sqrt 2

private theorem transverseScale_mul :
    (transverseScale : ℂ) * (transverseScale : ℂ) = 1 / 2 := by
  have h : transverseScale * transverseScale = 1 / 2 := by
    rw [transverseScale, div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← Complex.ofReal_mul, h, Complex.ofReal_div]
  norm_num

private def transverseMatrix : Mat :=
  let t : ℂ := transverseScale
  !![t, 0, t, 0; -t, 0, t, 0; 0, t, 0, t; 0, -t, 0, t]

/-- The negative and then positive eigenlines of `I ⊗ Pauli-X` in occupation order. -/
def transverseFrame : unitary Mat := by
  refine ⟨transverseMatrix, Unitary.mem_iff.mpr ⟨?_, ?_⟩⟩
  all_goals
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [transverseMatrix, Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
        Fin.sum_univ_four, Matrix.one_apply, transverseScale_mul]

/-- The left-mode lowering jump preserves each right-mode eigenspace. -/
private theorem transverse_left :
    star (transverseFrame : Mat) * lowering 0 * (transverseFrame : Mat) =
      !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0] := by
  change inFrame transverseFrame (lowering 0) = _
  apply Matrix.ext
  intro i j
  rw [inFrame_entry, (lowering_amplitudes _ _).1]
  fin_cases i <;> fin_cases j <;>
    norm_num [frameVector, transverseFrame, transverseMatrix, Complex.star_def,
      transverseScale_mul]

/-- The right-mode lowering jump has four entries of modulus `1/2` across the cut. -/
private theorem transverse_right :
    star (transverseFrame : Mat) * lowering 1 * (transverseFrame : Mat) =
      !![1 / 2, 0, -(1 / 2), 0; 0, -(1 / 2), 0, 1 / 2;
         1 / 2, 0, -(1 / 2), 0; 0, -(1 / 2), 0, 1 / 2] := by
  change inFrame transverseFrame (lowering 1) = _
  apply Matrix.ext
  intro i j
  rw [inFrame_entry, (lowering_amplitudes _ _).2]
  fin_cases i <;> fin_cases j <;>
    norm_num [frameVector, transverseFrame, transverseMatrix, Complex.star_def,
      transverseScale_mul]

private theorem transverse_energy (m : ℝ) :
    symmetricEnergy transverseFrame (levelsAt m m 1) = squareEnergy (levelsAt m m 1) := by
  have hhalf : Complex.normSq ((1 : ℂ) / 2) = 1 / 4 := by
    rw [show (1 : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.normSq_ofReal]
    norm_num
  simp only [symmetricEnergy, frameWeight, Fin.sum_univ_two,
    Unitary.conjStarAlgAut_symm_apply, transverse_left, transverse_right]
  norm_num [squareEnergy, Fin.sum_univ_four, Complex.normSq_neg, hhalf, levelsAt]
  ring

set_option maxHeartbeats 1000000 in
-- Elaborating the source split specializes the full spectral deficit.
private theorem transverse_square_deficit {m : ℝ} (hm : 0 ≤ m) (hm₁ : m ≤ 1) :
    normalizedDeficit 1 transverseFrame m m 1 = squareDeficit (levelsAt m m 1) := by
  have hsplit := source_split (t := 0) le_rfl hm le_rfl hm₁ transverseFrame
  have hΛ : thermalLambda 0 = 1 := by norm_num [thermalLambda]
  have hα : alpha 1 = 1 / 2 := by norm_num [alpha]
  have hmass : thermalMassCoefficient 0 = 0 := by
    norm_num [thermalMassCoefficient, Real.log_one]
  have hbias : bias 1 = 0 := by norm_num [bias]
  have he : e 1 = 0 := by norm_num [e]
  simpa only [add_zero, hΛ, hα, hmass, hbias, he, sub_self, zero_mul, mul_zero, sub_zero,
    one_mul, zero_add, transverse_energy] using hsplit

private theorem paired_entropy {m : ℝ} (hm : 0 ≤ m) :
    entropyGap (fun i => levelsAt m m 1 i ^ 3) = 2 * pairEntropy m 1 := by
  have hm₀ : 0 < m^3 + 1 := by positivity
  have hx (i : Fin 4) : 0 ≤ levelsAt m m 1 i := by
    fin_cases i <;> simp [levelsAt, hm]
  have hmass : mass (levelsAt m m 1) = 2 * (m^3 + 1) := by
    simp [mass, Fin.sum_univ_four, levelsAt] <;> ring
  have hM : 0 < mass (levelsAt m m 1) := by rw [hmass]; positivity
  have hE := entropy_center hx hM
  rw [hmass, show 2 * (m^3 + 1) / 4 = (m^3 + 1) / 2 by ring,
    Real.log_div hm₀.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hE
  simp only [Fin.sum_univ_four, levelsAt, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    one_pow, Real.log_one, mul_zero, add_zero] at hE
  simp only [pairEntropy, entropyPart, levelsAt, one_pow, Real.log_one, mul_zero, add_zero]
  linear_combination -hE

private theorem normalized_pair_eq_edge {m : ℝ} (hm : 0 ≤ m) (hm₁ : m ≤ 1) :
    normalizedDeficit 1 transverseFrame m m 1 = 2 * edgeDeficit m 1 := by
  rw [transverse_square_deficit hm hm₁, squareDeficit, paired_entropy hm]
  simp [squareEnergy, levelsAt, edgeDeficit] <;> ring

private theorem one_mode_eq_edge {m : ℝ} (hm : 0 ≤ m) :
    oneModeDeficit 1 m 1 0 = edgeDeficit m 1 := by
  have hm₀ : 0 < m^3 + 1 := by positivity
  have hzero : h 1 = 0 := by norm_num [h, gamma, gibbsLow, gibbsHigh, Real.log_one]
  have hhalf : alpha 1 = 1 / 2 := by norm_num [alpha]
  have hc : c 1 = 9 / 8 := by norm_num [c, gamma]
  have hb : cutB 1 m 1 = 0 := by norm_num [cutB, bias, e]
  unfold oneModeDeficit edgeDeficit cutA entropyPair pairEntropy entropyPart
  rw [hzero, hhalf, hc, hb]
  simp only [one_pow, Real.log_one, mul_zero, sub_zero, add_zero, zero_mul]
  rw [Real.log_div hm₀.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  ring

/-- The transverse frame gives twice the tracial one-mode defect. -/
theorem normalized_pair_eq_one_mode {m : ℝ} (hm : 0 ≤ m) (hm₁ : m ≤ 1) :
    normalizedDeficit 1 transverseFrame m m 1 = 2 * oneModeDeficit 1 m 1 0 := by
  rw [normalized_pair_eq_edge hm hm₁, one_mode_eq_edge hm]

private theorem pair_entropy_lower {m : ℝ} (hm : 0 < m) :
    (1 - m^3)^2 / (2 * (m^3 + 1)) ≤ pairEntropy m 1 := by
  let s := m^3 + 1
  have hs : 0 < s := by dsimp [s]; positivity
  have hm₃ : 0 < m^3 := pow_pos hm 3
  have hp : 0 ≤ m^3 / s ∧ m^3 / s ≤ 1 :=
    ⟨div_nonneg hm₃.le hs.le, (div_le_one hs).2 (by dsimp [s]; linarith)⟩
  have hpin := mul_le_mul_of_nonneg_left
    (binary_pinsker (m^3 / s) (1 / 2) hp (by norm_num)
      (by norm_num) (by norm_num)) hs.le
  have hq : 1 - m^3 / s = 1 / s := by
    field_simp [hs.ne'] <;> dsimp [s] <;> ring
  rw [hq, show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num,
    show (m^3 / s) / (1 / 2) = m^3 / s * 2 by ring,
    show (1 / s) / (1 / 2) = 1 / s * 2 by ring,
    Real.log_mul (div_ne_zero hm₃.ne' hs.ne') (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_mul (div_ne_zero one_ne_zero hs.ne') (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hm₃.ne' hs.ne', Real.log_div one_ne_zero hs.ne', Real.log_one] at hpin
  calc
    _ = s * (2 * (m^3 / s - 1 / 2)^2) := by
      change (1 - m^3)^2 / (2 * s) = _
      field_simp [hs.ne'] <;> dsimp [s] <;> ring
    _ ≤ s * (m^3 / s * (Real.log (m^3) - Real.log s + Real.log 2) +
        1 / s * (0 - Real.log s + Real.log 2)) := hpin
    _ = _ := by
      simp only [pairEntropy, entropyPart, one_pow, Real.log_one, mul_zero, add_zero]
      change _ = m^3 * Real.log (m^3) - s * Real.log s + s * Real.log 2
      field_simp [hs.ne'] <;> dsimp [s] <;> ring

private theorem pair_edge_upper {m : ℝ} (hm : 1 / 2 ≤ m) :
    2 * edgeDeficit m 1 ≤ (7 / 4 : ℝ) * (1 - m)^4 := by
  have hm₀ : 0 < m := by linarith
  have hs : 0 < m^3 + 1 := by positivity
  have ht : 0 < m + 1 := by positivity
  have hpoly : 5*m^2 + 11*m + 5 ≤ 14*(m^3 + 1) := by
    apply le_of_mul_le_mul_left ?_ ht
    have hfactor : (m + 1) * (5*m^2 + 11*m + 5) ≤ 21 * (m^3 + 1) := by
      nlinarith only [mul_nonneg ht.le (sq_nonneg (m - 1))]
    have hconst : (21 : ℝ) ≤ 14 * (m + 1) := by linarith
    exact hfactor.trans (by
      nlinarith only [mul_le_mul_of_nonneg_right hconst hs.le])
  unfold edgeDeficit
  calc
    _ ≤ (9 / 8 : ℝ) * (1 - m)^2 * (m + 1) - (1 - m^3)^2 / (2 * (m^3 + 1)) := by
      linear_combination pair_entropy_lower hm₀
    _ = (1 - m)^4 * (5*m^2 + 11*m + 5) / (8 * (m^3 + 1)) := by
      field_simp [hs.ne'] <;> ring
    _ ≤ _ := by
      apply (div_le_iff₀ (show 0 < 8 * (m^3 + 1) by positivity)).2
      calc
        _ ≤ (1 - m)^4 * (14 * (m^3 + 1)) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
        _ = _ := by ring

/-- A uniform quartic upper bound for this ordered family, including the scalar endpoint. -/
theorem normalized_pair_quartic {m : ℝ} (hm : 1 / 2 ≤ m) (hm₁ : m ≤ 1) :
    0 ≤ normalizedDeficit 1 transverseFrame m m 1 ∧
      normalizedDeficit 1 transverseFrame m m 1 ≤ (7 / 4 : ℝ) * (1 - m)^4 := by
  have hm₀ : 0 ≤ m := by linarith
  constructor
  · rw [normalized_pair_eq_one_mode hm₀ hm₁]
    exact mul_nonneg (by norm_num)
      (WuOneModeCubic.one_mode_bound (r := 1) le_rfl m 1 0 hm₀ hm₁ (by norm_num) (by norm_num))
  · rw [normalized_pair_eq_edge hm₀ hm₁]
    exact pair_edge_upper hm

/-- The physical operator assigns the paired levels to the transverse eigenframe. -/
def pairedOperator (m : ℝ) : WuCubicOperatorBridge.Mat :=
  normalizedEmbedded transverseFrame m m 1

private theorem pairedOperator_psd {m : ℝ} (hm : 0 ≤ m) : (pairedOperator m).PosSemidef := by
  have hnonneg (i : Fin 4) : 0 ≤ levelsAt m m 1 i := by
    fin_cases i <;> simp [levelsAt, hm]
  have hd : (diagonal (fun i => (levelsAt m m 1 i : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    exact (RCLike.ofReal_nonneg (K := ℂ)).mpr (hnonneg i)
  exact hd.mul_mul_conjTranspose_same (physicalFrame transverseFrame)

theorem pairedOperator_spectrum (m : ℝ) :
    spectrum ℝ (pairedOperator m) = Set.range (levelsAt m m 1) := by
  let D := diagonal (fun i => (levelsAt m m 1 i : ℂ))
  let U := (transverseFrame : Mat)
  have h : pairedOperator m = reindexAlgEquiv ℝ ℂ occupationBasis.symm (U * D * Uᴴ) := by
    change U.submatrix occupationBasis id * D * (U.submatrix occupationBasis id)ᴴ =
      (U * D * Uᴴ).submatrix occupationBasis occupationBasis
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul _ _ occupationBasis id occupationBasis Function.bijective_id,
      Matrix.submatrix_mul _ _ occupationBasis id id Function.bijective_id,
      Matrix.submatrix_id_id]
  rw [h, AlgEquiv.spectrum_eq]
  change spectrum ℝ ((transverseFrame : Mat) * D * star (transverseFrame : Mat)) = _
  refine (Unitary.spectrum_star_right_conjugate (R := ℝ) (U := transverseFrame)).trans ?_
  ext x
  dsimp only [D]
  rw [← spectrum.algebraMap_mem_iff ℂ, spectrum_diagonal]
  change ((x : ℂ) ∈ Set.range (fun i => (levelsAt m m 1 i : ℂ))) ↔ _
  simp only [Set.mem_range, Complex.ofReal_inj]

private theorem tracial_G :
    G 1 = (rootScale 1 : ℂ) • (1 : WuCubicOperatorBridge.Mat) := by
  rw [G, ← Matrix.diagonal_one, ← Matrix.diagonal_smul]
  congr 1
  funext o
  change (rootValue 1 o : ℂ) = (rootScale 1 : ℂ) * 1
  rw [mul_one]
  apply congrArg Complex.ofReal
  unfold rootValue
  generalize finProdFinEquiv o = i
  fin_cases i <;> simp [rootRatio]

/-- The sandwich has the same eigenframe and multiplies all four eigenvalues by the same scale. -/
theorem pairedOperator_sandwich (m : ℝ) :
    G 1 * pairedOperator m * G 1 =
      physicalFrame transverseFrame *
        diagonal (fun i => ((rootScale 1 ^ 2 * levelsAt m m 1 i : ℝ) : ℂ)) *
        (physicalFrame transverseFrame)ᴴ := by
  rw [scaled_diagonal, tracial_G, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, Complex.ofReal_pow, pow_two] <;> rfl

theorem pairedOperator_deficit (m : ℝ) :
    operatorDeficit 1 (pairedOperator m) =
      (1 / 4 : ℝ) * normalizedDeficit 1 transverseFrame m m 1 := by
  have hscale : (rootScale 1 ^ 2)^3 = (1 / 4 : ℝ) := by
    have hcube : rootScale 1 ^ 3 = (1 / 2 : ℝ) := by
      unfold rootScale
      rw [show gibbsLow 1 = (1 / 2 : ℝ) by norm_num [gibbsLow],
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    calc
      _ = (rootScale 1 ^ 3)^2 := by ring
      _ = _ := by rw [hcube]; norm_num
  rw [operatorDeficit_eq_scaled le_rfl (pairedOperator m) transverseFrame (rootScale 1 ^ 2)
    m m 1 (pairedOperator_sandwich m), hscale]

/-- Two-sided quartic bounds for the physical ordinary-trace deficit. -/
theorem pairedOperator_quartic {m : ℝ} (hm : 1 / 2 ≤ m) (hm₁ : m < 1) :
    (pairedOperator m).PosSemidef ∧
      (157 / 102400 : ℝ) * (1 - m)^4 ≤ operatorDeficit 1 (pairedOperator m) ∧
      operatorDeficit 1 (pairedOperator m) ≤ (7 / 16 : ℝ) * (1 - m)^4 := by
  have hm₀ : 0 ≤ m := by linarith
  refine ⟨pairedOperator_psd hm₀, ?_⟩
  rw [pairedOperator_deficit]
  constructor
  · linarith only [normalizedDeficit_tracial_quartic transverseFrame hm₀ le_rfl hm₁.le
      le_rfl hm₁]
  · linarith only [(normalized_pair_quartic hm hm₁.le).2]

/-- The roots of the sequence with physical spread tending to zero. -/
def pairedParameter (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

theorem pairedOperator_sequence :
    (∀ n : ℕ, let m := pairedParameter n
      (pairedOperator m).PosSemidef ∧
        (157 / 102400 : ℝ) * (1 - m)^4 ≤ operatorDeficit 1 (pairedOperator m) ∧
        operatorDeficit 1 (pairedOperator m) ≤ (7 / 16 : ℝ) * (1 - m)^4) ∧
    (∀ n : ℕ, 0 < spread (levelsAt (pairedParameter n) (pairedParameter n) 1)) ∧
    Tendsto (fun n : ℕ => spread (levelsAt (pairedParameter n) (pairedParameter n) 1))
      atTop (𝓝 0) := by
  have hspread (n : ℕ) :
      spread (levelsAt (pairedParameter n) (pairedParameter n) 1) = 1 / ((n : ℝ) + 2) := by
    simp [spread, levelsAt, pairedParameter]
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hd : 0 < (n : ℝ) + 2 := by positivity
    have hi : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
      (div_le_iff₀ hd).2 (by linarith)
    have hi₀ : 0 < 1 / ((n : ℝ) + 2) := by positivity
    exact pairedOperator_quartic (m := pairedParameter n) (by dsimp [pairedParameter]; linarith)
      (by dsimp [pairedParameter]; linarith)
  · intro n
    rw [hspread]
    positivity
  · simp_rw [hspread]
    have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def, Nat.cast_add, add_assoc, one_add_one_eq_two] using hlim

#print axioms transverse_energy
#print axioms normalized_pair_eq_one_mode
#print axioms normalized_pair_quartic
#print axioms pairedOperator_spectrum
#print axioms pairedOperator_sandwich
#print axioms pairedOperator_deficit
#print axioms pairedOperator_quartic
#print axioms pairedOperator_sequence

end

end D5.S3.Quantum.Semigroups.WuCubicTracialSharpness
