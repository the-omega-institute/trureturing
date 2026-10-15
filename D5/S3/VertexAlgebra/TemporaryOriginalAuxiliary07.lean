import D5.S3.VertexAlgebra.TemporaryOriginalQuartet06
import D5.S3.VertexAlgebra.LatticeSugawaraConformal
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic
set_option autoImplicit false

namespace D5.S3.VertexAlgebra.OriginalQQuartetSource

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
  LatticeSugawaraVirasoro LatticeSugawaraConformal LatticeBcGhostBrstCharge BcGhostFockSupport
open scoped BigOperators TensorProduct

noncomputable section

def frameGram (D : LatticeData) (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ := frame * gramComplex D * frame.transpose

def frameH (D : LatticeData) (H inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Matrix (Fin D.rank) (Fin D.rank) ℂ := inverse.transpose * H * inverse

def frameOscillatorNormal (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (first second : Fin D.rank)
    (mode internal : ℤ) : Module.End ℂ (Carrier D) :=
  if internal = 0 ∨ internal = mode then 0 else
    if internal < 0 then
      directionalCurrent D (frame first) internal * directionalCurrent D (frame second) (mode - internal)
    else
      directionalCurrent D (frame second) (mode - internal) * directionalCurrent D (frame first) internal

theorem frameGram_entry (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (first second : Fin D.rank) :
    frameGram D frame first second = gramPair D (frame first) (frame second) := by
  classical
  simp only [frameGram, Matrix.mul_apply, Matrix.transpose_apply, gramComplex,
    Matrix.map_apply, Finset.sum_mul, gramPair]
  rw [Finset.sum_comm]

theorem frameH_entry (D : LatticeData)
    (H inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ) (first second : Fin D.rank) :
    frameH D H inverse first second =
      ∑ original : Fin D.rank × Fin D.rank,
        H original.1 original.2 * inverse original.1 first * inverse original.2 second := by
  classical
  simp only [frameH, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro originalFirst firstMember
  apply Finset.sum_congr rfl
  intro originalSecond secondMember
  ring

theorem frame_inverseGram (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1)
    (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1)
    (rightFrameInverse : frame * inverse = 1) :
    frameH D H inverse * frameGram D frame = 1 ∧
      frameGram D frame * frameH D H inverse = 1 := by
  constructor
  · calc
      _ = inverse.transpose * H * (inverse * frame) * gramComplex D * frame.transpose := by
        simp only [frameH, frameGram, Matrix.mul_assoc]
      _ = inverse.transpose * (H * gramComplex D) * frame.transpose := by
        rw [leftFrameInverse]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by
        rw [leftGramInverse, Matrix.mul_one, ← Matrix.transpose_mul, rightFrameInverse]
        exact Matrix.transpose_one
  · calc
      _ = frame * gramComplex D * (frame.transpose * inverse.transpose) * H * inverse := by
        simp only [frameH, frameGram, Matrix.mul_assoc]
      _ = frame * (gramComplex D * H) * inverse := by
        rw [← Matrix.transpose_mul, leftFrameInverse, Matrix.transpose_one]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [rightGramInverse, Matrix.mul_one, rightFrameInverse]

theorem neutralMode_frame_expansion (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (original : Fin D.rank) (mode : ℤ) :
    neutralMode D original mode =
      ∑ axis, inverse original axis • directionalCurrent D (frame axis) mode := by
  classical
  have entry (index : Fin D.rank) :
      (∑ axis, inverse original axis * frame axis index) = if original = index then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.one_apply] using
      congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℂ => matrix original index)
        leftFrameInverse
  symm
  simp only [directionalCurrent, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, entry]
  simp

theorem frameOscillatorNormal_expansion (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (first second : Fin D.rank)
    (mode internal : ℤ) :
    frameOscillatorNormal D frame first second mode internal =
      ∑ original : Fin D.rank × Fin D.rank,
        (frame first original.1 * frame second original.2) •
          oscillatorNormalSummand D original.1 original.2 mode internal := by
  classical
  by_cases omitted : internal = 0 ∨ internal = mode
  · simp [frameOscillatorNormal, oscillatorNormalSummand, omitted]
  by_cases negative : internal < 0
  · simp only [frameOscillatorNormal, oscillatorNormalSummand, if_neg omitted,
      normalSummand, if_pos negative, directionalCurrent, Fintype.sum_prod_type,
      Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [Finset.smul_sum, smul_smul, mul_comm]
    conv_rhs => rw [Finset.sum_comm]
  · simp only [frameOscillatorNormal, oscillatorNormalSummand, if_neg omitted,
      normalSummand, if_neg negative, directionalCurrent, Fintype.sum_prod_type,
      Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [Finset.smul_sum, smul_smul, mul_comm]

theorem frameOscillatorNormal_finite (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (first second : Fin D.rank)
    (mode : ℤ) (matter : Carrier D) :
    Function.HasFiniteSupport (fun internal : ℤ =>
      frameOscillatorNormal D frame first second mode internal matter) := by
  classical
  simp only [frameOscillatorNormal_expansion, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Function.HasFiniteSupport.sum
  intro original
  exact (oscillatorNormalSummand_finite D original.1 original.2 mode matter).fun_comp
    (show (frame first original.1 * frame second original.2) • (0 : Carrier D) = 0 by simp)

theorem oscillatorNormalSummand_inverse_expansion (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (first second : Fin D.rank) (mode internal : ℤ) :
    oscillatorNormalSummand D first second mode internal =
      ∑ axes : Fin D.rank × Fin D.rank,
        (inverse first axes.1 * inverse second axes.2) •
          frameOscillatorNormal D frame axes.1 axes.2 mode internal := by
  classical
  by_cases omitted : internal = 0 ∨ internal = mode
  · simp [frameOscillatorNormal, oscillatorNormalSummand, omitted]
  by_cases negative : internal < 0
  · simp only [oscillatorNormalSummand, if_neg omitted, normalSummand, if_pos negative,
      neutralMode_frame_expansion D frame inverse leftFrameInverse,
      frameOscillatorNormal, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [Finset.smul_sum, smul_smul, mul_comm]
    conv_rhs => rw [Finset.sum_comm]
  · simp only [oscillatorNormalSummand, if_neg omitted, normalSummand, if_neg negative,
      neutralMode_frame_expansion D frame inverse leftFrameInverse,
      frameOscillatorNormal, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [Finset.smul_sum, smul_smul, mul_comm]

theorem oscillator_contraction_covariance (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (mode internal : ℤ) :
    (∑ original : Fin D.rank × Fin D.rank,
      H original.1 original.2 • oscillatorNormalSummand D original.1 original.2 mode internal) =
    ∑ axes : Fin D.rank × Fin D.rank,
      frameH D H inverse axes.1 axes.2 • frameOscillatorNormal D frame axes.1 axes.2 mode internal := by
  classical
  simp_rw [oscillatorNormalSummand_inverse_expansion D frame inverse leftFrameInverse,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro axes axesMember
  rw [frameH_entry, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro original originalMember
  rw [mul_assoc]

theorem oscillatorSugawaraMode_covariance (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (mode : ℤ) (matter : Carrier D) :
    oscillatorSugawaraMode D H mode matter =
      (2 : ℂ)⁻¹ • ∑ axes : Fin D.rank × Fin D.rank,
        frameH D H inverse axes.1 axes.2 •
          ∑ᶠ internal : ℤ, frameOscillatorNormal D frame axes.1 axes.2 mode internal matter := by
  classical
  have oldFinite (original : Fin D.rank × Fin D.rank) :=
    (oscillatorNormalSummand_finite D original.1 original.2 mode matter).fun_comp
      (show H original.1 original.2 • (0 : Carrier D) = 0 by simp)
  have newFinite (axes : Fin D.rank × Fin D.rank) :=
    (frameOscillatorNormal_finite D frame axes.1 axes.2 mode matter).fun_comp
      (show frameH D H inverse axes.1 axes.2 • (0 : Carrier D) = 0 by simp)
  have pointwise (internal : ℤ) := congrArg
    (fun operator : Module.End ℂ (Carrier D) => operator matter)
    (oscillator_contraction_covariance D H frame inverse leftFrameInverse mode internal)
  change (2 : ℂ)⁻¹ • (∑ first, ∑ second, H first second •
    ∑ᶠ internal : ℤ, oscillatorNormalSummand D first second mode internal matter) = _
  rw [← Fintype.sum_prod_type']
  congr 1
  simp_rw [smul_finsum' _ (oscillatorNormalSummand_finite D _ _ mode matter),
    smul_finsum' _ (frameOscillatorNormal_finite D frame _ _ mode matter)]
  rw [sum_finsum_comm Finset.univ _ (fun original _ => oldFinite original),
    sum_finsum_comm Finset.univ _ (fun axes _ => newFinite axes)]
  apply finsum_congr
  intro internal
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using pointwise internal

def transverseAxes (D : LatticeData) (xAxis yAxis : Fin D.rank) : Finset (Fin D.rank) :=
  (Finset.univ.erase xAxis).erase yAxis

theorem frameH_longitudinal_rows_columns (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0) :
    (∀ row, frameH D H inverse xAxis row = if row = yAxis then 1 else 0) ∧
    (∀ row, frameH D H inverse yAxis row = if row = xAxis then 1 else 0) ∧
    (∀ row, frameH D H inverse row xAxis = if row = yAxis then 1 else 0) ∧
    (∀ row, frameH D H inverse row yAxis = if row = xAxis then 1 else 0) := by
  classical
  obtain ⟨leftIdentity, rightIdentity⟩ := frame_inverseGram D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro row
    have entry := congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℂ => matrix yAxis row)
      rightIdentity
    simpa only [Matrix.mul_apply, frameGram_entry, xDual, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.one_apply, eq_comm] using entry
  · intro row
    have entry := congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℂ => matrix xAxis row)
      rightIdentity
    simpa only [Matrix.mul_apply, frameGram_entry, yDual, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.one_apply, eq_comm] using entry
  · intro row
    have entry := congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℂ => matrix row yAxis)
      leftIdentity
    simp only [Matrix.mul_apply, frameGram_entry] at entry
    simp_rw [gramPair_symm D _ (frame yAxis), xDual] at entry
    simpa [Matrix.one_apply] using entry
  · intro row
    have entry := congrArg (fun matrix : Matrix (Fin D.rank) (Fin D.rank) ℂ => matrix row xAxis)
      leftIdentity
    simp only [Matrix.mul_apply, frameGram_entry] at entry
    simp_rw [gramPair_symm D _ (frame xAxis), yDual] at entry
    simpa [Matrix.one_apply] using entry

theorem sum_split_xy (D : LatticeData) (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (values : Fin D.rank → Carrier D) :
    (∑ axis, values axis) = values xAxis + values yAxis +
      ∑ axis ∈ transverseAxes D xAxis yAxis, values axis := by
  classical
  have first := Finset.add_sum_erase Finset.univ values (Finset.mem_univ xAxis)
  have second := Finset.add_sum_erase (Finset.univ.erase xAxis) values
    (show yAxis ∈ Finset.univ.erase xAxis by simp [Ne.symm distinct])
  rw [← first, ← second]
  simp only [transverseAxes, add_assoc]

theorem oscillatorSugawaraMode_xy_transverse (D : LatticeData)
    (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftGramInverse : H * gramComplex D = 1) (rightGramInverse : gramComplex D * H = 1)
    (leftFrameInverse : inverse * frame = 1) (rightFrameInverse : frame * inverse = 1)
    (xAxis yAxis : Fin D.rank) (distinct : xAxis ≠ yAxis)
    (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
    (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
    (mode : ℤ) (matter : Carrier D) :
    oscillatorSugawaraMode D H mode matter = (2 : ℂ)⁻¹ •
      ((∑ᶠ internal : ℤ, frameOscillatorNormal D frame xAxis yAxis mode internal matter) +
       (∑ᶠ internal : ℤ, frameOscillatorNormal D frame yAxis xAxis mode internal matter) +
       ∑ first ∈ transverseAxes D xAxis yAxis, ∑ second ∈ transverseAxes D xAxis yAxis,
         frameH D H inverse first second •
           ∑ᶠ internal : ℤ, frameOscillatorNormal D frame first second mode internal matter) := by
  classical
  obtain ⟨xRow, yRow, xColumn, yColumn⟩ := frameH_longitudinal_rows_columns D H frame inverse
    leftGramInverse rightGramInverse leftFrameInverse rightFrameInverse xAxis yAxis xDual yDual
  rw [oscillatorSugawaraMode_covariance D H frame inverse leftFrameInverse rightFrameInverse,
    Fintype.sum_prod_type, sum_split_xy D xAxis yAxis distinct]
  simp_rw [xRow, yRow]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 2
  apply Finset.sum_congr rfl
  intro first firstMember
  have firstNotX : first ≠ xAxis :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp firstMember).2).1
  have firstNotY : first ≠ yAxis := (Finset.mem_erase.mp firstMember).1
  rw [sum_split_xy D xAxis yAxis distinct]
  simp [xColumn, yColumn, firstNotX, firstNotY]

end

end D5.S3.VertexAlgebra.OriginalQQuartetSource
