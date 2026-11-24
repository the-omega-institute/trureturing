/- GID: D5/S3/Quantum/Semigroups/WuConditionalPowerRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuConditionalPowerRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Semigroups/WuConditionalPowerRefutation.claim; result=D5/S3/Quantum/Semigroups/WuConditionalPowerRefutation.result; claim=D5/S3/Quantum/Semigroups/WuConditionalPowerRefutation.claim
   digest: A faithful qubit-ancilla refutation of the proposed ancillary extension of Wu (3.54) at s=2 using Wu's coefficient (3.55). -/

import D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Matrix.Positivity
import D5.S3.Quantum.Recovery.BKMFlagRefinement
import D5.S3.Resource.LogDet.PathSpectralClassical
import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
At inverse temperature log 4, the two signed modes from Wu's
arXiv:2610.33686v1, (3.24)–(3.27), admit a conditional power witness
with a faithful two-dimensional ancillary reference. We use ordinary
traces and the constant from (3.55) at s=2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)
open D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison (modeJump)

namespace D5.S3.Quantum.Semigroups.WuConditionalPowerRefutation

private abbrev Q := Fin 2
private abbrev Physical := Q × Q
private abbrev Full := Physical × Q
private abbrev Right := Q × Q
private abbrev Mat (n : Type) := Matrix n n ℂ

private def d (i : Q) : ℝ := ![1/5, 4/5] i
private def pi (i : Q) : ℝ := ![1/1025, 1024/1025] i
private def density : Mat Q := diagonal fun i => (d i : ℂ)
private def physDensity : Mat Physical := density ⊗ₖ density
private def reference : Mat Full := physDensity ⊗ₖ diagonal fun i => (pi i : ℂ)
private def quarter : Mat Full := reference ^ (1/4 : ℝ)

private def dissipator {n : Type} [Fintype n] (J X : Mat n) : Mat n :=
  (1/2 : ℂ) • ((Jᴴ * J) * X + X * (Jᴴ * J)) - Jᴴ * X * J

private def generator (X : Mat Full) : Mat Full :=
  ∑ i : Q, let J := modeJump i ⊗ₖ (1 : Mat Q)
    (2/5 : ℂ) • dissipator J X + (8/5 : ℂ) • dissipator Jᴴ X

private def embed (X : Mat Full) : Mat Full := quarter * X * quarter
private def power (X : Mat Full) : Mat Full := embed X * embed X
private def equilibrium (X : Mat Full) : Mat Full := physDensity ⊗ₖ partialTraceLeft (power X)
private def energy2 (X : Mat Full) : ℝ :=
  (embed X * (quarter * generator X * quarter)).trace.re
private def conditionalEntropy (X : Mat Full) : ℝ :=
  (power X * (CFC.log (power X) - CFC.log (equilibrium X))).trace.re

private def alpha : ℝ := 1 / (3 * Real.log 2)
private def weight : ℝ := 1/5125

/-- The conditional amplification of the s=2 power inequality at β = log 4. -/
def claim : Prop :=
  ∀ X : Matrix ((Fin 2 × Fin 2) × Fin 2) ((Fin 2 × Fin 2) × Fin 2) ℂ,
    X.PosDef → alpha * conditionalEntropy X ≤ energy2 X

private def assoc : Full ≃ Q × Right := Equiv.prodAssoc Q Q Q
private def reassoc := Matrix.reindexAlgEquiv ℂ ℂ assoc
private def liftRight (X : Mat Right) : Mat Full := reassoc.symm ((1 : Mat Q) ⊗ₖ X)

private def lower : Mat Q := !![0,1;0,0]
private def twist : Mat Q := diagonal ![-1,1]
private def rightGenerator (X : Mat Right) : Mat Right :=
  let J := lower ⊗ₖ (1 : Mat Q)
  (2/5 : ℂ) • dissipator J X + (8/5 : ℂ) • dissipator Jᴴ X

private theorem jump_zero : modeJump 0 = lower ⊗ₖ (1 : Mat Q) := rfl
private theorem jump_one : modeJump 1 = twist ⊗ₖ lower := rfl

private theorem reassoc_kron (U V W : Mat Q) :
    reassoc (U ⊗ₖ V ⊗ₖ W) = U ⊗ₖ (V ⊗ₖ W) :=
  Matrix.kronecker_assoc U V W

private theorem reassoc_adjoint (X : Mat Full) : reassoc Xᴴ = (reassoc X)ᴴ := rfl

private theorem reassoc_dissipator (J X : Mat Full) :
    reassoc (dissipator J X) = dissipator (reassoc J) (reassoc X) := by
  simp only [dissipator, map_sub, map_mul, map_add, map_smul, reassoc_adjoint]

private theorem kron_right_dissipator (U : Mat Q) (J X : Mat Right)
    (hU : Uᴴ * U = 1) :
    dissipator (U ⊗ₖ J) ((1 : Mat Q) ⊗ₖ X) =
      (1 : Mat Q) ⊗ₖ dissipator J X := by
  have hU' : Uᴴ * 1 * U = 1 := by rw [mul_one, hU]
  simp only [dissipator, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    hU, one_mul, hU']
  ext i j
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply, mul_sub,
    Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

private theorem kron_left_dissipator (U : Mat Q) (X : Mat Right) :
    dissipator (U ⊗ₖ (1 : Mat Right)) ((1 : Mat Q) ⊗ₖ X) = 0 := by
  simp only [dissipator, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, mul_one, one_mul, ← two_smul ℂ,
    smul_smul, show (1/2 : ℂ) * 2 = 1 by norm_num, one_smul, sub_self]

private theorem twist_adjoint : twistᴴ = twist := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [twist, Matrix.conjTranspose_apply, Matrix.diagonal]

private theorem twist_sq : twistᴴ * twist = 1 := by
  rw [twist_adjoint, twist, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> norm_num

private theorem generator_right (Y : Mat Right) :
    reassoc (generator (liftRight Y)) = (1 : Mat Q) ⊗ₖ rightGenerator Y := by
  simp only [generator, Fin.sum_univ_two, map_add, map_smul, reassoc_dissipator,
    liftRight, AlgEquiv.apply_symm_apply,
    jump_zero, jump_one, reassoc_kron, Matrix.one_kronecker_one,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    kron_left_dissipator, smul_zero, zero_add, twist_adjoint]
  rw [kron_right_dissipator _ _ _ twist_sq, kron_right_dissipator _ _ _ twist_sq]
  simp only [rightGenerator, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.kronecker_add, Matrix.kronecker_smul]

private def entries (x00 x01 x10 x11 xPair : ℂ) : Mat Right :=
  Matrix.of fun i j =>
    (!![x00, 0, 0, xPair; 0, x01, 0, 0; 0, 0, x10, 0; xPair, 0, 0, x11] :
      Mat (Fin 4)) (finProdFinEquiv i) (finProdFinEquiv j)

private def raw : Mat Right := entries 1 1 (1/128) 1 (1/8)
private def witness : Mat Full := liftRight raw

private theorem d_pos (i : Q) : 0 < d i := by fin_cases i <;> norm_num [d]
private theorem pi_pos (i : Q) : 0 < pi i := by fin_cases i <;> norm_num [pi]

private theorem density_pos : density.PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun i => by simpa using d_pos i

private theorem reference_pos : reference.PosDef :=
  (density_pos.kronecker density_pos).kronecker <|
    Matrix.posDef_diagonal_iff.mpr fun i => by simpa using pi_pos i

private theorem trace_density : density.trace = 1 := by
  norm_num [density, d, Matrix.trace_diagonal, Fin.sum_univ_two]

private theorem raw_pos : raw.PosDef := by
  let u : Right → ℂ := fun i => if i = (0,0) ∨ i = (1,1) then 1 else 0
  let v : Right → ℝ := fun i => ![7/8, 1, 1/128, 7/8] (finProdFinEquiv i)
  have hdiag : (diagonal fun i => (v i : ℂ)).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> norm_num [v, finProdFinEquiv]
  have hgram := Matrix.posSemidef_vecMulVec_self_star u
  have hc : 0 ≤ (1/8 : ℝ) := by norm_num
  convert hdiag.add_posSemidef (hgram.smul hc) using 1
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [raw, entries, finProdFinEquiv, u, v, diagonal, vecMulVec,
      Matrix.of_apply, Matrix.smul_apply, Matrix.add_apply]

private theorem witness_pos : witness.PosDef := by
  exact (Matrix.PosDef.one.kronecker raw_pos).submatrix assoc.injective

private def leftQuarter : Mat Q := diagonal fun i => ((d i ^ (1/4 : ℝ) : ℝ) : ℂ)
private def rightQuarter : Mat Right :=
  diagonal fun i => (((d i.1 * pi i.2) ^ (1/4 : ℝ) : ℝ) : ℂ)

private theorem quarter_factor : reassoc quarter = leftQuarter ⊗ₖ rightQuarter := by
  have hdiag : reference = diagonal (fun i : Full => ((d i.1.1 * d i.1.2 * pi i.2 : ℝ) : ℂ)) := by
    simp only [reference, physDensity, density, diagonal_kronecker_diagonal, Complex.ofReal_mul]
  rw [quarter, CFC.rpow_eq_cfc_real reference_pos.posSemidef.nonneg, hdiag]
  have hcfc := Matrix.cfc_diagonal_real (𝕜 := ℂ)
    (fun i : Full => d i.1.1 * d i.1.2 * pi i.2) (fun x : ℝ => x ^ (1/4 : ℝ))
  rw [show cfc (fun x : ℝ => x ^ (1/4 : ℝ))
      (diagonal fun i : Full => ((d i.1.1 * d i.1.2 * pi i.2 : ℝ) : ℂ)) =
      diagonal (fun i : Full => (((d i.1.1 * d i.1.2 * pi i.2) ^ (1/4 : ℝ) : ℝ) : ℂ)) by
    simpa [Function.comp_def] using hcfc]
  simp only [leftQuarter, rightQuarter, Matrix.diagonal_kronecker_diagonal, reassoc,
    Matrix.coe_reindexAlgEquiv]
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases h : (i,j) = (k,l)
  · cases h
    simp only [Matrix.diagonal_apply_eq]
    change (((d i * d j.1 * pi j.2) ^ (1/4 : ℝ) : ℝ) : ℂ) =
      (d i ^ (1/4 : ℝ) : ℝ) * ((d j.1 * pi j.2) ^ (1/4 : ℝ) : ℝ)
    rw [mul_assoc, Real.mul_rpow (d_pos _).le (mul_nonneg (d_pos _).le (pi_pos _).le),
      Complex.ofReal_mul]
  · rw [Matrix.diagonal_apply_ne _ h]
    exact Matrix.diagonal_apply_ne _ (fun e => h (assoc.symm.injective e))

private def rootWeight : ℝ := weight ^ (1/4 : ℝ)
private def rightShape : Mat Right :=
  diagonal fun i => ((![(1 : ℝ), 4 * Real.sqrt 2, Real.sqrt 2, 8] (finProdFinEquiv i) : ℝ) : ℂ)

private theorem fourth_pow_rpow (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1/4 : ℝ)) ^ (4 : ℕ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem right_quarter_shape : rightQuarter = (rootWeight : ℂ) • rightShape := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [rightQuarter, rightShape, ← Matrix.diagonal_smul]
  congr 1
  funext ⟨i,j⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have hroot : 0 ≤ rootWeight := Real.rpow_nonneg (by norm_num [weight]) _
  have hp := fourth_pow_rpow (d i * pi j) (mul_nonneg (d_pos _).le (pi_pos _).le)
  apply (pow_left_inj₀ (Real.rpow_nonneg (mul_nonneg (d_pos _).le (pi_pos _).le) _)
    (mul_nonneg hroot (by fin_cases i <;> fin_cases j <;> norm_num [finProdFinEquiv]))
    (by decide : (4 : ℕ) ≠ 0)).mp
  rw [hp, mul_pow, show rootWeight ^ 4 = weight from fourth_pow_rpow _ (by norm_num [weight])]
  have hs4 : Real.sqrt 2 ^ 4 = 4 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hs]; norm_num
  fin_cases i <;> fin_cases j <;> norm_num [d, pi, weight, finProdFinEquiv, mul_pow, hs4]

private theorem left_quarter_sq : leftQuarter * leftQuarter = diagonal fun i =>
    ((d i ^ (1/2 : ℝ) : ℝ) : ℂ) := by
  rw [leftQuarter, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, ← Real.rpow_add (d_pos _)]
  norm_num

private theorem left_half_sq :
    (diagonal fun i => ((d i ^ (1/2 : ℝ) : ℝ) : ℂ) : Mat Q) *
    (diagonal fun i => ((d i ^ (1/2 : ℝ) : ℝ) : ℂ) : Mat Q) = density := by
  rw [density, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, ← Real.rpow_add (d_pos _)]
  norm_num

private def reducedEmbedding : Mat Right := rightQuarter * raw * rightQuarter
private def reducedPower : Mat Right := reducedEmbedding * reducedEmbedding
private def halfDensity : Mat Q := diagonal fun i => ((d i ^ (1/2 : ℝ) : ℝ) : ℂ)

private theorem embed_lift (Y : Mat Right) :
    reassoc (embed (liftRight Y)) = halfDensity ⊗ₖ (rightQuarter * Y * rightQuarter) := by
  simp only [embed, map_mul, quarter_factor, liftRight, AlgEquiv.apply_symm_apply,
    ← Matrix.mul_kronecker_mul, mul_one, left_quarter_sq, halfDensity]

private theorem power_factor : reassoc (power witness) = density ⊗ₖ reducedPower := by
  simp only [power, witness, map_mul, embed_lift, ← Matrix.mul_kronecker_mul,
    halfDensity, left_half_sq, reducedPower, reducedEmbedding]

private theorem right_shape_mul (Y : Mat Right) (i j : Right) :
    (rightShape * Y * rightShape) i j =
      (![1, 4 * (Real.sqrt 2 : ℂ), (Real.sqrt 2 : ℂ), 8] (finProdFinEquiv i)) *
      Y i j * (![1, 4 * (Real.sqrt 2 : ℂ), (Real.sqrt 2 : ℂ), 8] (finProdFinEquiv j)) := by
  have h (k : Right) :
      ((![1, 4 * Real.sqrt 2, Real.sqrt 2, 8] (finProdFinEquiv k) : ℝ) : ℂ) =
      ![1, 4 * (Real.sqrt 2 : ℂ), (Real.sqrt 2 : ℂ), 8] (finProdFinEquiv k) := by
    rcases k with ⟨a,b⟩
    fin_cases a <;> fin_cases b <;> norm_num [finProdFinEquiv]
  simp only [rightShape, Matrix.mul_diagonal, Matrix.diagonal_mul, h]

private theorem shape_embedding :
    rightShape * raw * rightShape = entries 1 32 (1/64) 64 1 := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  ext ⟨i,j⟩ ⟨k,l⟩
  rw [right_shape_mul]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [raw, entries, finProdFinEquiv, Matrix.of_apply] <;>
      first | linear_combination (16 : ℂ) * hs | linear_combination (1/128 : ℂ) * hs

private theorem raw_generator :
    rightGenerator raw = entries (127/80) 0 (-127/320) 0 (1/8) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [rightGenerator, dissipator, lower, raw, entries, finProdFinEquiv,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.of_apply, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

private theorem shape_energy :
    rightShape * rightGenerator raw * rightShape = entries (127/80) 0 (-127/160) 0 1 := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [raw_generator]
  ext ⟨i,j⟩ ⟨k,l⟩
  rw [right_shape_mul]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [entries, finProdFinEquiv, Matrix.of_apply]
  rw [← pow_two] at hs
  ring_nf
  rw [hs]
  norm_num

private theorem scaled_sandwich (Y : Mat Right) :
    rightQuarter * Y * rightQuarter =
      (rootWeight : ℂ)^2 • (rightShape * Y * rightShape) := by
  simp only [right_quarter_shape, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two]

private theorem rootWeight_four : (rootWeight : ℂ)^2 * (rootWeight : ℂ)^2 = (weight : ℂ) := by
  rw [← pow_add, ← Complex.ofReal_pow]
  exact congrArg Complex.ofReal (fourth_pow_rpow weight (by norm_num [weight]))

private theorem reduced_power_entries :
    reducedPower = (weight : ℂ) • entries 2 1024 (1/4096) 4097 65 := by
  simp only [reducedPower, reducedEmbedding, scaled_sandwich, shape_embedding,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, rootWeight_four]
  congr 1
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [entries, finProdFinEquiv, Matrix.of_apply, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

private theorem trace_reindexed {n m : Type} [Fintype n] [Fintype m] (e : n ≃ m) (X : Mat n) :
    (Matrix.reindex e e X).trace = X.trace := by
  exact Equiv.sum_comp e.symm (fun i => X i i)

private theorem energy_value : energy2 witness = (36609/10240) * weight := by
  unfold energy2
  rw [← trace_reindexed assoc]
  change (reassoc (_ * (_ * _ * _))).trace.re = _
  simp only [map_mul, show witness = liftRight raw from rfl, embed_lift, quarter_factor,
    generator_right, ← Matrix.mul_kronecker_mul, mul_one, left_quarter_sq, halfDensity,
    left_half_sq, Matrix.trace_kronecker, trace_density, one_mul, scaled_sandwich, shape_embedding,
    shape_energy, Matrix.smul_mul, Matrix.mul_smul, smul_smul, rootWeight_four, Matrix.trace_smul]
  norm_num [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, entries, finProdFinEquiv,
    Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_re, smul_eq_mul]
  ring

private def rightMarginal : Mat Q := diagonal fun i => ((weight * ![8193/4096, 5121] i : ℝ) : ℂ)

private theorem marginal_value : partialTraceLeft (power witness) = rightMarginal := by
  have hp : power witness = reassoc.symm (density ⊗ₖ reducedPower) :=
    reassoc.eq_symm_apply.mpr power_factor
  rw [hp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceLeft, reassoc, Matrix.symm_reindexAlgEquiv,
      Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
      assoc, reduced_power_entries, density, d, rightMarginal, Matrix.diagonal,
      Matrix.kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, entries, finProdFinEquiv,
      Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two, weight]

private theorem marginal_pos : rightMarginal.PosDef := by
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [rightMarginal, weight]

private theorem equilibrium_pos : (equilibrium witness).PosDef := by
  rw [equilibrium, marginal_value]
  exact (density_pos.kronecker density_pos).kronecker marginal_pos

private theorem rightQuarter_pos : rightQuarter.PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun i => by
    exact_mod_cast Real.rpow_pos_of_pos (mul_pos (d_pos _) (pi_pos _)) (1/4 : ℝ)

private theorem reducedEmbedding_pos : reducedEmbedding.PosDef := by
  have hi : Function.Injective rightQuarter.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr rightQuarter_pos.isUnit
  simpa only [reducedEmbedding, rightQuarter_pos.isHermitian.eq] using
    raw_pos.conjTranspose_mul_mul_same hi

private theorem reducedPower_pos : reducedPower.PosDef := by
  unfold reducedPower
  have h := reducedEmbedding_pos
  have hi : Function.Injective reducedEmbedding.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr h.isUnit
  simpa only [h.isHermitian.eq] using Matrix.PosDef.conjTranspose_mul_self reducedEmbedding hi

private theorem power_pos : (power witness).PosDef := by
  have hp : power witness = reassoc.symm (density ⊗ₖ reducedPower) :=
    reassoc.eq_symm_apply.mpr power_factor
  rw [hp]
  exact (density_pos.kronecker reducedPower_pos).submatrix assoc.injective

open D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite (partialTranspose)

private def minorIndices : Q → Full := ![((0,0),1), ((0,1),0)]

private theorem raw_minor :
    ((partialTranspose witness).submatrix minorIndices minorIndices).det.re = -(1/128) := by
  rw [Matrix.det_fin_two]
  norm_num [Matrix.submatrix_apply, partialTranspose, minorIndices, witness,
    liftRight, reassoc, Matrix.symm_reindexAlgEquiv, Matrix.coe_reindexAlgEquiv,
    Matrix.reindex_apply, assoc, Matrix.kroneckerMap_apply, Matrix.one_apply, raw, entries,
    finProdFinEquiv, Matrix.of_apply, Complex.sub_re, Complex.mul_re, Complex.div_re]

private theorem power_minor :
    ((partialTranspose (power witness)).submatrix minorIndices minorIndices).det.re =
      -(16899/4) * (weight/5)^2 := by
  rw [show power witness = reassoc.symm (density ⊗ₖ reducedPower) from
    reassoc.eq_symm_apply.mpr power_factor, Matrix.det_fin_two]
  norm_num [Matrix.submatrix_apply, partialTranspose, minorIndices, density, d,
    reassoc, Matrix.symm_reindexAlgEquiv, Matrix.coe_reindexAlgEquiv, reduced_power_entries,
    Matrix.reindex_apply, assoc, Matrix.kroneckerMap_apply, Matrix.diagonal, Matrix.smul_apply,
    smul_eq_mul, entries, finProdFinEquiv, Matrix.of_apply, Complex.sub_re, Complex.mul_re,
    Complex.div_re, weight]

private theorem partial_transpose_not_psd (Y : Mat Full)
    (h : ((partialTranspose Y).submatrix minorIndices minorIndices).det.re < 0) :
    ¬ (partialTranspose Y).PosSemidef := by
  intro hp
  exact h.not_ge (Complex.nonneg_iff.mp (hp.submatrix minorIndices).det_nonneg).1

private theorem witness_npt : ¬ (partialTranspose witness).PosSemidef :=
  partial_transpose_not_psd _ (by rw [raw_minor]; norm_num)

private theorem power_npt : ¬ (partialTranspose (power witness)).PosSemidef :=
  partial_transpose_not_psd _ (by rw [power_minor]; norm_num [weight])


open D5.S3.Quantum.Recovery.BKMFlagRefinement (joint cfc_joint)
open D5.S3.Resource.LogDet.PathSpectralClassical (trace_cfc_eq_sum)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (spectral_sum_eq_of_charpoly_prod)

private def entropyPair {n : Type} [Fintype n] [DecidableEq n] (F T : Mat n) : ℝ :=
  (F * (CFC.log F - CFC.log T)).trace.re

private def reindexStar {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (e : n ≃ m) : Mat n ≃⋆ₐ[ℝ] Mat m :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℝ ℂ e) (fun _ => rfl)

private theorem entropy_reindex {n m : Type} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (e : n ≃ m) {F T : Mat n}
    (hF : F.IsHermitian) (hT : T.IsHermitian) :
    entropyPair (reindexStar e F) (reindexStar e T) = entropyPair F T := by
  let E := (reindexStar e).toStarAlgHom
  have hc : Continuous E := E.toLinearMap.continuous_of_finiteDimensional
  have hmap (S : Mat n) (hS : S.IsHermitian) : E (CFC.log S) = CFC.log (E S) := by
    unfold CFC.log
    exact E.map_cfc Real.log S (S.finite_real_spectrum.continuousOn _) hc
      hS.isSelfAdjoint (hS.isSelfAdjoint.map E)
  change entropyPair (E F) (E T) = entropyPair F T
  rw [entropyPair, entropyPair, ← hmap F hF, ← hmap T hT, ← map_sub, ← map_mul]
  exact congrArg Complex.re (trace_reindexed e _)

private theorem entropy_joint (F T : Q → Mat Right)
    (hF : ∀ i, (F i).IsHermitian) (hT : ∀ i, (T i).IsHermitian) :
    entropyPair (joint F) (joint T) = ∑ i, entropyPair (F i) (T i) := by
  unfold entropyPair CFC.log
  rw [cfc_joint _ F hF, cfc_joint _ T hT]
  simp only [joint, ← Matrix.blockDiagonal_sub, ← Matrix.blockDiagonal_mul,
    Matrix.trace_blockDiagonal, Complex.re_sum, Pi.sub_apply]

private theorem entropy_scale {n : Type} [Fintype n] [DecidableEq n]
    {F T : Mat n} (hF : F.PosDef) (hT : T.PosDef) {r : ℝ} (hr : 0 < r) :
    entropyPair (r • F) (r • T) = r * entropyPair F T := by
  simp only [entropyPair, CFC.log_smul' F hr hF.isStrictlyPositive,
    CFC.log_smul' T hr hT.isStrictlyPositive, add_sub_add_left_eq_sub,
    Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

private def reducedEquilibrium : Mat Right := density ⊗ₖ rightMarginal

private theorem reducedEquilibrium_pos : reducedEquilibrium.PosDef :=
  density_pos.kronecker marginal_pos

private theorem left_blocks (X : Mat Right) :
    reindexStar (Equiv.prodComm Q Right) (density ⊗ₖ X) = joint (fun i => d i • X) := by
  ext ⟨x,i⟩ ⟨y,j⟩
  change density i j * X x y = Matrix.blockDiagonal (fun i => d i • X) (x,i) (y,j)
  by_cases h : i = j
  · subst j
    simp [density, Matrix.smul_apply, Complex.real_smul]
  · simp [density, Matrix.diagonal_apply_ne _ h, Matrix.blockDiagonal_apply_ne _ _ _ h]

private theorem entropy_factor : conditionalEntropy witness =
    entropyPair reducedPower reducedEquilibrium := by
  change entropyPair (power witness) (equilibrium witness) = _
  rw [← entropy_reindex assoc power_pos.isHermitian equilibrium_pos.isHermitian]
  change entropyPair (reassoc (power witness)) (reassoc (equilibrium witness)) = _
  rw [power_factor, equilibrium, marginal_value, physDensity, reassoc_kron]
  change entropyPair (density ⊗ₖ reducedPower) (density ⊗ₖ reducedEquilibrium) = _
  rw [← entropy_reindex (Equiv.prodComm Q Right)
    (density_pos.kronecker reducedPower_pos).isHermitian
    (density_pos.kronecker reducedEquilibrium_pos).isHermitian, left_blocks, left_blocks]
  have hF (i : Q) := (reducedPower_pos.smul (d_pos i)).isHermitian
  have hT (i : Q) := (reducedEquilibrium_pos.smul (d_pos i)).isHermitian
  rw [entropy_joint _ _ hF hT]
  simp_rw [entropy_scale reducedPower_pos reducedEquilibrium_pos (d_pos _)]
  norm_num [Fin.sum_univ_two, d]
  ring

private def diagValues (i : Right) : ℝ :=
  weight * (![2, 1024, 1/4096, 4097] (finProdFinEquiv i))

private def diagonalPower : Mat Right := diagonal fun i => (diagValues i : ℂ)

private theorem diagValues_pos (i : Right) : 0 < diagValues i := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [diagValues, weight, finProdFinEquiv]

private theorem power_diag (i : Right) : reducedPower i i = (diagValues i : ℂ) := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [reduced_power_entries, diagValues, entries,
    finProdFinEquiv, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, weight]

private def refValues (i : Right) : ℝ := d i.1 * (weight * ![8193/4096, 5121] i.2)

private theorem refValues_pos (i : Right) : 0 < refValues i := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [refValues, d, weight]

private theorem diagonal_ref : reducedEquilibrium = diagonal fun i => (refValues i : ℂ) := by
  rw [reducedEquilibrium, density, rightMarginal, diagonal_kronecker_diagonal]
  congr 1
  funext i
  exact (Complex.ofReal_mul _ _).symm

private theorem trace_against_diagonal (F : Mat Right) (x y : Right → ℝ)
    (h : ∀ i, F i i = (x i : ℂ)) :
    (F * diagonal (fun i => (y i : ℂ))).trace.re = ∑ i, x i * y i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, h,
    ← Complex.ofReal_mul, Complex.re_sum, Complex.ofReal_re]

private theorem diagonal_log_pairing (F : Mat Right) (x y : Right → ℝ)
    (h : ∀ i, F i i = (x i : ℂ)) :
    (F * CFC.log (diagonal fun i => (y i : ℂ))).trace.re = ∑ i, x i * Real.log (y i) := by
  have hlog : CFC.log (diagonal fun i => (y i : ℂ)) =
      diagonal (fun i => (Real.log (y i) : ℂ)) := by
    simpa [CFC.log, Function.comp_def] using Matrix.cfc_diagonal_real (𝕜 := ℂ) y Real.log
  rw [hlog]
  exact trace_against_diagonal F x (Real.log ∘ y) h

-- The scalar supporting-line inequality for x log x.
private theorem log_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * (Real.log x - Real.log y) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have hh := mul_le_mul_of_nonneg_left h hx.le
  have hratio : x * (y / x - 1) = y - x := by field_simp
  rw [hratio] at hh
  linarith

private theorem diagonal_entropy_nonneg : 0 ≤ entropyPair diagonalPower reducedEquilibrium := by
  have he : ∑ i, (diagValues i - refValues i) = 0 := by
    norm_num [diagValues, refValues, d, weight, finProdFinEquiv,
      Fintype.sum_prod_type, Fin.sum_univ_two]
  have hdiag (i : Right) : diagonalPower i i = (diagValues i : ℂ) := Matrix.diagonal_apply_eq _ _
  unfold entropyPair
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, diagonal_ref,
    show (diagonalPower * CFC.log diagonalPower).trace.re =
      ∑ i, diagValues i * Real.log (diagValues i) from diagonal_log_pairing _ _ _ hdiag,
    diagonal_log_pairing _ _ _ hdiag, ← Finset.sum_sub_distrib, ← he]
  exact Finset.sum_le_sum fun i _ => by
    rw [← mul_sub]
    exact log_tangent (diagValues_pos i) (refValues_pos i)

private theorem entropy_decomposition :
    entropyPair reducedPower reducedEquilibrium =
      entropyPair diagonalPower reducedEquilibrium +
        ((reducedPower * CFC.log reducedPower).trace.re -
          (diagonalPower * CFC.log diagonalPower).trace.re) := by
  have hdiag (i : Right) : diagonalPower i i = (diagValues i : ℂ) := Matrix.diagonal_apply_eq _ _
  simp only [entropyPair, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [diagonal_ref, diagonal_log_pairing _ _ _ power_diag, diagonal_log_pairing _ _ _ hdiag]
  ring

private def shift : ℝ := (Real.sqrt (4095^2 + 4*65^2) - 4095) / 2

private theorem shift_equation : shift * (4095 + shift) = 65^2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 16785925 by norm_num)
  unfold shift
  rw [show (4095^2 + 4*65^2 : ℝ) = 16785925 by norm_num]
  linear_combination hs / 4

private theorem shift_bounds : 1 < shift ∧ shift < 2 := by
  have h₁ : (4097 : ℝ) < Real.sqrt (4095^2 + 4*65^2) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have h₂ : Real.sqrt (4095^2 + 4*65^2) < (4099 : ℝ) :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  unfold shift
  norm_num at h₁ h₂ ⊢
  constructor
  · linarith only [h₁]
  · linarith only [h₂]

private def pairedOrder : Q ⊕ Q ≃ Right :=
  (finSumFinEquiv.trans (Equiv.swap (1 : Fin 4) 3)).trans (finProdFinEquiv (m := 2) (n := 2)).symm

private def pairedBlock : Mat Q :=
  !![(weight * 2 : ℝ), (weight * 65 : ℝ);
     (weight * 65 : ℝ), (weight * 4097 : ℝ)]

private def otherValues (i : Q) : ℝ := weight * ![1/4096, 1024] i

private theorem power_blocks :
    Matrix.reindex pairedOrder.symm pairedOrder.symm reducedPower =
      Matrix.fromBlocks pairedBlock 0 0 (diagonal fun i => (otherValues i : ℂ)) := by
  have h0 : pairedOrder (.inl 0) = (0,0) := by decide
  have h1 : pairedOrder (.inl 1) = (1,1) := by decide
  have h2 : pairedOrder (.inr 0) = (1,0) := by decide
  have h3 : pairedOrder (.inr 1) = (0,1) := by decide
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.reindex_apply, Matrix.submatrix_apply, h0, h1, h2, h3, pairedBlock,
      reduced_power_entries, otherValues, entries, finProdFinEquiv, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.diagonal, ← Complex.ofReal_mul, weight]

private def pairedValues (i : Q) : ℝ := ![weight * (2 - shift), weight * (4097 + shift)] i

open Polynomial in
private theorem paired_charpoly :
    pairedBlock.charpoly = ∏ i : Q, (X - C ((pairedValues i : ℝ) : ℂ)) := by
  have hdet : weight * 2 * (weight * 4097) - (weight * 65) * (weight * 65) =
      weight * (2 - shift) * (weight * (4097 + shift)) := by
    linear_combination weight^2 * shift_equation
  have htr : weight * 2 + weight * 4097 =
      weight * (2 - shift) + weight * (4097 + shift) := by ring
  simp only [Matrix.charpoly_fin_two, Matrix.det_fin_two, Matrix.trace, Matrix.diag_apply,
    Fin.sum_univ_two, Fin.prod_univ_two, pairedBlock, pairedValues]
  change X ^ 2 - C ((↑(weight * 2) : ℂ) + ↑(weight * 4097)) * X +
      C ((↑(weight * 2) : ℂ) * ↑(weight * 4097) - ↑(weight * 65) * ↑(weight * 65)) =
    (X - C ((weight * (2 - shift) : ℝ) : ℂ)) *
      (X - C ((weight * (4097 + shift) : ℝ) : ℂ))
  rw [← Complex.ofReal_add, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    htr, hdet]
  set x := weight * (2 - shift)
  set y := weight * (4097 + shift)
  push_cast
  simp only [map_add, map_mul]
  ring

private def eigenvalueList : Right → ℝ :=
  fun i => Sum.elim pairedValues otherValues (pairedOrder.symm i)

open Polynomial in
private theorem power_charpoly :
    reducedPower.charpoly = ∏ i : Right, (X - C (RCLike.ofReal (eigenvalueList i) : ℂ)) := by
  rw [← Matrix.charpoly_reindex pairedOrder.symm, power_blocks,
    Matrix.charpoly_fromBlocks_zero₁₂, paired_charpoly, Matrix.charpoly_diagonal]
  rw [← Equiv.prod_comp pairedOrder (fun i => X - C (RCLike.ofReal (eigenvalueList i) : ℂ))]
  simp only [eigenvalueList, Equiv.symm_apply_apply, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  rfl

private def f (x : ℝ) : ℝ := x * Real.log x

private theorem spectral_gain :
    (reducedPower * CFC.log reducedPower).trace.re -
      (diagonalPower * CFC.log diagonalPower).trace.re =
      f (weight * (2 - shift)) + f (weight * (4097 + shift)) -
        f (weight * 2) - f (weight * 4097) := by
  unfold CFC.log
  have hself := reducedPower_pos.isHermitian.isSelfAdjoint
  have hcfc : reducedPower * cfc Real.log reducedPower = cfc f reducedPower := by
    conv_lhs => enter [1]; rw [← cfc_id' ℝ reducedPower hself]
    exact (cfc_mul (fun x : ℝ => x) Real.log reducedPower continuous_id.continuousOn
      (reducedPower.finite_real_spectrum.continuousOn _)).symm
  rw [hcfc, trace_cfc_eq_sum _ reducedPower_pos.isHermitian,
    spectral_sum_eq_of_charpoly_prod reducedPower_pos.isHermitian eigenvalueList f power_charpoly]
  rw [← Equiv.sum_comp pairedOrder (fun i => f (eigenvalueList i))]
  have hd (i : Right) : diagonalPower i i = (diagValues i : ℂ) := Matrix.diagonal_apply_eq _ _
  have hdiag : (diagonalPower * cfc Real.log diagonalPower).trace.re = ∑ i, f (diagValues i) :=
    diagonal_log_pairing _ _ _ hd
  rw [hdiag]
  simp only [eigenvalueList, Equiv.symm_apply_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fin.sum_univ_two, Fintype.sum_prod_type]
  norm_num [diagValues, pairedValues, otherValues, finProdFinEquiv]
  ring

private theorem gain_bound :
    11 * weight * Real.log 2 <
      f (weight * (2-shift)) + f (weight * (4097+shift)) - f (weight*2) - f (weight*4097) := by
  have hw : 0 < weight := by norm_num [weight]
  have hs := shift_bounds
  have h₁ := log_tangent (mul_pos hw (sub_pos.mpr hs.2)) (show 0 < weight * 2 by positivity)
  have h₂ := log_tangent (mul_pos hw (show 0 < 4097 + shift by linarith [hs.1]))
    (show 0 < weight * 4097 by positivity)
  have hbase : weight * shift * Real.log (4097/2) ≤
      f (weight*(2-shift)) + f (weight*(4097+shift)) - f (weight*2) - f (weight*4097) := by
    have hr : Real.log (weight * 4097) - Real.log (weight * 2) = Real.log (4097/2) := by
      rw [← Real.log_div (by positivity : 0 < weight * 4097).ne'
        (by positivity : 0 < weight * 2).ne']
      congr 1
      field_simp
    rw [← hr]
    unfold f
    linarith only [h₁, h₂]
  have hlog : 11 * Real.log 2 < Real.log (4097/2) := by
    simpa only [Real.log_pow, Nat.cast_ofNat] using
      (Real.log_lt_log (show 0 < (2 : ℝ)^11 by positivity) (by norm_num : (2 : ℝ)^11 < 4097/2))
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    11 * weight * Real.log 2 = weight * (11 * Real.log 2) := by ring
    _ < weight * Real.log (4097/2) := mul_lt_mul_of_pos_left hlog hw
    _ < weight * shift * Real.log (4097/2) := by
      apply mul_lt_mul_of_pos_right _ (by linarith : 0 < Real.log (4097/2))
      simpa using (mul_lt_mul_of_pos_left hs.1 hw)
    _ ≤ _ := hbase

private theorem entropy_bound : 11 * weight * Real.log 2 < conditionalEntropy witness := by
  rw [entropy_factor, entropy_decomposition, spectral_gain]
  linarith [gain_bound, diagonal_entropy_nonneg]

private theorem source_coefficient :
    4 * Real.sinh (Real.log 4 / 4)^2 / (Real.log 4 * Real.sinh (Real.log 4 / 2)) = alpha := by
  have hβ : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hs : Real.sinh (Real.log 2) = 3/4 := by
    rw [Real.sinh_eq, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hc : Real.cosh (Real.log 2) = 5/4 := by
    rw [Real.cosh_eq, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hh := Real.cosh_two_mul (Real.log 2 / 2)
  rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring, hc] at hh
  have hn : Real.sinh (Real.log 2 / 2)^2 = 1/8 := by
    linarith [Real.cosh_sq_sub_sinh_sq (Real.log 2 / 2)]
  rw [alpha, hβ, show 2 * Real.log 2 / 4 = Real.log 2 / 2 by ring, hn,
    show 2 * Real.log 2 / 2 = Real.log 2 by ring, hs]
  field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  ring

private theorem deficit_bound :
    energy2 witness - alpha * conditionalEntropy witness < -weight/15 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hw : 0 < weight := by norm_num [weight]
  have h := (lt_div_iff₀ (show 0 < 3 * Real.log 2 by positivity)).2
    (show (11/3 * weight) * (3 * Real.log 2) < conditionalEntropy witness by
      convert entropy_bound using 1
      ring)
  rw [energy_value, alpha, one_div, inv_mul_eq_div]
  linarith

/-- The original coefficient fails for the actual power marginal of a faithful input. -/
theorem result : ¬ claim := by
  intro h
  have hineq := h witness witness_pos
  have hw : 0 < weight := by norm_num [weight]
  linarith [deficit_bound]

-- Verify the exact physical witness and both independent PPT obstructions.
example : witness.PosDef ∧ reference.PosDef ∧ (power witness).PosDef ∧
    (equilibrium witness).PosDef ∧ partialTraceLeft (power witness) = rightMarginal ∧
    4 * Real.sinh (Real.log 4 / 4)^2 / (Real.log 4 * Real.sinh (Real.log 4 / 2)) = alpha ∧
    energy2 witness = (36609/10240) * weight ∧
    11 * weight * Real.log 2 < conditionalEntropy witness ∧
    energy2 witness - alpha * conditionalEntropy witness < -weight/15 ∧
    ¬ (partialTranspose witness).PosSemidef ∧ ¬ (partialTranspose (power witness)).PosSemidef :=
  ⟨witness_pos, reference_pos, power_pos, equilibrium_pos, marginal_value, source_coefficient,
    energy_value, entropy_bound, deficit_bound, witness_npt, power_npt⟩


end D5.S3.Quantum.Semigroups.WuConditionalPowerRefutation
