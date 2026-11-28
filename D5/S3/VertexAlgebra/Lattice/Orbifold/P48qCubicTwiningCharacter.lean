/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicTwiningCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/P48qCubicTwiningCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute convergence, theta-eta factorization and S interchange of the cubic traces. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicOscillatorTrace
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual
import D5.S3.VertexAlgebra.Lattice.LatticeSectorCharacterWeilCovariance
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qNativeConformalZero
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFullEnergySpectrum
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicMonodromy

/-! The real P48q Gram controls the charge sum. The actual integer-grade trace
groups the product of this fixed-charge sum and the sixteen-colour occupation
sum at three times the modular parameter. The integral fixed-lattice dual
determines the theta reindexing and the covolume for S inversion. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicTwiningCharacter

open Complex LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeThetaCharacter
open P48qTwistedChargeAction (Momentum lattice g g_apply g_cube momentum_index_iff)
open P48qGramCertificate (nebeGram)
open P48qGramPositivity (nebeGram_posDef)
open P48qFixedRankCertificate (nebeOrderThree rowAction nebeOrderThree_fixedRank16)
open P48qProjectedDual (fixed_dual_iff_projected_charge)
open P48qNormImageCertificate (nebeOrderThree_fixed_is_norm_image)
open P48qCubicOscillatorTrace
open LatticeDiscriminantTheta (gramReal)
open LatticeSectorCharacterWeilCovariance (oscillator_norm oscillator_eta)
open D5.S3.Fourier.MatrixGaussian (quadratic summable_norm_theta)
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation (integerEnergy)
open Matrix
open scoped Matrix
open private dotOfFn_eq from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFixedRankCertificate
open private gram_integral norm_fixed action_embed from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qProjectedDual
open private eta_S_principal from D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
open P48qFiniteEnergyEigenspaces (totalLZeroEigenspaceCoeffEquiv
  totalLZero_eigenspace_finiteDimensional totalWeight_fiber_finite)
open private momentumWeight_eq_chargeEnergy occupationSublevel_finite from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFiniteEnergyEigenspaces
open P48qNativeConformalZero (native_conformal_coeff_neg_six_eq_totalLZero)
open P48qThirdTwistedField (frequency)
open P48qAllJetWickField (nativeField)
open P48qTwistedStateEnergy (occupationFrequency totalWeight totalLZero)
open LatticeActualConformalState (omega)
open HalfFockSpectralFiberSource (actualInverse)
open P48qCubicMonodromy (conformalMonodromy conformalMonodromy_cube
  conformalMonodromy_native_conformal_eigenvector)

noncomputable section

/-- The integral lattice fixed by the standard cubic isometry. -/
abbrev FixedCharge := {a : Charge lattice // g a = a}
private abbrev Occupation := (Fin 16 × ℕ) →₀ ℕ

local notation "gramComplex" => nebeGram.map (Int.castRingHom ℂ)
local notation "castCharge" => (fun a : Charge lattice => Int.castRingHom ℂ ∘ a)

/-- The Gram dual in the fixed space is exactly one third of the integral fixed lattice. -/
theorem fixed_dual_iff_third_fixed_charge (μ : Fin 48 → ℂ) :
    (rowAction ℂ nebeOrderThree μ = μ ∧
      ∀ a : FixedCharge, ∃ k : ℤ, Matrix.toBilin' gramComplex (castCharge a.1) μ = (k : ℂ)) ↔
    ∃ a : FixedCharge, μ = (3 : ℂ)⁻¹ • castCharge a.1 := by
  constructor
  · rintro ⟨hμ, hpair⟩
    obtain ⟨x, hx⟩ := (fixed_dual_iff_projected_charge μ).mp
      ⟨hμ, fun a ha => hpair ⟨a, (g_apply a).trans ha⟩⟩
    refine ⟨⟨_, ?_⟩, hx⟩
    rw [g_apply]
    exact norm_fixed x
  · rintro ⟨a, rfl⟩
    have ha : a.1 ᵥ* nebeOrderThree = a.1 := (g_apply a.1).symm.trans a.2
    obtain ⟨x, hx⟩ := nebeOrderThree_fixed_is_norm_image a.1 ha
    obtain ⟨hμ, hpair⟩ := (fixed_dual_iff_projected_charge
      ((3 : ℂ)⁻¹ • castCharge a.1)).mpr ⟨x, by rw [hx]⟩
    exact ⟨hμ, fun b => hpair b.1 ((g_apply b.1).symm.trans b.2)⟩

/-- The integer-valued pairing on the fixed lattice with its Gram form divided by three. -/
def fixedChargePairing (a b : FixedCharge) : ℤ := bilinear lattice a.1 b.1 / 3

private theorem fixed_charge_pairing_mul_three (a b : FixedCharge) :
    3 * fixedChargePairing a b = bilinear lattice a.1 b.1 := by
  obtain ⟨k, hk⟩ :=
    ((fixed_dual_iff_third_fixed_charge _).mpr ⟨b, rfl⟩).2 a
  rw [LinearMap.BilinForm.smul_right, gram_integral] at hk
  have hB : nebeGram.toBilin' a.1 b.1 = bilinear lattice a.1 b.1 := by
    simp only [Matrix.toBilin'_apply, bilinear]
    rfl
  rw [hB] at hk
  have hcast : (3 : ℂ) * (k : ℂ) = (bilinear lattice a.1 b.1 : ℂ) := by
    rw [← hk]
    simp only [Int.coe_castRingHom,
      mul_inv_cancel_left₀ (by norm_num : (3 : ℂ) ≠ 0)]
  have heq : 3 * k = bilinear lattice a.1 b.1 := by exact_mod_cast hcast
  unfold fixedChargePairing
  omega

/-- Division by three preserves the even diagonal and positive square on nonzero
fixed charges. -/
theorem fixed_charge_pairing_even_pos (a : FixedCharge) :
    Even (fixedChargePairing a a) ∧
      (a.1 ≠ 0 → 0 < fixedChargePairing a a) := by
  have hscale := fixed_charge_pairing_mul_three a a
  have heven := two_chargeEnergy lattice a.1
  constructor
  · refine ⟨fixedChargePairing a a / 2, ?_⟩
    omega
  · intro ha
    have hpos := LatticeFiniteNegativeGeneration.norm_positive lattice nebeGram_posDef a.1 ha
    omega

-- Restriction to these sixteen columns is the coordinate inverse on the fixed space.
private def fixedColumns (i : Fin 16) : Fin 48 :=
  ![23, 29, 34, 14, 26, 37, 38, 39, 40, 11, 42, 27, 44, 45, 43, 36] i

private def fixedRowsData : Array (Array ℤ) := #[
  #[8, 8, 7, -11, -8, -14, 10, 4, 9, 6, 10, 0, -1, 8, 0, 8,
    5, 5, -5, 0, 2, -6, 4, 1, -1, 0, 0, 0, 3, 0, -2, 1,
    -3, -2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, -4],
  #[0, 8, 12, -3, -8, -13, 6, 0, 7, 4, 9, 0, -2, 8, 0, 5,
    4, 4, -4, -2, 0, -7, 4, 0, 2, -3, 0, 0, 2, 1, 0, 4,
    -4, -3, 0, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 2, -4],
  #[-7, -5, 1, 18, 11, 12, -13, 0, -7, -7, -12, 0, 2, -4, 0, -7,
    -1, -9, 7, 4, -1, 1, -3, 0, 2, 4, 0, 0, -7, 0, 1, 0,
    6, 1, 1, -3, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, -3, 0],
  #[1, -4, -9, 0, 5, 7, -3, -2, -5, -1, -6, 0, -1, -6, 1, -3,
    -4, -1, 1, 0, -1, 6, -2, 0, -1, -1, 0, 0, 0, 0, 0, -2,
    2, 2, 0, -2, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 3],
  #[7, 6, 3, -7, -5, -8, 7, 2, 6, 3, 5, 0, 0, 5, 0, 5,
    2, 4, -4, 1, 0, -2, 2, 0, -1, -1, 1, 0, 2, 0, -2, 1,
    -2, -2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, -2],
  #[-3, 2, 8, 3, -3, -4, 0, 0, 2, 0, 3, 0, -1, 4, 0, 1,
    2, 0, 0, -1, 0, -5, 2, 0, 2, 0, 0, 0, -1, 0, 1, 2,
    -1, -2, 0, 2, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -2],
  #[-4, 0, 0, -4, -6, -2, 2, -4, 1, 1, 5, 0, -2, 1, 0, 2,
    -2, 3, -2, -4, -1, -1, 1, 0, 0, -3, 0, 0, 4, 0, 1, 1,
    -4, -1, 0, 2, 0, 0, 1, 0, 0, -2, 0, 0, 0, 0, 1, 1],
  #[0, -1, -1, 15, 14, 9, -8, 6, -5, -6, -12, 0, 5, -4, 0, -6,
    2, -8, 7, 7, 0, 2, -3, 0, 1, 7, 0, 0, -9, 0, -1, -2,
    8, 2, 0, -4, 0, 0, 0, 1, 0, 4, 0, 0, 0, 0, -3, -1],
  #[7, 2, 0, 1, 6, 1, 0, 7, 1, -1, -4, 0, 3, 0, 0, 1,
    4, -4, 3, 7, 2, -1, -1, 0, -2, 7, 0, 0, -5, 0, -2, -2,
    4, 1, 0, -3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, -2],
  #[6, -2, -3, -4, 2, 1, 2, 2, 0, 0, -2, 1, 0, -2, 0, 0,
    0, 0, 0, 0, 1, 2, 0, 0, -1, 1, 0, 0, -1, 0, 0, -2,
    2, 2, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  #[12, 12, 11, -9, -7, -17, 13, 8, 13, 5, 10, 0, 1, 11, 0, 10,
    8, 4, -4, 4, 2, -9, 5, 0, -2, 3, 0, 0, 0, 0, -3, 2,
    -2, -3, 0, 2, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 3, -7],
  #[8, 7, 9, -10, -9, -14, 10, 3, 9, 5, 10, 0, -1, 8, 0, 7,
    5, 5, -5, -1, 2, -6, 4, 0, 0, -1, 0, 1, 2, 0, -1, 2,
    -3, -2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, -4],
  #[1, 0, 3, -5, -5, -5, 3, -2, 2, 2, 4, 0, -3, 2, 0, 2,
    0, 3, -3, -3, 0, -2, 2, 0, 1, -3, 0, 0, 2, 0, 1, 1,
    -2, -1, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 1, 0],
  #[8, 11, 12, -5, -5, -16, 10, 7, 10, 4, 9, 0, 1, 10, 0, 7,
    7, 3, -4, 3, 2, -8, 4, 0, 0, 2, 0, 0, -1, 0, -2, 2,
    -2, -3, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 2, -6],
  #[-10, -6, -3, 4, -1, 7, -6, -8, -6, -2, -2, 0, -3, -4, 0, -4,
    -5, 0, 0, -5, -2, 3, -1, 0, 2, -5, 0, 0, 3, 0, 2, 1,
    -2, 0, 0, 1, 0, 0, 0, 0, 0, -2, 0, 1, 0, 0, -1, 4],
  #[-1, 5, 2, -14, -13, -11, 9, -4, 4, 7, 12, 0, -4, 4, 0, 6,
    0, 9, -7, -7, 0, -3, 3, 0, 0, -7, 0, 0, 9, 0, 0, 2,
    -8, -2, 0, 4, 1, 0, 0, 0, 0, -3, 0, 0, 0, 0, 3, 1]
]

private def fixedRows : Matrix (Fin 16) (Fin 48) ℤ :=
  fun i j => (fixedRowsData.getD i.val #[]).getD j.val 0

private theorem fixedRows_columns : fixedRows.submatrix id fixedColumns = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxHeartbeats 2000000 in
-- Reduce the sixteen rows of the matrix-product certificate in the kernel.
private theorem fixedRows_action : fixedRows * nebeOrderThree = fixedRows := by
  ext i j
  suffices h : List.ofFn (fun j => (List.zipWith (· * ·) (List.ofFn (fixedRows i))
      (List.ofFn (fun k => nebeOrderThree k j))).sum) = List.ofFn (fixedRows i) by
    rw [Matrix.mul_apply, ← dotOfFn_eq]
    exact congrFun (List.ofFn_injective h) j
  fin_cases i <;> decide +kernel

private abbrev rowsOver (R : Type*) [Ring R] := fixedRows.map (Int.castRingHom R)

private theorem coordinates_of_rows {R : Type*} [Ring R] (x : Fin 16 → R) :
    (x ᵥ* rowsOver R) ∘ fixedColumns = x := by
  have hc : (rowsOver R).submatrix id fixedColumns = 1 := by
    have h := congrArg ((Int.castRingHom R).mapMatrix (m := Fin 16)) fixedRows_columns
    simpa only [RingHom.mapMatrix_apply, Matrix.submatrix_map, map_one] using h
  funext j
  have h := congrFun (congrArg (Matrix.vecMul x) hc) j
  rw [Matrix.vecMul_one] at h
  simpa only [Matrix.vecMul, Matrix.col_apply, Matrix.submatrix_apply, id_eq,
    Function.comp_apply] using h

private theorem rows_injective {R : Type*} [Ring R] :
    Function.Injective (rowsOver R).vecMul := by
  intro x y h
  simpa only [coordinates_of_rows] using congrArg (· ∘ fixedColumns) h

private theorem rows_fixed (x : Fin 16 → ℂ) :
    rowAction ℂ nebeOrderThree (x ᵥ* rowsOver ℂ) = x ᵥ* rowsOver ℂ := by
  change (nebeOrderThreeᵀ.map (Int.castRingHom ℂ)) *ᵥ (x ᵥ* rowsOver ℂ) =
    x ᵥ* rowsOver ℂ
  rw [Matrix.transpose_map, Matrix.mulVec_transpose, Matrix.vecMul_vecMul]
  change x ᵥ* (fixedRows.map (Int.castRingHom ℂ) *
    nebeOrderThree.map (Int.castRingHom ℂ)) = _
  rw [← Matrix.map_mul, fixedRows_action]

private theorem cast_rows {R : Type*} [Ring R] (x : Fin 16 → ℤ) :
    (Int.castRingHom R ∘ (x ᵥ* fixedRows)) = (Int.castRingHom R ∘ x) ᵥ* rowsOver R := by
  funext i
  exact (Int.castRingHom R).map_vecMul fixedRows x i

private def fixedChargeCoordinates : (Fin 16 → ℤ) ≃ FixedCharge where
  toFun x := ⟨x ᵥ* fixedRows, by
    rw [g_apply, Matrix.vecMul_vecMul, fixedRows_action]⟩
  invFun a := a.1 ∘ fixedColumns
  left_inv x := by
    simpa only [rowsOver, Int.castRingHom_int, RingHom.coe_id, Matrix.map_id] using
      coordinates_of_rows x
  right_inv a := by
    let F := LinearMap.ker (rowAction ℂ nebeOrderThree - 1)
    let f : (Fin 16 → ℂ) →ₗ[ℂ] F := (rowsOver ℂ).vecMulLinear.codRestrict F
      (fun x => by simpa [F, LinearMap.mem_ker, sub_eq_zero] using rows_fixed x)
    have hdim : Module.finrank ℂ (Fin 16 → ℂ) = Module.finrank ℂ F := by
      rw [nebeOrderThree_fixedRank16]
      simp
    have hf : Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
        (fun _ _ h => rows_injective (congrArg Subtype.val h))
    have ha : castCharge a.1 ∈ F := by
      have h := (g_apply a.1).symm.trans a.2
      change (rowAction ℂ nebeOrderThree - 1) (castCharge a.1) = 0
      rw [LinearMap.sub_apply, sub_eq_zero]
      change rowAction ℂ nebeOrderThree (castCharge a.1) = castCharge a.1
      rw [action_embed, h]
    obtain ⟨x, hx⟩ := hf ⟨castCharge a.1, ha⟩
    have hx' : x ᵥ* rowsOver ℂ = castCharge a.1 := congrArg Subtype.val hx
    have hcoord : x = Int.castRingHom ℂ ∘ (a.1 ∘ fixedColumns) := by
      simpa only [coordinates_of_rows, Function.comp_assoc] using
        congrArg (· ∘ fixedColumns) hx'
    apply Subtype.ext
    apply funext
    intro i
    apply Int.cast_injective (α := ℂ)
    change (Int.castRingHom ℂ ∘ ((a.1 ∘ fixedColumns) ᵥ* fixedRows)) i =
      (castCharge a.1) i
    rw [cast_rows, ← hcoord, hx']

private abbrev ambientGram (R : Type*) [Ring R] := (Int.castRingHom R).mapMatrix nebeGram
private abbrev coordinateGram (R : Type*) [Ring R] :=
  rowsOver R * ambientGram R * (rowsOver R)ᵀ

private theorem coordinate_form {R : Type*} [CommRing R] (x y : Fin 16 → R) :
    (coordinateGram R).toBilin' x y =
      (ambientGram R).toBilin' (x ᵥ* rowsOver R) (y ᵥ* rowsOver R) := by
  have h := Matrix.toBilin'_comp (ambientGram R) (rowsOver R)ᵀ (rowsOver R)ᵀ
  simpa only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply', Matrix.mulVecLin_apply,
    Matrix.mulVec_transpose, Matrix.transpose_transpose] using
      (congrArg (fun (b : LinearMap.BilinForm R (Fin 16 → R)) => b x y) h).symm

private theorem coordinateGram_pos : (coordinateGram ℝ).PosDef := by
  simpa only [coordinateGram, ambientGram, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    nebeGram_posDef.mul_mul_conjTranspose_same (B := rowsOver ℝ) rows_injective

private def dividedGram : Matrix (Fin 16) (Fin 16) ℤ :=
  fun i j => fixedChargePairing (fixedChargeCoordinates (Pi.single i 1))
    (fixedChargeCoordinates (Pi.single j 1))

private theorem coordinateGram_eq (R : Type*) [CommRing R] :
    coordinateGram R = (3 : R) • (Int.castRingHom R).mapMatrix dividedGram := by
  have h : coordinateGram ℤ = (3 : ℤ) • dividedGram := by
    ext i j
    have hform := coordinate_form (Pi.single i (1 : ℤ)) (Pi.single j (1 : ℤ))
    simp only [Matrix.toBilin'_apply', single_one_dotProduct, Matrix.mulVec_single_one,
      Matrix.col_apply] at hform
    rw [hform]
    rw [Matrix.smul_apply, zsmul_eq_mul]
    change _ = 3 * fixedChargePairing (fixedChargeCoordinates (Pi.single i 1))
      (fixedChargeCoordinates (Pi.single j 1))
    rw [fixed_charge_pairing_mul_three]
    simp [fixedChargeCoordinates, bilinear, rowsOver, ambientGram,
      dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rfl
  have hc := congrArg (fun M => M.map (Int.castRingHom R)) h
  have hs : ((3 : ℤ) • dividedGram).map (Int.castRingHom R) =
      (3 : R) • dividedGram.map (Int.castRingHom R) := by
    ext i j
    change (Int.castRingHom R) ((3 : ℤ) • dividedGram i j) =
      (3 : R) • (Int.castRingHom R) (dividedGram i j)
    rw [zsmul_eq_mul, smul_eq_mul, map_mul]
    exact congrArg (· * (Int.castRingHom R) (dividedGram i j))
      (map_natCast (Int.castRingHom R) 3)
  change (coordinateGram ℤ).map (Int.castRingHom R) =
    ((3 : ℤ) • dividedGram).map (Int.castRingHom R) at hc
  rw [hs] at hc
  have hid : (⇑(Int.castRingHom R)) ∘ (⇑(Int.castRingHom ℤ)) = Int.castRingHom R := by
    funext i
    simp
  simpa only [coordinateGram, ambientGram, rowsOver, RingHom.mapMatrix_apply, Matrix.map_mul,
    Matrix.transpose_map, Matrix.map_map, hid] using hc

private def gradePhase (τ : ℂ) (n : ℤ) : ℂ :=
  exp (2 * Real.pi * I * τ * ((n : ℂ) - lattice.rank / 24))

/-- The native cubic lift's finite full-grade trace with the rank-48 vacuum shift. -/
def traceTerm (τ : ℂ) (n : ℤ) : ℂ :=
  actualFullGradeStandardLiftTrace n * gradePhase τ n

/-- The normalized cubic twining character, formed from all integral grades. -/
def actualCubicTwiningCharacter (τ : ℂ) : ℂ :=
  ∑' n : ℤ, traceTerm τ n

private def chargeTerm (τ : ℂ) (a : Charge lattice) : ℂ :=
  exp (2 * Real.pi * I * τ * (chargeEnergy lattice a : ℂ))

/-- Theta series of the integrally fixed charges with the original lattice energy. -/
def fixedChargeTheta (τ : ℂ) : ℂ :=
  ∑' a : FixedCharge, chargeTerm τ a.1

private def occupationQ (τ : ℂ) : ℂ := exp (2 * Real.pi * I * (3 * τ))

private def occupationTerm (τ : ℂ) (d : Occupation) : ℂ :=
  occupationQ τ ^ integerEnergy (Fin 16) d

private def vacuum (τ : ℂ) : ℂ :=
  exp (-2 * Real.pi * I * τ * lattice.rank / 24)

private def totalEnergy (x : FixedCharge × Occupation) : ℤ :=
  chargeEnergy lattice x.1.1 + 3 * (integerEnergy (Fin 16) x.2 : ℤ)

private theorem gradePhase_totalEnergy (τ : ℂ) (x : FixedCharge × Occupation) :
    gradePhase τ (totalEnergy x) = vacuum τ * (chargeTerm τ x.1.1 * occupationTerm τ x.2) := by
  unfold gradePhase totalEnergy vacuum chargeTerm occupationTerm occupationQ
  rw [← exp_nat_mul, ← exp_add, ← exp_add]
  congr 1
  push_cast
  ring

private theorem chargeTerm_eq_gaussian (τ : ℂ) (a : Charge lattice) :
    chargeTerm τ a = exp (Real.pi * I * τ *
      (quadratic (gramReal lattice) (fun i => (a i : ℝ)) : ℂ)) := by
  have h : quadratic (gramReal lattice) (fun i => (a i : ℝ)) =
      2 * (chargeEnergy lattice a : ℝ) := by
    simpa [quadratic, gramReal, realQuadratic, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_assoc] using realQuadratic_charge lattice a
  unfold chargeTerm
  rw [h]
  push_cast
  congr 1
  ring


private theorem coordinateGram_complex :
    Complex.ofRealHom.mapMatrix (coordinateGram ℝ) = coordinateGram ℂ := by
  have hc : (⇑Complex.ofRealHom) ∘ (⇑(Int.castRingHom ℝ)) = Int.castRingHom ℂ := by
    funext i
    simp
  simp only [coordinateGram, ambientGram, rowsOver, RingHom.mapMatrix_apply, Matrix.map_mul,
    Matrix.transpose_map, Matrix.map_map, hc]

private theorem dividedGram_unit : IsUnit dividedGram := by
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  intro z
  let A := coordinateGram ℂ
  let c := Int.castRingHom ℂ
  let x := A⁻¹ *ᵥ (c ∘ z)
  have hA : IsUnit A.det := by
    change IsUnit (coordinateGram ℂ).det
    rw [← coordinateGram_complex, ← Complex.ofRealHom.map_det]
    exact (coordinateGram_pos.det_pos.ne'.isUnit).map Complex.ofRealHom
  have hx : A *ᵥ x = c ∘ z := by
    dsimp only [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]
  obtain ⟨a, ha⟩ := (fixed_dual_iff_third_fixed_charge (x ᵥ* rowsOver ℂ)).mp
    ⟨rows_fixed x, fun b => by
      obtain ⟨v, rfl⟩ := fixedChargeCoordinates.surjective b
      change ∃ k : ℤ, (ambientGram ℂ).toBilin' (c ∘ (v ᵥ* fixedRows))
        (x ᵥ* rowsOver ℂ) = (k : ℂ)
      rw [cast_rows, ← coordinate_form, Matrix.toBilin'_apply', hx]
      refine ⟨v ⬝ᵥ z, ?_⟩
      exact (c.map_dotProduct v z).symm⟩
  let y := a.1 ∘ fixedColumns
  have hxy : x = (3 : ℂ)⁻¹ • (c ∘ y) := by
    have h := congrArg (· ∘ fixedColumns) ha
    rw [coordinates_of_rows] at h
    exact h
  have h := hx
  change coordinateGram ℂ *ᵥ x = c ∘ z at h
  rw [hxy, coordinateGram_eq ℂ, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    mul_inv_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_smul] at h
  refine ⟨y, funext fun i => Int.cast_injective (α := ℂ) ?_⟩
  exact (c.map_mulVec dividedGram y i).trans (congrFun h i)

private theorem coordinateGram_sqrt_det : Real.sqrt (coordinateGram ℝ).det = 3 ^ 8 := by
  have hp := coordinateGram_pos.det_pos
  rw [coordinateGram_eq, Matrix.det_smul, Fintype.card_fin,
    ← (Int.castRingHom ℝ).map_det, Int.coe_castRingHom] at hp ⊢
  have hu : |dividedGram.det| = 1 :=
    Int.isUnit_iff_abs_eq.mp ((Matrix.isUnit_iff_isUnit_det dividedGram).mp dividedGram_unit)
  have hd : 0 < dividedGram.det := by
    exact Int.cast_pos.mp (pos_of_mul_pos_right hp (by positivity : 0 ≤ (3 : ℝ) ^ 16))
  rw [abs_of_pos hd] at hu
  rw [hu]
  have hone : ((fun x : ℤ => (x : ℝ)) 1) = (1 : ℝ) := Int.cast_one
  rw [hone, mul_one, show (3 : ℝ) ^ 16 = ((3 : ℝ) ^ 8) ^ 2 by norm_num,
    Real.sqrt_sq (by positivity)]

private theorem fixedChargeTheta_coordinate (τ : ℂ) :
    fixedChargeTheta τ = D5.S3.Fourier.MatrixGaussian.theta (coordinateGram ℝ) τ := by
  rw [fixedChargeTheta, D5.S3.Fourier.MatrixGaussian.theta]
  refine (fixedChargeCoordinates.tsum_eq _).symm.trans (tsum_congr fun x => ?_)
  rw [chargeTerm_eq_gaussian]
  congr 2
  apply congrArg (fun r : ℝ => (r : ℂ))
  change quadratic (ambientGram ℝ) (Int.castRingHom ℝ ∘ (x ᵥ* fixedRows)) =
    quadratic (coordinateGram ℝ) (Int.castRingHom ℝ ∘ x)
  simpa only [cast_rows, quadratic, Matrix.toBilin'_apply'] using
    (coordinate_form (Int.castRingHom ℝ ∘ x) (Int.castRingHom ℝ ∘ x)).symm

private theorem inverseTheta_fixedCharge (τ : ℂ) :
    D5.S3.Fourier.MatrixGaussian.theta (coordinateGram ℝ)⁻¹ τ = fixedChargeTheta (τ / 9) := by
  let e : (Fin 16 → ℤ) ≃ (Fin 16 → ℤ) := Equiv.ofBijective dividedGram.mulVec
    ⟨Matrix.mulVec_injective_of_isUnit dividedGram_unit,
      Matrix.mulVec_surjective_iff_isUnit.mpr dividedGram_unit⟩
  rw [fixedChargeTheta_coordinate, D5.S3.Fourier.MatrixGaussian.theta,
    D5.S3.Fourier.MatrixGaussian.theta]
  refine (e.tsum_eq _).symm.trans (tsum_congr fun x => ?_)
  let v := Int.castRingHom ℝ ∘ x
  let A := coordinateGram ℝ
  have hcast : (fun i => (e x i : ℝ)) = (3 : ℝ)⁻¹ • (A *ᵥ v) := by
    have h : (fun i => (e x i : ℝ)) = (Int.castRingHom ℝ).mapMatrix dividedGram *ᵥ v :=
      funext fun i => (Int.castRingHom ℝ).map_mulVec dividedGram x i
    rw [h]
    change _ = (3 : ℝ)⁻¹ • (coordinateGram ℝ *ᵥ v)
    rw [coordinateGram_eq, Matrix.smul_mulVec, smul_smul,
      inv_mul_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), one_smul]
  have hquad : quadratic A⁻¹ (fun i => (e x i : ℝ)) = (3 : ℝ)⁻¹ ^ 2 * quadratic A v := by
    rw [hcast, quadratic, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ coordinateGram_pos.det_pos.ne'.isUnit, Matrix.one_mulVec,
      smul_dotProduct, dotProduct_smul, pow_two, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, dotProduct_comm (A *ᵥ v), quadratic]
  rw [hquad]
  congr 1
  change Real.pi * I * τ * (((3 : ℝ)⁻¹ ^ 2 * quadratic A v : ℝ) : ℂ) =
    Real.pi * I * (τ / 9) * (quadratic A v : ℂ)
  push_cast
  ring

private def fixedChargeCutoff (n : ℤ) : Finset (Charge lattice) :=
  (positiveChargeCutoff lattice nebeGram_posDef n).filter (fun a => g a = a)

private abbrev GradeFiber (n : ℤ) := {x : FixedCharge × Occupation // totalEnergy x = n}

private abbrev OccupationFiber (n : ℤ) (a : Charge lattice) :=
  {d : Occupation // 3 * (integerEnergy (Fin 16) d : ℤ) = n - chargeEnergy lattice a}

private def gradeFiberEquiv (n : ℤ) :
    GradeFiber n ≃ Σ a : fixedChargeCutoff n, OccupationFiber n a.1 where
  toFun x := by
    have he := x.2
    change chargeEnergy lattice x.1.1.1 + 3 * (integerEnergy (Fin 16) x.1.2 : ℤ) = n at he
    have ha := chargeEnergy_nonneg lattice nebeGram_posDef x.1.1.1
    have hc : x.1.1.1 ∈ fixedChargeCutoff n := by
      refine Finset.mem_filter.mpr ⟨?_, x.1.1.2⟩
      simp only [positiveChargeCutoff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      rw [Int.toNat_of_nonneg (show 0 ≤ n by omega)]
      omega
    refine ⟨⟨x.1.1.1, hc⟩, ⟨x.1.2, ?_⟩⟩
    change 3 * (integerEnergy (Fin 16) x.1.2 : ℤ) = n - chargeEnergy lattice x.1.1.1
    omega
  invFun x := by
    have hf := (Finset.mem_filter.mp x.1.2).2
    have he := x.2.2
    refine ⟨(⟨x.1.1, hf⟩, x.2.1), ?_⟩
    change chargeEnergy lattice x.1.1 + 3 * (integerEnergy (Fin 16) x.2.1 : ℤ) = n
    omega
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Sigma.ext (Subtype.ext rfl)
    apply heq_of_eq
    rfl

private theorem occupationFrequency_eq_integerEnergy (d : Occupation) :
    occupationFrequency d = integerEnergy (Fin 16) d := by
  simp only [occupationFrequency, integerEnergy, frequency, Finsupp.weight_apply,
    Nat.nsmul_eq_mul, Nat.mul_comm]

private theorem occupationFiber_finite (n : ℤ) (a : Charge lattice) :
    Finite (OccupationFiber n a) := by
  let m := (n - chargeEnergy lattice a).toNat
  let := occupationSublevel_finite m
  let includeSublevel (d : OccupationFiber n a) : {d : Occupation // occupationFrequency d ≤ m} :=
    ⟨d.1, by
      rw [occupationFrequency_eq_integerEnergy]
      have hd := d.2
      change 3 * (integerEnergy (Fin 16) d.1 : ℤ) = n - chargeEnergy lattice a at hd
      dsimp only [m]
      omega⟩
  refine Finite.of_injective includeSublevel (fun _ _ h => Subtype.ext ?_)
  exact congrArg (fun d : {d : Occupation // occupationFrequency d ≤ m} => d.1) h

private theorem actual_full_grade_trace_eq_grade_fiber_card (n : ℤ) :
    actualFullGradeStandardLiftTrace n = (Nat.card (GradeFiber n) : ℂ) := by
  classical
  let (a : fixedChargeCutoff n) : Finite (OccupationFiber n a.1) := occupationFiber_finite n a.1
  rw [actual_full_grade_trace_eq_fixed_occupation, Nat.card_congr (gradeFiberEquiv n),
    Nat.card_sigma, Nat.cast_sum]
  exact (Finset.sum_coe_sort (fixedChargeCutoff n)
    (fun a : Charge lattice => (Nat.card (OccupationFiber n a) : ℂ))).symm

private theorem traceTerm_eq_fiber (τ : ℂ) (n : ℤ) :
    (∑' x : GradeFiber n, gradePhase τ (totalEnergy x.1)) = traceTerm τ n := by
  classical
  let (a : fixedChargeCutoff n) : Finite (OccupationFiber n a.1) := occupationFiber_finite n a.1
  let : Finite (GradeFiber n) := Finite.of_equiv _ (gradeFiberEquiv n).symm
  let : Fintype (GradeFiber n) := Fintype.ofFinite _
  calc
    _ = ∑' _x : GradeFiber n, gradePhase τ n :=
      tsum_congr (fun x => congrArg (gradePhase τ) x.2)
    _ = _ := by
      rw [traceTerm, actual_full_grade_trace_eq_grade_fiber_card, tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- In the upper half-plane the actual normalized cubic trace converges
absolutely and equals the fixed-charge theta series divided by eta(3τ) to
the sixteenth power. -/
theorem actual_cubic_twining_character_eq_theta_div_eta (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : ℤ => ‖traceTerm τ n‖) ∧
      actualCubicTwiningCharacter τ = fixedChargeTheta τ / ModularForm.eta (3 * τ) ^ 16 := by
  have hτ3 : 0 < (3 * τ).im := by
    simpa [Complex.mul_im] using mul_pos (by norm_num : (0 : ℝ) < 3) hτ
  have hq : ‖occupationQ τ‖ < 1 := by
    simpa [occupationQ, Function.Periodic.qParam] using
      Function.Periodic.norm_qParam_lt_one (by norm_num : (0 : ℝ) < 1) hτ3
  have hc_all : Summable (fun a : Charge lattice => ‖chargeTerm τ a‖) :=
    (summable_norm_theta (gramReal lattice) nebeGram_posDef τ hτ).congr
      (fun a => congrArg norm (chargeTerm_eq_gaussian τ a).symm)
  have hc : Summable (fun a : FixedCharge => ‖chargeTerm τ a.1‖) :=
    hc_all.subtype {a | g a = a}
  have ho : Summable (fun d : Occupation => ‖occupationTerm τ d‖) := oscillator_norm 16 hq
  let f : FixedCharge × Occupation → ℂ := fun x => gradePhase τ (totalEnergy x)
  have habs : Summable (fun x => ‖f x‖) := by
    simpa only [f, gradePhase_totalEnergy, norm_mul] using (hc.mul_norm ho).mul_left ‖vacuum τ‖
  have hnorm (n : ℤ) : ‖traceTerm τ n‖ ≤ ∑' x : GradeFiber n, ‖f x.1‖ := by
    rw [← traceTerm_eq_fiber τ n]
    exact norm_tsum_le_tsum_norm (habs.subtype _)
  have hgroup := habs.hasSum.tsum_fiberwise totalEnergy
  have hsum : HasSum (traceTerm τ) (∑' x, f x) :=
    (habs.of_norm.hasSum.tsum_fiberwise totalEnergy).congr_fun
      (fun n => (traceTerm_eq_fiber τ n).symm)
  refine ⟨hgroup.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm, ?_⟩
  rw [actualCubicTwiningCharacter, hsum.tsum_eq]
  simp_rw [f, gradePhase_totalEnergy]
  rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm hc ho]
  change vacuum τ * (fixedChargeTheta τ * ∑' d : Occupation, occupationTerm τ d) = _
  have hshift : vacuum τ = exp (-2 * Real.pi * I * (3 * τ) * (16 : ℕ) / 24) := by
    change exp (-2 * Real.pi * I * τ * (48 : ℂ) / 24) = _
    congr 1
    push_cast
    ring
  rw [mul_left_comm, hshift]
  simp only [occupationTerm, occupationQ, oscillator_eta 16 (3 * τ) hτ3,
    div_eq_mul_inv (fixedChargeTheta τ)]

/-- Poisson inversion of the integral fixed-charge theta series with its exact
dual scaling and covolume. -/
theorem fixed_charge_theta_S (τ : ℂ) (hτ : 0 < τ.im) :
    fixedChargeTheta (-1 / τ) = (-I * τ / 3) ^ 8 * fixedChargeTheta (τ / 9) := by
  rw [fixedChargeTheta_coordinate,
    D5.S3.Fourier.MatrixGaussian.theta_inversion _ coordinateGram_pos τ hτ,
    inverseTheta_fixedCharge, coordinateGram_sqrt_det, Complex.ofReal_pow, Complex.ofReal_ofNat]
  have hpower : ((16 : ℕ) : ℂ) / 2 = ((8 : ℕ) : ℂ) := by norm_num
  rw [hpower, Complex.cpow_natCast, div_pow]

/-- The analytic S transform of the character defined from the actual cubic
twining traces on the full P48q eigenspaces. -/
theorem actual_cubic_twining_character_S (τ : ℂ) (hτ : 0 < τ.im) :
    actualCubicTwiningCharacter (-1 / τ) = fixedChargeTheta (τ / 9) /
      ModularForm.eta (τ / 3) ^ 16 := by
  have hS : 0 < (-1 / τ).im := by
    simpa using UpperHalfPlane.im_pnat_div_pos 1 (⟨τ, hτ⟩ : UpperHalfPlane)
  have hτ3 : 0 < (τ / 3).im := by
    have h : τ / 3 = ((1 / 3 : ℝ) : ℂ) * τ := by
      push_cast
      ring
    rw [h]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
      mul_pos (by norm_num : (0 : ℝ) < 1 / 3) hτ
  have harg : 3 * (-1 / τ) = -1 / (τ / 3) := by
    rw [div_div_eq_mul_div]
    ring
  have hroot : sqrt (-I * (τ / 3)) ^ 16 = (-I * τ / 3) ^ 8 := by
    have hpower : (16 : ℂ) * (2 : ℂ)⁻¹ = ((8 : ℕ) : ℂ) := by norm_num
    rw [sqrt, ← cpow_nat_mul]
    change (-I * (τ / 3)) ^ ((16 : ℂ) * (2 : ℂ)⁻¹) = _
    rw [hpower, cpow_natCast, ← mul_div_assoc]
  have hweight : (-I * τ / 3) ^ 8 ≠ 0 := by
    have ht : τ ≠ 0 := by
      intro h
      simp [h] at hτ
    exact pow_ne_zero _ (div_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) ht) (by norm_num))
  rw [(actual_cubic_twining_character_eq_theta_div_eta _ hS).2, fixed_charge_theta_S τ hτ,
    harg, eta_S_principal _ hτ3, mul_pow, hroot, mul_div_mul_left _ _ hweight]

/-- The literal native twisted conformal trace coefficient at `L₀` grade
`16 / 9 + n / 3`, computed from the momentum and occupation weight basis. -/
noncomputable def nativeTwistedTraceCoeff (n : ℕ) : ℂ :=
  Module.finrank ℂ
    (Module.End.eigenspace
      (HVertexOperator.coeff (nativeField (omega lattice (actualInverse lattice))) (-6))
      (16 / 9 + (n : ℂ) / 3))

/-- The native coefficient is the cardinality of the exact finite weight fibre. -/
theorem native_twisted_trace_coeff_eq_weight_fiber_card (n : ℕ) :
    nativeTwistedTraceCoeff n =
      (Nat.card {x : P48qTwistedChargeAction.Momentum × P48qTwistedStateEnergy.Occupation //
        (totalWeight x.1 x.2 : ℂ) = 16 / 9 + (n : ℂ) / 3} : ℂ) := by
  unfold nativeTwistedTraceCoeff
  rw [native_conformal_coeff_neg_six_eq_totalLZero]
  let a : ℂ := 16 / 9 + (n : ℂ) / 3
  letI : FiniteDimensional ℂ (totalLZero.eigenspace a) :=
    totalLZero_eigenspace_finiteDimensional a
  letI : Finite {x : P48qTwistedChargeAction.Momentum ×
      P48qTwistedStateEnergy.Occupation //
      (totalWeight x.1 x.2 : ℂ) = a} :=
    (totalWeight_fiber_finite a).to_subtype
  letI : Fintype {x : P48qTwistedChargeAction.Momentum ×
      P48qTwistedStateEnergy.Occupation //
      (totalWeight x.1 x.2 : ℂ) = a} := Fintype.ofFinite _
  have hfin : Module.finrank ℂ (totalLZero.eigenspace a) =
      Nat.card {x : P48qTwistedChargeAction.Momentum ×
        P48qTwistedStateEnergy.Occupation //
        (totalWeight x.1 x.2 : ℂ) = a} := by
    rw [LinearEquiv.finrank_eq (totalLZeroEigenspaceCoeffEquiv a),
      Module.finrank_finsupp_self]
    simp only [Nat.card_eq_fintype_card]
  simpa [a] using congrArg (fun k : ℕ => (k : ℂ)) hfin

/-- The same coefficient is the literal identity trace on the native-field
eigenspace, so the weight-fibre formula is a finite-grade trace formula. -/
theorem native_twisted_identity_trace_eq_weight_fiber_card (n : ℕ) :
    LinearMap.trace ℂ
        (Module.End.eigenspace
          (HVertexOperator.coeff (nativeField (omega lattice (actualInverse lattice))) (-6))
          (16 / 9 + (n : ℂ) / 3)) LinearMap.id =
      (Nat.card {x : P48qTwistedChargeAction.Momentum × P48qTwistedStateEnergy.Occupation //
        (totalWeight x.1 x.2 : ℂ) = 16 / 9 + (n : ℂ) / 3} : ℂ) := by
  let a : ℂ := 16 / 9 + (n : ℂ) / 3
  letI : FiniteDimensional ℂ
      (Module.End.eigenspace
        (HVertexOperator.coeff (nativeField (omega lattice (actualInverse lattice))) (-6)) a) := by
    rw [native_conformal_coeff_neg_six_eq_totalLZero]
    exact totalLZero_eigenspace_finiteDimensional a
  rw [LinearMap.trace_id]
  simpa [nativeTwistedTraceCoeff, a] using
    native_twisted_trace_coeff_eq_weight_fiber_card n

private def momentumEquivFixedCharge : Momentum ≃ FixedCharge :=
  Equiv.subtypeEquivRight fun a => by
    constructor
    · rintro ⟨b, rfl⟩
      exact ThirdTwistedChargeAction.norm_fixed lattice g g_cube b
    · intro ha
      exact (momentum_index_iff a).mpr
        (nebeOrderThree_fixed_is_norm_image a ((g_apply a).symm.trans ha))

private theorem totalWeight_eq_totalEnergy (p : Momentum) (d : Occupation) :
    (totalWeight p d : ℂ) =
      16 / 9 + (totalEnergy (momentumEquivFixedCharge p, d) : ℂ) / 9 := by
  rw [totalWeight, occupationFrequency_eq_integerEnergy, momentumWeight_eq_chargeEnergy]
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_natCast,
    Complex.ofReal_intCast]
  change _ = 16 / 9 + ((chargeEnergy lattice p.1 +
    3 * (integerEnergy (Fin 16) d : ℤ) : ℤ) : ℂ) / 9
  push_cast
  ring

/-- The native twisted coefficient at weight `16 / 9 + k / 3` equals the
actual standard-lift trace at untwisted grade `3 * k`. -/
theorem native_twisted_trace_coeff_eq_actual_full_grade_trace (k : ℕ) :
    nativeTwistedTraceCoeff k = actualFullGradeStandardLiftTrace (3 * (k : ℤ)) := by
  rw [native_twisted_trace_coeff_eq_weight_fiber_card,
    actual_full_grade_trace_eq_grade_fiber_card]
  apply congrArg (fun n : ℕ => (n : ℂ))
  apply Nat.card_congr
  refine (momentumEquivFixedCharge.prodCongr (Equiv.refl Occupation)).subtypeEquiv ?_
  rintro ⟨p, d⟩
  rw [totalWeight_eq_totalEnergy]
  let n := totalEnergy (momentumEquivFixedCharge p, d)
  change 16 / 9 + (n : ℂ) / 9 = 16 / 9 + (k : ℂ) / 3 ↔ n = 3 * (k : ℤ)
  constructor
  · intro h
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination 9 * h
  · intro h
    rw [h]
    push_cast
    ring

private theorem actual_full_grade_trace_eq_zero_off_range (n : ℤ)
    (hn : n ∉ Set.range (fun k : ℕ => 3 * (k : ℤ))) :
    actualFullGradeStandardLiftTrace n = 0 := by
  have : IsEmpty (GradeFiber n) := ⟨fun x => by
    let p := momentumEquivFixedCharge.symm x.1.1
    obtain ⟨m, hm⟩ := P48qFullEnergySpectrum.six_dvd_momentumNorm p
    change bilinear lattice x.1.1.1 x.1.1.1 = 6 * m at hm
    have hnorm := two_chargeEnergy lattice x.1.1.1
    have hpos := chargeEnergy_nonneg lattice nebeGram_posDef x.1.1.1
    have hx := x.2
    change chargeEnergy lattice x.1.1.1 + 3 * (integerEnergy (Fin 16) x.1.2 : ℤ) = n at hx
    apply hn
    refine ⟨(m + (integerEnergy (Fin 16) x.1.2 : ℤ)).toNat, ?_⟩
    change 3 * (((m + (integerEnergy (Fin 16) x.1.2 : ℤ)).toNat : ℕ) : ℤ) = n
    omega⟩
  simp [actual_full_grade_trace_eq_grade_fiber_card]

/-- A native twisted identity-trace coefficient with its rank-48 vacuum shift. -/
def nativeTwistedTraceTerm (τ : ℂ) (k : ℕ) : ℂ :=
  nativeTwistedTraceCoeff k * exp (2 * Real.pi * I * τ *
    ((16 / 9 + (k : ℂ) / 3) - lattice.rank / 24))

/-- The normalized trace series of the native cubic twisted module. -/
def nativeTwistedCharacter (τ : ℂ) : ℂ :=
  ∑' k : ℕ, nativeTwistedTraceTerm τ k

private theorem nativeTwistedTraceTerm_eq_traceTerm (τ : ℂ) (k : ℕ) :
    nativeTwistedTraceTerm τ k = traceTerm (τ / 9) (3 * (k : ℤ)) := by
  rw [nativeTwistedTraceTerm, traceTerm, native_twisted_trace_coeff_eq_actual_full_grade_trace,
    gradePhase]
  congr 2
  change 2 * Real.pi * I * τ * ((16 / 9 + (k : ℂ) / 3) - 48 / 24) =
    2 * Real.pi * I * (τ / 9) * (((3 * (k : ℤ) : ℤ) : ℂ) - 48 / 24)
  push_cast
  ring

/-- On the upper half-plane the native twisted trace series converges
absolutely and is the actual untwisted twining character at `τ / 9`. -/
theorem native_twisted_character_eq_twining (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun k : ℕ => ‖nativeTwistedTraceTerm τ k‖) ∧
      nativeTwistedCharacter τ = actualCubicTwiningCharacter (τ / 9) := by
  have hτ9 : 0 < (τ / 9).im := by
    rw [Complex.div_ofNat_im]
    exact div_pos hτ (by norm_num)
  let scale (k : ℕ) : ℤ := 3 * (k : ℤ)
  have hinj : Function.Injective scale := by
    intro j k h
    dsimp only [scale] at h
    omega
  refine ⟨((actual_cubic_twining_character_eq_theta_div_eta _ hτ9).1.comp_injective hinj).congr
    (fun k => congrArg norm (nativeTwistedTraceTerm_eq_traceTerm τ k).symm), ?_⟩
  have hs : Function.support (traceTerm (τ / 9)) ⊆ Set.range scale := by
    intro n hn
    by_contra h
    exact hn (by rw [traceTerm, actual_full_grade_trace_eq_zero_off_range n h, zero_mul])
  exact (tsum_congr (nativeTwistedTraceTerm_eq_traceTerm τ)).trans (hinj.tsum_eq hs)

/-- Modular inversion interchanges the two actual normalized cubic trace
series on the upper half-plane. -/
theorem actual_cubic_trace_S_interchange (τ : ℂ) (hτ : 0 < τ.im) :
    actualCubicTwiningCharacter (-1 / τ) = nativeTwistedCharacter τ ∧
      nativeTwistedCharacter (-1 / τ) = actualCubicTwiningCharacter τ := by
  have forward (z : ℂ) (hz : 0 < z.im) :
      actualCubicTwiningCharacter (-1 / z) = nativeTwistedCharacter z := by
    have hz9 : 0 < (z / 9).im := by
      rw [Complex.div_ofNat_im]
      exact div_pos hz (by norm_num)
    rw [actual_cubic_twining_character_S z hz, (native_twisted_character_eq_twining z hz).2,
      (actual_cubic_twining_character_eq_theta_div_eta _ hz9).2]
    rw [show 3 * (z / 9) = z / 3 by ring]
  have hS : 0 < (-1 / τ).im := by
    simpa using UpperHalfPlane.im_pnat_div_pos 1 (⟨τ, hτ⟩ : UpperHalfPlane)
  refine ⟨forward τ hτ, (forward _ hS).symm.trans ?_⟩
  simp [div_eq_mul_inv]

local notation "period" => (2 * (Real.pi : ℂ) * I)
local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

/-- The weight `16 / 9 + k / 3` eigenspace of the actual native conformal mode. -/
abbrev NativeConformalGrade (k : ℕ) : Submodule ℂ P48qThirdTwistedField.State :=
  Module.End.eigenspace
    (HVertexOperator.coeff (nativeField (omega lattice (actualInverse lattice))) (-6))
    (16 / 9 + (k : ℂ) / 3)

private theorem nativeConformalGrade_finiteDimensional (k : ℕ) :
    FiniteDimensional ℂ (NativeConformalGrade k) := by
  unfold NativeConformalGrade
  rw [native_conformal_coeff_neg_six_eq_totalLZero]
  exact totalLZero_eigenspace_finiteDimensional _

/-- The restriction of the actual conformal monodromy to one conformal grade. -/
def nativeGradeMonodromy (k : ℕ) : Module.End ℂ (NativeConformalGrade k) :=
  conformalMonodromy.restrict fun v hv => by
    rw [conformalMonodromy_native_conformal_eigenvector v _
      (Module.End.mem_eigenspace_iff.mp hv)]
    exact (NativeConformalGrade k).smul_mem _ hv

private theorem nativeGradeMonodromy_eq_smul (k : ℕ) :
    nativeGradeMonodromy k = exp (period * (16 / 9 + (k : ℂ) / 3)) • 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact conformalMonodromy_native_conformal_eigenvector v _
    (Module.End.mem_eigenspace_iff.mp v.property)

private theorem nativeGradeMonodromy_pow_coe (k j : ℕ) (v : NativeConformalGrade k) :
    ((nativeGradeMonodromy k ^ j) v : P48qThirdTwistedField.State) =
      (conformalMonodromy ^ j) v := by
  unfold nativeGradeMonodromy
  rw [Module.End.pow_restrict]
  rfl

/-- The finite conformal-grade trace of a power of the inserted monodromy. -/
theorem native_twisted_monodromy_trace_eq (k j : ℕ) :
    LinearMap.trace ℂ (NativeConformalGrade k) (nativeGradeMonodromy k ^ j) =
      exp (period * (j : ℂ) * (16 / 9 + (k : ℂ) / 3)) * nativeTwistedTraceCoeff k := by
  rw [nativeGradeMonodromy_eq_smul, smul_pow, one_pow, map_smul, smul_eq_mul,
    Module.End.one_eq_id, native_twisted_identity_trace_eq_weight_fiber_card,
    ← native_twisted_trace_coeff_eq_weight_fiber_card, ← exp_nat_mul]
  congr 2
  ring

/-- The third insertion is multiplication of the identity trace by the primitive cubic root. -/
theorem native_twisted_monodromy_cube_trace (k : ℕ) :
    LinearMap.trace ℂ (NativeConformalGrade k) (nativeGradeMonodromy k ^ 3) =
      ζ * nativeTwistedTraceCoeff k := by
  have hcube : nativeGradeMonodromy k ^ 3 = ζ • 1 := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [nativeGradeMonodromy_pow_coe, conformalMonodromy_cube]
    rfl
  rw [hcube, map_smul, smul_eq_mul, Module.End.one_eq_id,
    native_twisted_identity_trace_eq_weight_fiber_card,
    ← native_twisted_trace_coeff_eq_weight_fiber_card]

/-- An inserted conformal-grade trace with its rank-48 vacuum shift. -/
def nativeTwistedInsertedTerm (τ : ℂ) (j k : ℕ) : ℂ :=
  LinearMap.trace ℂ (NativeConformalGrade k) (nativeGradeMonodromy k ^ j) *
    exp (period * τ * ((16 / 9 + (k : ℂ) / 3) - lattice.rank / 24))

/-- The normalized sum of the traces with the `j`-th monodromy insertion. -/
def nativeTwistedInsertedCharacter (τ : ℂ) (j : ℕ) : ℂ :=
  ∑' k : ℕ, nativeTwistedInsertedTerm τ j k

private theorem nativeTwistedInsertedTerm_eq_shift (τ : ℂ) (j k : ℕ) :
    nativeTwistedInsertedTerm τ j k = nativeTwistedTraceTerm (τ + (j : ℂ)) k := by
  have hperiod : exp (period * (j : ℂ) * 2) = 1 := by
    rw [show period * (j : ℂ) * 2 = ((2 * j : ℕ) : ℂ) * period by push_cast; ring]
    exact exp_nat_mul_two_pi_mul_I _
  have hrank : (lattice.rank : ℂ) / 24 = 2 := by
    change (48 : ℂ) / 24 = 2
    norm_num
  rw [nativeTwistedInsertedTerm, native_twisted_monodromy_trace_eq, nativeTwistedTraceTerm, hrank]
  rw [mul_comm (exp _) (nativeTwistedTraceCoeff k), mul_assoc, ← exp_add]
  rw [show period * (j : ℂ) * (16 / 9 + (k : ℂ) / 3) +
      period * τ * ((16 / 9 + (k : ℂ) / 3) - 2) =
    period * (τ + (j : ℂ)) * ((16 / 9 + (k : ℂ) / 3) - 2) + period * (j : ℂ) * 2 by ring,
    exp_add, hperiod, mul_one]

/-- Every monodromy-inserted trace series converges absolutely on the upper
half-plane and equals the native character at `τ + j`. -/
theorem native_twisted_inserted_character_eq_shift (τ : ℂ) (hτ : 0 < τ.im) (j : ℕ) :
    Summable (fun k : ℕ => ‖nativeTwistedInsertedTerm τ j k‖) ∧
      nativeTwistedInsertedCharacter τ j = nativeTwistedCharacter (τ + (j : ℂ)) := by
  have him : 0 < (τ + (j : ℂ)).im := by simpa using hτ
  exact ⟨(native_twisted_character_eq_twining _ him).1.congr
    (fun k => congrArg norm (nativeTwistedInsertedTerm_eq_shift τ j k).symm),
    tsum_congr (nativeTwistedInsertedTerm_eq_shift τ j)⟩

/-- The monodromy eigenphase at weight `16 / 9 + k / 3`. -/
def nativeCubicPhase (k : ℕ) : ℂ := exp (period * (16 / 9 + (k : ℂ) / 3))

private theorem nativeCubicPhase_eq_vacuum_mul (k : ℕ) :
    nativeCubicPhase k = nativeCubicPhase 0 * ζ ^ k := by
  change exp (period * (16 / 9 + (k : ℂ) / 3)) =
    exp (period * (16 / 9 + ((0 : ℕ) : ℂ) / 3)) * exp (period / 3) ^ k
  rw [← exp_nat_mul, ← exp_add]
  congr 1
  simp only [Nat.cast_zero]
  ring

private theorem nativeCubicPhase_eq_iff (k : ℕ) (r : Fin 3) :
    nativeCubicPhase k = nativeCubicPhase r.val ↔ k % 3 = r.val := by
  have hζ : IsPrimitiveRoot ζ 3 :=
    IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive
  have hphase : nativeCubicPhase 0 ≠ 0 := exp_ne_zero _
  rw [nativeCubicPhase_eq_vacuum_mul k, nativeCubicPhase_eq_vacuum_mul r.val,
    mul_right_inj' hphase, (hζ.isOfFinOrder (by decide)).pow_inj_mod, ← hζ.eq_orderOf]
  rw [Nat.mod_eq_of_lt r.isLt]

/-- The actual monodromy eigenspace in grade `k` for the phase indexed by `r`. -/
abbrev NativeCubicEigenspace (r : Fin 3) (k : ℕ) : Submodule ℂ (NativeConformalGrade k) :=
  (nativeGradeMonodromy k).eigenspace (nativeCubicPhase r.val)

/-- The identity trace on one of the three monodromy eigenspaces in grade `k`. -/
def nativeTwistedEigenspaceTraceCoeff (r : Fin 3) (k : ℕ) : ℂ :=
  LinearMap.trace ℂ (NativeCubicEigenspace r k) LinearMap.id

/-- Each eigenspace trace keeps exactly the grades in its residue class. -/
theorem native_twisted_eigenspace_trace_coeff_eq (r : Fin 3) (k : ℕ) :
    nativeTwistedEigenspaceTraceCoeff r k =
      if k % 3 = r.val then nativeTwistedTraceCoeff k else 0 := by
  let := nativeConformalGrade_finiteDimensional k
  have hrot : nativeGradeMonodromy k = nativeCubicPhase k • 1 :=
    nativeGradeMonodromy_eq_smul k
  rw [nativeTwistedEigenspaceTraceCoeff, LinearMap.trace_id]
  by_cases hr : k % 3 = r.val
  · have htop : NativeCubicEigenspace r k = ⊤ := by
      rw [eq_top_iff]
      intro v _
      apply Module.End.mem_eigenspace_iff.mpr
      rw [hrot, (nativeCubicPhase_eq_iff k r).mpr hr, LinearMap.smul_apply,
        Module.End.one_apply]
    rw [htop, finrank_top, ite_eq_left hr]
    rfl
  · have hbot : NativeCubicEigenspace r k = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      have h := Module.End.mem_eigenspace_iff.mp hv
      rw [hrot, LinearMap.smul_apply, Module.End.one_apply] at h
      by_contra hv0
      exact hr ((nativeCubicPhase_eq_iff k r).mp (smul_left_injective ℂ hv0 h))
    rw [hbot, finrank_bot, Nat.cast_zero, ite_eq_right hr]

private theorem nativeTwistedTraceCoeff_ne_zero (k : ℕ) : nativeTwistedTraceCoeff k ≠ 0 := by
  let := nativeConformalGrade_finiteDimensional k
  obtain ⟨v, hv, heig⟩ := (P48qFullEnergySpectrum.totalLZero_exact_eigenvalues
    (16 / 9 + (k : ℂ) / 3)).mpr ⟨k, rfl⟩
  have hmem : v ∈ NativeConformalGrade k := by
    unfold NativeConformalGrade
    rw [native_conformal_coeff_neg_six_eq_totalLZero]
    exact Module.End.mem_eigenspace_iff.mpr heig
  let : Nontrivial (NativeConformalGrade k) :=
    ⟨⟨⟨v, hmem⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hdim : 0 < Module.finrank ℂ (NativeConformalGrade k) := Module.finrank_pos
  exact Nat.cast_ne_zero.mpr hdim.ne'

/-- Every grade in the given residue class contributes a nonzero trace. -/
theorem native_twisted_eigenspace_trace_coeff_ne_zero_iff (r : Fin 3) (k : ℕ) :
    nativeTwistedEigenspaceTraceCoeff r k ≠ 0 ↔ k % 3 = r.val := by
  rw [native_twisted_eigenspace_trace_coeff_eq]
  split <;> simp_all [nativeTwistedTraceCoeff_ne_zero]

/-- The normalized term of the actual graded monodromy eigenspace trace. -/
def nativeTwistedEigenspaceTerm (τ : ℂ) (r : Fin 3) (k : ℕ) : ℂ :=
  nativeTwistedEigenspaceTraceCoeff r k *
    exp (period * τ * ((16 / 9 + (k : ℂ) / 3) - lattice.rank / 24))

/-- The normalized character of one of the three monodromy eigenspaces. -/
def nativeTwistedEigenspaceCharacter (τ : ℂ) (r : Fin 3) : ℂ :=
  ∑' k : ℕ, nativeTwistedEigenspaceTerm τ r k

private theorem nativeTwistedEigenspaceTerm_eq_filter (τ : ℂ) (r : Fin 3) (k : ℕ) :
    nativeTwistedEigenspaceTerm τ r k =
      if k % 3 = r.val then nativeTwistedTraceTerm τ k else 0 := by
  rw [nativeTwistedEigenspaceTerm, native_twisted_eigenspace_trace_coeff_eq]
  split <;> simp [nativeTwistedTraceTerm]

private theorem nativeCubicPhase_cube (k : ℕ) : nativeCubicPhase k ^ 3 = ζ := by
  unfold nativeCubicPhase
  rw [← exp_nat_mul, show (↑(3 : ℕ) : ℂ) * (period * (16 / 9 + (k : ℂ) / 3)) =
      period / 3 + ((5 + k : ℕ) : ℂ) * period by push_cast; ring,
    exp_add, exp_nat_mul_two_pi_mul_I, mul_one]
  rfl

private theorem nativeTwistedEigenspaceTerm_eq_fourier (τ : ℂ) (r : Fin 3) (k : ℕ) :
    nativeTwistedEigenspaceTerm τ r k = (3 : ℂ)⁻¹ *
      ∑ j ∈ Finset.range 3, (nativeCubicPhase r.val)⁻¹ ^ j * nativeTwistedInsertedTerm τ j k := by
  let x := (nativeCubicPhase r.val)⁻¹ * nativeCubicPhase k
  have hcube : x ^ 3 = 1 := by
    dsimp only [x]
    rw [mul_pow, inv_pow, nativeCubicPhase_cube, nativeCubicPhase_cube]
    exact inv_mul_cancel₀ (Units.ne_zero ThirdTwistedChargeCocycle.zeta)
  have hphase : x = 1 ↔ k % 3 = r.val := by
    rw [← nativeCubicPhase_eq_iff k r]
    change (nativeCubicPhase r.val)⁻¹ * nativeCubicPhase k = 1 ↔ _
    have hphase_ne : nativeCubicPhase r.val ≠ 0 := exp_ne_zero _
    rw [inv_mul_eq_iff_eq_mul₀ hphase_ne, mul_one]
  have hsum : (3 : ℂ)⁻¹ * (∑ j ∈ Finset.range 3, x ^ j) =
      if k % 3 = r.val then 1 else 0 := by
    by_cases hr : k % 3 = r.val
    · rw [hphase.mpr hr, ite_eq_left hr]
      norm_num
    · have hgeom := geom_sum_mul x 3
      rw [hcube, sub_self] at hgeom
      have hzero := (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr (mt hphase.mp hr))
      rw [hzero, mul_zero, ite_eq_right hr]
  have hterm (j : ℕ) : nativeTwistedInsertedTerm τ j k =
      nativeCubicPhase k ^ j * nativeTwistedTraceTerm τ k := by
    rw [nativeTwistedInsertedTerm, native_twisted_monodromy_trace_eq, nativeTwistedTraceTerm,
      nativeCubicPhase, ← exp_nat_mul, mul_assoc]
    congr 2
    ring
  simp_rw [hterm, ← mul_assoc ((nativeCubicPhase r.val)⁻¹ ^ _) (nativeCubicPhase k ^ _),
    ← mul_pow]
  rw [← Finset.sum_mul, ← mul_assoc, hsum, nativeTwistedEigenspaceTerm_eq_filter]
  split <;> simp_all

/-- The three actual eigenspace characters are the cubic Fourier filters of
the shifted native twisted character, with absolutely convergent grade sums. -/
theorem native_twisted_eigenspace_character_eq_fourier (τ : ℂ) (hτ : 0 < τ.im) (r : Fin 3) :
    Summable (fun k : ℕ => ‖nativeTwistedEigenspaceTerm τ r k‖) ∧
      nativeTwistedEigenspaceCharacter τ r = (3 : ℂ)⁻¹ *
        ∑ j ∈ Finset.range 3, (nativeCubicPhase r.val)⁻¹ ^ j *
          nativeTwistedCharacter (τ + (j : ℂ)) := by
  refine ⟨(native_twisted_character_eq_twining τ hτ).1.of_nonneg_of_le
    (fun k => norm_nonneg _) (fun k => ?_), ?_⟩
  · rw [nativeTwistedEigenspaceTerm_eq_filter]
    split <;> simp
  · unfold nativeTwistedEigenspaceCharacter
    simp_rw [nativeTwistedEigenspaceTerm_eq_fourier, tsum_mul_left]
    rw [Summable.tsum_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [tsum_mul_left]
      exact congrArg ((nativeCubicPhase r.val)⁻¹ ^ j * ·)
        (native_twisted_inserted_character_eq_shift τ hτ j).2
    · intro j _
      exact (native_twisted_inserted_character_eq_shift τ hτ j).1.of_norm.mul_left _

run_cmd do
  for name in [``fixed_dual_iff_third_fixed_charge, ``fixed_charge_pairing_even_pos,
      ``actual_cubic_twining_character_eq_theta_div_eta, ``fixed_charge_theta_S,
      ``actual_cubic_twining_character_S,
      ``native_twisted_trace_coeff_eq_weight_fiber_card,
      ``native_twisted_identity_trace_eq_weight_fiber_card,
      ``native_twisted_trace_coeff_eq_actual_full_grade_trace,
      ``native_twisted_character_eq_twining, ``actual_cubic_trace_S_interchange,
      ``nativeGradeMonodromy, ``native_twisted_monodromy_trace_eq,
      ``native_twisted_monodromy_cube_trace, ``native_twisted_inserted_character_eq_shift,
      ``nativeTwistedInsertedCharacter, ``nativeTwistedEigenspaceTraceCoeff,
      ``native_twisted_eigenspace_trace_coeff_eq, ``native_twisted_eigenspace_trace_coeff_ne_zero_iff,
      ``native_twisted_eigenspace_character_eq_fourier] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => [``propext, ``Classical.choice, ``Quot.sound].contains ax) do
      throwError "Unexpected axiom closure for {name}: {axioms}"
    Lean.logInfo m!"{name} depends on axioms: {axioms}"

end
end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCubicTwiningCharacter
