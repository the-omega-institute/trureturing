/- GID: D5/S3/VertexAlgebra/Characters/OriginalOrbifoldProjectedCharacters
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/OriginalOrbifoldProjectedCharacters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The projected Leech orbifold traces converge and transform by explicit matrices. -/

import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter
import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldSectorModularity
import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAmbientModularity
import Mathlib.NumberTheory.ModularForms.QExpansion

/-! The four projected traces of the actual Leech sign orbifold. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators MatrixGroups Topology
open Complex Filter

namespace D5.S3.VertexAlgebra.OriginalOrbifoldProjectedCharacters

open ActualLeechHyperbolic (leechData leech_spec)
open OriginalOrbifoldAnalyticCharacter (ambientCharacter character halfNome nome
  actual_leech_shifted_character)
open OriginalOrbifoldAmbientModularity (ambientCharacter_s_invariant)
open OriginalOrbifoldSectorModularity (B C D B_eq_eta C_eq_eta B_S C_S D_S B_T C_T D_T)
open LatticePositiveEnergy (grade grade_finiteDimensional)
open SourceBPZ.ThetaGradeTraceSplit (plusGrade minusGrade gradeTheta gradeSplitEquiv
  grade_theta_trace_eq_fixed_minus_anti)
open LatticeHalfFockGradedTrace (actualGrade actualTensorL0 actual_grade_finrank_bRank bRank)
open LatticeHalfFockParityT (actualParity_on_actualGrade)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open D5.S3.Combinatorics.Partitions.AnalyticOddOccupation (summable_norm_odd_coefficients)
open D5.S3.Combinatorics.Partitions.ColouredOddOccupation (ColouredOddFiber)
open D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity (card_colouredFiber)
open D5.S3.Combinatorics.Partitions.EtaOddOccupation (oddCoefficientSeries
  normalized_odd_character_eq_eta)

open private shiftedWeight shiftedWeight_eq ambient_shifted signed_shifted halfNome_sq
  halfNome_add_one norm_halfNome_lt_one from
  D5.S3.VertexAlgebra.Characters.OriginalOrbifoldAnalyticCharacter
open private coe_S coe_T from D5.S3.VertexAlgebra.Characters.OriginalOrbifoldSectorModularity

local notation "S" => ModularGroup.S
local notation "T" => ModularGroup.T
local notation "hu" => And.left (And.right leech_spec)
local notation "hpos" => And.left (And.right (And.right leech_spec))

/-- Fixed lattice, anti-fixed lattice, integral twisted, and half-integral twisted. -/
def projectedCharacters (τ : UpperHalfPlane) : Fin 4 → ℂ :=
  ![(ambientCharacter τ + B τ) / 2, (ambientCharacter τ - B τ) / 2,
    (C τ + D τ) / 2, (C τ - D τ) / 2]

/-- The trace term of the actual twisted conformal grade of half-occupation degree
`k`. The central charge subtraction changes its weight from `3/2 + k/2` to
`(k+1)/2`. -/
def twistedGradeTerm (τ : UpperHalfPlane) (k : ℕ) : ℂ :=
  (Module.finrank ℂ (actualGrade leechData hu k) : ℂ) * halfNome τ ^ (k + 1)

/-- Each actual twisted conformal grade lies in its indicated parity eigenspace. -/
theorem twisted_grade_eq_parity_eigenspace (k : ℕ) :
    paritySpace leechData hu ((-1 : ℂ) ^ k) ⊓
      (actualTensorL0 leechData hu).eigenspace (3 / 2 + (k : ℂ) / 2) =
        actualGrade leechData hu k := by
  have hweight : (leechData.rank : ℂ) / 16 + (k : ℂ) / 2 = 3 / 2 + (k : ℂ) / 2 := by
    rw [leech_spec.1]
    norm_num
  rw [Module.End.eigenspace_def, Module.End.one_eq_id, ← hweight]
  change paritySpace leechData hu ((-1 : ℂ) ^ k) ⊓ actualGrade leechData hu k = _
  rw [inf_eq_right]
  intro v hv
  simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using
    actualParity_on_actualGrade leechData hu k ⟨v, hv⟩

private theorem twisted_grade_term_eq (τ : UpperHalfPlane) (k : ℕ) :
    twistedGradeTerm τ k =
      (4096 * halfNome τ) *
        ((Nat.card (ColouredOddFiber (Fin 24) k) : ℂ) * halfNome τ ^ k) := by
  unfold twistedGradeTerm
  rw [actual_grade_finrank_bRank, leech_spec.1, bRank, ← card_colouredFiber, Nat.cast_mul,
    pow_succ]
  norm_num
  ring

/-- The full twisted trace is the convergent trace of the actual conformal
grades, including the degree-zero twisted ground. -/
theorem twisted_trace_hasSum (τ : UpperHalfPlane) :
    Summable (fun k => ‖twistedGradeTerm τ k‖) ∧
      HasSum (twistedGradeTerm τ) (C τ) := by
  have hs := summable_norm_odd_coefficients (Fin 24) (norm_halfNome_lt_one τ τ.im_pos)
  constructor
  · simpa only [twisted_grade_term_eq, norm_mul] using hs.mul_left ‖4096 * halfNome τ‖
  · have heta := normalized_odd_character_eq_eta 24 4096 τ τ.im_pos
    have hshift : 2 * Real.pi * I * (τ : ℂ) * (↑(24 : ℕ) : ℂ) / 48 =
        Real.pi * I * (τ : ℂ) := by push_cast; ring
    have hC : (4096 * halfNome τ) * oddCoefficientSeries 24 (halfNome τ) = C τ := by
      rw [hshift] at heta
      simpa only [C_eq_eta, halfNome, show (2 : ℂ) ^ (12 : ℕ) = 4096 by norm_num]
        using heta
    rw [← hC]
    exact (hs.of_norm.hasSum.mul_left (4096 * halfNome τ)).congr_fun (twisted_grade_term_eq τ)

private theorem twisted_grade_term_T (τ : UpperHalfPlane) (k : ℕ) :
    twistedGradeTerm (T • τ) k = (-1 : ℂ) ^ (k + 1) * twistedGradeTerm τ k := by
  rw [twistedGradeTerm, twistedGradeTerm, coe_T, halfNome_add_one, ← neg_one_mul (halfNome τ),
    mul_pow]
  ring

/-- Even and odd half-occupation degrees give the two Fourier projections of
the actual full twisted trace. Both subseries converge absolutely. Translation
gives the odd-degree sum minus the even-degree sum. -/
theorem twisted_trace_decomposition (τ : UpperHalfPlane) :
    Summable (fun k : ℕ => ‖twistedGradeTerm τ (2 * k)‖) ∧
    Summable (fun k : ℕ => ‖twistedGradeTerm τ (2 * k + 1)‖) ∧
    HasSum (fun k : ℕ => twistedGradeTerm τ (2 * k)) (projectedCharacters τ 3) ∧
    HasSum (fun k : ℕ => twistedGradeTerm τ (2 * k + 1)) (projectedCharacters τ 2) ∧
    C τ = (∑' k : ℕ, twistedGradeTerm τ (2 * k)) +
      (∑' k : ℕ, twistedGradeTerm τ (2 * k + 1)) ∧
    D τ = (∑' k : ℕ, twistedGradeTerm τ (2 * k + 1)) -
      (∑' k : ℕ, twistedGradeTerm τ (2 * k)) := by
  let e : ℕ → ℕ := fun k => 2 * k
  let o : ℕ → ℕ := fun k => 2 * k + 1
  have hf := twisted_trace_hasSum τ
  have he := hf.1.comp_injective (show Function.Injective e by
    intro a b h
    dsimp only [e] at h
    omega)
  have ho := hf.1.comp_injective (show Function.Injective o by
    intro a b h
    dsimp only [o] at h
    omega)
  let E := ∑' k : ℕ, twistedGradeTerm τ (2 * k)
  let O := ∑' k : ℕ, twistedGradeTerm τ (2 * k + 1)
  have hE : HasSum (fun k : ℕ => twistedGradeTerm τ (2 * k)) E := he.of_norm.hasSum
  have hO : HasSum (fun k : ℕ => twistedGradeTerm τ (2 * k + 1)) O := ho.of_norm.hasSum
  have hC : C τ = E + O := hf.2.unique (hE.even_add_odd hO)
  have heT : HasSum (fun k : ℕ => twistedGradeTerm (T • τ) (2 * k)) (-E) := by
    apply hE.neg.congr_fun
    intro k
    rw [twisted_grade_term_T, pow_succ, pow_mul]
    simp
  have hoT : HasSum (fun k : ℕ => twistedGradeTerm (T • τ) (2 * k + 1)) O := by
    apply hO.congr_fun
    intro k
    rw [twisted_grade_term_T, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, pow_mul]
    simp
  have hD : D τ = O - E := by
    rw [← C_T]
    exact ((twisted_trace_hasSum (T • τ)).2.unique (heT.even_add_odd hoT)).trans (by ring)
  refine ⟨he, ho, ?_, ?_, hC, hD⟩
  · change HasSum _ ((C τ - D τ) / 2)
    convert hE using 1
    rw [hC, hD]
    ring
  · change HasSum _ ((C τ + D τ) / 2)
    convert hO using 1
    rw [hC, hD]
    ring

private theorem lattice_grade_dimensions (n : ℕ) :
    Module.finrank ℂ (grade leechData n) =
      Module.finrank ℂ (plusGrade leechData n) + Module.finrank ℂ (minusGrade leechData n) := by
  let : FiniteDimensional ℂ (grade leechData n) := grade_finiteDimensional leechData hpos n
  let : FiniteDimensional ℂ (plusGrade leechData n) := Submodule.finiteDimensional_of_le inf_le_left
  let : FiniteDimensional ℂ (minusGrade leechData n) :=
    Submodule.finiteDimensional_of_le inf_le_left
  exact (gradeSplitEquiv leechData n).finrank_eq.trans Module.finrank_prod

/-- The fixed and anti-fixed analytic projections sum the dimensions of the
actual theta-eigenspace grades with weight `exp (2πiτ(n-1))` and absolute
convergence at every upper half-plane point. -/
theorem lattice_projected_traces (τ : UpperHalfPlane) :
    (Summable (fun n : ℕ => ‖shiftedWeight τ n *
      (Module.finrank ℂ (plusGrade leechData n) : ℂ)‖) ∧
      HasSum (fun n : ℕ => shiftedWeight τ n * (Module.finrank ℂ (plusGrade leechData n) : ℂ))
        (projectedCharacters τ 0)) ∧
    (Summable (fun n : ℕ => ‖shiftedWeight τ n *
      (Module.finrank ℂ (minusGrade leechData n) : ℂ)‖) ∧
      HasSum (fun n : ℕ => shiftedWeight τ n * (Module.finrank ℂ (minusGrade leechData n) : ℂ))
        (projectedCharacters τ 1)) := by
  have ha := ambient_shifted τ τ.im_pos
  have hb := signed_shifted τ τ.im_pos
  rw [← B_eq_eta τ] at hb
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ ha.1
    intro n
    simp only [norm_mul, Complex.norm_natCast]
    gcongr
    rw [lattice_grade_dimensions]
    exact Nat.le_add_right _ _
  · change HasSum _ ((ambientCharacter τ + B τ) / 2)
    rw [div_eq_inv_mul]
    apply ((ha.2.add hb.2).mul_left (2 : ℂ)⁻¹).congr_fun
    intro n
    rw [grade_theta_trace_eq_fixed_minus_anti leechData n hpos, lattice_grade_dimensions,
      Nat.cast_add]
    ring
  · apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ ha.1
    intro n
    simp only [norm_mul, Complex.norm_natCast]
    gcongr
    rw [lattice_grade_dimensions]
    exact Nat.le_add_left _ _
  · change HasSum _ ((ambientCharacter τ - B τ) / 2)
    rw [div_eq_inv_mul]
    apply ((ha.2.sub hb.2).mul_left (2 : ℂ)⁻¹).congr_fun
    intro n
    rw [grade_theta_trace_eq_fixed_minus_anti leechData n hpos, lattice_grade_dimensions,
      Nat.cast_add]
    ring

/-- The checked actual orbifold character is the sum of the fixed lattice and
integral twisted projected traces. -/
theorem character_eq_fixed_add_integral (τ : UpperHalfPlane) :
    character τ = projectedCharacters τ 0 + projectedCharacters τ 2 := by
  have htrace := actual_leech_shifted_character τ τ.im_pos
  change character τ = (ambientCharacter τ + B τ) / 2 + (C τ + D τ) / 2
  rw [htrace.2.1, htrace.2.2.1, B_eq_eta, C_eq_eta,
    OriginalOrbifoldSectorModularity.D_eq_eta]
  ring

/-- The ambient lattice trace is periodic because its nome is periodic. -/
theorem ambientCharacter_t_invariant (τ : UpperHalfPlane) :
    ambientCharacter (T • τ : UpperHalfPlane) = ambientCharacter τ := by
  have hnome : nome (T • τ : UpperHalfPlane) = nome τ := by
    rw [coe_T, ← halfNome_sq, ← halfNome_sq, halfNome_add_one, neg_sq]
  simp only [ambientCharacter, hnome]

/-- The Hadamard matrix in the fixed, anti-fixed, integral, half-integral order. -/
def projectedS : Matrix (Fin 4) (Fin 4) ℂ :=
  (2 : ℂ)⁻¹ • !![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]

/-- Translation acts by a sign on the half-integral grades. -/
def projectedT : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1]

/-- Simultaneous weight-zero covariance of the four projected characters under
the two generators of the modular group. -/
theorem projected_characters_covariant (τ : UpperHalfPlane) :
    projectedCharacters (S • τ) = projectedS.mulVec (projectedCharacters τ) ∧
    projectedCharacters (T • τ) = projectedT.mulVec (projectedCharacters τ) := by
  have haS : ambientCharacter (S • τ : UpperHalfPlane) = ambientCharacter τ := by
    rw [coe_S]
    exact ambientCharacter_s_invariant τ τ.im_pos
  constructor
  · funext i
    simp only [projectedCharacters, haS, B_S, C_S, D_S]
    fin_cases i <;> simp [projectedS, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
  · funext i
    simp only [projectedCharacters, ambientCharacter_t_invariant, B_T, C_T, D_T]
    fin_cases i <;> simp [projectedT, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

open ActualLeechHyperbolic (leechCoordinates)
open LatticePositiveEnergy (gradeBasis)
open Lattice.RootlessLowGrades (energyZeroEquiv)
open LatticeHalfFockGradedTrace (actual_rank24_grade_one_finrank_98304)
open D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity (partitionCount_small)

open private no_roots from D5.S3.VertexAlgebra.Lattice.LeechLowSpectrum
open private fixedGrade_zero_finrank fixedGrade_one_finrank gradeOneBasis from
  D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades

private theorem lattice_leading_ranks :
    Module.finrank ℂ (plusGrade leechData 0) = 1 ∧
    Module.finrank ℂ (minusGrade leechData 0) = 0 ∧
    Module.finrank ℂ (minusGrade leechData 1) = 24 := by
  have hroot := no_roots leechCoordinates leech_spec.2.2.2
  have hp0 : Module.finrank ℂ (plusGrade leechData 0) = 1 := by
    rw [plusGrade, inf_comm]
    exact fixedGrade_zero_finrank leechData hpos
  have hp1 : Module.finrank ℂ (plusGrade leechData 1) = 0 := by
    rw [plusGrade, inf_comm]
    exact fixedGrade_one_finrank leechData hpos hroot
  have hg0 : Module.finrank ℂ (grade leechData 0) = 1 := by
    rw [Module.finrank_eq_nat_card_basis (gradeBasis leechData 0),
      Nat.card_congr (energyZeroEquiv leechData hpos)]
    simp
  have hg1 : Module.finrank ℂ (grade leechData 1) = 24 := by
    rw [Module.finrank_eq_nat_card_basis (gradeOneBasis leechData hpos hroot),
      Nat.card_eq_fintype_card, Fintype.card_fin, leech_spec.1]
  have hs0 := lattice_grade_dimensions 0
  have hs1 := lattice_grade_dimensions 1
  change Module.finrank ℂ (grade leechData 0) =
    Module.finrank ℂ (plusGrade leechData 0) + Module.finrank ℂ (minusGrade leechData 0) at hs0
  change Module.finrank ℂ (grade leechData 1) =
    Module.finrank ℂ (plusGrade leechData 1) + Module.finrank ℂ (minusGrade leechData 1) at hs1
  rw [hg0, hp0] at hs0
  rw [hg1, hp1] at hs1
  exact ⟨hp0, by omega, by omega⟩

private theorem nome_eq_qParam (τ : UpperHalfPlane) :
    nome τ = Function.Periodic.qParam 1 τ := by
  simp [nome, Function.Periodic.qParam]

private theorem halfNome_eq_qParam (τ : UpperHalfPlane) :
    halfNome τ = Function.Periodic.qParam 2 τ := by
  unfold halfNome Function.Periodic.qParam
  congr 1
  push_cast
  ring

private theorem twisted_grade_zero_rank :
    Module.finrank ℂ (actualGrade leechData hu 0) = 4096 := by
  rw [actual_grade_finrank_bRank, leech_spec.1, bRank, (partitionCount_small 24).1]
  decide

/-- The cusp limits after removing the leading powers `q⁻¹, 1, q, q^(1/2)`
are the corresponding actual grade dimensions. -/
theorem projected_characters_leading_limits :
    Tendsto (fun τ : UpperHalfPlane => nome τ * projectedCharacters τ 0)
      UpperHalfPlane.atImInfty (𝓝 1) ∧
    Tendsto (fun τ : UpperHalfPlane => projectedCharacters τ 1)
      UpperHalfPlane.atImInfty (𝓝 24) ∧
    Tendsto (fun τ : UpperHalfPlane => (nome τ)⁻¹ * projectedCharacters τ 2)
      UpperHalfPlane.atImInfty (𝓝 98304) ∧
    Tendsto (fun τ : UpperHalfPlane => (halfNome τ)⁻¹ * projectedCharacters τ 3)
      UpperHalfPlane.atImInfty (𝓝 4096) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion (h := 1) one_pos
      (f := fun τ => nome τ * projectedCharacters τ 0)
      (c := fun n => (Module.finrank ℂ (plusGrade leechData n) : ℂ)) (fun τ => by
        apply ((lattice_projected_traces τ).1.2.mul_left (nome τ)).congr_fun
        intro n
        change _ = nome τ * (shiftedWeight τ n * _)
        rw [← nome_eq_qParam, shiftedWeight_eq, smul_eq_mul]
        field_simp [show nome τ ≠ 0 from exp_ne_zero _])
    change Tendsto _ _ (𝓝 (Module.finrank ℂ (plusGrade leechData 0) : ℂ)) at hs
    simpa only [lattice_leading_ranks.1, Nat.cast_one] using hs
  · have hs := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion (h := 1) one_pos
      (f := fun τ => projectedCharacters τ 1)
      (c := fun n => (Module.finrank ℂ (minusGrade leechData (n + 1 : ℕ)) : ℂ)) (fun τ => by
        have ht := (hasSum_nat_add_iff' 1).mpr (lattice_projected_traces τ).2.2
        simp only [Finset.sum_range_one] at ht
        change HasSum _ (projectedCharacters τ 1 -
          shiftedWeight τ 0 * (Module.finrank ℂ (minusGrade leechData 0) : ℂ)) at ht
        simp only [lattice_leading_ranks.2.1, Nat.cast_zero, mul_zero, sub_zero] at ht
        apply ht.congr_fun
        intro n
        rw [← nome_eq_qParam, shiftedWeight_eq, smul_eq_mul, pow_succ]
        field_simp [show nome τ ≠ 0 from exp_ne_zero _])
    change Tendsto _ _ (𝓝 (Module.finrank ℂ (minusGrade leechData 1) : ℂ)) at hs
    simpa only [lattice_leading_ranks.2.2, Nat.cast_ofNat] using hs
  · have hs := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion (h := 1) one_pos
      (f := fun τ => (nome τ)⁻¹ * projectedCharacters τ 2)
      (c := fun n => (Module.finrank ℂ (actualGrade leechData hu (2 * n + 1)) : ℂ)) (fun τ => by
        apply ((twisted_trace_decomposition τ).2.2.2.1.mul_left (nome τ)⁻¹).congr_fun
        intro n
        rw [← nome_eq_qParam, smul_eq_mul, twistedGradeTerm,
          show 2 * n + 1 + 1 = 2 * (n + 1) by omega, pow_mul, halfNome_sq, pow_succ]
        field_simp [show nome τ ≠ 0 from exp_ne_zero _])
    simpa only [mul_zero, zero_add, (actual_rank24_grade_one_finrank_98304
      leechData hu leech_spec.1).2.1, Nat.cast_ofNat] using hs
  · have hs := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion (h := 1) one_pos
      (f := fun τ => (halfNome τ)⁻¹ * projectedCharacters τ 3)
      (c := fun n => (Module.finrank ℂ (actualGrade leechData hu (2 * n)) : ℂ)) (fun τ => by
        apply ((twisted_trace_decomposition τ).2.2.1.mul_left (halfNome τ)⁻¹).congr_fun
        intro n
        rw [← nome_eq_qParam, smul_eq_mul, twistedGradeTerm, pow_succ, pow_mul, halfNome_sq]
        field_simp [show halfNome τ ≠ 0 from exp_ne_zero _])
    change Tendsto _ _ (𝓝 (Module.finrank ℂ (actualGrade leechData hu 0) : ℂ)) at hs
    simpa only [twisted_grade_zero_rank, Nat.cast_ofNat] using hs

/-- The four complex characters are linearly independent on the upper half-plane. -/
theorem projected_characters_linearIndependent :
    LinearIndependent ℂ (fun i : Fin 4 => fun τ : UpperHalfPlane => projectedCharacters τ i) := by
  obtain ⟨h0, h1, h2, h3⟩ := projected_characters_leading_limits
  have hq : Tendsto (fun τ : UpperHalfPlane => nome τ) UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [nome_eq_qParam] using UpperHalfPlane.qParam_tendsto_atImInfty one_pos
  have hh : Tendsto (fun τ : UpperHalfPlane => halfNome τ) UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa only [halfNome_eq_qParam] using
      UpperHalfPlane.qParam_tendsto_atImInfty (show (0 : ℝ) < 2 by norm_num)
  have h2zero : Tendsto (fun τ => projectedCharacters τ 2) UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa [mul_assoc, show ∀ τ : UpperHalfPlane, nome τ ≠ 0 from fun _ => exp_ne_zero _]
      using hq.mul h2
  have h3zero : Tendsto (fun τ => projectedCharacters τ 3) UpperHalfPlane.atImInfty (𝓝 0) := by
    simpa [mul_assoc, show ∀ τ : UpperHalfPlane, halfNome τ ≠ 0 from fun _ => exp_ne_zero _]
      using hh.mul h3
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have heq (τ : UpperHalfPlane) :
      a 0 * projectedCharacters τ 0 + a 1 * projectedCharacters τ 1 +
        a 2 * projectedCharacters τ 2 + a 3 * projectedCharacters τ 3 = 0 := by
    have ht := congrFun ha τ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ht
    simpa [Fin.sum_univ_succ, add_assoc] using ht
  have ha0 : a 0 = 0 := by
    have ht := (h0.const_mul (a 0)).add
      (((hq.mul h1).const_mul (a 1)).add
        (((hq.mul h2zero).const_mul (a 2)).add ((hq.mul h3zero).const_mul (a 3))))
    have hz : Tendsto (fun _ : UpperHalfPlane => (0 : ℂ))
        UpperHalfPlane.atImInfty (𝓝 (a 0)) := by
      simp only [mul_one, zero_mul, mul_zero, add_zero] at ht
      refine ht.congr (fun τ => ?_)
      linear_combination nome τ * heq τ
    exact tendsto_nhds_unique hz tendsto_const_nhds
  have ha1 : a 1 = 0 := by
    have ht := (h1.const_mul (a 1)).add
      ((h2zero.const_mul (a 2)).add (h3zero.const_mul (a 3)))
    have hz : Tendsto (fun _ : UpperHalfPlane => (0 : ℂ))
        UpperHalfPlane.atImInfty (𝓝 (a 1 * 24)) := by
      simp only [mul_zero, add_zero] at ht
      exact ht.congr (fun τ => by simpa only [ha0, zero_mul, zero_add, add_assoc] using heq τ)
    exact (mul_eq_zero.mp (tendsto_nhds_unique hz tendsto_const_nhds)).resolve_right (by norm_num)
  have ha3 : a 3 = 0 := by
    have ht := ((hh.mul h2).const_mul (a 2)).add (h3.const_mul (a 3))
    have hz : Tendsto (fun _ : UpperHalfPlane => (0 : ℂ))
        UpperHalfPlane.atImInfty (𝓝 (a 3 * 4096)) := by
      simp only [zero_mul, mul_zero, zero_add] at ht
      refine ht.congr (fun τ => ?_)
      have hn : halfNome τ ≠ 0 := exp_ne_zero _
      have hrel : a 2 * projectedCharacters τ 2 + a 3 * projectedCharacters τ 3 = 0 := by
        simpa only [ha0, ha1, zero_mul, zero_add] using heq τ
      change a 2 * (halfNome τ * ((nome τ)⁻¹ * projectedCharacters τ 2)) +
        a 3 * ((halfNome τ)⁻¹ * projectedCharacters τ 3) = 0
      calc
        _ = (halfNome τ)⁻¹ * (a 2 * projectedCharacters τ 2 + a 3 * projectedCharacters τ 3) := by
          rw [← halfNome_sq]
          field_simp [hn]
        _ = 0 := by rw [hrel, mul_zero]
    exact (mul_eq_zero.mp (tendsto_nhds_unique hz tendsto_const_nhds)).resolve_right (by norm_num)
  have ha2 : a 2 = 0 := by
    have hz : Tendsto (fun _ : UpperHalfPlane => (0 : ℂ))
        UpperHalfPlane.atImInfty (𝓝 (a 2 * 98304)) := by
      apply (h2.const_mul (a 2)).congr
      intro τ
      have hrel : a 2 * projectedCharacters τ 2 = 0 := by simpa [ha0, ha1, ha3] using heq τ
      change a 2 * ((nome τ)⁻¹ * projectedCharacters τ 2) = 0
      linear_combination (nome τ)⁻¹ * hrel
    exact (mul_eq_zero.mp (tendsto_nhds_unique hz tendsto_const_nhds)).resolve_right (by norm_num)
  intro i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact ha2
  · exact ha3

#print axioms projectedCharacters
#print axioms twistedGradeTerm
#print axioms twisted_grade_eq_parity_eigenspace
#print axioms twisted_trace_hasSum
#print axioms twisted_trace_decomposition
#print axioms lattice_projected_traces
#print axioms character_eq_fixed_add_integral
#print axioms ambientCharacter_t_invariant
#print axioms projectedS
#print axioms projectedT
#print axioms projected_characters_covariant
#print axioms projected_characters_leading_limits
#print axioms projected_characters_linearIndependent

end D5.S3.VertexAlgebra.OriginalOrbifoldProjectedCharacters
