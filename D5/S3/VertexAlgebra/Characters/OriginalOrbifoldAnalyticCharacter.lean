/- GID: D5/S3/VertexAlgebra/Characters/OriginalOrbifoldAnalyticCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/OriginalOrbifoldAnalyticCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original shifted orbifold character converges and splits into three terms. -/

import D5.S3.VertexAlgebra.Characters.OriginalOrbifoldGradedCharacter
import D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentThermal
import D5.S3.Fourier.MatrixGaussianTheta

/-! The analytic (L_0-1) trace of the original rank-24 orbifold. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators
open Complex

namespace D5.S3.VertexAlgebra.OriginalOrbifoldAnalyticCharacter

open ActualLeechHyperbolic (leechData leech_spec)
open TwistedGround.OriginalOrbifoldConformal (L)
open OriginalOrbifoldGradedCharacter
open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open LatticePositiveEnergy
open LatticeThetaCharacter (positive_full_theta_character positiveFullThetaTrace)
open SourceBPZ.ThetaGradeTraceSplit (gradeTheta)
open LatticeTwoCurrentThermal (oscillatorCharacter chargeTheta)
open CanonicalOccupationSewing (Occ level)
open LatticeHalfFockGradedTrace (bRank)
open D5.S3.Fourier.MatrixGaussian (quadratic summable_norm_theta)
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
  (integerEnergy signedIntegerMonomial summable_norm_signed_integer_occupations)
open D5.S3.Combinatorics.Partitions.AnalyticOddOccupation (summable_norm_odd_coefficients)
open D5.S3.Combinatorics.Partitions.ColouredOddOccupation (ColouredOddFiber)
open D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity (card_colouredFiber)
open D5.S3.Combinatorics.Partitions.EtaOddOccupation (oddCoefficientSeries
  normalized_odd_character_eq_eta)

open private naturalFiberEquiv energyIndex baseTerm base_summable base_sum from
  D5.S3.VertexAlgebra.Characters.LatticeTwoCurrentThermal
open private fixedEnergy oddEnergy fixedEnergy_finite oddEnergy_finite finrank_eigenspace from
  D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum

/-- The canonical half nome on the upper half-plane. -/
def halfNome (τ : ℂ) : ℂ := exp (Real.pi * I * τ)

/-- The ordinary nome, with the same exponential convention as the signed trace. -/
def nome (τ : ℂ) : ℂ := exp (2 * Real.pi * I * τ)

private theorem halfNome_sq (τ : ℂ) : halfNome τ ^ 2 = nome τ := by
  unfold halfNome nome
  rw [← exp_nat_mul]
  push_cast
  congr 1
  ring

private theorem norm_halfNome_lt_one (τ : ℂ) (hτ : 0 < τ.im) : ‖halfNome τ‖ < 1 := by
  rw [halfNome, norm_exp, Real.exp_lt_one_iff]
  simpa [mul_re, mul_im] using neg_lt_zero.mpr (mul_pos Real.pi_pos hτ)

private theorem norm_nome_lt_one (τ : ℂ) (hτ : 0 < τ.im) : ‖nome τ‖ < 1 := by
  rw [← halfNome_sq, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (norm_halfNome_lt_one τ hτ) (by decide)

private def shiftedWeight (τ : ℂ) (n : ℕ) : ℂ := exp (2 * Real.pi * I * τ * (n - 1))

private theorem shiftedWeight_eq (τ : ℂ) (n : ℕ) :
    shiftedWeight τ n = (nome τ)⁻¹ * nome τ ^ n := by
  rw [shiftedWeight, nome, ← exp_neg, ← exp_nat_mul, ← exp_add]
  congr 1
  ring

private theorem charge_summable (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun a : Charge D => ‖nome τ ^ (chargeEnergy D a).toNat‖) := by
  have he (a : Charge D) : nome τ ^ (chargeEnergy D a).toNat =
      exp (Real.pi * I * τ *
        (quadratic (D.G.map (Int.cast : ℤ → ℝ)) (fun i => (a i : ℝ)) : ℂ)) := by
    have hq : quadratic (D.G.map (Int.cast : ℤ → ℝ)) (fun i => (a i : ℝ)) =
        (bilinear D a a : ℝ) := by
      simp [quadratic, bilinear, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [hq, ← two_chargeEnergy, nome, ← exp_nat_mul]
    push_cast
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (chargeEnergy_nonneg D hD a)]
    congr 1
    ring
  simpa only [he] using summable_norm_theta _ hD τ hτ

private theorem occupation_summable (D : LatticeData) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun d : Occ D => ‖q ^ level D d‖) := by
  simpa [signedIntegerMonomial, integerEnergy, level, oscillatorEnergy] using
    summable_norm_signed_integer_occupations (Fin D.rank) hq

private theorem fiber_card_eq_grade (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℕ) :
    Nat.card {z : Charge D × Occ D // energyIndex D z = n} =
      Module.finrank ℂ (grade D n) := by
  let : Finite (EnergyFiber D (n : ℤ)) := energyFiber_finite D hD n
  exact (Nat.card_congr (naturalFiberEquiv D hD n)).trans
    (Module.finrank_eq_nat_card_basis (gradeBasis D n)).symm

private theorem ambient_unshifted (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : ℕ => ‖(Module.finrank ℂ (grade D n) : ℂ) * nome τ ^ n‖) ∧
    HasSum (fun n : ℕ => (Module.finrank ℂ (grade D n) : ℂ) * nome τ ^ n)
      (chargeTheta D (nome τ) * oscillatorCharacter D (nome τ)) := by
  classical
  let q := nome τ
  let c : Charge D → ℂ := fun _ => 1
  have hc : Summable (fun a : Charge D => ‖c a * q ^ (chargeEnergy D a).toNat‖) := by
    simpa only [c, one_mul] using charge_summable D hD τ hτ
  have ho := occupation_summable D (norm_nome_lt_one τ hτ)
  have hnorm := (base_summable D q c hc ho).hasSum.tsum_fiberwise (energyIndex D)
  have hsum := (base_sum D q c hc ho).tsum_fiberwise (energyIndex D)
  constructor
  · apply HasSum.summable (hnorm.congr_fun ?_)
    intro n
    let : Finite (EnergyFiber D (n : ℤ)) := energyFiber_finite D hD n
    let : Finite {z : Charge D × Occ D // energyIndex D z = n} :=
      Finite.of_equiv _ (naturalFiberEquiv D hD n).symm
    let := Fintype.ofFinite {z : Charge D × Occ D // energyIndex D z = n}
    change ‖(Module.finrank ℂ (grade D n) : ℂ) * q ^ n‖ =
      ∑' z : {z : Charge D × Occ D // energyIndex D z = n}, ‖baseTerm D q c z.1‖
    simp only [baseTerm, c, one_mul, show ∀ z : {z : Charge D × Occ D //
      energyIndex D z = n}, energyIndex D z.1 = n from fun z => z.2,
      tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, fiber_card_eq_grade D hD n, norm_mul, Complex.norm_natCast]
  · unfold chargeTheta
    simp only [c, one_mul] at hsum
    apply hsum.congr_fun
    intro n
    let : Finite (EnergyFiber D (n : ℤ)) := energyFiber_finite D hD n
    let : Finite {z : Charge D × Occ D // energyIndex D z = n} :=
      Finite.of_equiv _ (naturalFiberEquiv D hD n).symm
    let := Fintype.ofFinite {z : Charge D × Occ D // energyIndex D z = n}
    change (Module.finrank ℂ (grade D n) : ℂ) * q ^ n =
      ∑' z : {z : Charge D × Occ D // energyIndex D z = n}, baseTerm D q c z.1
    simp only [baseTerm, c, one_mul, show ∀ z : {z : Charge D × Occ D //
      energyIndex D z = n}, energyIndex D z.1 = n from fun z => z.2,
      tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, fiber_card_eq_grade D hD n]

private def twistedCoefficient (n : ℕ) : ℂ :=
  (if 2 ≤ n then 4096 * bRank 24 (2 * n - 3) else 0 : ℕ)

private def halfOccupationTerm (h : ℂ) (k : ℕ) : ℂ :=
  (Nat.card (ColouredOddFiber (Fin 24) k) : ℂ) * h ^ k

private theorem halfOccupation_odd_sum {h : ℂ} (hh : ‖h‖ < 1) :
    HasSum (fun k : ℕ => halfOccupationTerm h (2 * k + 1))
      ((oddCoefficientSeries 24 h - oddCoefficientSeries 24 (-h)) / 2) := by
  have hs : Summable (halfOccupationTerm h) :=
    (summable_norm_odd_coefficients (Fin 24) hh).of_norm
  have he : Summable (fun k : ℕ => halfOccupationTerm h (2 * k)) :=
    hs.comp_injective (show Function.Injective (fun k : ℕ => 2 * k) by
      intro a b hab
      dsimp only at hab
      omega)
  have ho : Summable (fun k : ℕ => halfOccupationTerm h (2 * k + 1)) :=
    hs.comp_injective (show Function.Injective (fun k : ℕ => 2 * k + 1) by
      intro a b hab
      dsimp only at hab
      omega)
  have he' : HasSum (fun k : ℕ => halfOccupationTerm (-h) (2 * k))
      (∑' k : ℕ, halfOccupationTerm h (2 * k)) := by
    apply he.hasSum.congr_fun
    intro k
    simp [halfOccupationTerm, pow_mul]
  have ho' : HasSum (fun k : ℕ => halfOccupationTerm (-h) (2 * k + 1))
      (-(∑' k : ℕ, halfOccupationTerm h (2 * k + 1))) := by
    apply ho.hasSum.neg.congr_fun
    intro k
    simp [halfOccupationTerm, pow_succ, pow_mul]
  have hp := (he.hasSum.even_add_odd ho.hasSum).tsum_eq
  have hm := (he'.even_add_odd ho').tsum_eq
  change oddCoefficientSeries 24 h = _ at hp
  change oddCoefficientSeries 24 (-h) = _ at hm
  have hproj : ((oddCoefficientSeries 24 h - oddCoefficientSeries 24 (-h)) / 2) =
      ∑' k : ℕ, halfOccupationTerm h (2 * k + 1) := by
    rw [hp, hm]
    ring
  rw [hproj]
  exact ho.hasSum

private theorem twisted_tail (τ : ℂ) (k : ℕ) :
    shiftedWeight τ (k + 2) * twistedCoefficient (k + 2) =
      (4096 * halfNome τ) * halfOccupationTerm (halfNome τ) (2 * k + 1) := by
  have hd : 2 * (k + 2) - 3 = 2 * k + 1 := by omega
  have hn : 2 ≤ k + 2 := by omega
  rw [shiftedWeight_eq, pow_add, ← halfNome_sq, twistedCoefficient, ite_eq_left hn, hd,
    Nat.cast_mul, bRank, ← card_colouredFiber, halfOccupationTerm, pow_add, pow_mul]
  have h0 : halfNome τ ≠ 0 := exp_ne_zero _
  push_cast
  field_simp

private theorem twisted_shifted (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : ℕ => ‖shiftedWeight τ n * twistedCoefficient n‖) ∧
    HasSum (fun n : ℕ => shiftedWeight τ n * twistedCoefficient n)
      ((4096 * halfNome τ) *
        ((oddCoefficientSeries 24 (halfNome τ) - oddCoefficientSeries 24 (-halfNome τ)) / 2)) := by
  have hh := norm_halfNome_lt_one τ hτ
  have hnorm := ((summable_norm_odd_coefficients (Fin 24) hh).comp_injective
    (show Function.Injective (fun k : ℕ => 2 * k + 1) by
      intro a b hab
      dsimp only at hab
      omega)).mul_left ‖4096 * halfNome τ‖
  have hs := (halfOccupation_odd_sum hh).mul_left (4096 * halfNome τ)
  constructor
  · apply Summable.comp_nat_add (k := 2)
    simpa only [twisted_tail, norm_mul, halfOccupationTerm, Function.comp_apply] using hnorm
  · let f : ℕ → ℂ := fun n => shiftedWeight τ n * twistedCoefficient n
    have ht : HasSum (fun k : ℕ => f (k + 2)) _ :=
      hs.congr_fun (twisted_tail τ)
    have hzero : f 0 = 0 := by simp [f, twistedCoefficient]
    have hone : f 1 = 0 := by simp [f, twistedCoefficient]
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, hzero, hone, zero_add]
      using ht.sum_range_add

private theorem signed_shifted (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : ℕ => ‖shiftedWeight τ n *
      LinearMap.trace ℂ (grade leechData n) (gradeTheta leechData n)‖) ∧
    HasSum (fun n : ℕ => shiftedWeight τ n *
      LinearMap.trace ℂ (grade leechData n) (gradeTheta leechData n))
      ((ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ 24) := by
  let D := leechData
  have hD := leech_spec.2.2.1
  obtain ⟨H, hHG, hGH⟩ := complex_inverse_exists D hD
  have hs := positive_full_theta_character D H hHG hGH hD (norm_nome_lt_one τ hτ)
  have hc (n : ℕ) : positiveFullThetaTrace D H hHG hGH hD n =
      LinearMap.trace ℂ (grade D n) (gradeTheta D n) := by
    rw [grade_theta_trace_eq_signedThetaCoefficient D hD]
    simpa using hs.1 (n : ℤ)
  have hshift : exp (-2 * Real.pi * I * τ * D.rank / 24) = (nome τ)⁻¹ := by
    rw [nome, ← exp_neg]
    congr 1
    change -2 * Real.pi * I * τ * (leechData.rank : ℂ) / 24 = -(2 * Real.pi * I * τ)
    rw [leech_spec.1]
    push_cast
    ring
  have ht := hs.2.2.2 τ hτ
  rw [hshift] at ht
  constructor
  · simpa only [hc, shiftedWeight_eq, nome, mul_left_comm, mul_comm, mul_assoc] using ht.1
  · simpa only [hc, shiftedWeight_eq, nome, mul_left_comm, mul_comm, mul_assoc,
      show D.rank = 24 from leech_spec.1] using ht.2.1

/-- The ordinary lattice term in the shifted rank-24 trace. -/
def ambientCharacter (τ : ℂ) : ℂ :=
  (nome τ)⁻¹ * (chargeTheta leechData (nome τ) * oscillatorCharacter leechData (nome τ))

/-- The negative twisted contribution, selected by odd half-occupation degree. -/
def negativeTwistedCharacter (τ : ℂ) : ℂ :=
  (4096 * halfNome τ) *
    ((oddCoefficientSeries 24 (halfNome τ) - oddCoefficientSeries 24 (-halfNome τ)) / 2)

/-- The fixed and negative-parity sector multiplicities at integer conformal weight `n`. -/
def multiplicity (n : ℕ) : ℕ :=
  Module.finrank ℂ (fixedEnergy leechData (n : ℂ)) +
    Module.finrank ℂ (oddEnergy leechData leech_spec.2.1 (n : ℂ))

/-- The sector dimensions give exactly the dimension of the full original `L₀` eigenspace. -/
theorem multiplicity_eq_finrank_eigenspace (n : ℕ) :
    multiplicity n =
      Module.finrank ℂ ((L leechData leech_spec.2.1 leech_spec.2.2.1 0).eigenspace (n : ℂ)) := by
  let := fixedEnergy_finite leechData leech_spec.2.2.1 (n : ℂ) (n : ℤ) (Int.cast_natCast n)
  let := oddEnergy_finite leechData leech_spec.2.1 leech_spec.2.2.1 leech_spec.1 n
  exact (finrank_eigenspace leechData leech_spec.2.1 leech_spec.2.2.1 (n : ℂ)).2.symm

/-- The actual shifted orbifold trace with central charge 24. -/
def character (τ : ℂ) : ℂ :=
  ∑' n : ℕ, exp (2 * Real.pi * I * τ * (n - 1)) * (multiplicity n : ℂ)

/-- The sector presentation of the character equals the literal shifted `L₀` trace. -/
theorem character_eq_literal_shifted_trace (τ : ℂ) :
    character τ = ∑' n : ℕ, exp (2 * Real.pi * I * τ * (n - 1)) *
      (Module.finrank ℂ ((L leechData leech_spec.2.1 leech_spec.2.2.1 0).eigenspace (n : ℂ)) : ℂ) := by
  unfold character
  simp_rw [multiplicity_eq_finrank_eigenspace]

private theorem ambient_shifted (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : ℕ => ‖shiftedWeight τ n *
      (Module.finrank ℂ (grade leechData n) : ℂ)‖) ∧
    HasSum (fun n : ℕ => shiftedWeight τ n * (Module.finrank ℂ (grade leechData n) : ℂ))
      (ambientCharacter τ) := by
  have ha := ambient_unshifted leechData leech_spec.2.2.1 τ hτ
  constructor
  · simpa only [shiftedWeight_eq, ← mul_assoc, mul_comm, norm_mul] using
      ha.1.mul_left ‖(nome τ)⁻¹‖
  · simpa only [ambientCharacter, shiftedWeight_eq, mul_left_comm, mul_comm, mul_assoc] using
      ha.2.mul_left (nome τ)⁻¹

private theorem halfNome_add_one (τ : ℂ) : halfNome (τ + 1) = -halfNome τ := by
  simp [halfNome, mul_add, exp_add, exp_pi_mul_I]

private theorem shiftedCharacter_add_one (τ : ℂ) : character (τ + 1) = character τ := by
  have hnome : nome (τ + 1) = nome τ := by
    rw [← halfNome_sq, ← halfNome_sq, halfNome_add_one]
    ring
  unfold character
  apply tsum_congr
  intro n
  change shiftedWeight (τ + 1) n * (multiplicity n : ℂ) =
    shiftedWeight τ n * (multiplicity n : ℂ)
  rw [shiftedWeight_eq, shiftedWeight_eq, hnome]

private theorem negativeTwisted_eta (τ : ℂ) (hτ : 0 < τ.im) :
    negativeTwistedCharacter τ =
      2048 * ((ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ 24 +
        (ModularForm.eta (τ + 1) / ModularForm.eta ((τ + 1) / 2)) ^ 24) := by
  have hτ' : 0 < (τ + 1).im := by simpa using hτ
  have heta (z : ℂ) (hz : 0 < z.im) :
      halfNome z * oddCoefficientSeries 24 (halfNome z) =
        (ModularForm.eta z / ModularForm.eta (z / 2)) ^ 24 := by
    have he := normalized_odd_character_eq_eta 24 1 z hz
    have hshift : (2 * Real.pi * I * z * (↑(24 : ℕ) : ℂ) / 48) = Real.pi * I * z := by
      push_cast
      ring
    simpa only [hshift, one_mul, halfNome] using he
  rw [← heta τ hτ, ← heta (τ + 1) hτ', halfNome_add_one, negativeTwistedCharacter]
  ring

set_option maxHeartbeats 1200000 in
-- Elaborating the graded coefficient equality expands the concrete Leech carrier.
/-- The shifted actual grade series converges absolutely. Its value consists of
the fixed projection of the ambient and signed traces and the negative twisted trace. -/
theorem actual_leech_shifted_character (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun n : ℕ => ‖exp (2 * Real.pi * I * τ * (n - 1)) * (multiplicity n : ℂ)‖) ∧
    character τ =
      (ambientCharacter τ + (ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ 24) / 2 +
        negativeTwistedCharacter τ ∧
    negativeTwistedCharacter τ =
      2048 * ((ModularForm.eta τ / ModularForm.eta (τ / 2)) ^ 24 +
        (ModularForm.eta (τ + 1) / ModularForm.eta ((τ + 1) / 2)) ^ 24) ∧
    character (τ + 1) = character τ := by
  have ha := ambient_shifted τ hτ
  have hs := signed_shifted τ hτ
  have ht := twisted_shifted τ hτ
  let a : ℕ → ℂ := fun n => shiftedWeight τ n * (Module.finrank ℂ (grade leechData n) : ℂ)
  let s : ℕ → ℂ := fun n => shiftedWeight τ n *
    LinearMap.trace ℂ (grade leechData n) (gradeTheta leechData n)
  let t : ℕ → ℂ := fun n => shiftedWeight τ n * twistedCoefficient n
  have hterm (n : ℕ) : shiftedWeight τ n * (multiplicity n : ℂ) =
      (a n + s n) / 2 + t n := by
    rw [multiplicity_eq_finrank_eigenspace, actual_leech_graded_character_coefficient]
    dsimp [a, s, t, twistedCoefficient]
    ring
  refine ⟨?_, ?_, negativeTwisted_eta τ hτ, shiftedCharacter_add_one τ⟩
  · change Summable (fun n : ℕ => ‖shiftedWeight τ n * (multiplicity n : ℂ)‖)
    simp_rw [hterm]
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ <|
      ((ha.1.add hs.1).mul_left ‖(2 : ℂ)⁻¹‖).add ht.1
    intro n
    change ‖(a n + s n) / 2 + t n‖ ≤ ‖(2 : ℂ)⁻¹‖ * (‖a n‖ + ‖s n‖) + ‖t n‖
    calc
      _ ≤ ‖(a n + s n) / 2‖ + ‖t n‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [div_eq_inv_mul, norm_mul]
        gcongr
        exact norm_add_le _ _
  · have has : HasSum a (ambientCharacter τ) := ha.2
    have hss : HasSum s ((ModularForm.eta τ / ModularForm.eta (2 * τ)) ^ 24) := hs.2
    have hts : HasSum t (negativeTwistedCharacter τ) := ht.2
    have hsum := ((has.add hss).mul_left (2 : ℂ)⁻¹).add hts
    unfold character
    refine (hsum.congr_fun ?_).tsum_eq.trans ?_
    · intro n
      change shiftedWeight τ n * (multiplicity n : ℂ) = _
      rw [hterm, div_eq_inv_mul]
    · simp only [div_eq_inv_mul]

#print axioms multiplicity_eq_finrank_eigenspace
#print axioms character_eq_literal_shifted_trace
#print axioms actual_leech_shifted_character

end D5.S3.VertexAlgebra.OriginalOrbifoldAnalyticCharacter
