/- GID: D5/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/LatticeOrdinaryCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual full Sugawara dimensions and the convergent theta over eta character. -/

import D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
import D5.S3.Arith.Lattices.LatticeThetaTransformation
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # The ordinary character of the full positive even lattice grading -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators
open Complex

namespace D5.S3.VertexAlgebra.LatticeOrdinaryCharacter

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticePositiveEnergy
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeThetaCharacter
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open D5.S3.Combinatorics.Partitions.AnalyticOddOccupation
open D5.S3.Arith.Lattices.LatticeThetaTransformation

/-- The ordinary coefficient: dimension of the actual full canonical L0
eigenspace, rather than a stipulated finite model or an inserted trace. -/
def actualOrdinaryCoefficient (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (N : ℕ) : ℕ :=
  Module.finrank ℂ ((sugawaraMode D H 0).eigenspace (N : ℂ))

/-- Vacuum-normalized ordinary character. Convergence is proved below. -/
def actualOrdinaryCharacter (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (τ : ℂ) : ℂ :=
  exp (-2 * Real.pi * I * τ * D.rank / 24) *
    ∑' N : ℕ, (actualOrdinaryCoefficient D H N : ℂ) *
      exp (2 * Real.pi * I * τ) ^ N

/-- This is the genuine, untruncated integer energy of a basis label,
viewed in the natural numbers. Positivity justifies this view below. -/
def totalDegree (D : LatticeData) (a : Label D) : ℕ := (energy D a).toNat

abbrev NaturalEnergyFiber (D : LatticeData) (N : ℕ) :=
  {a : Label D // totalDegree D a = N}

private theorem energy_nonneg (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Label D) :
    0 ≤ energy D a := by
  have h := chargeEnergy_nonneg D hD a.1
  dsimp [energy]
  omega

private theorem totalDegree_cast (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Label D) :
    (totalDegree D a : ℤ) = energy D a :=
  Int.toNat_of_nonneg (energy_nonneg D hD a)

private theorem totalDegree_eq_iff (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a : Label D) (N : ℕ) :
    totalDegree D a = N ↔ energy D a = (N : ℤ) := by
  constructor
  · intro h
    rw [← totalDegree_cast D hD a, h]
  · intro h
    simp only [totalDegree, h, Int.toNat_natCast]

private theorem totalDegree_add (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Label D) :
    totalDegree D a = (chargeEnergy D a.1).toNat + oscillatorEnergy a.2 := by
  have hq := chargeEnergy_nonneg D hD a.1
  have he := totalDegree_cast D hD a
  have hc := Int.toNat_of_nonneg hq
  dsimp [energy] at he
  omega

/-- Every label at a fixed integer energy lies in the existing finite charge
ellipsoid. This is an equivalence of the complete index sets, with no cutoff
on the allowed states left in its domain. -/
private def fullFiberCutoffEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℤ) :
    EnergyFiber D n ≃ CutoffIndex D (positiveChargeCutoff D hD n) n where
  toFun a := ⟨a.1, by
    refine ⟨?_, a.2⟩
    simp only [positiveChargeCutoff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    have he := a.2
    dsimp [energy] at he
    omega⟩
  invFun a := ⟨a.1, a.2.2⟩
  left_inv _a := Subtype.ext rfl
  right_inv _a := Subtype.ext rfl

private def naturalEnergyFiberEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ) :
    NaturalEnergyFiber D N ≃ EnergyFiber D (N : ℤ) where
  toFun a := ⟨a.1, (totalDegree_eq_iff D hD a.1 N).mp a.2⟩
  invFun a := ⟨a.1, (totalDegree_eq_iff D hD a.1 N).mpr a.2⟩
  left_inv _a := Subtype.ext rfl
  right_inv _a := Subtype.ext rfl

/-- Finiteness is inherited from the canonical positive-energy fiber theorem,
not from a growth assumption on a proposed character. -/
theorem naturalEnergyFiber_finite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ) :
    Finite (NaturalEnergyFiber D N) := by
  haveI := energyFiber_finite D hD (N : ℤ)
  exact Finite.of_injective (naturalEnergyFiberEquiv D hD N)
    (naturalEnergyFiberEquiv D hD N).injective

/-- Positivity makes the literal full Sugawara eigenspace finite-dimensional.
The supplied inverse H identifies the canonical L0 operator with the grading. -/
theorem actualOrdinaryGrade_finiteDimensional (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ) :
    FiniteDimensional ℂ ((sugawaraMode D H 0).eigenspace (N : ℂ)) := by
  have he := positive_full_grade_eq_cutoff D H hHG hGH hD (N : ℤ)
  simp only [Int.cast_natCast] at he
  rw [he]
  exact cutoffActualGrade_finiteDimensional D H hHG hGH _ _

/-- Count the actual full eigenspace using the existing cutoffCoeffEquiv /
cutoffBasis and a genuine equivalence from all labels of the given energy.
This includes N=0 and rank=0. -/
theorem actualOrdinaryCoefficient_eq_card (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ) :
    actualOrdinaryCoefficient D H N = Nat.card (EnergyFiber D (N : ℤ)) := by
  haveI := actualOrdinaryGrade_finiteDimensional D H hHG hGH hD N
  have he := positive_full_grade_eq_cutoff D H hHG hGH hD (N : ℤ)
  simp only [Int.cast_natCast] at he
  let b : Module.Basis (CutoffIndex D (positiveChargeCutoff D hD (N : ℤ)) (N : ℤ))
      ℂ ((sugawaraMode D H 0).eigenspace (N : ℂ)) :=
    (cutoffBasis D H hHG hGH (positiveChargeCutoff D hD (N : ℤ)) (N : ℤ)).map
      (LinearEquiv.ofEq _ _ he).symm
  have hc : actualOrdinaryCoefficient D H N =
      Nat.card (CutoffIndex D (positiveChargeCutoff D hD (N : ℤ)) (N : ℤ)) := by
    have h := congrArg Cardinal.toNat (Module.mk_finrank_eq_card_basis b)
    simpa only [Cardinal.toNat_natCast] using h
  exact hc.trans (Nat.card_congr (fullFiberCutoffEquiv D hD (N : ℤ)).symm)

private theorem actualOrdinaryCoefficient_eq_naturalCard (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (N : ℕ) :
    actualOrdinaryCoefficient D H N = Nat.card (NaturalEnergyFiber D N) := by
  rw [actualOrdinaryCoefficient_eq_card D H hHG hGH hD N]
  exact Nat.card_congr (naturalEnergyFiberEquiv D hD N).symm

/- The unsigned occupation evaluation is a consumed analytic helper. It does
not introduce a second formal Fock-character module or rename a signed trace. -/

private theorem unsigned_monomial (D : LatticeData) (q : ℂ) (d : Exponent D) :
    monomial (fun a : Index D => q ^ (a.2 + 1)) d =
      q ^ oscillatorEnergy d := by
  classical
  unfold monomial Finsupp.prod oscillatorEnergy
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => Nat.mul_comm _ _)

private theorem summable_norm_unsigned (D : LatticeData)
    {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun d : Exponent D => ‖q ^ oscillatorEnergy d‖) := by
  apply (summable_norm_signed_integer_occupations (Fin D.rank) hq).congr
  intro d
  simp [signedIntegerMonomial, integerEnergy, oscillatorEnergy]

private theorem hasProd_unsigned (D : LatticeData)
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasProd (fun n : ℕ => ((1 - q ^ (n + 1))⁻¹) ^ D.rank)
      (∑' d : Exponent D, q ^ oscillatorEnergy d) := by
  let z : Index D → ℂ := fun a => q ^ (a.2 + 1)
  have hm : Summable (fun d : Exponent D => ‖monomial z d‖) := by
    apply (summable_norm_unsigned D hq).congr
    intro d
    exact (congrArg norm (unsigned_monomial D q d)).symm
  have hz (a : Index D) : ‖z a‖ < 1 := by
    dsimp [z]
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hp := hasProd_inverse_eq_occupation_sum z hm hz
  have hs : (∑' d : Exponent D, monomial z d) =
      ∑' d : Exponent D, q ^ oscillatorEnergy d :=
    tsum_congr (unsigned_monomial D q)
  rw [hs] at hp
  have hswap : HasProd
      (fun p : ℕ × Fin D.rank => (1 - q ^ (p.1 + 1))⁻¹)
      (∑' d : Exponent D, q ^ oscillatorEnergy d) := by
    simpa [z, Function.comp_def, Equiv.prodComm_apply] using
      (Equiv.prodComm ℕ (Fin D.rank)).hasProd_iff.mpr hp
  apply hswap.prod_fiberwise
  intro n
  simpa using hasProd_fintype (fun _ : Fin D.rank => (1 - q ^ (n + 1))⁻¹)

private theorem ordinary_q_norm (τ : ℂ) (hτ : 0 < τ.im) :
    ‖exp (2 * Real.pi * I * τ)‖ < 1 := by
  rw [norm_exp, Real.exp_lt_one_iff]
  simpa [Complex.mul_re, Complex.mul_im] using
    neg_lt_zero.mpr (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) hτ)

private theorem normalized_unsigned_eq_eta (D : LatticeData)
    (τ : ℂ) (hτ : 0 < τ.im) :
    exp (-2 * Real.pi * I * τ * D.rank / 24) *
      (∑' d : Exponent D, exp (2 * Real.pi * I * τ) ^ oscillatorEnergy d) =
      1 / (ModularForm.eta τ) ^ D.rank := by
  let q := exp (2 * Real.pi * I * τ)
  let P : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1))
  have hq : ‖q‖ < 1 := ordinary_q_norm τ hτ
  have hP : P ≠ 0 := by
    simpa [P, q, ModularForm.eta_q, Function.Periodic.qParam] using
      ModularForm.eta_tprod_ne_zero hτ
  have he := (((ModularForm.multipliable_one_sub_pow hq).hasProd.inv₀ hP).pow D.rank)
  have hs : (∑' d : Exponent D, q ^ oscillatorEnergy d) = (P⁻¹) ^ D.rank :=
    (hasProd_unsigned D hq).unique he
  have hη : ModularForm.eta τ = exp (2 * Real.pi * I * τ / 24) * P := by
    simp [ModularForm.eta, ModularForm.eta_q, Function.Periodic.qParam, P, q]
  have hshift : exp (-2 * Real.pi * I * τ * D.rank / 24) =
      (exp (2 * Real.pi * I * τ / 24) ^ D.rank)⁻¹ := by
    rw [← exp_nat_mul, ← exp_neg]
    congr 1
    ring
  change exp (-2 * Real.pi * I * τ * D.rank / 24) *
    (∑' d : Exponent D, q ^ oscillatorEnergy d) = _
  rw [hs, hη, hshift]
  simp only [one_div, mul_pow, mul_inv_rev, inv_pow]
  ring

/- The all-charge Gaussian convergence is used for arbitrary positive D.
Neither unimodularity nor an even-rank condition enters this argument. -/

private theorem real_quadratic_charge (D : LatticeData) (a : Charge D) :
    D5.S3.Fourier.MatrixGaussian.quadratic
      (D.G.map (Int.cast : ℤ → ℝ)) (fun i => (a i : ℝ)) =
        (bilinear D a a : ℝ) := by
  simp [D5.S3.Fourier.MatrixGaussian.quadratic, bilinear,
    dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

private theorem summable_norm_charge_exp (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun a : Charge D =>
      ‖exp (Real.pi * I * τ * (bilinear D a a : ℂ))‖) := by
  simpa only [real_quadratic_charge, Complex.ofReal_intCast] using
    D5.S3.Fourier.MatrixGaussian.summable_norm_theta
      (D.G.map (Int.cast : ℤ → ℝ)) hD τ hτ

private theorem charge_power_eq_exp (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (τ : ℂ) (a : Charge D) :
    exp (2 * Real.pi * I * τ) ^ (chargeEnergy D a).toNat =
      exp (Real.pi * I * τ * (bilinear D a a : ℂ)) := by
  have hc : ((chargeEnergy D a).toNat : ℂ) = (chargeEnergy D a : ℂ) := by
    exact_mod_cast (Int.toNat_of_nonneg (chargeEnergy_nonneg D hD a))
  have hb : (bilinear D a a : ℂ) = 2 * (chargeEnergy D a : ℂ) := by
    exact_mod_cast (two_chargeEnergy D a).symm
  rw [← exp_nat_mul, hc, hb]
  congr 1
  ring

/-- Absolute convergence of the actual basis-label series and its exact
charge/occupation factorization. The charge exponent is the even integral
half-norm supplied by LatticeData, not a rounded real quadratic form. -/
theorem ordinary_label_series (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun a : Label D =>
      ‖exp (2 * Real.pi * I * τ) ^ totalDegree D a‖) ∧
    (∑' a : Label D, exp (2 * Real.pi * I * τ) ^ totalDegree D a) =
      latticeTheta D τ *
        (∑' d : Exponent D, exp (2 * Real.pi * I * τ) ^ oscillatorEnergy d) := by
  let q := exp (2 * Real.pi * I * τ)
  have hc : Summable (fun a : Charge D => ‖q ^ (chargeEnergy D a).toNat‖) := by
    simpa only [q, charge_power_eq_exp D hD τ] using
      summable_norm_charge_exp D hD τ hτ
  have ho : Summable (fun d : Exponent D => ‖q ^ oscillatorEnergy d‖) :=
    summable_norm_unsigned D (ordinary_q_norm τ hτ)
  have hp : Summable (fun a : Label D =>
      ‖q ^ (chargeEnergy D a.1).toNat * q ^ oscillatorEnergy a.2‖) :=
    Summable.mul_norm (f := fun a : Charge D => q ^ (chargeEnergy D a).toNat)
      (g := fun d : Exponent D => q ^ oscillatorEnergy d) hc ho
  have hn : Summable (fun a : Label D => ‖q ^ totalDegree D a‖) := by
    apply hp.congr
    intro a
    rw [totalDegree_add D hD a, pow_add]
  refine ⟨hn, ?_⟩
  calc
    (∑' a : Label D, q ^ totalDegree D a) =
        ∑' a : Label D, q ^ (chargeEnergy D a.1).toNat * q ^ oscillatorEnergy a.2 :=
      tsum_congr (fun a => by rw [totalDegree_add D hD a, pow_add])
    _ = (∑' a : Charge D, q ^ (chargeEnergy D a).toNat) *
        (∑' d : Exponent D, q ^ oscillatorEnergy d) :=
      (tsum_mul_tsum_of_summable_norm
        (f := fun a : Charge D => q ^ (chargeEnergy D a).toNat)
        (g := fun d : Exponent D => q ^ oscillatorEnergy d) hc ho).symm
    _ = latticeTheta D τ * (∑' d : Exponent D, q ^ oscillatorEnergy d) := by
      congr 1
      exact tsum_congr (charge_power_eq_exp D hD τ)

/-- Reindex the genuine all-label series by total energy. Finite fibers are
counted with the dimension of the actual L0 eigenspace; norms are reindexed
as well, so absolute convergence of the dimension series is proved. -/
theorem actual_ordinary_series (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun N : ℕ =>
      ‖(actualOrdinaryCoefficient D H N : ℂ) * exp (2 * Real.pi * I * τ) ^ N‖) ∧
    HasSum (fun N : ℕ =>
      (actualOrdinaryCoefficient D H N : ℂ) * exp (2 * Real.pi * I * τ) ^ N)
      (latticeTheta D τ *
        (∑' d : Exponent D, exp (2 * Real.pi * I * τ) ^ oscillatorEnergy d)) := by
  classical
  let q := exp (2 * Real.pi * I * τ)
  haveI (N : ℕ) : Finite (NaturalEnergyFiber D N) := naturalEnergyFiber_finite D hD N
  haveI (N : ℕ) : Fintype (NaturalEnergyFiber D N) := Fintype.ofFinite _
  have hfiber (N : ℕ) :
      (∑' a : NaturalEnergyFiber D N, q ^ totalDegree D a.1) =
        (actualOrdinaryCoefficient D H N : ℂ) * q ^ N := by
    rw [actualOrdinaryCoefficient_eq_naturalCard D H hHG hGH hD N]
    calc
      _ = ∑' _a : NaturalEnergyFiber D N, q ^ N :=
        tsum_congr (fun a => congrArg (fun n => q ^ n) a.2)
      _ = _ := by
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Nat.card_eq_fintype_card]
  have hnormfiber (N : ℕ) :
      (∑' a : NaturalEnergyFiber D N, ‖q ^ totalDegree D a.1‖) =
        ‖(actualOrdinaryCoefficient D H N : ℂ) * q ^ N‖ := by
    rw [actualOrdinaryCoefficient_eq_naturalCard D H hHG hGH hD N]
    calc
      _ = ∑' _a : NaturalEnergyFiber D N, ‖q ^ N‖ :=
        tsum_congr (fun a => congrArg (fun n => ‖q ^ n‖) a.2)
      _ = _ := by
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Nat.card_eq_fintype_card, norm_mul, Complex.norm_natCast]
  obtain ⟨hlabel, hfactor⟩ := ordinary_label_series D hD τ hτ
  have hnormGroup : HasSum
      (fun N : ℕ => ∑' a : NaturalEnergyFiber D N, ‖q ^ totalDegree D a.1‖)
      (∑' a : Label D, ‖q ^ totalDegree D a‖) :=
    hlabel.hasSum.tsum_fiberwise (totalDegree D)
  have hgroup : HasSum
      (fun N : ℕ => ∑' a : NaturalEnergyFiber D N, q ^ totalDegree D a.1)
      (∑' a : Label D, q ^ totalDegree D a) :=
    hlabel.of_norm.hasSum.tsum_fiberwise (totalDegree D)
  have hcoeff : HasSum
      (fun N : ℕ => (actualOrdinaryCoefficient D H N : ℂ) * q ^ N)
      (∑' a : Label D, q ^ totalDegree D a) :=
    hgroup.congr_fun (fun N => (hfiber N).symm)
  refine ⟨(hnormGroup.congr_fun (fun N => (hnormfiber N).symm)).summable, ?_⟩
  rw [hfactor] at hcoeff
  exact hcoeff

/-- The ordinary character of the actual full positive even lattice VOA.
Every coefficient is the finrank of its canonical Sugawara L0 eigenspace.
The proof factors an absolutely convergent, genuinely reindexed basis sum
and evaluates its unsigned oscillator factor by the eta Euler product.
No unimodularity, rootlessness, parity of rank, or nonzero rank is required. -/
theorem actual_ordinary_character (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable (fun N : ℕ =>
      ‖exp (-2 * Real.pi * I * τ * D.rank / 24) *
        ((Module.finrank ℂ ((sugawaraMode D H 0).eigenspace (N : ℂ)) : ℂ) *
          exp (2 * Real.pi * I * τ) ^ N)‖) ∧
    HasSum (fun N : ℕ =>
      exp (-2 * Real.pi * I * τ * D.rank / 24) *
        ((Module.finrank ℂ ((sugawaraMode D H 0).eigenspace (N : ℂ)) : ℂ) *
          exp (2 * Real.pi * I * τ) ^ N))
      (latticeTheta D τ / (ModularForm.eta τ) ^ D.rank) ∧
    actualOrdinaryCharacter D H τ = latticeTheta D τ / (ModularForm.eta τ) ^ D.rank := by
  obtain ⟨hnorm, hsum⟩ := actual_ordinary_series D H hHG hGH hD τ hτ
  let c := exp (-2 * Real.pi * I * τ * D.rank / 24)
  have hnorm' : Summable (fun N : ℕ =>
      ‖c * ((actualOrdinaryCoefficient D H N : ℂ) *
        exp (2 * Real.pi * I * τ) ^ N)‖) := by
    simpa only [norm_mul] using hnorm.mul_left ‖c‖
  have heval : c * (latticeTheta D τ *
      (∑' d : Exponent D, exp (2 * Real.pi * I * τ) ^ oscillatorEnergy d)) =
      latticeTheta D τ / (ModularForm.eta τ) ^ D.rank := by
    calc
      _ = latticeTheta D τ * (c *
          (∑' d : Exponent D, exp (2 * Real.pi * I * τ) ^ oscillatorEnergy d)) :=
        mul_left_comm _ _ _
      _ = latticeTheta D τ * (1 / (ModularForm.eta τ) ^ D.rank) := by
        rw [normalized_unsigned_eq_eta D τ hτ]
      _ = _ := by simp only [div_eq_mul_inv, one_mul]
  have hsum' := hsum.mul_left c
  rw [heval] at hsum'
  refine ⟨hnorm', hsum', ?_⟩
  unfold actualOrdinaryCharacter
  rw [hsum.tsum_eq]
  exact heval

#print axioms actualOrdinaryCoefficient_eq_card
#print axioms actual_ordinary_series
#print axioms actual_ordinary_character

end D5.S3.VertexAlgebra.LatticeOrdinaryCharacter
