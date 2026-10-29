/- GID: D5/S3/VertexAlgebra/Sewing/CanonicalFullChargeLoop
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sewing/CanonicalFullChargeLoop
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint charge and occupation convergence and actual full-energy compressed traces. -/

import D5.S3.VertexAlgebra.Sewing.CanonicalTwoVertexLoop
import D5.S3.VertexAlgebra.LatticeEnergyGrading
import D5.S3.Fourier.MatrixGaussianPoisson
import Mathlib.LinearAlgebra.Trace

/-! Polynomial charge growth, Gaussian moments, and original finite-energy traces. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.CanonicalFullChargeLoop

open LatticeGeneratingFieldLocality LatticeSectorIntertwiner LatticeAllStateField
open CanonicalOccupationSewing LatticePositiveEnergy
open LatticeActualGeneratorLocality LatticeFiniteNegativeGeneration
open scoped BigOperators VertexOperator

open private wordCoeff from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow
open private canonical_basis_input_expansion
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupation
open private mixedConstant mixedRadius mixedEnergy mixedConstant_nonneg
  mixed_descendant_bound mixedEnvelope mixedEnvelope_nonneg
  from D5.S3.VertexAlgebra.Sewing.CanonicalTwoCutOccupation
open private radial_polynomial_bound
  from D5.S3.VertexAlgebra.Sewing.CanonicalTwoCutScalar
open private cyclic_envelope_summable
  from D5.S3.VertexAlgebra.Sewing.CanonicalTwoVertexLoop
open private summable_fin_prod from D5.S3.Fourier.MatrixGaussianPoisson

noncomputable section

private def chargeSize (D : LatticeData) (β : Charge D) : ℝ :=
  ∏ i : Fin D.rank, (1 + ‖(β i : ℂ)‖)

private theorem chargeSize_one_le (D : LatticeData) (β : Charge D) :
    1 ≤ chargeSize D β :=
  Finset.one_le_prod₀ (fun _ _ => le_add_of_nonneg_right (norm_nonneg _))

private theorem coordinate_le_chargeSize (D : LatticeData) (β : Charge D)
    (i : Fin D.rank) : ‖(β i : ℂ)‖ ≤ chargeSize D β := by
  have hh : 1 + ‖(β i : ℂ)‖ ≤ chargeSize D β :=
    by
      have he (j : Fin D.rank) : max (1+‖(β j : ℂ)‖) 1 = 1+‖(β j : ℂ)‖ :=
        max_eq_left (le_add_of_nonneg_right (norm_nonneg _))
      simpa only [he, chargeSize] using Finset.le_prod_max_one (Finset.mem_univ i)
        (fun j : Fin D.rank => (1+‖(β j : ℂ)‖ : ℝ))
  linarith [norm_nonneg (β i : ℂ)]

private theorem bilinear_charge_bound (D : LatticeData) (β : Charge D)
    (i : Fin D.rank) :
    ‖(bilinear D (unitCharge D i) β : ℂ)‖ ≤
      (∑ j : Fin D.rank, ‖(D.G i j : ℂ)‖) * chargeSize D β := by
  classical
  have heq : (bilinear D (unitCharge D i) β : ℂ) =
      ∑ j : Fin D.rank, (D.G i j : ℂ) * (β j : ℂ) := by
    simp [bilinear, unitCharge, Int.cast_sum, Int.cast_mul]
  rw [heq]
  apply (norm_sum_le _ _).trans
  calc
    _ = ∑ j : Fin D.rank, ‖(D.G i j : ℂ)‖ * ‖(β j : ℂ)‖ := by
      simp only [norm_mul]
    _ ≤ ∑ j : Fin D.rank, ‖(D.G i j : ℂ)‖ * chargeSize D β :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (coordinate_le_chargeSize D β j) (norm_nonneg _))
    _ = _ := (Finset.sum_mul ..).symm

private def chargeConstant (D : LatticeData) (δ : Charge D) (A T : ℝ) :
    List (Index D) → ℝ
  | [] => 1
  | (i,k) :: ω => chargeConstant D δ A T ω *
      (A⁻¹ + ‖(bilinear D (unitCharge D i) δ : ℂ)‖ +
        (∑ j : Fin D.rank, ‖(D.G i j : ℂ)‖) +
        ((k+1 : ℕ) : ℝ)^k * (∑ j : Fin D.rank, ‖(D.G i j : ℂ)‖) / T)

private theorem chargeConstant_nonneg (D : LatticeData) (δ : Charge D)
    (A T : ℝ) (hA : 1 ≤ A) (hT : 1 ≤ T) (ω : List (Index D)) :
    0 ≤ chargeConstant D δ A T ω := by
  induction ω with
  | nil => simp [chargeConstant]
  | cons x ω ih =>
    dsimp [chargeConstant]
    have hA0 : 0 ≤ A := by linarith
    have hT0 : 0 ≤ T := by linarith
    exact mul_nonneg ih (by positivity)

/-- The literal finite occurrence list gives a polynomial charge degree equal
 to its length; the mode and both occupations do not enter this bound. -/
private theorem mixedConstant_charge_bound (D : LatticeData) (a δ β : Charge D)
    (A T : ℝ) (hA : 1 ≤ A) (hT : 1 ≤ T) (ω : List (Index D)) :
    mixedConstant D a (δ+β) A T ω ≤
      chargeConstant D δ A T ω * chargeSize D β ^ ω.length := by
  have hR := chargeSize_one_le D β
  have hA0 : 0 ≤ A := by linarith
  have hT0 : 0 ≤ T := by linarith
  induction ω with
  | nil => simp [mixedConstant, chargeConstant]
  | cons x ω ih =>
    have hb : ‖(bilinear D (unitCharge D x.1) (δ+β) : ℂ)‖ ≤
        ‖(bilinear D (unitCharge D x.1) δ : ℂ)‖ +
          (∑ j : Fin D.rank, ‖(D.G x.1 j : ℂ)‖) * chargeSize D β := by
      rw [bilinear_add_right, Int.cast_add]
      exact (norm_add_le _ _).trans (add_le_add (le_refl _) (bilinear_charge_bound D β x.1))
    have hf : A⁻¹ + ‖(bilinear D (unitCharge D x.1) (δ+β) : ℂ)‖ +
        ((x.2+1 : ℕ) : ℝ)^x.2 * (∑ j, ‖(D.G x.1 j : ℂ)‖) / T ≤
        (A⁻¹ + ‖(bilinear D (unitCharge D x.1) δ : ℂ)‖ +
          (∑ j, ‖(D.G x.1 j : ℂ)‖) +
          ((x.2+1 : ℕ) : ℝ)^x.2 * (∑ j, ‖(D.G x.1 j : ℂ)‖) / T) * chargeSize D β := by
      have hz : 0 ≤ A⁻¹ + ‖(bilinear D (unitCharge D x.1) δ : ℂ)‖ +
          ((x.2+1 : ℕ) : ℝ)^x.2 * (∑ j, ‖(D.G x.1 j : ℂ)‖) / T := by positivity
      nlinarith [mul_nonneg hz (sub_nonneg.mpr hR)]
    change mixedConstant D a (δ+β) A T ω * _ ≤ _
    calc
      _ ≤ (chargeConstant D δ A T ω * chargeSize D β ^ ω.length) *
          ((A⁻¹ + ‖(bilinear D (unitCharge D x.1) δ : ℂ)‖ +
            (∑ j, ‖(D.G x.1 j : ℂ)‖) +
            ((x.2+1 : ℕ) : ℝ)^x.2 * (∑ j, ‖(D.G x.1 j : ℂ)‖) / T) * chargeSize D β) :=
        mul_le_mul ih hf (by positivity)
          (mul_nonneg (chargeConstant_nonneg D δ A T hA hT ω)
            (pow_nonneg (by linarith) _))
      _ = _ := by simp only [chargeConstant, List.length_cons, pow_succ]; ring

private theorem scalar_gaussian_moment (decay : ℝ) (hdecay : 0 < decay) (L : ℕ) :
    Summable (fun n : ℤ => (1+‖(n : ℂ)‖)^L * Real.exp (-decay*(n : ℝ)^2)) := by
  have hm (k : ℕ) : Summable (fun n : ℤ => |(n : ℝ)|^k * Real.exp (-decay*(n : ℝ)^2)) := by
    have hh := summable_pow_mul_jacobiTheta₂_term_bound 0
      (div_pos hdecay Real.pi_pos) k
    convert hh using 1
    ext n
    congr 1 <;> simp <;> field_simp <;> simp
  have hs : Summable (fun n : ℤ => ∑ k ∈ Finset.range (L+1),
      (|(n : ℝ)|^k * Real.exp (-decay*(n : ℝ)^2)) * (L.choose k : ℝ)) :=
    summable_sum (fun k _ => (hm k).mul_right _)
  convert hs using 1
  ext n
  rw [Complex.norm_intCast, add_comm 1, add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow, mul_one]
  ring

private theorem charge_gaussian_moment (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (r : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (L : ℕ) :
    Summable (fun β : Charge D => r^(chargeEnergy D β).toNat * chargeSize D β^L) := by
  obtain ⟨c,hc,hcoercive⟩ := quadratic_coercive D hD
  let ρ := (1+r)/2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρ' : ρ < 1 := by dsimp [ρ]; linarith
  have hrρ : r ≤ ρ := by dsimp [ρ]; linarith
  have hlog : Real.log ρ < 0 := Real.log_neg hρ hρ'
  let decay := -Real.log ρ * c / 2
  have hdecay : 0 < decay := by
    dsimp [decay]
    exact div_pos (mul_pos (neg_pos.mpr hlog) hc) (by norm_num)
  have hs := summable_fin_prod (fun _ : Fin D.rank =>
    fun n : ℤ => (1+‖(n : ℂ)‖)^L * Real.exp (-decay*(n : ℝ)^2))
    (fun _ => scalar_gaussian_moment decay hdecay L) (fun _ _ => by positivity)
  refine hs.of_nonneg_of_le (fun β => by
    have hsize := chargeSize_one_le D β
    positivity) (fun β => ?_)
  have hQ := chargeEnergy_nonneg D hD β
  have hQc : ((chargeEnergy D β).toNat : ℝ) = (chargeEnergy D β : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hQ
  have hquad : c * (∑ i : Fin D.rank, (β i : ℝ)^2) ≤
      2*(chargeEnergy D β : ℝ) := by
    simpa only [realQuadratic_charge] using
      hcoercive (WithLp.toLp 2 (fun i => (β i : ℝ)))
  have hweight : r^(chargeEnergy D β).toNat ≤
      Real.exp (-decay * ∑ i : Fin D.rank, (β i : ℝ)^2) := by
    calc
      _ ≤ ρ^(chargeEnergy D β).toNat := pow_le_pow_left₀ hr hrρ _
      _ = Real.exp (((chargeEnergy D β).toNat : ℝ)*Real.log ρ) := by
        rw [Real.exp_nat_mul, Real.exp_log hρ]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [hQc]
        dsimp [decay]
        nlinarith [mul_le_mul_of_nonneg_left hquad (neg_nonneg.mpr hlog.le)]
  calc
    _ ≤ Real.exp (-decay * ∑ i : Fin D.rank, (β i : ℝ)^2) * chargeSize D β^L :=
      mul_le_mul_of_nonneg_right hweight (pow_nonneg (by
        have := chargeSize_one_le D β; linarith) _)
    _ = _ := by
      simp only [chargeSize, Finset.prod_mul_distrib, ← Finset.prod_pow,
        ← Real.exp_sum, ← Finset.mul_sum]
      ring

private theorem polynomial_cyclic_summable (D : LatticeData) (A T : ℝ)
    (hA : 1 ≤ A) (hT : 1 ≤ T) (J : ℕ) (r1 r2 : ℝ)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hr1' : r1 < 1) (hr2' : r2 < 1) :
    Summable (fun z : Occ D × Occ D => r1^level D z.1 * r2^level D z.2 *
      mixedEnergy D z.1 z.2^J * mixedEnvelope D A T z.1 z.2 *
        mixedEnvelope D A T z.2 z.1) := by
  obtain ⟨C1,hC1,hb1⟩ := radial_polynomial_bound J r1 hr1 hr1'
  obtain ⟨C2,hC2,hb2⟩ := radial_polynomial_bound J r2 hr2 hr2'
  have hs := (cyclic_envelope_summable D A T hA (by linarith)
    ((1+r1)/2) ((1+r2)/2) (by positivity) (by positivity)
    (by linarith) (by linarith)).mul_left (C1*C2)
  refine hs.of_nonneg_of_le (fun z => by
    have := mixedEnvelope_nonneg D A T (by linarith) (by linarith) z.1 z.2
    have := mixedEnvelope_nonneg D A T (by linarith) (by linarith) z.2 z.1
    dsimp [mixedEnergy]; positivity) ?_
  rintro ⟨d,e⟩
  have hM := mixedEnvelope_nonneg D A T (by linarith) (by linarith) d e
  have hM' := mixedEnvelope_nonneg D A T (by linarith) (by linarith) e d
  have hpoly : mixedEnergy D d e^J ≤
      (1+(level D d : ℝ))^J * (1+(level D e : ℝ))^J := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by dsimp [mixedEnergy]; positivity)
    dsimp [mixedEnergy]
    nlinarith [Nat.cast_nonneg (α := ℝ) (level D d),
      Nat.cast_nonneg (α := ℝ) (level D e)]
  calc
    _ ≤ r1^level D d * r2^level D e *
        ((1+(level D d : ℝ))^J * (1+(level D e : ℝ))^J) *
          mixedEnvelope D A T d e * mixedEnvelope D A T e d := by gcongr
    _ = (r1^level D d * (1+(level D d : ℝ))^J) *
        (r2^level D e * (1+(level D e : ℝ))^J) *
          mixedEnvelope D A T d e * mixedEnvelope D A T e d := by ring
    _ ≤ (C1*((1+r1)/2)^level D d) * (C2*((1+r2)/2)^level D e) *
          mixedEnvelope D A T d e * mixedEnvelope D A T e d := by
      apply mul_le_mul_of_nonneg_right _ hM'
      apply mul_le_mul_of_nonneg_right _ hM
      exact mul_le_mul (hb1 _) (hb2 _) (by positivity) (by positivity)
    _ = _ := by ring

private theorem word_joint_summable (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Charge D)
    (ω ν : List (Index D)) (m1 m2 : Charge D × (Occ D × Occ D) → ℤ)
    (q1 q2 : ℂ) (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun z : Charge D × (Occ D × Occ D) =>
      ‖q1^((chargeEnergy D z.1).toNat+level D z.2.1) *
        q2^((chargeEnergy D (-a+z.1)).toNat+level D z.2.2) *
        wordCoeff D a (-a+z.1) ω (m1 z) z.2.1 z.2.2 *
        wordCoeff D (-a) z.1 ν (m2 z) z.2.2 z.2.1‖) := by
  classical
  let A : ℝ := 1+∑ i : Fin D.rank, ‖(a i : ℂ)‖
  let T : ℝ := 1+∑ i : Fin D.rank, ‖(bilinear D a (unitCharge D i) : ℂ)‖
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg (by intros; positivity))
  have hT : 1 ≤ T := le_add_of_nonneg_right (Finset.sum_nonneg (by intros; positivity))
  have ha (i : Fin D.rank) : ‖(a i : ℂ)‖ ≤ A := by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => norm_nonneg (a j : ℂ))
      (Finset.mem_univ i)
    dsimp [A]; linarith
  have ht (i : Fin D.rank) : ‖(bilinear D a (unitCharge D i) : ℂ)‖ ≤ T := by
    have := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      norm_nonneg (bilinear D a (unitCharge D j) : ℂ)) (Finset.mem_univ i)
    dsimp [T]; linarith
  have hna (i : Fin D.rank) : ‖((-a) i : ℂ)‖ ≤ A := by simpa using ha i
  have hnt (i : Fin D.rank) : ‖(bilinear D (-a) (unitCharge D i) : ℂ)‖ ≤ T := by
    simpa [bilinear_neg_left] using ht i
  let C := chargeConstant D (-a) A T ω * chargeConstant D 0 A T ν
  let L := ω.length+ν.length
  let J := mixedRadius D ω+mixedRadius D ν
  have hC1 := chargeConstant_nonneg D (-a) A T hA hT ω
  have hC2 := chargeConstant_nonneg D 0 A T hA hT ν
  have hC : 0 ≤ C := mul_nonneg hC1 hC2
  let f := fun β : Charge D => ‖q1‖^(chargeEnergy D β).toNat * chargeSize D β^L
  let g := fun z : Occ D × Occ D => ‖q1‖^level D z.1 * ‖q2‖^level D z.2 *
    mixedEnergy D z.1 z.2^J * mixedEnvelope D A T z.1 z.2 * mixedEnvelope D A T z.2 z.1
  have hf : Summable f := charge_gaussian_moment D hD ‖q1‖ (norm_nonneg _) hq1 L
  have hg : Summable g := polynomial_cyclic_summable D A T hA hT J ‖q1‖ ‖q2‖
    (norm_nonneg _) (norm_nonneg _) hq1 hq2
  have hf0 (β : Charge D) : 0 ≤ f β := by
    dsimp [f]; have := chargeSize_one_le D β; positivity
  have hg0 (z : Occ D × Occ D) : 0 ≤ g z := by
    dsimp [g]; have := mixedEnvelope_nonneg D A T (by linarith) (by linarith) z.1 z.2
    have := mixedEnvelope_nonneg D A T (by linarith) (by linarith) z.2 z.1
    dsimp [mixedEnergy]; positivity
  have hs := (hf.mul_of_nonneg hg hf0 hg0).mul_left C
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  rintro ⟨β,d,e⟩
  have hR := chargeSize_one_le D β
  have hM := mixedEnvelope_nonneg D A T (by linarith) (by linarith) d e
  have hM' := mixedEnvelope_nonneg D A T (by linarith) (by linarith) e d
  have hb1 := (mixed_descendant_bound D a (-a+β) A T hA hT ha ht ω
    (m1 (β,d,e)) d e).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mixedConstant_charge_bound D a (-a) β A T hA hT ω)
        (pow_nonneg (by dsimp [mixedEnergy]; positivity) _)) hM)
  have hb2 := (mixed_descendant_bound D (-a) β A T hA hT hna hnt ν
    (m2 (β,d,e)) e d).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by simpa using
        (mixedConstant_charge_bound D (-a) 0 β A T hA hT ν))
        (pow_nonneg (by dsimp [mixedEnergy]; positivity) _)) hM')
  have hN : 0 ≤ mixedEnergy D d e := by dsimp [mixedEnergy]; positivity
  have hpair := mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
  have he : mixedEnergy D e d = mixedEnergy D d e := by dsimp [mixedEnergy]; ring
  rw [he] at hpair
  have hpair' : ‖wordCoeff D a (-a+β) ω (m1 (β,d,e)) d e‖ *
      ‖wordCoeff D (-a) β ν (m2 (β,d,e)) e d‖ ≤
      C * chargeSize D β^L * mixedEnergy D d e^J *
        mixedEnvelope D A T d e * mixedEnvelope D A T e d := by
    convert hpair using 1
    dsimp [C,L,J]
    rw [pow_add,pow_add]
    ring
  have hq2Q : ‖q2‖^(chargeEnergy D (-a+β)).toNat ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hq2.le
  simp only [norm_mul,norm_pow,pow_add]
  calc
    _ = (‖q1‖^(chargeEnergy D β).toNat * ‖q2‖^(chargeEnergy D (-a+β)).toNat) *
        (‖q1‖^level D d * ‖q2‖^level D e) *
        (‖wordCoeff D a (-a+β) ω (m1 (β,d,e)) d e‖ *
          ‖wordCoeff D (-a) β ν (m2 (β,d,e)) e d‖) := by ring
    _ ≤ (‖q1‖^(chargeEnergy D β).toNat * 1) *
        (‖q1‖^level D d * ‖q2‖^level D e) *
        (C * chargeSize D β^L * mixedEnergy D d e^J *
          mixedEnvelope D A T d e * mixedEnvelope D A T e d) := by gcongr
    _ = _ := by dsimp [f,g]; ring

/-- The literal ordinary two-vertex cycle, with both total-energy offsets. -/
def loopTerm (D : LatticeData) (a : Charge D) (u v : Oscillator D)
    (r s : ℤ) (q1 q2 : ℂ) (z : Charge D × (Occ D × Occ D)) : ℂ :=
  q1^((chargeEnergy D z.1).toNat+level D z.2.1) *
    q2^((chargeEnergy D (-a+z.1)).toNat+level D z.2.2) *
    (canonical D a (-a+z.1) u
      (r+energy D (-a+z.1,z.2.2)-energy D (z.1,z.2.1)) (b D z.2.2)).coeff z.2.1 *
    (canonical D (-a) z.1 v
      (s+energy D (z.1,z.2.1)-energy D (-a+z.1,z.2.2)) (b D z.2.1)).coeff z.2.2

/-- Absolute convergence over every internal integral charge and both
 unrestricted occupations, for positive real Gram and both open disks. -/
theorem full_charge_loop_summable (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Charge D)
    (u v : Oscillator D) (r s : ℤ) (q1 q2 : ℂ)
    (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun z : Charge D × (Occ D × Occ D) => ‖loopTerm D a u v r s q1 q2 z‖) := by
  classical
  let m1 := fun z : Charge D × (Occ D × Occ D) =>
    r+energy D (-a+z.1,z.2.2)-energy D (z.1,z.2.1)
  let m2 := fun z : Charge D × (Occ D × Occ D) =>
    s+energy D (z.1,z.2.1)-energy D (-a+z.1,z.2.2)
  have hs : Summable (fun z : Charge D × (Occ D × Occ D) =>
      ∑ U ∈ u.support, ∑ V ∈ v.support,
        ‖(u.coeff U*v.coeff V) *
          (q1^((chargeEnergy D z.1).toNat+level D z.2.1) *
            q2^((chargeEnergy D (-a+z.1)).toNat+level D z.2.2) *
            wordCoeff D a (-a+z.1) (occurrences D U) (m1 z) z.2.1 z.2.2 *
            wordCoeff D (-a) z.1 (occurrences D V) (m2 z) z.2.2 z.2.1)‖) := by
    apply summable_sum
    intro U hU
    apply summable_sum
    intro V hV
    simpa only [norm_mul] using
      (word_joint_summable D hD a (occurrences D U) (occurrences D V)
        m1 m2 q1 q2 hq1 hq2).mul_left ‖u.coeff U*v.coeff V‖
  refine hs.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro z
  have heq : loopTerm D a u v r s q1 q2 z =
      ∑ U ∈ u.support, ∑ V ∈ v.support,
        (u.coeff U*v.coeff V) *
          (q1^((chargeEnergy D z.1).toNat+level D z.2.1) *
            q2^((chargeEnergy D (-a+z.1)).toNat+level D z.2.2) *
            wordCoeff D a (-a+z.1) (occurrences D U) (m1 z) z.2.1 z.2.2 *
            wordCoeff D (-a) z.1 (occurrences D V) (m2 z) z.2.2 z.2.1) := by
    simp only [loopTerm,canonical_basis_input_expansion,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    dsimp [m1,m2]
    ring
  rw [heq]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun U hU => norm_sum_le _ _))

private theorem energy_toNat (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (x : Label D) :
    (energy D x).toNat = (chargeEnergy D x.1).toNat+level D x.2 := by
  have := chargeEnergy_nonneg D hD x.1
  dsimp [energy,level]
  omega

/-- Projection of an actual Y mode, restricted to an actual full-energy grade. -/
def energyBlock (D : LatticeData) (a : Charge D) (u : Oscillator D)
    (r : ℤ) (n m : ℕ) : grade D (m : ℤ) →ₗ[ℂ] grade D (n : ℤ) :=
  ((gradeProjection D (n : ℤ)).comp
    ((((Y D (inclusion D a u))[[r+(m : ℤ)-(n : ℤ)]] )).comp
      (grade D (m : ℤ)).subtype)).codRestrict (grade D (n : ℤ))
        (fun _ => gradeProjection_mem D (n : ℤ) _)

/-- Trace of the two original full-energy grade compressions. -/
def blockTrace (D : LatticeData) (a : Charge D) (u v : Oscillator D)
    (r s : ℤ) (n m : ℕ) : ℂ :=
  LinearMap.trace ℂ (grade D (n : ℤ))
    ((energyBlock D a u r n m).comp (energyBlock D (-a) v s m n))

private theorem grade_repr_coeff (D : LatticeData) (n : ℤ)
    (v : grade D n) (x : EnergyFiber D n) :
    (gradeBasis D n).repr v x = (v.1 x.1.1).coeff x.1.2 := rfl

private theorem gradeBasis_coe (D : LatticeData) (n : ℤ) (x : EnergyFiber D n) :
    (gradeBasis D n x : Carrier D) = inclusion D x.1.1 (b D x.1.2) := by
  classical
  apply (carrierCoeffEquiv D).injective
  ext y
  by_cases hy : energy D y = n
  · have hh := congrArg (fun f : EnergyFiber D n →₀ ℂ => f ⟨y,hy⟩)
      ((gradeBasis D n).repr_self x)
    rw [grade_repr_coeff] at hh
    change ((gradeBasis D n x : Carrier D) y.1).coeff y.2 =
      ((inclusion D x.1.1 (b D x.1.2)) y.1).coeff y.2
    rw [hh]
    by_cases hc : x.1.1 = y.1 <;> by_cases hd : x.1.2 = y.2 <;>
      simp [inclusion,b,Finsupp.single_apply,MvPolynomial.coeff_monomial,
        Subtype.ext_iff,Prod.ext_iff,hc,hd,Ne.symm]
  · have hh := (mem_grade_iff D n (gradeBasis D n x).1).mp (gradeBasis D n x).2 y hy
    change ((gradeBasis D n x : Carrier D) y.1).coeff y.2 =
      ((inclusion D x.1.1 (b D x.1.2)) y.1).coeff y.2
    rw [hh]
    have hxy : x.1 ≠ y := by rintro h; exact hy (h ▸ x.2)
    by_cases hc : x.1.1 = y.1
    · have hd : x.1.2 ≠ y.2 := fun hd => hxy (Prod.ext hc hd)
      simp [inclusion,b,Finsupp.single_apply,MvPolynomial.coeff_monomial,hc,hd,Ne.symm]
    · simp [inclusion,Finsupp.single_apply,hc]

private theorem block_matrix (D : LatticeData) (a : Charge D) (u : Oscillator D)
    (r : ℤ) (n m : ℕ) (x : EnergyFiber D (n : ℤ)) (y : EnergyFiber D (m : ℤ)) :
    (gradeBasis D (n : ℤ)).repr (energyBlock D a u r n m (gradeBasis D (m : ℤ) y)) x =
      if x.1.1 = a+y.1.1 then
        (canonical D a y.1.1 u (r+(m : ℤ)-(n : ℤ)) (b D y.1.2)).coeff x.1.2 else 0 := by
  classical
  change carrierCoeffEquiv D (gradeProjection D (n : ℤ)
    (((Y D (inclusion D a u))[[r+(m : ℤ)-(n : ℤ)]])
      (gradeBasis D (m : ℤ) y : Carrier D))) x.1 = _
  rw [gradeProjection_coeff, ite_eq_left x.2, gradeBasis_coe, ← inclusion_canonical]
  change ((inclusion D (a+y.1.1)
    (canonical D a y.1.1 u (r+(m : ℤ)-(n : ℤ)) (b D y.1.2))) x.1.1).coeff x.1.2 = _
  by_cases hx : x.1.1 = a+y.1.1 <;> simp [inclusion,hx]

private def pairTerm (D : LatticeData) (a : Charge D) (u v : Oscillator D)
    (r s : ℤ) (q1 q2 : ℂ) (z : Label D × Label D) : ℂ :=
  if z.2.1 = -a+z.1.1 then
    q1^(energy D z.1).toNat * q2^(energy D z.2).toNat *
      (canonical D a z.2.1 u (r+energy D z.2-energy D z.1) (b D z.2.2)).coeff z.1.2 *
      (canonical D (-a) z.1.1 v (s+energy D z.1-energy D z.2) (b D z.1.2)).coeff z.2.2
  else 0

private def cycleEmbedding (D : LatticeData) (a : Charge D) :
    Charge D × (Occ D × Occ D) ↪ Label D × Label D where
  toFun z := ((z.1,z.2.1),(-a+z.1,z.2.2))
  inj' := by
    rintro ⟨β,d,e⟩ ⟨β',d',e'⟩ h
    simp only [Prod.ext_iff, add_left_cancel_iff] at h ⊢
    tauto

private theorem pairTerm_cycle (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a : Charge D) (u v : Oscillator D) (r s : ℤ) (q1 q2 : ℂ)
    (z : Charge D × (Occ D × Occ D)) :
    pairTerm D a u v r s q1 q2 (cycleEmbedding D a z) = loopTerm D a u v r s q1 q2 z := by
  simp only [pairTerm,cycleEmbedding,Function.Embedding.coeFn_mk,ite_true,
    energy_toNat D hD,loopTerm]

private theorem pairTerm_off_cycle (D : LatticeData) (a : Charge D)
    (u v : Oscillator D) (r s : ℤ) (q1 q2 : ℂ) (z : Label D × Label D)
    (hz : z ∉ Set.range (cycleEmbedding D a)) : pairTerm D a u v r s q1 q2 z = 0 := by
  have hh : z.2.1 ≠ -a+z.1.1 := by
    intro h
    apply hz
    exact ⟨(z.1.1,z.1.2,z.2.2), by ext <;> simp [cycleEmbedding,h]⟩
  simp [pairTerm,hh]

private theorem weighted_trace_fibers (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a : Charge D) (u v : Oscillator D) (r s : ℤ) (q1 q2 : ℂ) (n m : ℕ) :
    q1^n * q2^m * blockTrace D a u v r s n m =
      ∑' x : EnergyFiber D (n : ℤ), ∑' y : EnergyFiber D (m : ℤ),
        pairTerm D a u v r s q1 q2 (x.1,y.1) := by
  classical
  letI := energyFiber_finite D hD (n : ℤ)
  letI := energyFiber_finite D hD (m : ℤ)
  letI : Fintype (EnergyFiber D (n : ℤ)) := Fintype.ofFinite _
  letI : Fintype (EnergyFiber D (m : ℤ)) := Fintype.ofFinite _
  rw [blockTrace,LinearMap.trace_eq_matrix_trace ℂ (gradeBasis D (n : ℤ)),
    LinearMap.toMatrix_comp (gradeBasis D (n : ℤ)) (gradeBasis D (m : ℤ))
      (gradeBasis D (n : ℤ))]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,LinearMap.toMatrix_apply,
    block_matrix,tsum_fintype,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have hcharge : x.1.1 = a+y.1.1 ↔ y.1.1 = -a+x.1.1 := by
    constructor <;> intro h <;> rw [h] <;> abel
  by_cases hc : y.1.1 = -a+x.1.1
  · have hc' := hcharge.mpr hc
    simp only [ite_eq_left hc,ite_eq_left hc',pairTerm,x.2,y.2,Int.toNat_natCast]
    ring
  · have hc' := mt hcharge.mp hc
    simp [pairTerm,hc,hc']

private def energyPair (D : LatticeData) (z : Label D × Label D) : ℕ × ℕ :=
  ((energy D z.1).toNat,(energy D z.2).toNat)

private def energyPairFiber (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n m : ℕ) :
    {z : Label D × Label D // energyPair D z = (n,m)} ≃
      EnergyFiber D (n : ℤ) × EnergyFiber D (m : ℤ) where
  toFun z := (⟨z.1.1,by
    have h := congrArg Prod.fst z.2
    have hQ := chargeEnergy_nonneg D hD z.1.1.1
    dsimp [energyPair,energy] at h ⊢
    omega⟩,⟨z.1.2,by
    have h := congrArg Prod.snd z.2
    have hQ := chargeEnergy_nonneg D hD z.1.2.1
    dsimp [energyPair,energy] at h ⊢
    omega⟩)
  invFun z := ⟨(z.1.1,z.2.1),by simp [energyPair,z.1.2,z.2.2]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The literal absolutely convergent all-charge loop equals the absolutely
 convergent double series of actual finite full-energy compressed traces. -/
theorem full_charge_loop_trace (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (a : Charge D)
    (u v : Oscillator D) (r s : ℤ) (q1 q2 : ℂ)
    (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (fun nm : ℕ × ℕ => ‖q1^nm.1*q2^nm.2*blockTrace D a u v r s nm.1 nm.2‖) ∧
      (∑' z : Charge D × (Occ D × Occ D), loopTerm D a u v r s q1 q2 z) =
        ∑' nm : ℕ × ℕ, q1^nm.1*q2^nm.2*blockTrace D a u v r s nm.1 nm.2 := by
  have hs := (full_charge_loop_summable D hD a u v r s q1 q2 hq1 hq2).of_norm
  have hp : Summable (pairTerm D a u v r s q1 q2) :=
    ((cycleEmbedding D a).injective.summable_iff
      (pairTerm_off_cycle D a u v r s q1 q2)).mp
        (by simpa only [Function.comp_def,pairTerm_cycle D hD] using hs)
  have hg := hp.hasSum.tsum_fiberwise (energyPair D)
  have heq (nm : ℕ × ℕ) :
      (∑' z : {z : Label D × Label D // energyPair D z = nm},
        pairTerm D a u v r s q1 q2 z.1) =
        q1^nm.1*q2^nm.2*blockTrace D a u v r s nm.1 nm.2 := by
    rw [← (energyPairFiber D hD nm.1 nm.2).symm.tsum_eq]
    have hf : Summable (fun z : EnergyFiber D (nm.1 : ℤ) × EnergyFiber D (nm.2 : ℤ) =>
        pairTerm D a u v r s q1 q2 (z.1.1,z.2.1)) := by
      haveI := energyFiber_finite D hD (nm.1 : ℤ)
      haveI := energyFiber_finite D hD (nm.2 : ℤ)
      letI : Fintype (EnergyFiber D (nm.1 : ℤ) × EnergyFiber D (nm.2 : ℤ)) :=
        Fintype.ofFinite _
      exact (hasSum_fintype _).summable
    exact hf.tsum_prod.trans (weighted_trace_fibers D hD a u v r s q1 q2 nm.1 nm.2).symm
  have hg' : HasSum (fun nm : ℕ × ℕ => q1^nm.1*q2^nm.2*blockTrace D a u v r s nm.1 nm.2)
      (∑' z, pairTerm D a u v r s q1 q2 z) := hg.congr_fun (fun nm => (heq nm).symm)
  refine ⟨hg'.summable.norm, ?_⟩
  rw [hg'.tsum_eq]
  have hh := (cycleEmbedding D a).injective.tsum_eq
    (f := pairTerm D a u v r s q1 q2)
    (by
      intro z hz
      by_contra h
      exact hz (pairTerm_off_cycle D a u v r s q1 q2 z h))
  simpa only [pairTerm_cycle D hD] using hh

end
end D5.S3.VertexAlgebra.CanonicalFullChargeLoop

#print axioms D5.S3.VertexAlgebra.CanonicalFullChargeLoop.full_charge_loop_summable
#print axioms D5.S3.VertexAlgebra.CanonicalFullChargeLoop.full_charge_loop_trace
