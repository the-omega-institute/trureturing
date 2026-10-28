/- GID: D5/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Sewing/CanonicalTwoCutOccupation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-cut analytic sewing majorant for the literal canonical occupation coefficients. -/

import D5.S3.VertexAlgebra.Sewing.CanonicalOccupation
import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
import Batteries.Tactic.OpenPrivate

/-! The literal two-cut occupation envelope and its analytic comparison bridge.
The coefficient recurrence and the summability of the overlap majorant remain
separate obligations of the owning sewing development. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.CanonicalTwoCutOccupation

open LatticeGeneratingFieldLocality LatticeSectorIntertwiner
open ActualSeriesDerivation MvPolynomial
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open LatticeAllStateField LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open FieldNormalProduct
open scoped BigOperators VertexOperator

open D5.S3.VertexAlgebra.CanonicalOccupationSewing
open private wordMap wordCoeff wordCoeff_cons occupation_sub_bounds rowWeight rowWeight_nonneg
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow
open private factorialEnvelope columnWeight columnWeight_nonneg
  canonical_coefficient_expansion canonical_basis_input_expansion
  inner_coefficient_expansion inner_basis_coordinate
  polynomial_factorialEnvelope_summable factorialEnvelope_summable
  polynomial_geometric_bound factorialEnvelope_nonneg
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupation

noncomputable section

abbrev Occ (D : LatticeData) := Index D →₀ ℕ

private def overlapBinomial (D : LatticeData) (e u : Occ D) : ℝ :=
  e.prod (fun x n => (Nat.choose n (u x) : ℝ))

private def mixedEnvelope (D : LatticeData) (A T : ℝ) (d e : Occ D) : ℝ :=
  ∑ u ∈ (Finset.Iic d).filter (fun u => u ≤ e),
    overlapBinomial D e u * T ^ (e - u).degree * factorialEnvelope D A (d - u)

private def mixedEnergy (D : LatticeData) (d e : Occ D) : ℝ :=
  1 + (level D d : ℝ) + (level D e : ℝ)

private def mixedRadius (D : LatticeData) (ω : List (Index D)) : ℕ :=
  ω.foldr (fun x r => r + x.2 + 1) 0

private def mixedConstant (D : LatticeData) (a b : Charge D)
    (A T : ℝ) : List (Index D) → ℝ
  | [] => 1
  | (i,k) :: ω =>
      mixedConstant D a b A T ω *
        (A⁻¹ + ‖(bilinear D (unitCharge D i) b : ℂ)‖ +
          ((k + 1 : ℕ) : ℝ) ^ k *
            (∑ j : Fin D.rank, ‖(D.G i j : ℂ)‖) / T)

private theorem overlapBinomial_nonneg (D : LatticeData) (e u : Occ D) :
    0 ≤ overlapBinomial D e u := by
  classical
  unfold overlapBinomial
  exact Finset.prod_nonneg (fun x hx => Nat.cast_nonneg _)

private theorem factorialEnvelope_nonneg' (D : LatticeData) (A : ℝ) (hA : 0 ≤ A)
    (d : Occ D) : 0 ≤ factorialEnvelope D A d := by
  exact factorialEnvelope_nonneg D A hA d

private theorem mixedEnvelope_nonneg (D : LatticeData) (A T : ℝ)
    (hA : 0 ≤ A) (hT : 0 ≤ T) (d e : Occ D) :
    0 ≤ mixedEnvelope D A T d e := by
  classical
  unfold mixedEnvelope
  apply Finset.sum_nonneg
  intro u hu
  exact mul_nonneg (mul_nonneg (overlapBinomial_nonneg D e u) (by positivity))
    (factorialEnvelope_nonneg' D A hA (d - u))

/- The live analytic interface for the new sewing unit.  The hypothesis is the
   exact closed mixed descendant estimate supplied by the coefficient induction;
   keeping it explicit here makes the summability proof independently reusable
   while the literal recurrence proof is completed in the owner module. -/
def MixedControl (D : LatticeData) (a b : Charge D) (ω : List (Index D))
    (A T : ℝ) : Prop :=
  1 ≤ A ∧ 1 ≤ T ∧
    (∀ i : Fin D.rank, ‖(a i : ℂ)‖ ≤ A) ∧
    (∀ i : Fin D.rank,
      ‖(bilinear D a (unitCharge D i) : ℂ)‖ ≤ T) ∧
    (∀ (m : ℤ) (d e : Occ D),
      ‖wordCoeff D a b ω m d e‖ ≤
        mixedConstant D a b A T ω * mixedEnergy D d e ^ mixedRadius D ω *
          mixedEnvelope D A T d e)

private theorem mixedConstant_nonneg (D : LatticeData) (a b : Charge D)
    (ω : List (Index D)) (A T : ℝ) (hA : 1 ≤ A) (hT : 1 ≤ T) :
    0 ≤ mixedConstant D a b A T ω := by
  induction ω generalizing A T with
  | nil => simp [mixedConstant]
  | cons x ω ih =>
      dsimp [mixedConstant]
      exact mul_nonneg (ih A T hA hT) (by
        have hT0 : 0 ≤ T := by linarith
        have hA0 : 0 ≤ A := by linarith
        positivity)

theorem mixed_pair_summable_of_control
    (D : LatticeData) (a b : Charge D) (ω : List (Index D)) (s : ℤ)
    (L B : ℝ) (hL : 1 ≤ L) (hB : 1 ≤ B) (K1 K2 : ℕ)
    (q1 q2 : ℂ) (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1)
    (A T : ℝ) (hcontrol : MixedControl D a b ω A T)
    (hmajor : Summable (fun z : Occ D × Occ D =>
      ‖q1‖ ^ level D z.1 * ‖q2‖ ^ level D z.2 *
        rowWeight D L K1 z.1 *
        (mixedConstant D a b A T ω * mixedEnergy D z.1 z.2 ^ mixedRadius D ω *
          mixedEnvelope D A T z.1 z.2) *
        columnWeight D B K2 z.2)) :
    Summable (fun z : Occ D × Occ D =>
      ‖q1‖ ^ level D z.1 * ‖q2‖ ^ level D z.2 *
        rowWeight D L K1 z.1 *
        ‖wordCoeff D a b ω
          (s + (level D z.2 : ℤ) - (level D z.1 : ℤ)) z.1 z.2‖ *
        columnWeight D B K2 z.2) := by
  classical
  rcases hcontrol with ⟨hA, hT, ha, ht, hcoeff⟩
  have hC : 0 ≤ mixedConstant D a b A T ω :=
    mixedConstant_nonneg D a b ω A T hA hT
  have hrow (d : Occ D) : 0 ≤ rowWeight D L K1 d :=
    rowWeight_nonneg D L hL K1 d
  have hcol (e : Occ D) : 0 ≤ columnWeight D B K2 e :=
    columnWeight_nonneg D B hB K2 e
  refine hmajor.of_nonneg_of_le (fun z => by
    have hrowz := hrow z.1
    have hcolz := hcol z.2
    have hq1z : 0 ≤ ‖q1‖ ^ level D z.1 := by positivity
    have hq2z : 0 ≤ ‖q2‖ ^ level D z.2 := by positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hq1z hq2z) hrowz)
        (norm_nonneg _)) hcolz) ?_
  intro z
  have hb := hcoeff (s + (level D z.2 : ℤ) - (level D z.1 : ℤ)) z.1 z.2
  have hq10 : 0 ≤ ‖q1‖ ^ level D z.1 := by positivity
  have hq20 : 0 ≤ ‖q2‖ ^ level D z.2 := by positivity
  have hw : 0 ≤ ‖q1‖ ^ level D z.1 * ‖q2‖ ^ level D z.2 *
      rowWeight D L K1 z.1 := by
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (hrow z.1)
  have he : 0 ≤ mixedEnvelope D A T z.1 z.2 :=
    mixedEnvelope_nonneg D A T (by linarith) (by linarith) _ _
  have hm : 0 ≤ mixedEnergy D z.1 z.2 ^ mixedRadius D ω := by
    dsimp [mixedEnergy]
    positivity
  calc
    ‖q1‖ ^ level D z.1 * ‖q2‖ ^ level D z.2 * rowWeight D L K1 z.1 *
        ‖wordCoeff D a b ω (s + (level D z.2 : ℤ) - (level D z.1 : ℤ)) z.1 z.2‖ *
        columnWeight D B K2 z.2
        ≤ ‖q1‖ ^ level D z.1 * ‖q2‖ ^ level D z.2 * rowWeight D L K1 z.1 *
          (mixedConstant D a b A T ω * mixedEnergy D z.1 z.2 ^ mixedRadius D ω *
            mixedEnvelope D A T z.1 z.2) * columnWeight D B K2 z.2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb hw) (hcol z.2)

end
end D5.S3.VertexAlgebra.CanonicalTwoCutOccupation
