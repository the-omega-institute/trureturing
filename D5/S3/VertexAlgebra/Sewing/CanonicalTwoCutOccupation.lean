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
open private wordMap wordCoeff wordMap_nil wordCoeff_nil_add_single wordCoeff_cons
  occupation_sub_bounds rowWeight rowWeight_nonneg
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow
open private factorialEnvelope columnWeight columnWeight_nonneg
  canonical_coefficient_expansion canonical_basis_input_expansion
  inner_coefficient_expansion inner_basis_coordinate
  polynomial_factorialEnvelope_summable factorialEnvelope_summable
  polynomial_geometric_bound factorialEnvelope_nonneg creation_factorialEnvelope
  factorialEnvelope_add_single
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

private def chooseKernel (D : LatticeData) (e u : Occ D) : ℝ :=
  u.prod (fun x n => (Nat.choose (e x) n : ℝ))

private theorem chooseKernel_eq_prod (D : LatticeData) (e u : Occ D)
    (S : Finset (Index D)) (hS : u.support ⊆ S) :
    chooseKernel D e u = ∏ x ∈ S, (Nat.choose (e x) (u x) : ℝ) := by
  classical
  exact Finsupp.prod_of_support_subset u hS _ (by simp)

private theorem chooseKernel_eq (D : LatticeData) (e u : Occ D) (hu : u ≤ e) :
    chooseKernel D e u = overlapBinomial D e u := by
  classical
  have hs : u.support ⊆ e.support := by
    intro x hx
    simp only [Finsupp.mem_support_iff] at hx ⊢
    have hh := hu x
    omega
  rw [chooseKernel_eq_prod D e u e.support hs]
  rfl

private theorem chooseKernel_zero (D : LatticeData) (e u : Occ D) (hu : ¬ u ≤ e) :
    chooseKernel D e u = 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, e x < u x := by
    simpa only [Finsupp.le_def, not_forall, not_le] using hu
  unfold chooseKernel Finsupp.prod
  apply Finset.prod_eq_zero (i := x)
  · exact Finsupp.mem_support_iff.mpr (by omega)
  · simp [Nat.choose_eq_zero_of_lt hx]

private theorem chooseKernel_add_single (D : LatticeData) (e u : Occ D)
    (x : Index D) :
    chooseKernel D (e + Finsupp.single x 1) u = chooseKernel D e u +
      if u x = 0 then 0 else chooseKernel D e (u - Finsupp.single x 1) := by
  classical
  by_cases hx : u x = 0
  · rw [if_pos hx]
    simp only [add_zero]
    unfold chooseKernel
    apply Finsupp.prod_congr
    intro y hy
    have hxy : x ≠ y := by
      intro heq
      subst y
      exact Finsupp.mem_support_iff.mp hy hx
    simp [Finsupp.single_apply, hxy]
  · rw [if_neg hx]
    let S := insert x u.support
    have hs : u.support ⊆ S := Finset.subset_insert _ _
    have hs' : (u - Finsupp.single x 1).support ⊆ S := by
      intro y hy
      apply hs
      simp only [Finsupp.mem_support_iff, Finsupp.sub_apply] at hy ⊢
      omega
    rw [chooseKernel_eq_prod D (e + Finsupp.single x 1) u S hs,
      chooseKernel_eq_prod D e u S hs,
      chooseKernel_eq_prod D e (u - Finsupp.single x 1) S hs']
    have hxS : x ∈ S := Finset.mem_insert_self _ _
    rw [← Finset.mul_prod_erase _ _ hxS, ← Finset.mul_prod_erase _ _ hxS,
      ← Finset.mul_prod_erase _ _ hxS]
    have hp : (∏ y ∈ S.erase x,
        ((e + Finsupp.single x 1) y).choose (u y) : ℝ) =
        ∏ y ∈ S.erase x, ((e y).choose (u y) : ℝ) := by
      apply Finset.prod_congr rfl
      intro y hy
      have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
      simp [Finsupp.single_apply, hxy]
    have hp' : (∏ y ∈ S.erase x,
        ((e y).choose ((u - Finsupp.single x 1) y) : ℝ)) =
        ∏ y ∈ S.erase x, ((e y).choose (u y) : ℝ) := by
      apply Finset.prod_congr rfl
      intro y hy
      have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
      simp [Finsupp.single_apply, hxy]
    rw [hp, hp']
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.sub_apply]
    have hn : u x = (u x - 1) + 1 := by omega
    rw [hn, Nat.choose_succ_succ', Nat.cast_add]
    simp only [Nat.add_sub_cancel]
    ring

private def translationEnvelope (D : LatticeData) (T : ℝ) (e u : Occ D) : ℝ :=
  chooseKernel D e u * T ^ (e - u).degree

private theorem translationEnvelope_zero (D : LatticeData) (T : ℝ) (e u : Occ D)
    (hu : ¬ u ≤ e) : translationEnvelope D T e u = 0 := by
  simp [translationEnvelope, chooseKernel_zero D e u hu]

private theorem translationEnvelope_add_single (D : LatticeData) (T : ℝ)
    (e u : Occ D) (x : Index D) :
    translationEnvelope D T (e + Finsupp.single x 1) u =
      T * translationEnvelope D T e u +
        if u x = 0 then 0 else translationEnvelope D T e (u - Finsupp.single x 1) := by
  classical
  by_cases hle : u ≤ e + Finsupp.single x 1
  · have hdeg (hu : u ≤ e) :
        (e + Finsupp.single x 1 - u).degree = (e - u).degree + 1 := by
      have heq : e + Finsupp.single x 1 - u = e - u + Finsupp.single x 1 := by
        ext y
        have hh := hu y
        simp only [Finsupp.add_apply, Finsupp.sub_apply]
        omega
      rw [heq, map_add, Finsupp.degree_single]
    by_cases hx : u x = 0
    · have hu : u ≤ e := by
        intro y
        have hh := hle y
        by_cases hy : x = y
        · subst y; simp [hx]
        · simpa [Finsupp.single_apply, hy] using hh
      simp only [translationEnvelope, chooseKernel_add_single, hx, if_pos,
        add_zero, hdeg hu, pow_succ]
      ring
    · have hsub : e - (u - Finsupp.single x 1) = e + Finsupp.single x 1 - u := by
        ext y
        have hh := hle y
        simp only [Finsupp.add_apply, Finsupp.sub_apply]
        by_cases hy : x = y
        · subst y; simp only [Finsupp.single_eq_same] at hh ⊢; omega
        · simp [Finsupp.single_apply, hy]
      simp only [translationEnvelope, chooseKernel_add_single, hx, if_false, hsub]
      by_cases hu : u ≤ e
      · rw [hdeg hu, pow_succ]
        ring
      · rw [chooseKernel_zero D e u hu]
        ring
  · have hu : ¬ u ≤ e := fun h => hle (h.trans (by
      intro y; simp only [Finsupp.add_apply]; omega))
    rw [translationEnvelope_zero D T _ _ hle,
      translationEnvelope_zero D T _ _ hu]
    by_cases hx : u x = 0
    · simp [hx]
    · have hu' : ¬ u - Finsupp.single x 1 ≤ e := by
        intro hh
        apply hle
        rw [← Finsupp.sub_add_single_one_cancel hx]
        exact add_le_add_right hh _
      simp [hx, translationEnvelope_zero D T _ _ hu']

private theorem mixedEnvelope_eq_sum (D : LatticeData) (A T : ℝ) (d e : Occ D) :
    mixedEnvelope D A T d e = ∑ u ∈ Finset.Iic d,
      translationEnvelope D T e u * factorialEnvelope D A (d - u) := by
  classical
  unfold mixedEnvelope
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : u ≤ e
  · simp [h, translationEnvelope, chooseKernel_eq D e u h]
  · simp [h, translationEnvelope_zero D T e u h]

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
