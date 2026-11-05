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

/-! Uniform control of both occupations for the literal canonical word recurrence.
The finite positive overlap retains the shared occupation and exact factorials. -/

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
  · rw [ite_eq_left hx]
    simp only [add_zero]
    unfold chooseKernel
    apply Finsupp.prod_congr
    intro y hy
    have hxy : x ≠ y := by
      intro heq
      subst y
      exact Finsupp.mem_support_iff.mp hy hx
    simp [Finsupp.single_apply, hxy]
  · rw [ite_eq_right hx]
    let S := insert x u.support
    have hs : u.support ⊆ S := Finset.subset_insert _ _
    have hs' : (u - Finsupp.single x 1).support ⊆ S := by
      intro y hy
      apply hs
      simp only [Finsupp.mem_support_iff, Finsupp.tsub_apply] at hy ⊢
      omega
    rw [chooseKernel_eq_prod D (e + Finsupp.single x 1) u S hs,
      chooseKernel_eq_prod D e u S hs,
      chooseKernel_eq_prod D e (u - Finsupp.single x 1) S hs']
    have hxS : x ∈ S := Finset.mem_insert_self _ _
    rw [← Finset.mul_prod_erase _ _ hxS, ← Finset.mul_prod_erase _ _ hxS,
      ← Finset.mul_prod_erase _ _ hxS]
    have hp : (∏ y ∈ S.erase x,
        ((e + Finsupp.single x 1 : Occ D) y).choose (u y) : ℝ) =
        ∏ y ∈ S.erase x, ((e y).choose (u y) : ℝ) := by
      apply Finset.prod_congr rfl
      intro y hy
      have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
      simp [Finsupp.single_apply, hxy]
    have hp' : (∏ y ∈ S.erase x,
        ((e y).choose ((u - Finsupp.single x 1 : Occ D) y) : ℝ)) =
        ∏ y ∈ S.erase x, ((e y).choose (u y) : ℝ) := by
      apply Finset.prod_congr rfl
      intro y hy
      have hxy : x ≠ y := (Finset.mem_erase.mp hy).1.symm
      simp [Finsupp.single_apply, hxy]
    rw [hp, hp']
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.tsub_apply]
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
        simp only [Finsupp.add_apply, Finsupp.tsub_apply]
        omega
      rw [heq, map_add, Finsupp.degree_single]
    by_cases hx : u x = 0
    · have hu : u ≤ e := by
        intro y
        have hh := hle y
        by_cases hy : x = y
        · subst y; simp [hx]
        · simpa [Finsupp.single_apply, hy] using hh
      simp only [translationEnvelope, chooseKernel_add_single, hx, ite_eq_left,
        add_zero, hdeg hu, pow_succ]
      ring
    · have hsub : e - (u - Finsupp.single x 1) = e + Finsupp.single x 1 - u := by
        ext y
        have hh := hle y
        simp only [Finsupp.add_apply, Finsupp.tsub_apply]
        by_cases hy : x = y
        · subst y; simp only [Finsupp.single_eq_same] at hh ⊢; omega
        · simp [Finsupp.single_apply, hy]
      simp only [translationEnvelope, chooseKernel_add_single, hx, ite_false, hsub]
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
        exact add_le_add hh le_rfl
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

private theorem occupation_shift_sum (D : LatticeData) (d : Occ D) (x : Index D)
    (f : Occ D → Occ D → ℝ) :
    (∑ u ∈ Finset.Iic d, if u x = 0 then 0 else
      f (u - Finsupp.single x 1) (d - u)) =
      if d x = 0 then 0 else ∑ v ∈ Finset.Iic (d - Finsupp.single x 1),
        f v (d - Finsupp.single x 1 - v) := by
  classical
  by_cases hx : d x = 0
  · rw [ite_eq_left hx]
    apply Finset.sum_eq_zero
    intro u hu
    have hh := (Finset.mem_Iic.mp hu) x
    have hz : u x = 0 := by omega
    simp [hz]
  · rw [ite_eq_right hx]
    rw [show (∑ u ∈ Finset.Iic d, if u x = 0 then 0 else
        f (u - Finsupp.single x 1) (d - u)) =
        ∑ u ∈ (Finset.Iic d).filter (fun u => u x ≠ 0),
          f (u - Finsupp.single x 1) (d - u) by
      rw [Finset.sum_filter]; apply Finset.sum_congr rfl
      intro u hu; by_cases hh : u x = 0 <;> simp [hh]
      ]
    apply Finset.sum_bij (fun u _ => u - Finsupp.single x 1)
    · intro u hu
      exact Finset.mem_Iic.mpr (tsub_le_tsub_right (Finset.mem_Iic.mp
        (Finset.mem_filter.mp hu).1) _)
    · intro u hu v hv huv
      have hux := (Finset.mem_filter.mp hu).2
      have hvx := (Finset.mem_filter.mp hv).2
      exact (Finsupp.sub_add_single_one_cancel hux).symm.trans
        ((congrArg (fun z : Occ D => z + Finsupp.single x 1) huv).trans
          (Finsupp.sub_add_single_one_cancel hvx))
    · intro v hv
      refine ⟨v + Finsupp.single x 1, ?_, by simp⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Iic.mpr
        have hh := add_le_add (Finset.mem_Iic.mp hv) (le_refl (Finsupp.single x 1))
        simpa only [Finsupp.sub_add_single_one_cancel hx] using hh
      · simp
    · intro u hu
      congr 1
      have hux := (Finset.mem_filter.mp hu).2
      ext y
      simp only [Finsupp.tsub_apply]
      by_cases hy : x = y
      · subst y
        simp only [Finsupp.single_eq_same]
        have hud := (Finset.mem_Iic.mp (Finset.mem_filter.mp hu).1) x
        omega
      · simp [Finsupp.single_apply, hy]

private theorem mixedEnvelope_add_single (D : LatticeData) (A T : ℝ)
    (d e : Occ D) (x : Index D) :
    mixedEnvelope D A T d (e + Finsupp.single x 1) =
      T * mixedEnvelope D A T d e +
        if d x = 0 then 0 else mixedEnvelope D A T (d - Finsupp.single x 1) e := by
  classical
  simp only [mixedEnvelope_eq_sum, translationEnvelope_add_single, add_mul,
    Finset.sum_add_distrib]
  rw [show (∑ u ∈ Finset.Iic d,
      (if u x = 0 then 0 else translationEnvelope D T e (u - Finsupp.single x 1)) *
        factorialEnvelope D A (d - u)) =
      ∑ u ∈ Finset.Iic d, if u x = 0 then 0 else
        translationEnvelope D T e (u - Finsupp.single x 1) *
          factorialEnvelope D A (d - u) by
    apply Finset.sum_congr rfl
    intro u hu; split_ifs <;> simp]
  rw [occupation_shift_sum D d x
    (fun v w => translationEnvelope D T e v * factorialEnvelope D A w)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

private theorem mixedEnvelope_zero_input (D : LatticeData) (A T : ℝ) (d : Occ D) :
    mixedEnvelope D A T d 0 = factorialEnvelope D A d := by
  classical
  unfold mixedEnvelope
  have hs : (Finset.Iic d).filter (fun u : Occ D => u ≤ 0) = {0} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Iic, le_zero_iff, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ (fun _ => Nat.zero_le _), h⟩⟩
  rw [hs]
  simp [overlapBinomial]

private theorem ground_mixed_bound (D : LatticeData) (a b : Charge D)
    (A T : ℝ) (hA : 1 ≤ A) (hT : 1 ≤ T)
    (ha : ∀ i, ‖(a i : ℂ)‖ ≤ A)
    (ht : ∀ i, ‖(bilinear D a (unitCharge D i) : ℂ)‖ ≤ T)
    (m : ℤ) (d e : Occ D) :
    ‖wordCoeff D a b [] m d e‖ ≤ mixedEnvelope D A T d e := by
  classical
  have hA0 : 0 ≤ A := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hzero (d : Occ D) (m : ℤ) :
      ‖wordCoeff D a b [] m d 0‖ ≤ factorialEnvelope D A d := by
    have hc : LatticeActualProductKernel.convolution D a (-m - 1 - bilinear D a b) 1 =
        creationCoeff D a (-m - 1 - bilinear D a b) := by
      simpa using LatticeActualProductKernel.convolution_monomial D a
        (-m - 1 - bilinear D a b) 0 (1 : Oscillator D)
    have hp : ‖epsilon D a b‖ = 1 := by
      unfold epsilon paritySign
      split_ifs <;> norm_num
    have hh : wordCoeff D a b [] m d 0 = epsilon D a b *
        (creationCoeff D a (-m - 1 - bilinear D a b)).coeff d := by
      simp [wordCoeff, CanonicalOccupationSewing.b, wordMap_nil, translatedPolynomial, hc]
    rw [hh, norm_mul, hp, one_mul]
    exact creation_factorialEnvelope D a A hA0 ha _ d
  have haux : ∀ n : ℕ, ∀ e : Occ D, e.degree = n → ∀ (d : Occ D) (m : ℤ),
      ‖wordCoeff D a b [] m d e‖ ≤ mixedEnvelope D A T d e := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro e he d m
      by_cases hz : e = 0
      · subst e
        simpa only [mixedEnvelope_zero_input] using hzero d m
      · obtain ⟨x, hx⟩ : ∃ x : Index D, e x ≠ 0 := by
          by_contra hh
          push Not at hh
          exact hz (Finsupp.ext hh)
        let e' := e - Finsupp.single x 1
        have hadd : e' + Finsupp.single x 1 = e := Finsupp.sub_add_single_one_cancel hx
        have hdeg : e'.degree + 1 = e.degree := by
          rw [← hadd, map_add, Finsupp.degree_single]
        have hi (d' : Occ D) (m' : ℤ) := ih e'.degree (by omega) e' rfl d' m'
        rw [← hadd, wordCoeff_nil_add_single, mixedEnvelope_add_single]
        have hleft : ‖if x ∈ d.support then
            wordCoeff D a b [] m (d - Finsupp.single x 1) e' else 0‖ ≤
            if d x = 0 then 0 else mixedEnvelope D A T (d - Finsupp.single x 1) e' := by
          by_cases hd : d x = 0
          · simp [hd]
          · simpa [hd] using hi (d - Finsupp.single x 1) m
        calc
          _ ≤ ‖if x ∈ d.support then
                wordCoeff D a b [] m (d - Finsupp.single x 1) e' else 0‖ +
              ‖(bilinear D a (unitCharge D x.1) : ℂ) *
                wordCoeff D a b [] (m - (x.2 + 1 : ℕ)) d e'‖ := norm_sub_le _ _
          _ ≤ (if d x = 0 then 0 else mixedEnvelope D A T (d - Finsupp.single x 1) e') +
              T * mixedEnvelope D A T d e' := by
            rw [norm_mul]
            exact add_le_add hleft (mul_le_mul (ht x.1) (hi d _)
              (norm_nonneg _) hT0)
          _ = _ := add_comm _ _
  exact haux e.degree e rfl d m

private theorem mixedEnvelope_input_removal (D : LatticeData) (A T : ℝ)
    (hA : 0 ≤ A) (hT : 0 < T) (d e : Occ D) (x : Index D) (hx : e x ≠ 0) :
    mixedEnvelope D A T d (e - Finsupp.single x 1) ≤ mixedEnvelope D A T d e / T := by
  have hh := mixedEnvelope_add_single D A T d (e - Finsupp.single x 1) x
  rw [Finsupp.sub_add_single_one_cancel hx] at hh
  have hn : 0 ≤ if d x = 0 then 0 else
      mixedEnvelope D A T (d - Finsupp.single x 1) (e - Finsupp.single x 1) := by
    split_ifs
    · exact le_rfl
    · exact mixedEnvelope_nonneg D A T hA hT.le _ _
  apply (le_div_iff₀ hT).mpr
  nlinarith

private theorem translationEnvelope_nonneg (D : LatticeData) (T : ℝ) (hT : 0 ≤ T)
    (e u : Occ D) : 0 ≤ translationEnvelope D T e u := by
  unfold translationEnvelope chooseKernel Finsupp.prod
  positivity

private theorem mixedEnvelope_output_removal (D : LatticeData) (A T : ℝ)
    (hA : 0 < A) (hT : 0 ≤ T) (d e : Occ D) (x : Index D) (hx : d x ≠ 0) :
    mixedEnvelope D A T (d - Finsupp.single x 1) e ≤
      (x.2 + 1 : ℝ) * (d x : ℝ) * mixedEnvelope D A T d e / A := by
  classical
  have hn : (x.2 + 1 : ℝ) ≠ 0 := by positivity
  have hF (u : Occ D) (hu : u ≤ d - Finsupp.single x 1) :
      A * factorialEnvelope D A (d - Finsupp.single x 1 - u) ≤
        (x.2 + 1 : ℝ) * (d x : ℝ) * factorialEnvelope D A (d - u) := by
    let v := d - Finsupp.single x 1 - u
    have hv : v + Finsupp.single x 1 = d - u := by
      ext y
      have hh := hu y
      simp only [Finsupp.tsub_apply] at hh
      dsimp only [v]
      simp only [Finsupp.add_apply, Finsupp.tsub_apply]
      by_cases hy : x = y
      · subst y; simp only [Finsupp.single_eq_same] at hh ⊢; omega
      · simp [Finsupp.single_apply, hy]
    have hvx : (v x + 1 : ℝ) ≤ (d x : ℝ) := by
      have hh := hu x
      dsimp only [v]
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hh ⊢
      exact_mod_cast (show d x - 1 - u x + 1 ≤ d x by omega)
    have hrec := factorialEnvelope_add_single D A v x
    rw [hv] at hrec
    have heq : A * factorialEnvelope D A v =
        (x.2 + 1 : ℝ) * (v x + 1 : ℝ) * factorialEnvelope D A (d - u) := by
      field_simp at hrec
      nlinarith
    rw [heq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvx (by positivity))
      (factorialEnvelope_nonneg D A hA.le _)
  have hsub : Finset.Iic (d - Finsupp.single x 1) ⊆ Finset.Iic d := by
    intro u hu
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hu).trans tsub_le_self)
  apply (le_div_iff₀ hA).mpr
  rw [mixedEnvelope_eq_sum, mixedEnvelope_eq_sum]
  calc
    _ = ∑ u ∈ Finset.Iic (d - Finsupp.single x 1),
        translationEnvelope D T e u *
          (A * factorialEnvelope D A (d - Finsupp.single x 1 - u)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u hu; ring
    _ ≤ ∑ u ∈ Finset.Iic (d - Finsupp.single x 1),
        translationEnvelope D T e u *
          ((x.2 + 1 : ℝ) * (d x : ℝ) * factorialEnvelope D A (d - u)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (hF u (Finset.mem_Iic.mp hu))
        (translationEnvelope_nonneg D T hT _ _)
    _ ≤ ∑ u ∈ Finset.Iic d, translationEnvelope D T e u *
        ((x.2 + 1 : ℝ) * (d x : ℝ) * factorialEnvelope D A (d - u)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro u hu hnot
      exact mul_nonneg (translationEnvelope_nonneg D T hT _ _) (by
        exact mul_nonneg (by positivity) (factorialEnvelope_nonneg D A hA.le _))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu; ring

private theorem occupation_partial_moment (D : LatticeData) (d : Occ D)
    (S : Finset (Index D)) :
    (∑ x ∈ S, (x.2 + 1 : ℝ) * (d x : ℝ)) ≤ (level D d : ℝ) := by
  classical
  have heq : (∑ x ∈ S, (x.2 + 1 : ℝ) * (d x : ℝ)) =
      ∑ x ∈ S ∩ d.support, (x.2 + 1 : ℝ) * (d x : ℝ) := by
    apply (Finset.sum_subset Finset.inter_subset_left _).symm
    intro x hx hn
    have hz : d x = 0 := by
      by_contra hh
      exact hn (Finset.mem_inter.mpr ⟨hx, Finsupp.mem_support_iff.mpr hh⟩)
    simp [hz]
  rw [heq]
  calc
    _ ≤ ∑ x ∈ d.support, (x.2 + 1 : ℝ) * (d x : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (by intros; positivity)
    _ = _ := by
      simp [level, LatticePositiveEnergy.oscillatorEnergy, Finsupp.weight_apply,
        Finsupp.sum, Nat.cast_sum, Nat.cast_mul, mul_comm]

private theorem occupation_negative_moment (D : LatticeData) (d : Occ D)
    (i : Fin D.rank) (k n : ℕ) :
    (∑ j ∈ Finset.range n, (j + k + 1 : ℝ) * (d (i,j+k) : ℝ)) ≤ (level D d : ℝ) := by
  classical
  have hi : Set.InjOn (fun j : ℕ => (i,j+k)) (Finset.range n) := by
    intro j hj l hl h
    have hh := congrArg Prod.snd h
    dsimp only at hh
    omega
  have hh := occupation_partial_moment D d ((Finset.range n).image (fun j => (i,j+k)))
  rw [Finset.sum_image hi] at hh
  simpa [Nat.cast_add, Nat.cast_one] using hh

private theorem occupation_positive_moment (D : LatticeData) (e : Occ D)
    (i : Fin D.rank) (k n : ℕ) :
    (∑ j ∈ (Finset.range n).filter (fun j => k < j),
      ((j : ℝ) - k) * (e (i,j-k-1) : ℝ)) ≤ (level D e : ℝ) := by
  classical
  have hi : Set.InjOn (fun j : ℕ => (i,j-k-1))
      ((Finset.range n).filter (fun j => k < j)) := by
    intro j hj l hl h
    have hjk := (Finset.mem_filter.mp hj).2
    have hlk := (Finset.mem_filter.mp hl).2
    have hh := congrArg Prod.snd h
    dsimp only at hh
    omega
  have hh := occupation_partial_moment D e
    (((Finset.range n).filter (fun j => k < j)).image (fun j => (i,j-k-1)))
  rw [Finset.sum_image hi] at hh
  apply le_trans (le_of_eq _) hh
  apply Finset.sum_congr rfl
  intro j hj
  have hjk := (Finset.mem_filter.mp hj).2
  congr 1
  rw [← Nat.cast_sub (show k ≤ j by omega)]
  exact_mod_cast (show j - k = j - k - 1 + 1 by omega)

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

private theorem occupation_colored_moment (D : LatticeData) (e : Occ D)
    (i : Fin D.rank) (k n : ℕ) :
    (∑ j ∈ (Finset.range n).filter (fun j => k < j),
      ((j : ℝ) - k) * ∑ a : Fin D.rank,
        ‖(D.G i a : ℂ)‖ * (e (a,j-k-1) : ℝ)) ≤
      (∑ a : Fin D.rank, ‖(D.G i a : ℂ)‖) * (level D e : ℝ) := by
  classical
  calc
    _ = ∑ a : Fin D.rank, ‖(D.G i a : ℂ)‖ *
        ∑ j ∈ (Finset.range n).filter (fun j => k < j),
          ((j : ℝ) - k) * (e (a,j-k-1) : ℝ) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ ∑ a : Fin D.rank, ‖(D.G i a : ℂ)‖ * (level D e : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (occupation_positive_moment D e a k n) (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

private theorem mixed_descendant_bound (D : LatticeData) (a b : Charge D)
    (A T : ℝ) (hA : 1 ≤ A) (hT : 1 ≤ T)
    (ha : ∀ i, ‖(a i : ℂ)‖ ≤ A)
    (ht : ∀ i, ‖(bilinear D a (unitCharge D i) : ℂ)‖ ≤ T)
    (ω : List (Index D)) (m : ℤ) (d e : Occ D) :
    ‖wordCoeff D a b ω m d e‖ ≤
      mixedConstant D a b A T ω * mixedEnergy D d e ^ mixedRadius D ω *
        mixedEnvelope D A T d e := by
  classical
  have hA0 : 0 < A := by linarith
  have hT0 : 0 < T := by linarith
  induction ω generalizing m d e with
  | nil => simpa [mixedConstant, mixedRadius] using ground_mixed_bound D a b A T hA hT ha ht m d e
  | cons x ω ih =>
    let C := mixedConstant D a b A T ω
    let R := mixedRadius D ω
    let N := mixedEnergy D d e
    let M := mixedEnvelope D A T d e
    let V := C * N ^ R * M
    let P : ℝ := (x.2 + 1 : ℝ) ^ x.2
    let Z : ℝ := ‖(bilinear D (unitCharge D x.1) b : ℂ)‖
    let G : ℝ := ∑ a : Fin D.rank, ‖(D.G x.1 a : ℂ)‖
    have hC : 0 ≤ C := mixedConstant_nonneg D a b ω A T hA hT
    have hN : 1 ≤ N := by
      dsimp [N, mixedEnergy]
      have hd0 := Nat.cast_nonneg (α := ℝ) (level D d)
      have he0 := Nat.cast_nonneg (α := ℝ) (level D e)
      linarith
    have hM : 0 ≤ M := mixedEnvelope_nonneg D A T hA0.le hT0.le d e
    have hV : 0 ≤ V := by dsimp [V]; positivity
    have hP : 0 ≤ P := by dsimp [P]; positivity
    have hG : 0 ≤ G := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hde : (level D d : ℝ) ≤ N := by
      dsimp [N, mixedEnergy]
      have he0 := Nat.cast_nonneg (α := ℝ) (level D e)
      linarith
    have hee : (level D e : ℝ) ≤ N := by
      dsimp [N, mixedEnergy]
      have hd0 := Nat.cast_nonneg (α := ℝ) (level D d)
      linarith
    have htail (m' : ℤ) : ‖wordCoeff D a b ω m' d e‖ ≤ V := ih m' d e
    have hout (y : Index D) (hy : d y ≠ 0) (m' : ℤ) :
        ‖wordCoeff D a b ω m' (d - Finsupp.single y 1) e‖ ≤
          V * ((y.2 + 1 : ℝ) * (d y : ℝ) / A) := by
      have henergy : mixedEnergy D (d - Finsupp.single y 1) e ≤ N := by
        dsimp [mixedEnergy, N]
        have hh : (level D (d-Finsupp.single y 1) : ℝ) ≤ level D d :=
          Nat.cast_le.mpr (occupation_sub_bounds D d y).1
        linarith
      calc
        _ ≤ C * N ^ R * mixedEnvelope D A T (d - Finsupp.single y 1) e := by
          apply (ih m' _ e).trans
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by dsimp [mixedEnergy]; positivity) henergy R) hC)
            (mixedEnvelope_nonneg D A T hA0.le hT0.le _ _)
        _ ≤ C * N ^ R * ((y.2 + 1 : ℝ) * (d y : ℝ) * M / A) :=
          mul_le_mul_of_nonneg_left
            (mixedEnvelope_output_removal D A T hA0 hT0.le d e y hy) (by positivity)
        _ = _ := by dsimp [V]; ring
    have hin (y : Index D) (hy : e y ≠ 0) (m' : ℤ) :
        ‖wordCoeff D a b ω m' d (e - Finsupp.single y 1)‖ ≤ V / T := by
      have henergy : mixedEnergy D d (e - Finsupp.single y 1) ≤ N := by
        dsimp [mixedEnergy, N]
        have hh : (level D (e-Finsupp.single y 1) : ℝ) ≤ level D e :=
          Nat.cast_le.mpr (occupation_sub_bounds D e y).1
        linarith
      calc
        _ ≤ C * N ^ R * mixedEnvelope D A T d (e - Finsupp.single y 1) := by
          apply (ih m' d _).trans
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by dsimp [mixedEnergy]; positivity) henergy R) hC)
            (mixedEnvelope_nonneg D A T hA0.le hT0.le _ _)
        _ ≤ C * N ^ R * (M / T) := mul_le_mul_of_nonneg_left
          (mixedEnvelope_input_removal D A T hA0.le hT0 d e y hy) (by positivity)
        _ = _ := by dsimp [V]; ring
    have hnegpoint (j : ℕ) (hj : j ∈ Finset.range (level D d)) :
        ‖((j + x.2).choose x.2 : ℂ) *
          if (x.1,j+x.2) ∈ d.support then
            wordCoeff D a b ω (m+j) (d - Finsupp.single (x.1,j+x.2) 1) e else 0‖ ≤
          (V * N ^ x.2 / A) * ((j+x.2+1 : ℝ) * (d (x.1,j+x.2) : ℝ)) := by
      have hchoose : ((j + x.2).choose x.2 : ℝ) ≤ N ^ x.2 := by
        calc
          _ ≤ (j+1 : ℝ) ^ x.2 := by exact_mod_cast Nat.choose_add_le_add_one_pow j x.2
          _ ≤ N ^ x.2 := pow_le_pow_left₀ (by positivity) (by
            have hh : j+1 ≤ level D d := by simpa using Finset.mem_range.mp hj
            exact (by exact_mod_cast hh : (j+1 : ℝ) ≤ (level D d : ℝ)).trans hde) _
      rw [norm_mul, Complex.norm_natCast]
      split_ifs with hd
      · have hb := hout (x.1,j+x.2) (Finsupp.mem_support_iff.mp hd) (m+j)
        have hb' := hb
        simp only [Nat.cast_add, Nat.cast_one] at hb'
        calc
          _ ≤ N ^ x.2 * (V * ((j+x.2+1 : ℝ) * (d (x.1,j+x.2) : ℝ) / A)) :=
            mul_le_mul hchoose hb' (norm_nonneg _) (by positivity)
          _ = _ := by push_cast; ring
      · have hz := Finsupp.notMem_support_iff.mp hd
        simp [hz]
    have hneg : ‖∑ j ∈ Finset.range (level D d),
        ((j+x.2).choose x.2 : ℂ) *
          if (x.1,j+x.2) ∈ d.support then
            wordCoeff D a b ω (m+j) (d-Finsupp.single (x.1,j+x.2) 1) e else 0‖ ≤
        V * N ^ (x.2+1) / A := by
      calc
        _ ≤ ∑ j ∈ Finset.range (level D d),
            (V*N^x.2/A) * ((j+x.2+1 : ℝ) * (d (x.1,j+x.2) : ℝ)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hnegpoint)
        _ = (V*N^x.2/A) * ∑ j ∈ Finset.range (level D d),
            (j+x.2+1 : ℝ) * (d (x.1,j+x.2) : ℝ) := (Finset.mul_sum ..).symm
        _ ≤ (V*N^x.2/A) * N := mul_le_mul_of_nonneg_left
          ((occupation_negative_moment D d x.1 x.2 _).trans hde) (by positivity)
        _ = _ := by rw [pow_succ]; ring
    have hchoose (j : ℕ) (hj : j ∈ Finset.range (x.2 + level D e + 1)) :
        (j.choose x.2 : ℝ) ≤ P * N ^ x.2 := by
      have hjN : (j : ℝ) ≤ (x.2 + 1 : ℝ) * N := by
        have hh : (j : ℝ) ≤ x.2 + (level D e : ℝ) := by
          exact_mod_cast (show j ≤ x.2 + level D e by simpa using Finset.mem_range.mp hj)
        nlinarith [Nat.cast_nonneg (α := ℝ) x.2]
      calc
        _ ≤ (j : ℝ) ^ x.2 := by exact_mod_cast Nat.choose_le_pow j x.2
        _ ≤ ((x.2+1 : ℝ)*N)^x.2 := pow_le_pow_left₀ (by positivity) hjN _
        _ = _ := mul_pow _ _ _
    let pos := fun j : ℕ => (-1 : ℂ)^x.2 * (j.choose x.2 : ℂ) *
      (if j < x.2 then 0 else if j = x.2 then
        (bilinear D (unitCharge D x.1) b : ℂ) * wordCoeff D a b ω (m-j-1) d e
      else ((j : ℤ)-x.2 : ℂ) * ∑ a' : Fin D.rank,
        (D.G x.1 a' : ℂ) * (e (a',j-x.2-1) : ℂ) *
          wordCoeff D a b ω (m-j-1) d (e-Finsupp.single (a',j-x.2-1) 1))
    have hpospoint (j : ℕ) (hj : j ∈ Finset.range (x.2 + level D e + 1)) :
        ‖pos j‖ ≤ (if j = x.2 then Z*V else 0) +
          (P*N^x.2*V/T) * (if x.2 < j then
            ((j : ℝ)-x.2) * ∑ a' : Fin D.rank,
              ‖(D.G x.1 a' : ℂ)‖ * (e (a',j-x.2-1) : ℝ) else 0) := by
      dsimp only [pos]
      by_cases hjlt : j < x.2
      · simp [hjlt, show j ≠ x.2 by omega, show ¬ x.2 < j by omega]
      · by_cases hjeq : j = x.2
        · subst j
          simpa [Z, norm_mul, Complex.norm_natCast] using
            mul_le_mul_of_nonneg_left (htail (m-x.2-1)) (norm_nonneg
              (bilinear D (unitCharge D x.1) b : ℂ))
        · have hjgt : x.2 < j := by omega
          simp only [hjlt, hjeq, hjgt, ite_false, ite_true, zero_add,
            norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
            Complex.norm_natCast]
          have hnorm : ‖((j : ℤ)-x.2 : ℂ)‖ = (j : ℝ)-x.2 := by
            simp only [Int.cast_natCast]
            rw [← Nat.cast_sub (show x.2 ≤ j by omega), Complex.norm_natCast,
              Nat.cast_sub (show x.2 ≤ j by omega)]
          rw [hnorm]
          have hinner : ‖∑ a' : Fin D.rank,
              (D.G x.1 a' : ℂ) * (e (a',j-x.2-1) : ℂ) *
                wordCoeff D a b ω (m-j-1) d (e-Finsupp.single (a',j-x.2-1) 1)‖ ≤
              (∑ a' : Fin D.rank, ‖(D.G x.1 a' : ℂ)‖ *
                (e (a',j-x.2-1) : ℝ)) * (V/T) := by
            apply (norm_sum_le _ _).trans
            rw [Finset.sum_mul]
            apply Finset.sum_le_sum
            intro a' ha'
            rw [norm_mul, norm_mul, Complex.norm_natCast]
            by_cases hz : e (a',j-x.2-1) = 0
            · simp [hz]
            · exact mul_le_mul_of_nonneg_left (hin _ hz _) (by positivity)
          calc
            _ ≤ (P*N^x.2) * (((j : ℝ)-x.2) *
                ((∑ a' : Fin D.rank, ‖(D.G x.1 a' : ℂ)‖ * (e (a',j-x.2-1) : ℝ)) * (V/T))) :=
              mul_le_mul (hchoose j hj)
                (mul_le_mul_of_nonneg_left hinner (sub_nonneg.mpr (Nat.cast_le.mpr (Nat.le_of_lt hjgt))))
                (mul_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr (Nat.le_of_lt hjgt)))
                  (norm_nonneg _)) (by positivity)
            _ = _ := by ring
    have hpos : ‖∑ j ∈ Finset.range (x.2 + level D e + 1), pos j‖ ≤
        Z*V + P*G*V*N^(x.2+1)/T := by
      calc
        _ ≤ ∑ j ∈ Finset.range (x.2 + level D e + 1),
            ((if j = x.2 then Z*V else 0) + (P*N^x.2*V/T) *
              (if x.2 < j then ((j : ℝ)-x.2) * ∑ a' : Fin D.rank,
                ‖(D.G x.1 a' : ℂ)‖ * (e (a',j-x.2-1) : ℝ) else 0)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum hpospoint)
        _ = Z*V + (P*N^x.2*V/T) *
            ∑ j ∈ (Finset.range (x.2 + level D e + 1)).filter (fun j => x.2 < j),
              ((j : ℝ)-x.2) * ∑ a' : Fin D.rank,
                ‖(D.G x.1 a' : ℂ)‖ * (e (a',j-x.2-1) : ℝ) := by
          have hcharge : (∑ j ∈ Finset.range (x.2+level D e+1),
              if j = x.2 then Z*V else 0) = Z*V := by simp
          rw [Finset.sum_add_distrib, hcharge, ← Finset.mul_sum, Finset.sum_filter]
        _ ≤ Z*V + (P*N^x.2*V/T) * (G*N) := by
          gcongr
          exact (occupation_colored_moment D e x.1 x.2 _).trans
            (mul_le_mul_of_nonneg_left hee hG)
        _ = _ := by rw [pow_succ]; ring
    rw [wordCoeff_cons]
    calc
      _ ≤ V*N^(x.2+1)/A + (Z*V + P*G*V*N^(x.2+1)/T) :=
        (norm_add_le _ _).trans (add_le_add hneg hpos)
      _ ≤ V*N^(x.2+1)/A + (Z*(V*N^(x.2+1)) + P*G*V*N^(x.2+1)/T) := by
        gcongr
        exact le_mul_of_one_le_right hV (one_le_pow₀ hN)
      _ = _ := by
        dsimp [V, C, R, N, M, P, Z, G, mixedConstant, mixedRadius]
        rw [pow_add, pow_succ]
        push_cast
        ring

end
end D5.S3.VertexAlgebra.CanonicalTwoCutOccupation
