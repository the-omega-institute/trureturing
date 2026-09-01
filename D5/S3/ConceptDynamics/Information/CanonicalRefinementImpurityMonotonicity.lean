/- GID: D5/S3/ConceptDynamics/Information/CanonicalRefinementImpurityMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Information/CanonicalRefinementImpurityMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical joint-fiber masses witness impurity monotonicity under refinement. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal
import D5.S3.ConceptDynamics.Information.ConditionalLogicalImpurity
import Mathlib.MeasureTheory.Integral.MeanInequalities

/- Library-search audit trail (2026-08-25):
   * Exact repository hits `Concept`, `Refines`, `conceptJoin`,
     `conceptFiberMass`, `pairDisagreementMass`, and
     `conditionalLogicalImpurity` are imported and used directly.
   * Body-shape search for `conceptFiberMass mu (conceptJoin` found no existing
     canonical joint-fiber monotonicity proof. The older sibling theorem uses
     private duplicate mass constructions and is therefore not imported.
   * Pinned Mathlib has no exact conditional logical-impurity theorem. The
     countable convexity step uses `ENNReal.lintegral_mul_le_Lp_mul_Lq`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Information.CanonicalRefinementImpurityMonotonicity

open MeasureTheory
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Information.ConditionalLogicalImpurity

noncomputable section

local instance {α : Type*} : DecidableEq α := Classical.decEq α

private theorem join_fiber_mass_le_concept_fiber_mass
    {X B A : Type*} (mu : PMF X) (concept : Concept X B)
    (target : Concept X A) (b : B) (a : A) :
    conceptFiberMass mu (conceptJoin concept target) (b, a) <=
      conceptFiberMass mu concept b := by
  classical
  rw [conceptFiberMass, conceptFiberMass]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hconcept : concept x = b
  · by_cases htarget : target x = a <;>
      simp [Set.indicator, conceptJoin, hconcept, htarget]
  · simp [Set.indicator, conceptJoin, hconcept]

private theorem concept_fiber_mass_ne_top
    {X B : Type*} (mu : PMF X) (concept : Concept X B) (b : B) :
    conceptFiberMass mu concept b ≠ ⊤ :=
  mu.tsum_coe_indicator_ne_top {x | concept x = b}

private theorem join_fiber_mass_eq_zero_of_concept_fiber_mass_eq_zero
    {X B A : Type*} (mu : PMF X) (concept : Concept X B)
    (target : Concept X A) (b : B)
    (hzero : conceptFiberMass mu concept b = 0) :
    forall a, conceptFiberMass mu (conceptJoin concept target) (b, a) = 0 := by
  intro a
  exact nonpos_iff_eq_zero.mp <|
    hzero ▸ join_fiber_mass_le_concept_fiber_mass mu concept target b a

private theorem join_fiber_mass_tsum
    {X B A : Type*} (mu : PMF X) (concept : Concept X B)
    (target : Concept X A) (b : B) :
    (∑' a, conceptFiberMass mu (conceptJoin concept target) (b, a)) =
      conceptFiberMass mu concept b := by
  classical
  simp only [conceptFiberMass, conceptJoin]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro x
  by_cases hconcept : concept x = b
  · rw [tsum_eq_single (target x)]
    · simp [Set.indicator, hconcept]
    · intro a hne
      simp [Set.indicator, hconcept, Ne.symm hne]
  · simp [Set.indicator, hconcept]

private theorem join_fiber_mass_sq_tsum
    {X B A : Type*} (mu : PMF X) (concept : Concept X B)
    (target : Concept X A) (b : B) :
    (∑' a, conceptFiberMass mu (conceptJoin concept target) (b, a) ^ 2) =
      ∑' x, ∑' y,
        if concept x = b ∧ concept y = b ∧ target x = target y then
          mu x * mu y
        else 0 := by
  classical
  simp only [conceptFiberMass, conceptJoin, Set.indicator, Set.mem_setOf_eq,
    Prod.mk.injEq]
  calc
    (∑' a,
        (∑' x, if concept x = b ∧ target x = a then mu x else 0) ^ 2) =
        ∑' a, ∑' x, ∑' y,
          if concept x = b ∧ target x = a ∧
              concept y = b ∧ target y = a then
            mu x * mu y
          else 0 := by
      apply tsum_congr
      intro a
      rw [pow_two, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro x
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro y
      by_cases hcx : concept x = b <;>
        by_cases hcy : concept y = b <;>
        by_cases htx : target x = a <;>
        by_cases hty : target y = a <;>
        simp [hcx, hcy, htx, hty]
    _ = ∑' x, ∑' y, ∑' a,
          if concept x = b ∧ target x = a ∧
              concept y = b ∧ target y = a then
            mu x * mu y
          else 0 := by
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro x
      rw [ENNReal.tsum_comm]
    _ = ∑' x, ∑' y,
          if concept x = b ∧ concept y = b ∧ target x = target y then
            mu x * mu y
          else 0 := by
      apply tsum_congr
      intro x
      apply tsum_congr
      intro y
      by_cases hcx : concept x = b
      · by_cases hcy : concept y = b
        · by_cases htarget : target x = target y
          · rw [tsum_eq_single (target x)]
            · simp [hcx, hcy, htarget]
            · intro a hne
              simp [hcx, hcy, Ne.symm hne]
          · simp only [hcx, hcy, htarget, true_and, and_false, if_false]
            rw [ENNReal.tsum_eq_zero]
            intro a
            by_cases hxa : target x = a
            · by_cases hya : target y = a
              · exact (htarget (hxa.trans hya.symm)).elim
              · simp [hxa, hya]
            · simp [hxa]
        · simp [hcy]
      · simp [hcx]

private theorem concept_fiber_mass_sq
    {X B : Type*} (mu : PMF X) (concept : Concept X B) (b : B) :
    conceptFiberMass mu concept b ^ 2 =
      ∑' x, ∑' y,
        if concept x = b ∧ concept y = b then mu x * mu y else 0 := by
  classical
  simp only [conceptFiberMass]
  rw [pow_two, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro x
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro y
  by_cases hcx : concept x = b <;>
    by_cases hcy : concept y = b <;>
    simp [Set.indicator, hcx, hcy]

private theorem pair_disagreement_add_join_fiber_squares
    {X B A : Type*} (mu : PMF X) (concept : Concept X B)
    (target : Concept X A) (b : B) :
    pairDisagreementMass mu concept target b +
        (∑' a,
          conceptFiberMass mu (conceptJoin concept target) (b, a) ^ 2) =
      conceptFiberMass mu concept b ^ 2 := by
  classical
  rw [pairDisagreementMass, join_fiber_mass_sq_tsum,
    concept_fiber_mass_sq, ← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  rw [← ENNReal.tsum_add]
  apply tsum_congr
  intro y
  by_cases hcx : concept x = b <;>
    by_cases hcy : concept y = b <;>
    by_cases htarget : target x = target y <;>
    simp [hcx, hcy, htarget]

private theorem join_fiber_squares_div
    {X B A : Type*} (mu : PMF X) (concept : Concept X B)
    (target : Concept X A) (b : B) :
    (∑' a,
        conceptFiberMass mu (conceptJoin concept target) (b, a) ^ 2 /
          conceptFiberMass mu concept b) =
      (∑' a,
          conceptFiberMass mu (conceptJoin concept target) (b, a) ^ 2) /
        conceptFiberMass mu concept b := by
  simp_rw [div_eq_mul_inv]
  exact ENNReal.tsum_mul_right

private theorem fiber_impurity_add_join_collision
    {X B A : Type*} (mu : PMF X) (concept : Concept X B)
    (target : Concept X A) (b : B) :
    pairDisagreementMass mu concept target b /
          conceptFiberMass mu concept b +
        (∑' a,
          conceptFiberMass mu (conceptJoin concept target) (b, a) ^ 2 /
            conceptFiberMass mu concept b) =
      conceptFiberMass mu concept b := by
  by_cases hzero : conceptFiberMass mu concept b = 0
  · have htargets :=
      join_fiber_mass_eq_zero_of_concept_fiber_mass_eq_zero
        mu concept target b hzero
    have hpairs : pairDisagreementMass mu concept target b = 0 := by
      have hpartition :=
        pair_disagreement_add_join_fiber_squares mu concept target b
      rw [hzero, zero_pow (by norm_num)] at hpartition
      exact nonpos_iff_eq_zero.mp <|
        calc
          pairDisagreementMass mu concept target b <=
              pairDisagreementMass mu concept target b +
                (∑' a,
                  conceptFiberMass mu (conceptJoin concept target) (b, a) ^ 2) :=
            self_le_add_right _ _
          _ = 0 := hpartition
    simp [hzero, hpairs, htargets]
  · rw [join_fiber_squares_div, ENNReal.div_add_div_same,
      pair_disagreement_add_join_fiber_squares, pow_two,
      ENNReal.mul_div_cancel_right hzero
        (concept_fiber_mass_ne_top mu concept b)]

private theorem concept_fiber_mass_tsum_all
    {X B : Type*} (mu : PMF X) (concept : Concept X B) :
    (∑' b, conceptFiberMass mu concept b) = 1 := by
  classical
  simp only [conceptFiberMass]
  rw [ENNReal.tsum_comm]
  calc
    (∑' x, ∑' b, {x | concept x = b}.indicator mu x) =
        ∑' x, mu x := by
      apply tsum_congr
      intro x
      rw [tsum_eq_single (concept x)]
      · simp [Set.indicator]
      · intro b hne
        simp [Set.indicator, Ne.symm hne]
    _ = 1 := mu.tsum_coe

private theorem impurity_add_join_collision
    {X B A : Type*} (mu : PMF X) (concept : Concept X B)
    (target : Concept X A) :
    conditionalLogicalImpurity mu concept target +
        (∑' b, ∑' a,
          conceptFiberMass mu (conceptJoin concept target) (b, a) ^ 2 /
            conceptFiberMass mu concept b) = 1 := by
  rw [conditionalLogicalImpurity, ← ENNReal.tsum_add]
  simp_rw [fiber_impurity_add_join_collision]
  exact concept_fiber_mass_tsum_all mu concept

private theorem join_fiber_mass_comp
    {X C D A : Type*} (mu : PMF X) (refined : Concept X D)
    (target : Concept X A) (factor : D -> C) (c : C) (a : A) :
    conceptFiberMass mu (conceptJoin (factor ∘ refined) target) (c, a) =
      ∑' d, if factor d = c then
        conceptFiberMass mu (conceptJoin refined target) (d, a)
      else 0 := by
  classical
  simp only [conceptFiberMass, conceptJoin]
  unfold Function.comp
  have hdistribute :
      (∑' d, if factor d = c then
          (∑' x, {x | (refined x, target x) = (d, a)}.indicator mu x)
        else 0) =
        ∑' d, ∑' x,
          if factor d = c then
            {x | (refined x, target x) = (d, a)}.indicator mu x
          else 0 := by
    apply tsum_congr
    intro d
    by_cases hfactor : factor d = c <;> simp [hfactor]
  rw [hdistribute, ENNReal.tsum_comm]
  apply tsum_congr
  intro x
  by_cases hcoarse : factor (refined x) = c
  · rw [tsum_eq_single (refined x)]
    · simp [Set.indicator, hcoarse]
    · intro d hne
      simp [Set.indicator, Ne.symm hne]
  · simp only [Set.indicator, Set.mem_setOf_eq, Prod.mk.injEq, hcoarse,
      false_and, if_false]
    symm
    rw [ENNReal.tsum_eq_zero]
    intro d
    by_cases hfactor : factor d = c
    · by_cases hreadout : refined x = d
      · exact (hcoarse (hreadout ▸ hfactor)).elim
      · simp [hfactor, hreadout]
    · simp [hfactor]

private theorem concept_fiber_mass_comp
    {X C D : Type*} (mu : PMF X) (refined : Concept X D)
    (factor : D -> C) (c : C) :
    conceptFiberMass mu (factor ∘ refined) c =
      ∑' d, if factor d = c then conceptFiberMass mu refined d else 0 := by
  classical
  simp only [conceptFiberMass]
  unfold Function.comp
  have hdistribute :
      (∑' d, if factor d = c then
          (∑' x, {x | refined x = d}.indicator mu x)
        else 0) =
        ∑' d, ∑' x,
          if factor d = c then {x | refined x = d}.indicator mu x else 0 := by
    apply tsum_congr
    intro d
    by_cases hfactor : factor d = c <;> simp [hfactor]
  rw [hdistribute, ENNReal.tsum_comm]
  apply tsum_congr
  intro x
  by_cases hcoarse : factor (refined x) = c
  · rw [tsum_eq_single (refined x)]
    · simp [Set.indicator, hcoarse]
    · intro d hne
      simp [Set.indicator, Ne.symm hne]
  · change (if factor (refined x) = c then mu x else 0) = _
    rw [if_neg hcoarse]
    symm
    rw [ENNReal.tsum_eq_zero]
    intro d
    by_cases hfactor : factor d = c
    · by_cases hreadout : refined x = d
      · exact (hcoarse (hreadout ▸ hfactor)).elim
      · simp [Set.indicator, hfactor, hreadout]
    · simp [hfactor]

private theorem tsum_sq_div_le_tsum_sq_div
    {I : Type*} (f g : I -> ENNReal)
    (f_zero : forall i, g i = 0 -> f i = 0)
    (g_ne_top : forall i, g i ≠ ⊤) :
    (∑' i, f i) ^ 2 / (∑' i, g i) <=
      ∑' i, f i ^ 2 / g i := by
  letI : MeasurableSpace I := ⊤
  let u : I -> ENNReal := fun i => f i / g i ^ (1 / 2 : Real)
  let v : I -> ENNReal := fun i => g i ^ (1 / 2 : Real)
  have hu : Measurable u := measurable_from_top
  have hv : Measurable v := measurable_from_top
  have huv : forall i, u i * v i = f i := by
    intro i
    by_cases hgi : g i = 0
    · simp [u, v, hgi, f_zero i hgi]
    · change (f i / g i ^ (1 / 2 : Real)) * g i ^ (1 / 2 : Real) = f i
      rw [ENNReal.div_mul_cancel]
      · simpa [ENNReal.rpow_eq_zero_iff_of_pos (by norm_num : (0 : Real) < 1 / 2)]
      · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (g_ne_top i)
  have hu_sq : forall i, u i ^ (2 : Real) = f i ^ 2 / g i := by
    intro i
    change (f i / g i ^ (1 / 2 : Real)) ^ (2 : Real) = f i ^ 2 / g i
    rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_two]
  have hv_sq : forall i, v i ^ (2 : Real) = g i := by
    intro i
    change (g i ^ (1 / 2 : Real)) ^ (2 : Real) = g i
    rw [← ENNReal.rpow_mul]
    norm_num
  have holder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (Measure.count : Measure I) Real.HolderConjugate.two_two
    hu.aemeasurable hv.aemeasurable
  rw [lintegral_count, lintegral_count, lintegral_count] at holder
  change (∑' i, u i * v i) <=
    (∑' i, u i ^ (2 : Real)) ^ (1 / 2 : Real) *
      (∑' i, v i ^ (2 : Real)) ^ (1 / 2 : Real) at holder
  simp_rw [huv, hu_sq, hv_sq] at holder
  have holder' :
      (∑' i, f i) <=
        (∑' i, f i ^ 2 / g i) ^ (2 : Real)⁻¹ *
          (∑' i, g i) ^ (2 : Real)⁻¹ := by
    simpa [one_div] using holder
  have holder_sq :
      (∑' i, f i) ^ 2 <=
        ((∑' i, f i ^ 2 / g i) ^ (2 : Real)⁻¹ *
          (∑' i, g i) ^ (2 : Real)⁻¹) ^ 2 := by
    gcongr
  have root_sq (x : ENNReal) : (x ^ (2 : Real)⁻¹) ^ 2 = x := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have product_bound :
      (∑' i, f i) ^ 2 <=
        (∑' i, f i ^ 2 / g i) * (∑' i, g i) := by
    calc
      (∑' i, f i) ^ 2 <=
          ((∑' i, f i ^ 2 / g i) ^ (2 : Real)⁻¹ *
            (∑' i, g i) ^ (2 : Real)⁻¹) ^ 2 := holder_sq
      _ = (∑' i, f i ^ 2 / g i) * (∑' i, g i) := by
        rw [mul_pow, root_sq, root_sq]
  exact ENNReal.div_le_of_le_mul (by simpa [mul_comm] using product_bound)

private theorem factor_collision_term_le
    {X C D A : Type*} (mu : PMF X) (refined : Concept X D)
    (target : Concept X A) (factor : D -> C) (c : C) (a : A) :
    (∑' d, if factor d = c then
        conceptFiberMass mu (conceptJoin refined target) (d, a)
      else 0) ^ 2 /
        (∑' d, if factor d = c then conceptFiberMass mu refined d else 0) <=
      ∑' d, if factor d = c then
        conceptFiberMass mu (conceptJoin refined target) (d, a) ^ 2 /
          conceptFiberMass mu refined d
      else 0 := by
  classical
  calc
    (∑' d, if factor d = c then
          conceptFiberMass mu (conceptJoin refined target) (d, a) else 0) ^ 2 /
        (∑' d, if factor d = c then conceptFiberMass mu refined d else 0) <=
        ∑' d,
          (if factor d = c then
              conceptFiberMass mu (conceptJoin refined target) (d, a) else 0) ^ 2 /
            (if factor d = c then conceptFiberMass mu refined d else 0) := by
      apply tsum_sq_div_le_tsum_sq_div
      · intro d hzero
        by_cases hfactor : factor d = c
        · simp only [hfactor, if_true] at hzero ⊢
          exact join_fiber_mass_eq_zero_of_concept_fiber_mass_eq_zero
            mu refined target d hzero a
        · simp [hfactor]
      · intro d
        by_cases hfactor : factor d = c
        · simpa [hfactor] using concept_fiber_mass_ne_top mu refined d
        · simp [hfactor]
    _ = ∑' d, if factor d = c then
          conceptFiberMass mu (conceptJoin refined target) (d, a) ^ 2 /
            conceptFiberMass mu refined d
        else 0 := by
      apply tsum_congr
      intro d
      by_cases hfactor : factor d = c <;> simp [hfactor]

private theorem join_collision_comp_le
    {X C D A : Type*} (mu : PMF X) (refined : Concept X D)
    (target : Concept X A) (factor : D -> C) :
    (∑' c, ∑' a,
        conceptFiberMass mu
            (conceptJoin (factor ∘ refined) target) (c, a) ^ 2 /
          conceptFiberMass mu (factor ∘ refined) c) <=
      ∑' d, ∑' a,
        conceptFiberMass mu (conceptJoin refined target) (d, a) ^ 2 /
          conceptFiberMass mu refined d := by
  classical
  simp_rw [join_fiber_mass_comp, concept_fiber_mass_comp]
  calc
    (∑' c, ∑' a,
        (∑' d, if factor d = c then
            conceptFiberMass mu (conceptJoin refined target) (d, a)
          else 0) ^ 2 /
          (∑' d, if factor d = c then conceptFiberMass mu refined d else 0)) <=
        ∑' c, ∑' a, ∑' d, if factor d = c then
          conceptFiberMass mu (conceptJoin refined target) (d, a) ^ 2 /
            conceptFiberMass mu refined d
        else 0 := by
      apply ENNReal.tsum_le_tsum
      intro c
      apply ENNReal.tsum_le_tsum
      intro a
      exact factor_collision_term_le mu refined target factor c a
    _ = ∑' a, ∑' c, ∑' d, if factor d = c then
          conceptFiberMass mu (conceptJoin refined target) (d, a) ^ 2 /
            conceptFiberMass mu refined d
        else 0 := ENNReal.tsum_comm
    _ = ∑' a, ∑' d,
          conceptFiberMass mu (conceptJoin refined target) (d, a) ^ 2 /
            conceptFiberMass mu refined d := by
      apply tsum_congr
      intro a
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro d
      rw [tsum_eq_single (factor d)]
      · simp
      · intro c hne
        simp [Ne.symm hne]
    _ = ∑' d, ∑' a,
          conceptFiberMass mu (conceptJoin refined target) (d, a) ^ 2 /
            conceptFiberMass mu refined d := ENNReal.tsum_comm

private theorem impurity_comp_le
    {X C D A : Type*} (mu : PMF X) (refined : Concept X D)
    (target : Concept X A) (factor : D -> C) :
    conditionalLogicalImpurity mu refined target <=
      conditionalLogicalImpurity mu (factor ∘ refined) target := by
  have hcollision := join_collision_comp_le mu refined target factor
  have hrefined := impurity_add_join_collision mu refined target
  have hcoarse := impurity_add_join_collision mu (factor ∘ refined) target
  have hcollision_ne_top :
      (∑' c, ∑' a,
        conceptFiberMass mu
            (conceptJoin (factor ∘ refined) target) (c, a) ^ 2 /
          conceptFiberMass mu (factor ∘ refined) c) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      (∑' c, ∑' a,
          conceptFiberMass mu
              (conceptJoin (factor ∘ refined) target) (c, a) ^ 2 /
            conceptFiberMass mu (factor ∘ refined) c) <=
          conditionalLogicalImpurity mu (factor ∘ refined) target +
            (∑' c, ∑' a,
              conceptFiberMass mu
                  (conceptJoin (factor ∘ refined) target) (c, a) ^ 2 /
                conceptFiberMass mu (factor ∘ refined) c) :=
        self_le_add_left _ _
      _ = 1 := hcoarse
  apply (ENNReal.add_le_add_iff_right hcollision_ne_top).mp
  calc
    conditionalLogicalImpurity mu refined target +
        (∑' c, ∑' a,
          conceptFiberMass mu
              (conceptJoin (factor ∘ refined) target) (c, a) ^ 2 /
            conceptFiberMass mu (factor ∘ refined) c) <=
      conditionalLogicalImpurity mu refined target +
        (∑' d, ∑' a,
          conceptFiberMass mu (conceptJoin refined target) (d, a) ^ 2 /
            conceptFiberMass mu refined d) := by
        exact add_le_add_right hcollision _
    _ = 1 := hrefined
    _ = conditionalLogicalImpurity mu (factor ∘ refined) target +
        (∑' c, ∑' a,
          conceptFiberMass mu
              (conceptJoin (factor ∘ refined) target) (c, a) ^ 2 /
            conceptFiberMass mu (factor ∘ refined) c) := hcoarse.symm

/-- Refining a concept readout cannot increase its target-relative conditional
logical impurity, with every target-conditioned mass represented by the
canonical fiber mass of the concept-target join. -/
theorem canonical_refinement_impurity_monotone
    {X C D A : Type*} (mu : PMF X) (coarse : Concept X C)
    (refined : Concept X D) (target : Concept X A)
    (refinement : Refines coarse refined) :
    conditionalLogicalImpurity mu refined target <=
      conditionalLogicalImpurity mu coarse target := by
  rcases refinement with ⟨factor, rfl⟩
  exact impurity_comp_le mu refined target factor

#print axioms canonical_refinement_impurity_monotone

end

end D5.S3.ConceptDynamics.Information.CanonicalRefinementImpurityMonotonicity
