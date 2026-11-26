/- GID: D5/S3/ConceptDynamics/Information/ConditionalGiniTV
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Information/ConditionalGiniTV
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The optimal conditional Gini bound for posterior total variation is attained on two fibers. -/

import D5.S3.ConceptDynamics.Information.ConditionalGiniDefect
import D5.S3.TotalVariation.Metric

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Information.ConditionalGiniTV

open scoped BigOperators ENNReal
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Information.ConditionalLogicalImpurity
open D5.S3.ConceptDynamics.Information.RefinementImpurityMonotonicity
open D5.S3.ConceptDynamics.Information.ConditionalGiniDefect
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.Metric

private theorem card_product_le (n k : ℕ) (hk : k ≤ n) :
    k * (n - k) ≤ n ^ 2 / 4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).2
  have h : (k : ℝ) * ((n : ℝ) - k) * 4 ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2 * k)]
  exact_mod_cast (show ((k * (n - k) * 4 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 by
    push_cast [Nat.cast_sub hk]
    exact h)

private theorem totalVariation_sq_le_of_sum_eq {A : Type*} [Fintype A]
    (hcard : 2 ≤ Fintype.card A) (u v : A → ℝ) (hmass : ∑ a, u a = ∑ a, v a) :
    totalVariation u v ^ 2 ≤
      (((Fintype.card A ^ 2 / 4 : ℕ) : ℝ) / (Fintype.card A : ℝ)) *
        ∑ a, (u a - v a) ^ 2 := by
  classical
  let s := Finset.univ.filter (fun a : A => v a ≤ u a)
  let z : A → ℝ := fun a => u a - v a
  let n : ℝ := Fintype.card A
  let k : ℝ := s.card
  let indicator : A → ℝ := fun a => if a ∈ s then 1 else 0
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (show 0 < Fintype.card A by omega)
  have hkn : s.card ≤ Fintype.card A := Finset.card_le_univ s
  have hprod : k * (n - k) ≤ ((Fintype.card A ^ 2 / 4 : ℕ) : ℝ) := by
    dsimp [k, n]
    have hc := (Nat.cast_le (α := ℝ)).mpr (card_product_le _ _ hkn)
    simpa only [Nat.cast_mul, Nat.cast_sub hkn] using hc
  have hz : ∑ a, z a = 0 := by
    simp [z, Finset.sum_sub_distrib, hmass]
  have hindicator_sum : ∑ a, indicator a = k := by
    rw [show (∑ a, indicator a) = ∑ a ∈ s, (1 : ℝ) by
      rw [← Finset.sum_filter]
      simp]
    simp [k]
  -- Centering the sign indicator leaves its dot product with the zero-sum difference unchanged.
  have hdot : (∑ a, (indicator a - k / n) * z a) = totalVariation u v := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hz, mul_zero, sub_zero]
    rw [total_variation_eq_sum_positive u v hmass]
    change (∑ a, indicator a * z a) = ∑ a ∈ s, z a
    calc
      _ = ∑ a, if a ∈ s then z a else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a ∈ s <;> simp [indicator, ha]
      _ = _ := by rw [← Finset.sum_filter]; simp
  have hnorm : (∑ a, (indicator a - k / n) ^ 2) = k * (n - k) / n := by
    have hterm (a : A) :
        (indicator a - k / n) ^ 2 =
          indicator a - (2 * (k / n)) * indicator a + (k / n) ^ 2 := by
      by_cases ha : a ∈ s
      · simp only [indicator, ite_eq_left ha]
        ring
      · simp only [indicator, ite_eq_right ha]
        ring
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hindicator_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change k - 2 * (k / n) * k + n * (k / n) ^ 2 = _
    field_simp
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun a => indicator a - k / n) z
  rw [hdot, hnorm] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hprod hn.le)
    (Finset.sum_nonneg fun a _ => sq_nonneg (z a)))

/-- Real coordinates of the native totalized fiber posterior. -/
private noncomputable def posterior {X B A : Type*} (p : PMF X)
    (r : Concept X B) (t : Concept X A) (b : B) (a : A) : ℝ :=
  (targetFiberMass p r t b a / conceptFiberMass p r b).toReal

private theorem posterior_sum_eq_one {X B A : Type*} [Fintype A] (p : PMF X)
    (r : Concept X B) (t : Concept X A) (b : B) (hb : conceptFiberMass p r b ≠ 0) :
    ∑ a, posterior p r t b a = 1 := by
  have hm : conceptFiberMass p r b ≠ ⊤ :=
    ENNReal.ne_top_of_tsum_ne_top
      ((conceptFiberMass_tsum_all p r).trans_ne ENNReal.one_ne_top) b
  have hj (a : A) : targetFiberMass p r t b a ≠ ⊤ := by
    apply ne_top_of_le_ne_top hm
    rw [← targetFiberMass_tsum p r t b]
    exact ENNReal.le_tsum a
  have hsum : (∑' a, targetFiberMass p r t b a / conceptFiberMass p r b) = 1 := by
    simp only [div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right, targetFiberMass_tsum, ← div_eq_mul_inv, ENNReal.div_self hb hm]
  have hr := ENNReal.tsum_toReal_eq (fun a : A => ENNReal.div_ne_top (hj a) hb)
  rw [hsum, tsum_fintype, ENNReal.toReal_one] at hr
  exact hr.symm

private theorem fiberMass_le_coarse {X C D : Type*} (p : PMF X) (r : Concept X D)
    (f : D → C) (d : D) : conceptFiberMass p r d ≤ conceptFiberMass p (f ∘ r) (f d) := by
  classical
  unfold conceptFiberMass
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : r x = d
  · have hfx : (f ∘ r) x = f d := congrArg f hx
    simp [Set.indicator, hx, hfx]
  · simp [Set.indicator, hx]

private theorem impurity_ne_top {X B A : Type*} (p : PMF X) (r : Concept X B)
    (t : Concept X A) : conditionalLogicalImpurity p r t ≠ ⊤ := by
  apply ne_top_of_le_ne_top ENNReal.one_ne_top
  calc
    _ ≤ conditionalLogicalImpurity p r t + collisionScore p r t := self_le_add_right _ _
    _ = 1 := impurity_add_collision p r t

private theorem weighted_tsum_sq_le {D : Type*} (w v : D → ℝ)
    (hw : ∀ d, 0 ≤ w d) (hsw : Summable w) (hweight : ∑' d, w d = 1)
    (hmean : Summable (fun d => w d * v d))
    (hsquare : Summable (fun d => w d * v d ^ 2)) :
    (∑' d, w d * v d) ^ 2 ≤ ∑' d, w d * v d ^ 2 := by
  -- Unconditional summability lets finite weighted Cauchy–Schwarz pass to the limit.
  have hfinite (s : Finset D) :
      (∑ d ∈ s, w d * v d) ^ 2 ≤ (∑ d ∈ s, w d) * ∑ d ∈ s, w d * v d ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun d _ => hw d)
      (fun d _ => mul_nonneg (hw d) (sq_nonneg _))
      (fun d _ => by rw [mul_pow, pow_two (w d), mul_assoc])
  have h := le_of_tendsto_of_tendsto' (hmean.hasSum.pow 2)
    (Filter.Tendsto.mul hsw.hasSum hsquare.hasSum) hfinite
  simpa only [hweight, one_mul] using h

/-- The square of the mass-weighted posterior total variation is bounded by the exact
conditional Gini defect times the cardinality coefficient. -/
theorem weighted_posterior_totalVariation_sq_le_gini_defect {X C D A : Type*} [Fintype A]
    (hcard : 2 ≤ Fintype.card A) (p : PMF X) (r : Concept X D) (t : Concept X A)
    (f : D → C) :
    (∑' d, (conceptFiberMass p r d).toReal *
      D5.S3.TotalVariation.Pinsker.totalVariation
        (fun a => (targetFiberMass p r t d a / conceptFiberMass p r d).toReal)
        (fun a => (targetFiberMass p (f ∘ r) t (f d) a /
          conceptFiberMass p (f ∘ r) (f d)).toReal)) ^ 2 ≤
      (((Fintype.card A ^ 2 / 4 : ℕ) : ℝ) / (Fintype.card A : ℝ)) *
        ((conditionalLogicalImpurity p (f ∘ r) t).toReal -
          (conditionalLogicalImpurity p r t).toReal) := by
  let m : D → ENNReal := conceptFiberMass p r
  let w : D → ℝ := fun d => (m d).toReal
  let u : D → A → ℝ := posterior p r t
  let v : D → A → ℝ := fun d => posterior p (f ∘ r) t (f d)
  let tv : D → ℝ := fun d => totalVariation (u d) (v d)
  let energy : D → ℝ := fun d => ∑ a, (u d a - v d a) ^ 2
  let coeff : ℝ := ((Fintype.card A ^ 2 / 4 : ℕ) : ℝ) / (Fintype.card A : ℝ)
  change (∑' d, w d * tv d) ^ 2 ≤ coeff *
    ((conditionalLogicalImpurity p (f ∘ r) t).toReal -
      (conditionalLogicalImpurity p r t).toReal)
  have hm : ∑' d, m d = 1 := conceptFiberMass_tsum_all p r
  have hw (d : D) : 0 ≤ w d := ENNReal.toReal_nonneg
  have hm_finite := hm.trans_ne ENNReal.one_ne_top
  have hm_ne_top := ENNReal.ne_top_of_tsum_ne_top hm_finite
  have hsw : Summable w := ENNReal.summable_toReal hm_finite
  have hweight : ∑' d, w d = 1 := by
    rw [← ENNReal.tsum_toReal_eq hm_ne_top, hm, ENNReal.toReal_one]
  have htv (d : D) : 0 ≤ tv d := total_variation_nonneg (u d) (v d)
  have hpoint (d : D) :
      w d * tv d ≤ w d ∧ w d * tv d ^ 2 ≤ w d ∧
      w d * tv d ^ 2 ≤ coeff * (w d * energy d) := by
    by_cases hd : m d = 0
    · simp [w, hd]
    have hcoarse : conceptFiberMass p (f ∘ r) (f d) ≠ 0 := by
      intro hz
      exact hd (nonpos_iff_eq_zero.mp (hz ▸ fiberMass_le_coarse p r f d))
    have hu : ∑ a, u d a = 1 := posterior_sum_eq_one p r t d hd
    have hv : ∑ a, v d a = 1 := posterior_sum_eq_one p (f ∘ r) t (f d) hcoarse
    have ht : tv d ≤ 1 := total_variation_le_one (u d) (v d)
      ⟨fun _ => ENNReal.toReal_nonneg, hu⟩ ⟨fun _ => ENNReal.toReal_nonneg, hv⟩
    refine ⟨mul_le_of_le_one_right (hw d) ht,
      mul_le_of_le_one_right (hw d) (pow_le_one₀ (htv d) ht), ?_⟩
    calc
      w d * tv d ^ 2 ≤ w d * (coeff * energy d) :=
        mul_le_mul_of_nonneg_left
          (totalVariation_sq_le_of_sum_eq hcard (u d) (v d) (hu.trans hv.symm)) (hw d)
      _ = _ := by ring
  have hmean : Summable (fun d => w d * tv d) :=
    Summable.of_nonneg_of_le (fun d => mul_nonneg (hw d) (htv d)) (fun d => (hpoint d).1) hsw
  have hsquare : Summable (fun d => w d * tv d ^ 2) :=
    Summable.of_nonneg_of_le (fun d => mul_nonneg (hw d) (sq_nonneg _))
      (fun d => (hpoint d).2.1) hsw
  let term : D → ENNReal := fun d => ∑' a, m d * ENNReal.ofReal ((u d a - v d a) ^ 2)
  have hexact : conditionalLogicalImpurity p (f ∘ r) t =
      conditionalLogicalImpurity p r t + ∑' d, term d :=
    conditional_gini_exact_defect p r t f
  have hdelta : (∑' d, term d) ≠ ⊤ := by
    apply (ENNReal.add_ne_top.mp (show
      conditionalLogicalImpurity p r t + ∑' d, term d ≠ ⊤ by
        rw [← hexact]
        exact impurity_ne_top p (f ∘ r) t)).2
  have hterm (d : D) : (term d).toReal = w d * energy d := by
    dsimp only [term]
    rw [ENNReal.tsum_toReal_eq
      (fun a => ENNReal.mul_ne_top (hm_ne_top d) ENNReal.ofReal_ne_top), tsum_fintype]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ← Finset.mul_sum, w, energy]
  have henergy : Summable (fun d => w d * energy d) := by
    simpa only [hterm] using ENNReal.summable_toReal hdelta
  have hdeltaReal : (∑' d, w d * energy d) =
      (conditionalLogicalImpurity p (f ∘ r) t).toReal -
        (conditionalLogicalImpurity p r t).toReal := by
    calc
      _ = (∑' d, term d).toReal := by
        rw [ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hdelta)]
        simp only [hterm]
      _ = _ := by
        rw [hexact, ENNReal.toReal_add (impurity_ne_top p r t) hdelta]
        ring
  calc
    (∑' d, w d * tv d) ^ 2 ≤ ∑' d, w d * tv d ^ 2 :=
      weighted_tsum_sq_le w tv hw hsw hweight hmean hsquare
    _ ≤ ∑' d, coeff * (w d * energy d) :=
      hsquare.tsum_le_tsum (fun d => (hpoint d).2.2) (henergy.mul_left coeff)
    _ = _ := by rw [tsum_mul_left, hdeltaReal]

#print axioms weighted_posterior_totalVariation_sq_le_gini_defect

noncomputable section

private def partitionReadout {A : Type*} [DecidableEq A] (s : Finset A) :
    Concept A Bool := fun a => if a ∈ s then true else false

private def blockWeight (k : ℕ) : ℝ≥0∞ :=
  1 / (2 * (k : ℝ≥0∞))

private theorem blockWeight_toReal (k : ℕ) :
    (blockWeight k).toReal = 1 / (2 * (k : ℝ)) := by
  simp [blockWeight, ENNReal.toReal_mul]

private theorem blockWeight_ne_top {k : ℕ} (hk : 0 < k) : blockWeight k ≠ ⊤ := by
  apply ENNReal.div_ne_top ENNReal.one_ne_top
  exact mul_ne_zero (by norm_num) (by exact_mod_cast hk.ne')

private theorem blockWeight_total {k : ℕ} (hk : 0 < k) :
    (k : ℝ≥0∞) * blockWeight k = 1 / 2 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top (by simp) (blockWeight_ne_top hk))
    (ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num))).mp
  rw [ENNReal.toReal_mul, blockWeight_toReal]
  norm_num [ENNReal.toReal_div]
  field_simp

private def partitionWeight {A : Type*} [Fintype A] [DecidableEq A] (s : Finset A)
    (a : A) : ℝ≥0∞ :=
  if a ∈ s then blockWeight s.card else blockWeight sᶜ.card

private theorem partitionWeight_sum_block {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (hs : 0 < s.card) :
    (∑ a ∈ s, partitionWeight s a) = 1 / 2 := by
  have hsum : (∑ a ∈ s, partitionWeight s a) = ∑ _a ∈ s, blockWeight s.card :=
    Finset.sum_congr rfl fun a ha => by simp [partitionWeight, ha]
  rw [hsum]
  rw [Finset.sum_const, nsmul_eq_mul]
  exact blockWeight_total hs

private theorem partitionWeight_sum_compl {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (hs : 0 < sᶜ.card) :
    (∑ a ∈ sᶜ, partitionWeight s a) = 1 / 2 := by
  have hsum : (∑ a ∈ sᶜ, partitionWeight s a) = ∑ _a ∈ sᶜ, blockWeight sᶜ.card :=
    Finset.sum_congr rfl fun a ha => by simp [partitionWeight, Finset.mem_compl.mp ha]
  rw [hsum]
  rw [Finset.sum_const, nsmul_eq_mul]
  exact blockWeight_total hs

private def partitionPMF {A : Type*} [Fintype A] [DecidableEq A] (s : Finset A)
    (hs : 0 < s.card) (hc : 0 < sᶜ.card) : PMF A :=
  PMF.ofFintype (partitionWeight s) (by
    rw [← Finset.sum_add_sum_compl s, partitionWeight_sum_block s hs,
      partitionWeight_sum_compl s hc]
    have hhalf : (1 / 2 : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨hhalf, hhalf⟩)
      ENNReal.one_ne_top).mp
    rw [ENNReal.toReal_add hhalf hhalf]
    norm_num [ENNReal.toReal_div])

private theorem partitionPMF_mass {A : Type*} [Fintype A] [DecidableEq A] (s : Finset A)
    (hs : 0 < s.card) (hc : 0 < sᶜ.card) (b : Bool) :
    conceptFiberMass (partitionPMF s hs hc) (partitionReadout s) b = 1 / 2 := by
  let massAt : A → ℝ≥0∞ := fun a =>
    ({x | partitionReadout s x = b} : Set A).indicator (partitionPMF s hs hc) a
  change (∑' a, massAt a) = _
  rw [tsum_fintype, ← Finset.sum_add_sum_compl s]
  cases b
  · have hblock : (∑ a ∈ s, massAt a) = 0 :=
      Finset.sum_eq_zero fun a ha => by simp [massAt, Set.indicator, partitionReadout, ha]
    have hcompl : (∑ a ∈ sᶜ, massAt a) = ∑ a ∈ sᶜ, partitionWeight s a :=
      Finset.sum_congr rfl fun a ha => by
        simp [massAt, Set.indicator, partitionReadout, Finset.mem_compl.mp ha, partitionPMF]
    rw [hblock, hcompl, zero_add, partitionWeight_sum_compl s hc]
  · have hcompl : (∑ a ∈ sᶜ, massAt a) = 0 :=
      Finset.sum_eq_zero fun a ha => by
        simp [massAt, Set.indicator, partitionReadout, Finset.mem_compl.mp ha]
    have hblock : (∑ a ∈ s, massAt a) = ∑ a ∈ s, partitionWeight s a :=
      Finset.sum_congr rfl fun a ha => by
        simp [massAt, Set.indicator, partitionReadout, ha, partitionPMF]
    rw [hblock, hcompl, add_zero, partitionWeight_sum_block s hs]

private theorem constantFiber_mass {A : Type*} (p : PMF A) :
    conceptFiberMass p (fun _ => ()) () = 1 := by
  simp [conceptFiberMass]

private theorem identityTarget_mass {A B : Type*} (p : PMF A)
    (r : Concept A B) (b : B) (a : A) :
    letI := Classical.decEq B
    targetFiberMass p r id b a = if r a = b then p a else 0 := by
  classical
  unfold targetFiberMass
  rw [tsum_eq_single a]
  · simp
  · intro x hx
    simp [hx]

private def realPosterior {A B X : Type*} (p : PMF X) (r : Concept X B) (t : Concept X A)
    (b : B) (a : A) : ℝ :=
  (targetFiberMass p r t b a / conceptFiberMass p r b).toReal

private theorem partitionPMF_coarse_posterior {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (hs : 0 < s.card) (hc : 0 < sᶜ.card) (a : A) :
    realPosterior (partitionPMF s hs hc) (fun _ => ()) id () a =
      (partitionWeight s a).toReal := by
  classical
  unfold realPosterior
  rw [identityTarget_mass (partitionPMF s hs hc) (fun _ => ()) () a,
    constantFiber_mass (partitionPMF s hs hc)]
  simp [partitionPMF]

private theorem partitionPMF_refined_posterior {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (hs : 0 < s.card) (hc : 0 < sᶜ.card) (b : Bool) (a : A) :
    realPosterior (partitionPMF s hs hc) (partitionReadout s) id b a =
      if partitionReadout s a = b then 2 * (partitionWeight s a).toReal else 0 := by
  classical
  unfold realPosterior
  rw [identityTarget_mass, partitionPMF_mass]
  by_cases ha : partitionReadout s a = b
  · simp only [ha, ite_true, ENNReal.toReal_div, partitionPMF, PMF.ofFintype_apply]
    norm_num [ENNReal.toReal_div]
    ring
  · simp [ha]

private theorem partitionPMF_abs_gap {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (hs : 0 < s.card) (hc : 0 < sᶜ.card) (b : Bool) (a : A) :
    |realPosterior (partitionPMF s hs hc) (partitionReadout s) id b a -
      realPosterior (partitionPMF s hs hc) (fun _ => ()) id () a| =
      (partitionWeight s a).toReal := by
  rw [partitionPMF_refined_posterior s hs hc b a, partitionPMF_coarse_posterior s hs hc a]
  have hnonneg : 0 ≤ (partitionWeight s a).toReal := ENNReal.toReal_nonneg
  by_cases ha : partitionReadout s a = b
  · simp only [ha, ite_true]
    rw [show 2 * (partitionWeight s a).toReal - (partitionWeight s a).toReal =
      (partitionWeight s a).toReal by ring, abs_of_nonneg hnonneg]
  · simp [ha, abs_of_nonneg hnonneg]

private theorem partitionPMF_avgTV {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (hs : 0 < s.card) (hc : 0 < sᶜ.card) :
    (∑' b, (conceptFiberMass (partitionPMF s hs hc) (partitionReadout s) b).toReal *
      D5.S3.TotalVariation.Pinsker.totalVariation
        (realPosterior (partitionPMF s hs hc) (partitionReadout s) id b)
        (realPosterior (partitionPMF s hs hc) (fun _ => ()) id ())) = 1 / 2 := by
  have hp : (∑ a, partitionPMF s hs hc a) = 1 := by
    simpa only [tsum_fintype] using (partitionPMF s hs hc).tsum_coe
  have hsum : (∑ a, (partitionWeight s a).toReal) = 1 := by
    change (∑ a, (partitionPMF s hs hc a).toReal) = 1
    rw [← ENNReal.toReal_sum (fun a _ => (partitionPMF s hs hc).apply_ne_top a), hp]
    simp
  simp_rw [D5.S3.TotalVariation.Pinsker.totalVariation,
    partitionPMF_abs_gap s hs hc, hsum, partitionPMF_mass s hs hc]
  rw [tsum_fintype, Fintype.sum_bool]
  norm_num [ENNReal.toReal_div]

private theorem partitionPMF_defect_eq_squares {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (hs : 0 < s.card) (hc : 0 < sᶜ.card) :
    (conditionalLogicalImpurity (partitionPMF s hs hc) (fun _ => ()) id).toReal -
      (conditionalLogicalImpurity (partitionPMF s hs hc) (partitionReadout s) id).toReal =
        ∑ a, (partitionWeight s a).toReal ^ 2 := by
  let p := partitionPMF s hs hc
  let r := partitionReadout s
  let f : Bool → Unit := fun _ => ()
  let squareAt : A → ℝ := fun a => (partitionWeight s a).toReal ^ 2
  have hsquare (b : Bool) (a : A) :
      (realPosterior p r id b a - realPosterior p (f ∘ r) id (f b) a)^2 =
        squareAt a := by
    rw [← sq_abs (realPosterior p r id b a - realPosterior p (f ∘ r) id (f b) a)]
    exact congrArg (· ^ 2) (partitionPMF_abs_gap s hs hc b a)
  have hcharge : (∑' b, ∑' a, conceptFiberMass p r b * ENNReal.ofReal
      ((realPosterior p r id b a - realPosterior p (f ∘ r) id (f b) a)^2)) =
      ENNReal.ofReal (∑ a, squareAt a) := by
    have hmass (b : Bool) : conceptFiberMass p r b = 1 / 2 :=
      partitionPMF_mass s hs hc b
    have hhalf : (1 / 2 : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.div_ne_top ENNReal.one_ne_top (by norm_num)
    have hadd : (1 / 2 : ℝ≥0∞) + 1 / 2 = 1 := by
      apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.mpr ⟨hhalf, hhalf⟩)
        ENNReal.one_ne_top).mp
      rw [ENNReal.toReal_add hhalf hhalf]
      norm_num [ENNReal.toReal_div]
    simp_rw [hsquare, hmass, tsum_fintype]
    rw [Fintype.sum_bool, ← Finset.sum_add_distrib]
    simp_rw [← add_mul, hadd, one_mul]
    exact (ENNReal.ofReal_sum_of_nonneg fun a _ => sq_nonneg (partitionWeight s a).toReal).symm
  have hdefect := conditional_gini_exact_defect p r id f
  change conditionalLogicalImpurity p (f ∘ r) id = conditionalLogicalImpurity p r id +
    (∑' b, ∑' a, conceptFiberMass p r b * ENNReal.ofReal
      ((realPosterior p r id b a - realPosterior p (f ∘ r) id (f b) a)^2)) at hdefect
  rw [hcharge] at hdefect
  have hrefined : conditionalLogicalImpurity p r id ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    calc
      _ ≤ conditionalLogicalImpurity p r id + collisionScore p r id := self_le_add_right _ _
      _ = 1 := impurity_add_collision p r id
  have hreal := congrArg ENNReal.toReal hdefect
  rw [ENNReal.toReal_add hrefined ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun a _ => sq_nonneg (partitionWeight s a).toReal)]
    at hreal
  change (conditionalLogicalImpurity p (f ∘ r) id).toReal -
    (conditionalLogicalImpurity p r id).toReal = ∑ a, squareAt a
  rw [hreal]
  ring

private theorem partitionWeight_sum_squares {A : Type*} [Fintype A] [DecidableEq A]
    (s : Finset A) (hs : 0 < s.card) (hc : 0 < sᶜ.card) :
    (∑ a, (partitionWeight s a).toReal ^ 2) =
      (Fintype.card A : ℝ) / (4 * (s.card : ℝ) * (sᶜ.card : ℝ)) := by
  have hblock : (∑ a ∈ s, (partitionWeight s a).toReal ^ 2) =
      ∑ _a ∈ s, (1 / (2 * (s.card : ℝ))) ^ 2 :=
    Finset.sum_congr rfl fun a ha => by simp [partitionWeight, ha, blockWeight_toReal]
  have hcompl : (∑ a ∈ sᶜ, (partitionWeight s a).toReal ^ 2) =
      ∑ _a ∈ sᶜ, (1 / (2 * (sᶜ.card : ℝ))) ^ 2 :=
    Finset.sum_congr rfl fun a ha => by
      simp [partitionWeight, Finset.mem_compl.mp ha, blockWeight_toReal]
  have hcard : (s.card : ℝ) + (sᶜ.card : ℝ) = (Fintype.card A : ℝ) := by
    exact_mod_cast Finset.card_add_card_compl s
  have hsR : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hcR : (sᶜ.card : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← Finset.sum_add_sum_compl s, hblock, hcompl, ← hcard]
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

private theorem balanced_block_product (n : ℕ) :
    (n / 2) * (n - n / 2) = n ^ 2 / 4 := by
  let k := n / 2
  change k * (n - k) = n ^ 2 / 4
  have hn : n = 2 * k ∨ n = 2 * k + 1 := by
    dsimp [k]
    omega
  rcases hn with hn | hn
  · have hsub : n - k = k := by omega
    have hsq : n ^ 2 = 4 * (k * k) := by
      rw [hn]
      ring
    rw [hsub, hsq]
    omega
  · have hsub : n - k = k + 1 := by omega
    have hsq : n ^ 2 = 4 * (k * (k + 1)) + 1 := by
      rw [hn]
      ring
    rw [hsub, hsq]
    omega

/-- The balanced two-block PMF attains the posterior TV bound for every finite target alphabet
with at least two elements. Its two refined fibers each carry half the mass. -/
theorem conditional_gini_tv_attained {A : Type*} [Fintype A] (hA : 2 ≤ Fintype.card A) :
    ∃ (p : PMF A) (r : Concept A Bool),
      let f : Bool → Unit := fun _ => ()
      let averagedTV := ∑' b, (conceptFiberMass p r b).toReal *
        D5.S3.TotalVariation.Pinsker.totalVariation
          (fun a => (targetFiberMass p r id b a / conceptFiberMass p r b).toReal)
          (fun a => (targetFiberMass p (f ∘ r) id (f b) a /
            conceptFiberMass p (f ∘ r) (f b)).toReal)
      let defect := (conditionalLogicalImpurity p (f ∘ r) id).toReal -
        (conditionalLogicalImpurity p r id).toReal
      (∀ b, conceptFiberMass p r b = 1 / 2) ∧
      averagedTV = 1 / 2 ∧
      0 < defect ∧
      averagedTV ^ 2 = (((Fintype.card A ^ 2 / 4 : ℕ) : ℝ) /
        (Fintype.card A : ℝ)) * defect := by
  classical
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset A)) (n := Fintype.card A / 2) (by
      rw [Finset.card_univ]
      omega)
  have hblock : 0 < s.card := by omega
  have hcompl : 0 < sᶜ.card := by rw [Finset.card_compl]; omega
  let p := partitionPMF s hblock hcompl
  let r := partitionReadout s
  have hTV := partitionPMF_avgTV s hblock hcompl
  have hdefect := (partitionPMF_defect_eq_squares s hblock hcompl).trans
    (partitionWeight_sum_squares s hblock hcompl)
  have hnR : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast (show 0 < Fintype.card A by omega)
  have hblockR : 0 < (s.card : ℝ) := by exact_mod_cast hblock
  have hcomplR : 0 < (sᶜ.card : ℝ) := by exact_mod_cast hcompl
  have hprod : s.card * sᶜ.card = Fintype.card A ^ 2 / 4 := by
    rw [Finset.card_compl, hs, balanced_block_product]
  have hprodR : (s.card : ℝ) * (sᶜ.card : ℝ) =
      ((Fintype.card A ^ 2 / 4 : ℕ) : ℝ) := by exact_mod_cast hprod
  refine ⟨p, r, partitionPMF_mass s hblock hcompl, hTV, ?_, ?_⟩
  · rw [hdefect]
    positivity
  · calc
      _ = (1 / 2 : ℝ)^2 := congrArg (· ^ 2) hTV
      _ = _ := by
        rw [hdefect, ← hprodR]
        field_simp
        ring

#print axioms conditional_gini_tv_attained

end

end D5.S3.ConceptDynamics.Information.ConditionalGiniTV
