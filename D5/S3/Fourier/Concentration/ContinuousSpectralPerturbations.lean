/- GID: D5/S3/Fourier/Concentration/ContinuousSpectralPerturbations
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/ContinuousSpectralPerturbations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interval averaging bounds the near-collisions of a perturbed spectrum. -/

import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.ProductMeasure
import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment

/-! Closed near-collision bands on continuous perturbation intervals. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open Finset
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (monomialFrequency monomialWeight)
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open scoped ENNReal NNReal

namespace D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations

private def intervalNoise (radius : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (2 * radius))⁻¹ • volume.restrict (Icc (-radius) radius)

private theorem intervalNoise_probability {radius : ℝ} (hradius : 0 < radius) :
    IsProbabilityMeasure (intervalNoise radius) := by
  constructor
  have hlen : radius - -radius = 2 * radius := by ring
  rw [intervalNoise, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Icc, hlen]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

private theorem intervalNoise_affine_local {radius a b η : ℝ}
    (hradius : 0 < radius) (ha : a ≠ 0) :
    intervalNoise radius {x | |a * x + b| ≤ η} ≤ ENNReal.ofReal (η / (|a| * radius)) := by
  let center := -b / a
  let reach := η / |a|
  have hfactor (x : ℝ) : a * x + b = a * (x - center) := by
    dsimp [center]
    field_simp
    ring
  have hset : {x : ℝ | |a * x + b| ≤ η} = Icc (center - reach) (center + reach) := by
    ext x
    change |a * x + b| ≤ η ↔ _
    rw [hfactor, abs_mul, mul_comm |a|, ← le_div_iff₀ (abs_pos.mpr ha), abs_le]
    change -reach ≤ x - center ∧ x - center ≤ reach ↔ _
    rw [Set.mem_Icc, le_sub_iff_add_le, sub_le_iff_le_add, neg_add_eq_sub, add_comm reach]
  have hlen : center + reach - (center - reach) = 2 * reach := by ring
  have hmeasure : volume (Icc (center - reach) (center + reach) ∩
      Icc (-radius) radius) ≤ ENNReal.ofReal (2 * reach) := by
    calc
      _ ≤ volume (Icc (center - reach) (center + reach)) := measure_mono inter_subset_left
      _ = _ := by rw [Real.volume_Icc, hlen]
  rw [hset, intervalNoise, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Icc, smul_eq_mul]
  calc
    _ ≤ (ENNReal.ofReal (2 * radius))⁻¹ * ENNReal.ofReal (2 * reach) :=
      by gcongr
    _ = ENNReal.ofReal (reach / radius) := by
      rw [mul_comm, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (by positivity)]
      congr 1
      field_simp
    _ = _ := by simp [reach, div_div]

private theorem intervalNoise_fin_affine {n : ℕ} (radius a : Fin (n + 1) → ℝ)
    (b η : ℝ) (hradius : ∀ j, 0 < radius j) (i : Fin (n + 1)) (ha : a i ≠ 0) :
    (Measure.pi fun j => intervalNoise (radius j))
      {x | |(∑ j, a j * x j) + b| ≤ η} ≤ ENNReal.ofReal (η / (|a i| * radius i)) := by
  let μ (j : Fin (n + 1)) := intervalNoise (radius j)
  have (j : Fin (n + 1)) : IsProbabilityMeasure (μ j) := intervalNoise_probability (hradius j)
  let ν := Measure.pi fun j : Fin n => μ (i.succAbove j)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let rest (y : Fin n → ℝ) := (∑ j : Fin n, a (i.succAbove j) * y j) + b
  let S := {xy : ℝ × (Fin n → ℝ) | |a i * xy.1 + rest xy.2| ≤ η}
  have hS : MeasurableSet S := by
    change MeasurableSet {xy : ℝ × (Fin n → ℝ) | |a i * xy.1 + rest xy.2| ≤ η}
    apply measurableSet_le _ measurable_const
    unfold rest
    fun_prop
  have hpre : e ⁻¹' S = {x | |(∑ j, a j * x j) + b| ≤ η} := by
    ext x
    change |a i * x i + rest (fun j => x (i.succAbove j))| ≤ η ↔
      |(∑ j, a j * x j) + b| ≤ η
    simp only [rest, i.sum_univ_succAbove (f := fun j => a j * x j), add_assoc]
  have hp : MeasurePreserving e (Measure.pi μ) ((μ i).prod ν) :=
    measurePreserving_piFinSuccAbove μ i
  rw [← hpre, ← Measure.map_apply hp.measurable hS, hp.map_eq, Measure.prod_apply_symm hS]
  calc
    _ ≤ ∫⁻ _, ENNReal.ofReal (η / (|a i| * radius i)) ∂ν := by
      apply lintegral_mono
      intro y
      change intervalNoise (radius i) {x | |a i * x + rest y| ≤ η} ≤ _
      exact intervalNoise_affine_local (b := rest y) (η := η) (hradius i) ha
    _ = _ := by simp [ν]

private theorem intervalNoise_pi_affine {J : Type*} [Fintype J] (radius a : J → ℝ)
    (b η : ℝ) (hradius : ∀ j, 0 < radius j) (i : J) (ha : a i ≠ 0) :
    (Measure.pi fun j => intervalNoise (radius j))
      {x | |(∑ j, a j * x j) + b| ≤ η} ≤ ENNReal.ofReal (η / (|a i| * radius i)) := by
  let μ (j : J) := intervalNoise (radius j)
  have (j : J) : IsProbabilityMeasure (μ j) := intervalNoise_probability (hradius j)
  let S := {x : J → ℝ | |(∑ j, a j * x j) + b| ≤ η}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    fun_prop
  have hcard : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  let e : Fin (n + 1) ≃ J := (Fintype.equivFinOfCardEq hn).symm
  let move := MeasurableEquiv.piCongrLeft (fun _ : J => ℝ) e
  have hmove : MeasurePreserving move (Measure.pi fun j => μ (e j)) (Measure.pi μ) :=
    measurePreserving_piCongrLeft μ e
  have hpre : move ⁻¹' S = {x | |(∑ j, a (e j) * x j) + b| ≤ η} := by
    ext x
    change |(∑ j, a j * move x j) + b| ≤ η ↔ _
    have heq : (∑ j, a (e j) * x j) = ∑ j, a j * move x j :=
      Fintype.sum_equiv e _ _ (fun j => by simp [move, MeasurableEquiv.piCongrLeft_apply_apply])
    rw [mem_ofPred_eq, heq]
  change Measure.pi μ S ≤ _
  rw [← hmove.map_eq, Measure.map_apply hmove.measurable hS, hpre]
  have h := intervalNoise_fin_affine (radius ∘ e) (a ∘ e) b η (fun j => hradius (e j)) (e.symm i)
  simpa [μ, Function.comp_def] using h (by simpa using ha)

/-- Maximum perturbation radius after weighting each coordinate by the coefficient difference. -/
def pairRadius {J : Type*} [Fintype J] (radius : J → ℝ) (m n : J → ℕ) : ℝ :=
  (univ.sup fun j => (|(m j : ℝ) - (n j : ℝ)| * radius j).toNNReal : ℝ≥0)

private theorem pairRadius_attained {J : Type*} [Fintype J] (radius : J → ℝ)
    (hradius : ∀ j, 0 < radius j) {m n : J → ℕ} (hmn : m ≠ n) :
    ∃ i, (m i : ℝ) - (n i : ℝ) ≠ 0 ∧
      pairRadius radius m n = |(m i : ℝ) - (n i : ℝ)| * radius i := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, m j ≠ n j := by
    by_contra! h
    exact hmn (funext h)
  let q (i : J) := (|(m i : ℝ) - (n i : ℝ)| * radius i).toNNReal
  have hnonneg (i : J) : 0 ≤ |(m i : ℝ) - (n i : ℝ)| * radius i :=
    mul_nonneg (abs_nonneg _) (hradius i).le
  have hpos : 0 < q j := by
    have hreal : (m j : ℝ) ≠ (n j : ℝ) := by exact_mod_cast hj
    exact Real.toNNReal_pos.mpr (mul_pos (abs_pos.mpr (sub_ne_zero.mpr hreal)) (hradius j))
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (univ : Finset J)
    ⟨j, mem_univ j⟩ q
  have hposi : 0 < q i := hpos.trans_le (hi ▸ (le_sup (f := q) (mem_univ j)))
  have hnonzero : (m i : ℝ) - (n i : ℝ) ≠ 0 := by
    intro heq
    simp [q, heq] at hposi
  refine ⟨i, hnonzero, ?_⟩
  change ((univ.sup q : ℝ≥0) : ℝ) = _
  rw [hi]
  exact Real.coe_toNNReal _ (hnonneg i)

private theorem pair_event_measure_le {J : Type*} [Fintype J] (g radius : J → ℝ)
    (hradius : ∀ j, 0 < radius j) {m n : J → ℕ} (hmn : m ≠ n) {η : ℝ} :
    (Measure.pi fun j => intervalNoise (radius j))
      {x | |monomialFrequency (fun j => g j + x j) m -
        monomialFrequency (fun j => g j + x j) n| ≤ η} ≤
      min 1 (ENNReal.ofReal (η / pairRadius radius m n)) := by
  let μ (j : J) := intervalNoise (radius j)
  have (j : J) : IsProbabilityMeasure (μ j) := intervalNoise_probability (hradius j)
  obtain ⟨i, hi, hmax⟩ := pairRadius_attained radius hradius hmn
  let a (j : J) := (m j : ℝ) - (n j : ℝ)
  let b := ∑ j, a j * g j
  have hdiff (x : J → ℝ) :
      monomialFrequency (fun j => g j + x j) m -
        monomialFrequency (fun j => g j + x j) n = (∑ j, a j * x j) + b := by
    unfold monomialFrequency
    rw [← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl (fun j _ => by dsimp [a]; ring)
  simp_rw [hdiff]
  change Measure.pi μ _ ≤ _
  refine le_min (prob_le_one) ?_
  rw [hmax]
  exact intervalNoise_pi_affine radius a b η hradius i hi

/-- The sum of the pairwise small-interval bounds with their multinomial weights. -/
def excessBound {J : Type*} [Fintype J] [DecidableEq J] (w radius : J → ℝ)
    (p : ℕ) (η : ℝ) : ℝ≥0∞ :=
  let s := piAntidiag univ p
  ∑ m ∈ s, ∑ n ∈ s.erase m,
    ENNReal.ofReal (monomialWeight w m * monomialWeight w n) *
      min 1 (ENNReal.ofReal (η / pairRadius radius m n))

theorem collision_excess_eq {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (p : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    let s := piAntidiag univ p
    tailCollisionMass g w p η - (∑ m ∈ s, monomialWeight w m ^ 2) =
      ∑ m ∈ s, ∑ n ∈ s.erase m,
        if |monomialFrequency g m - monomialFrequency g n| ≤ η
          then monomialWeight w m * monomialWeight w n else 0 := by
  intro s
  let term (m n : J → ℕ) := if |monomialFrequency g m - monomialFrequency g n| ≤ η
    then monomialWeight w m * monomialWeight w n else 0
  change (∑ m ∈ s, ∑ n ∈ s, term m n) - (∑ m ∈ s, monomialWeight w m ^ 2) =
    ∑ m ∈ s, ∑ n ∈ s.erase m, term m n
  rw [← sum_sub_distrib]
  refine sum_congr rfl (fun m hm => ?_)
  rw [← sum_erase_add _ _ hm]
  simp [term, hη, pow_two]

private theorem expected_excess_le {J : Type*} [Fintype J] [DecidableEq J]
    (g w radius : J → ℝ) (hw : ∀ j, 0 ≤ w j) (hradius : ∀ j, 0 < radius j)
    (p : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    let μ := Measure.pi fun j => intervalNoise (radius j)
    let D := ∑ m ∈ piAntidiag univ p, monomialWeight w m ^ 2
    (∫⁻ x, ENNReal.ofReal (tailCollisionMass (fun j => g j + x j) w p η - D) ∂μ) ≤
      excessBound w radius p η := by
  intro μ D
  let s := piAntidiag (univ : Finset J) p
  let c := monomialWeight w
  let hit (m n : J → ℕ) := {x : J → ℝ |
    |monomialFrequency (fun j => g j + x j) m -
      monomialFrequency (fun j => g j + x j) n| ≤ η}
  have hmeas (m n : J → ℕ) : MeasurableSet (hit m n) := by
    apply measurableSet_le _ measurable_const
    dsimp [monomialFrequency]
    fun_prop
  let term (m n : J → ℕ) := (hit m n).indicator (fun _ => ENNReal.ofReal (c m * c n))
  have hterm (m n : J → ℕ) : Measurable (term m n) := measurable_const.indicator (hmeas m n)
  have hc (m n : J → ℕ) : 0 ≤ c m * c n :=
    mul_nonneg (monomialWeight_nonneg w hw m) (monomialWeight_nonneg w hw n)
  have hsplit (x : J → ℝ) :
      ENNReal.ofReal (tailCollisionMass (fun j => g j + x j) w p η - D) =
        ∑ m ∈ s, ∑ n ∈ s.erase m, term m n x := by
    rw [show tailCollisionMass (fun j => g j + x j) w p η - D = _ from
      collision_excess_eq (fun j => g j + x j) w p hη]
    rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => sum_nonneg (fun n _ =>
      by split_ifs <;> first | exact hc m n | exact le_rfl))]
    refine sum_congr rfl (fun m _ => ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ =>
      by split_ifs <;> first | exact hc m n | exact le_rfl)]
    refine sum_congr rfl (fun n _ => ?_)
    by_cases hh : x ∈ hit m n
    · rw [show term m n x = _ from Set.indicator_of_mem hh _]
      simp only [hit, Set.mem_ofPred_eq] at hh
      rw [ite_eq_left hh]
    · rw [show term m n x = _ from Set.indicator_of_notMem hh _]
      simp only [hit, Set.mem_ofPred_eq] at hh
      rw [ite_eq_right hh, ENNReal.ofReal_zero]
  simp_rw [hsplit]
  have hsum (m : J → ℕ) : Measurable (fun x => ∑ n ∈ s.erase m, term m n x) :=
    Finset.measurable_sum _ (fun n _ => hterm m n)
  rw [lintegral_finsetSum _ (fun m _ => hsum m)]
  unfold excessBound
  refine sum_le_sum (fun m _ => ?_)
  rw [lintegral_finsetSum _ (fun n _ => hterm m n)]
  refine sum_le_sum (fun n hn => ?_)
  rw [show term m n = _ from rfl, lintegral_indicator_const (hmeas m n)]
  exact mul_le_mul_right
    (pair_event_measure_le g radius hradius (ne_of_mem_erase hn).symm (η := η)) _

private theorem measurable_collision_of_offsets {J : Type*} [Fintype J] [DecidableEq J]
    (g w : J → ℝ) (p : ℕ) (η : ℝ) :
    Measurable (fun x : J → ℝ => tailCollisionMass (fun j => g j + x j) w p η) := by
  unfold tailCollisionMass nearCollisionMass
  refine Finset.measurable_sum _ (fun m _ => Finset.measurable_sum _ (fun n _ => ?_))
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_le _ measurable_const
  unfold monomialFrequency
  fun_prop

/-- A countable family of collision budgets is satisfied by one spectrum close to the original. -/
theorem exists_continuous_common_nearby_bounds {J K : Type*} [DecidableEq J]
    [Countable J] [Countable K] (g radius : J → ℝ) (hradius : ∀ j, 0 < radius j)
    (support : K → Finset J) (w : ∀ k, support k → ℝ) (hw : ∀ k j, 0 ≤ w k j)
    (p : K → ℕ) (η budget : K → ℝ) (hη : ∀ k, 0 ≤ η k) (hbudget : ∀ k, 0 < budget k)
    (htotal : (∑' k, excessBound (w k) (fun j : support k => radius j) (p k) (η k) /
      ENNReal.ofReal (budget k)) ≤ 1) :
    ∃ g' : J → ℝ, (∀ j, |g' j - g j| ≤ radius j) ∧
      (∑' k, ENNReal.ofReal (tailCollisionMass (fun j : support k => g' j) (w k) (p k) (η k) -
        ∑ m ∈ piAntidiag univ (p k), monomialWeight (w k) m ^ 2) / ENNReal.ofReal (budget k)) ≤
        (∑' k, excessBound (w k) (fun j : support k => radius j) (p k) (η k) /
          ENNReal.ofReal (budget k)) ∧
      ∀ k, tailCollisionMass (fun j : support k => g' j) (w k) (p k) (η k) ≤
        (∑ m ∈ piAntidiag univ (p k), monomialWeight (w k) m ^ 2) + budget k := by
  let ν (j : J) := intervalNoise (radius j)
  have (j : J) : IsProbabilityMeasure (ν j) := intervalNoise_probability (hradius j)
  let μ := Measure.infinitePi ν
  let inside (x : J → ℝ) := ∀ j, x j ∈ Icc (-radius j) (radius j)
  have hinside : ∀ᵐ x ∂μ, inside x := by
    apply ae_all_iff.mpr
    intro j
    have hmeas : Measurable (fun x : J → ℝ => x j) := measurable_pi_apply j
    apply (ae_map_iff hmeas.aemeasurable measurableSet_Icc).mp
    rw [show μ.map (fun x => x j) = ν j from Measure.infinitePi_map_eval ν j]
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  let D (k : K) := ∑ m ∈ piAntidiag univ (p k), monomialWeight (w k) m ^ 2
  let excess (k : K) (y : support k → ℝ) := ENNReal.ofReal
    (tailCollisionMass (fun j : support k => g j + y j) (w k) (p k) (η k) - D k)
  have hexcess (k : K) : Measurable (excess k) :=
    (measurable_collision_of_offsets (fun j : support k => g j) (w k) (p k) (η k)).sub_const
      (D k) |>.ennreal_ofReal
  let loss (k : K) (x : J → ℝ) := excess k ((support k).restrict x) / ENNReal.ofReal (budget k)
  have hmeas (k : K) : Measurable (loss k) :=
    ((hexcess k).comp (Finset.measurable_restrict (support k))).div_const _
  have hlocal (k : K) :
      (∫⁻ x, loss k x ∂μ) ≤
        excessBound (w k) (fun j : support k => radius j) (p k) (η k) /
          ENNReal.ofReal (budget k) := by
    have hmarginal : μ.map (support k).restrict = Measure.pi (fun j : support k => ν j) :=
      Measure.infinitePi_map_restrict ν
    rw [show loss k = fun x => excess k ((support k).restrict x) / ENNReal.ofReal (budget k) from rfl,
      ← lintegral_map ((hexcess k).div_const _) (Finset.measurable_restrict (support k)), hmarginal]
    simp only [div_eq_mul_inv]
    rw [lintegral_mul_const _ (hexcess k)]
    exact mul_le_mul_left
      (expected_excess_le (fun j : support k => g j) (w k) (fun j : support k => radius j)
        (hw k) (fun j => hradius j) (p k) (hη k)) _
  have houtside : μ {x | ¬ inside x} = 0 := ae_iff.mp hinside
  let total (x : J → ℝ) : ℝ≥0∞ := ∑' k : K, loss k x
  have htotalMeas : Measurable total := Measurable.tsum hmeas
  obtain ⟨x, hx, hle⟩ :=
    exists_notMem_null_le_lintegral htotalMeas.aemeasurable houtside
  have hx : inside x := by simpa using hx
  dsimp only [total] at hle
  rw [lintegral_tsum (fun k => (hmeas k).aemeasurable)] at hle
  have hbound := hle.trans (ENNReal.tsum_le_tsum hlocal)
  refine ⟨fun j => g j + x j, ?_, hbound, ?_⟩
  · intro j
    rw [add_sub_cancel_left]
    exact abs_le.mpr (hx j)
  · intro k
    have hk : loss k x ≤ 1 :=
      (ENNReal.le_tsum (f := fun l => loss l x) k).trans (hbound.trans htotal)
    dsimp only [loss, excess] at hk
    rw [← ENNReal.ofReal_div_of_pos (hbudget k), ← ENNReal.ofReal_one,
      ENNReal.ofReal_le_ofReal_iff zero_le_one, div_le_iff₀ (hbudget k), one_mul] at hk
    exact (sub_le_iff_le_add.mp hk).trans_eq (add_comm _ _)

#print axioms exists_continuous_common_nearby_bounds

end D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
