/- GID: D5/S3/Analytic/Probability/DiscardedOccupancy/Characteristic
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/DiscardedOccupancy/Characteristic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A conditional characteristic function compares a centered occupancy increment with its Gaussian factor. -/

import D5.S3.Analytic.Probability.DiscardedOccupancy.Transitions
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance

section

open scoped BigOperators Topology ENNReal ProbabilityTheory
open Finset Filter MeasureTheory ProbabilityTheory

namespace DiscardedOccupancy

noncomputable section

instance instMeasurableSpaceOptionFin_d5 (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤

instance instMeasurableSingletonClassOptionFin_d5 (n : ℕ) : MeasurableSingletonClass (Option (Fin n)) := ⟨fun _ => trivial⟩

theorem mem_occupied_iff {n : ℕ} (i : Fin n) {j : ℕ} (ω : History n j) :
    i ∈ occupied n j ω ↔ ∃ t : Fin j, ω t = some i := by
  induction j with
  | zero => simp [occupied]
  | succ j ih =>
    have h (b : Option (Fin n)) (s : Finset (Fin n)) :
        i ∈ insertThrow s b ↔ b = some i ∨ i ∈ s := by
      cases b <;> simp [insertThrow, eq_comm]
    rw [occupied, h, ih]
    constructor
    · rintro (hl | ⟨t, ht⟩)
      · exact ⟨Fin.last j, hl⟩
      · exact ⟨t.castSucc, ht⟩
    · rintro ⟨t, ht⟩
      induction t using Fin.lastCases with
      | last => exact Or.inl ht
      | cast t => exact Or.inr ⟨t, ht⟩

private theorem throwMass_sum {n : ℕ} (hn : 0 < n) (p : ℝ) :
    ∑ b, throwMass n p b = 1 := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Fintype.sum_option]
  simp [throwMass, nsmul_eq_mul, mul_div_cancel₀ _ hn']

private theorem wordMass_sum {n : ℕ} (hn : 0 < n) (p : ℝ) (j : ℕ) :
    ∑ ω : History n j, wordMass n p ω = 1 := by
  simpa [expect, average, smul_eq_mul] using expect_const hn p j (1 : ℝ)

private theorem throwMass_nonneg (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (b : Option (Fin n)) : 0 ≤ throwMass n p b := by
  cases b with
  | none => exact sub_nonneg.mpr hp'
  | some i => exact div_nonneg hp (Nat.cast_nonneg n)

def throwPMF {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    PMF (Option (Fin n)) :=
  PMF.ofFintype (fun b => ENNReal.ofReal (throwMass n p b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => throwMass_nonneg n hp hp' b),
      throwMass_sum hn, ENNReal.ofReal_one])

def wordPMF {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (j : ℕ) : PMF (History n j) :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (wordMass n p ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => wordMass_nonneg hp hp' ω),
      wordMass_sum hn, ENNReal.ofReal_one])

theorem wordMeasure_eq_pi {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (j : ℕ) :
    (wordPMF hn hp hp' j).toMeasure =
      Measure.pi (fun _ : Fin j => (throwPMF hn hp hp').toMeasure) := by
  apply Measure.ext_of_singleton
  intro ω
  rw [Measure.pi_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [wordPMF, throwPMF, PMF.ofFintype_apply,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), wordMass]
  exact ENNReal.ofReal_prod_of_nonneg (fun b _ => throwMass_nonneg n hp hp' (ω b))

private theorem integral_expect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (j : ℕ) (f : ℕ → E) :
    (∫ ω, f (count n j ω) ∂(wordPMF hn hp hp' j).toMeasure) = expect n p j f := by
  rw [PMF.integral_eq_sum]
  simp [wordPMF, expect, average, ENNReal.toReal_ofReal, wordMass_nonneg hp hp']

theorem integral_count {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (j : ℕ) :
    (∫ ω, (count n j ω : ℝ) ∂(wordPMF hn hp hp' j).toMeasure) = mean n p j :=
  integral_expect hn hp hp' j (fun x => (x : ℝ))

theorem variance_count {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (j : ℕ) :
    Var[(fun ω => (count n j ω : ℝ)); (wordPMF hn hp hp' j).toMeasure] = variance n p j := by
  rw [ProbabilityTheory.variance_eq_integral (measurable_of_countable _).aemeasurable,
    integral_count hn hp hp']
  exact integral_expect hn hp hp' j (fun x => ((x : ℝ) - mean n p j)^2)

def standardized (n : ℕ) (p : ℝ) (j : ℕ) (x : ℕ) : ℝ :=
  ((x : ℝ) - mean n p j) / Real.sqrt (variance n p j)

def standardizedLaw {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (j : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(wordPMF hn hp hp' j).toMeasure.map (fun ω => standardized n p j (count n j ω)),
    (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2
      inferInstance⟩

def phase (s : ℝ) : ℂ := Complex.exp ((s : ℂ) * Complex.I)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp [phase, add_mul, Complex.exp_add]

@[simp] private theorem phase_zero : phase 0 = 1 := by simp [phase]

@[simp] private theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

theorem charFun_standardizedLaw {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) (j : ℕ) (t : ℝ) :
    charFun (standardizedLaw hn hp hp' j).toMeasure t =
      expect n p j (fun x => phase (t * standardized n p j x)) := by
  rw [charFun_apply_real]
  let η := (wordPMF hn hp hp' j).toMeasure
  let F : History n j → ℝ := fun ω => standardized n p j (count n j ω)
  let G : ℝ → ℂ := fun z => Complex.exp ((t : ℂ) * (z : ℂ) * Complex.I)
  change (∫ z, G z ∂(η.map F)) = _
  have hG : Continuous G := by dsimp [G]; fun_prop
  rw [integral_map (measurable_of_countable F).aemeasurable hG.aestronglyMeasurable]
  simpa only [G, F, η, phase, Complex.ofReal_mul] using integral_expect hn hp hp' j
    (fun x => phase (t * standardized n p j x))

def paletteP (k : ℕ) : ℝ := (k : ℝ)⁻¹

theorem palette_bounds {k : ℕ} (hk : 2 ≤ k) : 0 < paletteP k ∧ paletteP k < 1 := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ (by linarith)⟩

theorem palette_throw_mass {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) :
    ((throwPMF hn (palette_bounds hk).1.le (palette_bounds hk).2.le).toMeasure {none} =
      ENNReal.ofReal (1 - 1 / (k : ℝ))) ∧
    (∀ i : Fin n,
      (throwPMF hn (palette_bounds hk).1.le (palette_bounds hk).2.le).toMeasure {some i} =
        ENNReal.ofReal (1 / ((k : ℝ) * n))) := by
  constructor
  · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [throwPMF, throwMass, paletteP, one_div]
  · intro i
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [throwPMF, throwMass, paletteP, div_eq_mul_inv, mul_comm]

def rowLaw (k : ℕ) (hk : 2 ≤ k) (N : ℕ) : ProbabilityMeasure ℝ :=
  standardizedLaw (Nat.succ_pos N) (palette_bounds hk).1.le (palette_bounds hk).2.le N

end
end DiscardedOccupancy

end

section

open scoped BigOperators Topology
open Finset Filter MeasureTheory ProbabilityTheory

namespace DiscardedOccupancy

noncomputable section

private def phaseTaylor (y : ℝ) : ℂ :=
  1 + (y : ℂ) * Complex.I - (y : ℂ)^2 / 2

private theorem phase_taylor_bound {y : ℝ} (hy : |y| ≤ 1) :
    ‖phase y - phaseTaylor y‖ ≤ Real.exp 1 * |y|^3 := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((y : ℂ) * Complex.I) 3
  have he : (∑ m ∈ range 3, ((y : ℂ) * Complex.I)^m / (m.factorial : ℂ)) =
      phaseTaylor y := by
    simp [phaseTaylor, sum_range_succ, mul_pow, Complex.I_sq]
    ring
  rw [he, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs] at h
  exact h.trans (by
    rw [mul_comm (Real.exp 1)]
    gcongr)

def centeredBernoulli (r s : ℝ) : ℂ :=
  (1 - r) • phase (s * (-r)) + r • phase (s * (1 - r))

private theorem bernoulli_taylor {r s : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1) (hs : |s| ≤ 1) :
    ‖centeredBernoulli r s - Complex.ofReal (1 - s^2 * (r * (1 - r)) / 2)‖ ≤
      Real.exp 1 * |s|^3 := by
  have hu : |s * (-r)| ≤ |s| := by
    rw [abs_mul, abs_neg, abs_of_nonneg hr]
    exact mul_le_of_le_one_right (abs_nonneg _) hr'
  have hw : |s * (1-r)| ≤ |s| := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hr')]
    exact mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  have h1 := (phase_taylor_bound (hu.trans hs)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hu 3) (Real.exp_nonneg _))
  have h2 := (phase_taylor_bound (hw.trans hs)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hw 3) (Real.exp_nonneg _))
  have he : Complex.ofReal (1 - s^2 * (r * (1 - r)) / 2) =
      (1 - r) • phaseTaylor (s * (-r)) + r • phaseTaylor (s * (1 - r)) := by
    simp only [phaseTaylor, Complex.real_smul]
    push_cast
    ring
  rw [he, centeredBernoulli, add_sub_add_comm, ← smul_sub, ← smul_sub]
  calc
    _ ≤ ‖(1-r) • (phase (s * (-r)) - phaseTaylor (s * (-r)))‖ +
        ‖r • (phase (s * (1-r)) - phaseTaylor (s * (1-r)))‖ := norm_add_le _ _
    _ ≤ (1-r) * (Real.exp 1 * |s|^3) + r * (Real.exp 1 * |s|^3) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hr'), abs_of_nonneg hr]
      gcongr
    _ = _ := by ring

private theorem gaussian_taylor {s u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) (hs : |s| ≤ 1) :
    |Real.exp (-s^2 * u / 2) - (1 - s^2 * u / 2)| ≤ |s|^3 := by
  have hs2 : s^2 = |s|^2 := (sq_abs s).symm
  have hx : |-s^2 * u / 2| ≤ |s|^2 := by
    rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg s)) hu) (by norm_num)), hs2]
    nlinarith [mul_le_mul_of_nonneg_left hu' (sq_nonneg |s|)]
  have hx' := hx.trans (pow_le_one₀ (abs_nonneg s) hs)
  have ht := Real.abs_exp_sub_one_sub_id_le hx'
  rw [show Real.exp (-s^2 * u / 2) - (1 - s^2 * u / 2) =
      Real.exp (-s^2 * u / 2) - 1 - (-s^2 * u / 2) by ring]
  calc
    _ ≤ (-s^2 * u / 2)^2 := ht
    _ = (|-s^2 * u / 2|)^2 := (sq_abs _).symm
    _ ≤ (|s|^2)^2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
    _ = |s|^3 * |s| := by ring
    _ ≤ |s|^3 := mul_le_of_le_one_right (by positivity) hs

private theorem bernoulli_gaussian_comparison {r s u : ℝ}
    (hr : 0 ≤ r) (hr' : r ≤ 1) (hu : 0 ≤ u) (hu' : u ≤ 1) (hs : |s| ≤ 1) :
    ‖centeredBernoulli r s - (↑(Real.exp (-s^2 * u / 2)) : ℂ)‖ ≤
      (Real.exp 1 + 1) * |s|^3 + (s^2 / 2) * |r * (1 - r) - u| := by
  let P : ℝ → ℂ := fun b => Complex.ofReal (1 - s^2 * b / 2)
  let g : ℂ := ↑(Real.exp (-s^2 * u / 2))
  let b := r * (1 - r)
  have h1 : ‖centeredBernoulli r s - P b‖ ≤ Real.exp 1 * |s|^3 :=
    bernoulli_taylor hr hr' hs
  have h2 : ‖P b - P u‖ = (s^2 / 2) * |b - u| := by
    have he : P b - P u = Complex.ofReal (-(s^2 / 2) * (b - u)) := by
      dsimp [P]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ s^2 / 2)]
  have h3 : ‖P u - g‖ ≤ |s|^3 := by
    dsimp [P, g]
    rw [norm_sub_rev, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact gaussian_taylor hu hu' hs
  change ‖centeredBernoulli r s - g‖ ≤ _
  calc
    _ ≤ ‖centeredBernoulli r s - P b‖ + ‖P b - P u‖ + ‖P u - g‖ := by
      have hh (x y z : ℂ) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
        simpa only [dist_eq_norm] using dist_triangle x y z
      exact (hh _ (P u) _).trans (add_le_add (hh _ (P b) _) le_rfl)
    _ ≤ Real.exp 1 * |s|^3 + (s^2 / 2) * |b - u| + |s|^3 := by
      rw [h2]
      gcongr
    _ = _ := by ring

theorem expect_sub {E : Type*} [AddCommGroup E] [Module ℝ E] (n : ℕ) (p : ℝ)
    (j : ℕ) (f g : ℕ → E) :
    expect n p j (fun x => f x - g x) = expect n p j f - expect n p j g := by
  simp only [expect, average, smul_sub, Finset.sum_sub_distrib]

private theorem expect_mul_complex (n : ℕ) (p : ℝ) (j : ℕ) (f : ℕ → ℂ) (c : ℂ) :
    expect n p j (fun x => f x * c) = expect n p j f * c := by
  simp only [expect, average, Complex.real_smul, Finset.sum_mul, mul_assoc]

theorem norm_expect_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n j : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (f : ℕ → E) :
    ‖expect n p j f‖ ≤ expect n p j (fun x => ‖f x‖) := by
  unfold expect average
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro ω _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (wordMass_nonneg hp hp' ω), smul_eq_mul]

private theorem v_lipschitz {n : ℕ} {p x y : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hx : 0 ≤ x) (hx' : x ≤ n) (hy : 0 ≤ y) (hy' : y ≤ n) :
    |v n p x - v n p y| ≤ (p / n) * |x - y| := by
  have hq := q_bounds hp hx hx'
  have hr := q_bounds hp hy hy'
  have hb : |1 - q n p x - q n p y| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : v n p x - v n p y =
      (-(p / n) * (x - y)) * (1 - q n p x - q n p y) := by
    unfold v q
    ring
  rw [he, abs_mul, abs_mul, abs_neg, abs_of_nonneg (div_nonneg hp (Nat.cast_nonneg n))]
  exact mul_le_of_le_one_right (by positivity) hb

private theorem centered_abs_bound {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) {j : ℕ} (hj : j ≤ n) :
    expect n p j (fun x => |(x : ℝ) - mean n p j|) ≤ Real.sqrt n := by
  let r := Real.sqrt (n : ℝ)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.2 hn'
  have hsq : r^2 = n := Real.sq_sqrt hn'.le
  have hv : variance n p j ≤ n :=
    (variance_le_time hn hp hp' j).trans (by exact_mod_cast hj)
  calc
    _ ≤ expect n p j (fun x => ((2*r)⁻¹ : ℝ) • (((x : ℝ) - mean n p j)^2 + n)) := by
      apply expect_mono hp hp'
      intro x _ _
      rw [smul_eq_mul, ← div_eq_inv_mul]
      apply (le_div_iff₀ (by positivity)).2
      nlinarith [sq_nonneg (|(x : ℝ) - mean n p j| - r),
        sq_abs ((x : ℝ) - mean n p j)]
    _ = (2*r)⁻¹ * (variance n p j + n) := by
      rw [expect_smul, expect_add, expect_const hn, smul_eq_mul, variance]
    _ ≤ (2*r)⁻¹ * ((n : ℝ) + n) :=
      mul_le_mul_of_nonneg_left (add_le_add hv le_rfl) (by positivity)
    _ = _ := by
      change (2*r)⁻¹ * ((n : ℝ) + n) = r
      field_simp
      nlinarith

def predictableVariance (n : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  v n p (mean n p j)

def fluctuationBound (n : ℕ) (p : ℝ) : ℝ := (p / n) * Real.sqrt n

theorem variance_fluctuation {n : ℕ} (hn : 0 < n) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) {j : ℕ} (hj : j ≤ n) :
    expect n p j (fun x => |v n p x - predictableVariance n p j|) ≤ fluctuationBound n p := by
  have hm := mean_bounds hn hp hp' j
  calc
    _ ≤ expect n p j (fun x => (p / n : ℝ) • |(x : ℝ) - mean n p j|) := by
      apply expect_mono hp hp'
      intro x _ hx
      exact v_lipschitz hp hp' (Nat.cast_nonneg x) (by exact_mod_cast hx) hm.1 hm.2
    _ ≤ _ := by
      rw [expect_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (centered_abs_bound hn hp hp' hj) (by positivity)

def weight (n : ℕ) (p : ℝ) (m j : ℕ) : ℝ := a n p ^ (m - j)

def rowPhase (n : ℕ) (p : ℝ) (j : ℕ) (s : ℝ) : ℂ :=
  expect n p j (fun x => phase (s * ((x : ℝ) - mean n p j)))

def gaussianFactor (s u : ℝ) : ℂ := ↑(Real.exp (-s^2 * u / 2))

theorem norm_gaussianFactor_le (s : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ‖gaussianFactor s u‖ ≤ 1 := by
  rw [gaussianFactor, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg s)) hu) (by norm_num))

theorem rowPhase_zero (n : ℕ) (p s : ℝ) : rowPhase n p 0 s = 1 := by
  simp [rowPhase, mean, expect_zero_time]

private theorem rowPhase_succ {n : ℕ} (hn : 0 < n) (p : ℝ) (j : ℕ) (s : ℝ) :
    rowPhase n p (j+1) s = expect n p j (fun x =>
      phase ((a n p * s) * ((x : ℝ) - mean n p j)) * centeredBernoulli (q n p x) s) := by
  unfold rowPhase
  rw [expect_succ hn]
  apply expect_congr
  intro x _ _
  have h0 : s * ((x : ℝ) - mean n p (j+1)) =
      (a n p * s) * ((x : ℝ) - mean n p j) + s * (-q n p x) := by
    rw [mean_succ hn]
    unfold a q
    ring
  have h1 : s * (((x+1 : ℕ) : ℝ) - mean n p (j+1)) =
      (a n p * s) * ((x : ℝ) - mean n p j) + s * (1 - q n p x) := by
    rw [mean_succ hn]
    push_cast
    unfold a q
    ring
  rw [h0, h1, phase_add, phase_add, centeredBernoulli]
  simp only [Complex.real_smul]
  ring

theorem conditional_comparison {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {j : ℕ} (hj : j ≤ n) {s : ℝ} (hs : |s| ≤ 1) :
    ‖rowPhase n p (j+1) s -
        rowPhase n p j (a n p * s) * gaussianFactor s (predictableVariance n p j)‖ ≤
      (Real.exp 1 + 1) * |s|^3 + (s^2 / 2) * fluctuationBound n p := by
  let A := Real.exp 1 + 1
  let u := predictableVariance n p j
  have hm := mean_bounds hn hp hp' j
  have hu : 0 ≤ u ∧ u ≤ 1 := v_bounds hp hp' hm.1 hm.2
  have he := variance_fluctuation hn hp hp' hj
  rw [rowPhase_succ hn, rowPhase, ← expect_mul_complex, ← expect_sub]
  refine (norm_expect_le hp hp' _).trans ?_
  calc
    _ ≤ expect n p j (fun x =>
        A * |s|^3 + (s^2 / 2 : ℝ) • |v n p x - u|) := by
      apply expect_mono hp hp'
      intro x _ hx
      rw [← mul_sub, norm_mul, phase_norm, one_mul, smul_eq_mul]
      have hq := q_bounds hp (Nat.cast_nonneg x) (by exact_mod_cast hx)
      exact bernoulli_gaussian_comparison hq.1 (hq.2.trans hp') hu.1 hu.2 hs
    _ ≤ _ := by
      rw [expect_add, expect_const hn, expect_smul, smul_eq_mul]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left he (show 0 ≤ s^2 / 2 by positivity))

end
end DiscardedOccupancy

end
