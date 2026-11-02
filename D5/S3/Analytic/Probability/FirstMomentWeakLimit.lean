/- GID: D5/S3/Analytic/Probability/FirstMomentWeakLimit
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/FirstMomentWeakLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coordinate first-moment tails preserve displacement integrals under weak limits. -/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Weak convergence and first-moment tails for real-plane probability laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter Topology

namespace D5.S3.Analytic.Probability.FirstMomentWeakLimit

private def clip (R x : ℝ) : ℝ := max (-R) (min R x)

private lemma continuous_clip (R : ℝ) : Continuous (clip R) :=
  continuous_const.max (continuous_const.min continuous_id)

private lemma clip_eq {R x : ℝ} (hx : |x| ≤ R) : clip R x = x := by
  rw [clip, min_eq_right (le_abs_self x |>.trans hx),
    max_eq_right (neg_le_of_abs_le hx)]

private lemma abs_clip_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |clip R x| ≤ R := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

private lemma abs_clip_le_abs {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    |clip R x| ≤ |x| := by
  by_cases hx : |x| ≤ R
  · rw [clip_eq hx]
  · exact (abs_clip_le hR x).trans (le_of_not_ge hx)

private lemma clip_error_le {R r : ℝ} (hR : 0 ≤ R) (hRr : R ≤ r) (x : ℝ) :
    |x - clip r x| ≤ {x : ℝ | R < |x|}.indicator (fun x => |x|) x := by
  by_cases hx : R < |x|
  · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | R < |x|} from hx)]
    rcases le_or_gt x r with hxr | hxr
    · rcases le_or_gt (-r) x with hrx | hrx
      · rw [clip_eq (abs_le.mpr ⟨hrx, hxr⟩), sub_self, abs_zero]
        exact abs_nonneg _
      · have hx0 : x ≤ 0 := by linarith
        have heq : clip r x = -r := by
          simp [clip, min_eq_right hxr, max_eq_left hrx.le]
        rw [heq, abs_of_nonpos (by linarith), abs_of_nonpos hx0]
        linarith
    · have hx0 : 0 ≤ x := by linarith
      have heq : clip r x = r := by
        simp [clip, min_eq_left hxr.le, max_eq_right (by linarith : -r ≤ r)]
      rw [heq, abs_of_nonneg (by linarith), abs_of_nonneg hx0]
      linarith
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | R < |x|} from hx),
      clip_eq ((le_of_not_gt hx).trans hRr), sub_self, abs_zero]

private def test (h : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := (p.2 - p.1) * h p.1

private def clippedTest (h : ℝ → ℝ) (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  (clip R p.2 - clip R p.1) * h p.1

private lemma integrable_test {ρ : Measure (ℝ × ℝ)}
    (hfst : Integrable Prod.fst ρ) (hsnd : Integrable Prod.snd ρ)
    {h : ℝ → ℝ} (hh : Continuous h) {M : ℝ} (_hM : 0 ≤ M)
    (hb : ∀ x, |h x| ≤ M) : Integrable (test h) ρ := by
  apply ((hsnd.abs.add hfst.abs).mul_const M).mono'
    (((continuous_snd.sub continuous_fst).mul (hh.comp continuous_fst)).aestronglyMeasurable)
  filter_upwards with p
  dsimp [test]
  rw [abs_mul]
  exact mul_le_mul (abs_sub _ _) (hb _) (abs_nonneg _) (by positivity)

private lemma integrable_clippedTest {ρ : Measure (ℝ × ℝ)}
    (hfst : Integrable Prod.fst ρ) (hsnd : Integrable Prod.snd ρ)
    {h : ℝ → ℝ} (hh : Continuous h) {M R : ℝ} (_hM : 0 ≤ M) (hR : 0 ≤ R)
    (hb : ∀ x, |h x| ≤ M) : Integrable (clippedTest h R) ρ := by
  apply ((hsnd.abs.add hfst.abs).mul_const M).mono'
    ((((continuous_clip R).comp continuous_snd).sub
      ((continuous_clip R).comp continuous_fst)).mul (hh.comp continuous_fst)).aestronglyMeasurable
  filter_upwards with p
  dsimp [clippedTest]
  rw [abs_mul]
  exact mul_le_mul ((abs_sub _ _).trans
    (add_le_add (abs_clip_le_abs hR _) (abs_clip_le_abs hR _))) (hb _)
    (abs_nonneg _) (by positivity)

private lemma integral_clip_error_le {ρ : Measure (ℝ × ℝ)}
    (hfst : Integrable Prod.fst ρ) (hsnd : Integrable Prod.snd ρ)
    {h : ℝ → ℝ} (hh : Continuous h) {M R r : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |h x| ≤ M) (hR : 0 ≤ R) (hRr : R ≤ r) :
    |(∫ p, test h p ∂ρ) - ∫ p, clippedTest h r p ∂ρ| ≤
      ((∫ p in {p : ℝ × ℝ | R < |p.1|}, |p.1| ∂ρ) +
       ∫ p in {p : ℝ × ℝ | R < |p.2|}, |p.2| ∂ρ) * M := by
  have hsx : MeasurableSet {p : ℝ × ℝ | R < |p.1|} :=
    isOpen_lt continuous_const continuous_fst.abs |>.measurableSet
  have hsy : MeasurableSet {p : ℝ × ℝ | R < |p.2|} :=
    isOpen_lt continuous_const continuous_snd.abs |>.measurableSet
  let X := {p : ℝ × ℝ | R < |p.1|}.indicator (fun p => |p.1|)
  let Y := {p : ℝ × ℝ | R < |p.2|}.indicator (fun p => |p.2|)
  have hX : Integrable X ρ := hfst.abs.indicator hsx
  have hY : Integrable Y ρ := hsnd.abs.indicator hsy
  have hi := (integrable_test hfst hsnd hh hM hb).sub
    (integrable_clippedTest hfst hsnd hh hM (hR.trans hRr) hb)
  rw [← integral_sub (integrable_test hfst hsnd hh hM hb)
    (integrable_clippedTest hfst hsnd hh hM (hR.trans hRr) hb)]
  calc
    _ ≤ ∫ p, ‖test h p - clippedTest h r p‖ ∂ρ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun p => test h p - clippedTest h r p)
    _ ≤ ∫ p, (X p + Y p) * M ∂ρ := by
      apply integral_mono_ae hi.norm ((hX.add hY).mul_const M)
      filter_upwards with p
      have hx := clip_error_le hR hRr p.1
      have hy := clip_error_le hR hRr p.2
      have heq : test h p - clippedTest h r p =
          ((p.2 - clip r p.2) - (p.1 - clip r p.1)) * h p.1 := by
        dsimp [test, clippedTest]; ring
      change |test h p - clippedTest h r p| ≤ (X p + Y p) * M
      rw [heq, abs_mul]
      have hxy : |(p.2 - clip r p.2) - (p.1 - clip r p.1)| ≤ X p + Y p := by
        have := (abs_sub (p.2 - clip r p.2) (p.1 - clip r p.1)).trans (add_le_add hy hx)
        simpa [X, Y, indicator, add_comm] using this
      exact mul_le_mul hxy (hb _) (abs_nonneg _) (by
        exact add_nonneg (indicator_nonneg (fun p _ => abs_nonneg p.1) p)
          (indicator_nonneg (fun p _ => abs_nonneg p.2) p))
    _ = _ := by rw [integral_mul_const, integral_add hX hY];
                simp only [X, Y, integral_indicator hsx, integral_indicator hsy]

private lemma clippedTest_bcf (h : ℝ → ℝ) (hh : Continuous h)
    {M R : ℝ} (_hM : 0 ≤ M) (hR : 0 ≤ R) (hb : ∀ x, |h x| ≤ M) :
    ∃ g : BoundedContinuousFunction (ℝ × ℝ) ℝ, ∀ p, g p = clippedTest h R p := by
  have hc : Continuous (clippedTest h R) :=
    (((continuous_clip R).comp continuous_snd).sub
      ((continuous_clip R).comp continuous_fst)).mul (hh.comp continuous_fst)
  have hb' (p : ℝ × ℝ) : |clippedTest h R p| ≤ (2 * R) * M := by
    dsimp [clippedTest]
    rw [abs_mul]
    exact mul_le_mul ((abs_sub _ _).trans
      (by linarith [abs_clip_le hR p.2, abs_clip_le hR p.1])) (hb _)
      (abs_nonneg _) (by positivity)
  refine ⟨BoundedContinuousFunction.mkOfBound ⟨_, hc⟩ (2 * ((2 * R) * M)) ?_, fun _ => rfl⟩
  intro p q
  rw [Real.dist_eq]
  calc
    _ ≤ |clippedTest h R p| + |clippedTest h R q| := abs_sub _ _
    _ ≤ _ := by linarith [hb' p, hb' q]

private lemma tendsto_integral_clippedTest {ρ : Measure (ℝ × ℝ)}
    (hfst : Integrable Prod.fst ρ) (hsnd : Integrable Prod.snd ρ)
    {h : ℝ → ℝ} (hh : Continuous h) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |h x| ≤ M) :
    Tendsto (fun k : ℕ => ∫ p, clippedTest h k p ∂ρ) atTop
      (𝓝 (∫ p, test h p ∂ρ)) := by
  apply tendsto_integral_of_dominated_convergence (fun p => (|p.2| + |p.1|) * M)
  · intro k
    exact (integrable_clippedTest hfst hsnd hh hM (Nat.cast_nonneg k) hb).aestronglyMeasurable
  · exact (hsnd.abs.add hfst.abs).mul_const M
  · intro k
    filter_upwards with p
    dsimp [clippedTest]
    rw [abs_mul]
    exact mul_le_mul ((abs_sub _ _).trans
      (add_le_add (abs_clip_le_abs (Nat.cast_nonneg k) _) (abs_clip_le_abs (Nat.cast_nonneg k) _)))
      (hb _) (abs_nonneg _) (by positivity)
  · filter_upwards with p
    obtain ⟨K, hK⟩ := exists_nat_ge (max |p.1| |p.2|)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
    dsimp [clippedTest, test]
    rw [clip_eq ((le_max_right _ _).trans (hK.trans hKk)),
      clip_eq ((le_max_left _ _).trans (hK.trans hKk))]

/-- Weak convergence plus uniform absolute first-moment tails preserves every
bounded-continuous first-coordinate displacement test, on the same joint laws. -/
theorem tendsto_integral_displacement
    {πn : ℕ → ProbabilityMeasure (ℝ × ℝ)} {π : ProbabilityMeasure (ℝ × ℝ)}
    (hweak : Tendsto πn atTop (𝓝 π))
    (hfst : ∀ n, Integrable Prod.fst (πn n : Measure (ℝ × ℝ)))
    (hsnd : ∀ n, Integrable Prod.snd (πn n : Measure (ℝ × ℝ)))
    (hfstInf : Integrable Prod.fst (π : Measure (ℝ × ℝ)))
    (hsndInf : Integrable Prod.snd (π : Measure (ℝ × ℝ)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ n,
      (∫ p in {p : ℝ × ℝ | R < |p.1|}, |p.1| ∂(πn n : Measure (ℝ × ℝ))) +
      (∫ p in {p : ℝ × ℝ | R < |p.2|}, |p.2| ∂(πn n : Measure (ℝ × ℝ))) < ε)
    (h : ℝ → ℝ) (hh : Continuous h)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |h x| ≤ M) :
    Tendsto (fun n => ∫ p, (p.2 - p.1) * h p.1 ∂(πn n : Measure (ℝ × ℝ))) atTop
      (𝓝 (∫ p, (p.2 - p.1) * h p.1 ∂(π : Measure (ℝ × ℝ)))) := by
  obtain ⟨M₀, hM₀, hb₀⟩ := hb
  let M := max M₀ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbM (x : ℝ) : |h x| ≤ M := (hb₀ x).trans (le_max_left _ _)
  have hlim := tendsto_integral_clippedTest hfstInf hsndInf hh hM.le hbM
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R, hR, htailR⟩ := htail (ε / (3 * M)) (by positivity)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hlim (ε / 3) (by positivity)
  obtain ⟨J, hJ⟩ := exists_nat_ge R
  let k := max K J
  have hRk : R ≤ (k : ℝ) := hJ.trans (by exact_mod_cast le_max_right K J)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  obtain ⟨g, hg⟩ := clippedTest_bcf h hh hM.le hk0 hbM
  have hgw := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak g
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hgw (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have herr := integral_clip_error_le (hfst n) (hsnd n) hh hM.le hbM hR.le hRk
  have hsmall : |(∫ p, test h p ∂(πn n : Measure (ℝ × ℝ))) -
      ∫ p, clippedTest h k p ∂(πn n : Measure (ℝ × ℝ))| < ε / 3 := by
    refine herr.trans_lt ?_
    have := mul_lt_mul_of_pos_right (htailR n) hM
    calc
      _ < (ε / (3 * M)) * M := this
      _ = ε / 3 := by field_simp
  have hmiddle := hN n hn
  have hlast := hK k (le_max_left _ _)
  simp only [Real.dist_eq] at hmiddle hlast ⊢
  simp only [hg] at hmiddle
  calc
    _ ≤ |(∫ p, test h p ∂(πn n : Measure (ℝ × ℝ))) -
          ∫ p, clippedTest h k p ∂(πn n : Measure (ℝ × ℝ))| +
        |(∫ p, clippedTest h k p ∂(πn n : Measure (ℝ × ℝ))) -
          ∫ p, clippedTest h k p ∂(π : Measure (ℝ × ℝ))| +
        |(∫ p, clippedTest h k p ∂(π : Measure (ℝ × ℝ))) -
          ∫ p, test h p ∂(π : Measure (ℝ × ℝ))| := by
      have tri (a b c d : ℝ) : |a - d| ≤ |a - b| + |b - c| + |c - d| := by
        calc
          _ = |(a - b) + (b - c) + (c - d)| := by congr 1 <;> ring
          _ ≤ |(a - b) + (b - c)| + |c - d| :=
            abs_add_le ((a - b) + (b - c)) (c - d)
          _ ≤ _ := by linarith [abs_add_le (a - b) (b - c)]
      exact tri _ _ _ _
    _ < ε := by linarith

end D5.S3.Analytic.Probability.FirstMomentWeakLimit
