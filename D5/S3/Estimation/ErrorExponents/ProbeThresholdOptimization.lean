/- GID: D5/S3/Estimation/ErrorExponents/ProbeThresholdOptimization
   generality: G
   mirror-B: D5/B/S3/Estimation/ErrorExponents/ProbeThresholdOptimization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive probability vector has an exact capped probe optimizer. -/

import D5.S3.Analytic.Curvature.CardinalSplineRecurrence
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization

open scoped BigOperators
open Filter Topology

open scoped Classical in
/-- Let `a` be a strictly positive probability vector and let `0 < ε < 1`.  The capped
square-root vector has a unique threshold, globally maximizes the probe quadratic on the unit
box, and admits the finite active-set formula of Proposition 46.2. -/
theorem probe_threshold_optimization {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ l, 0 < a l) (hsum : ∑ l, a l = 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    let v : ι → ℝ := fun l => Real.sqrt (a l)
    let F : (ι → ℝ) → ℝ := fun x => (∑ l, v l * x l) ^ 2 - ε * ∑ l, (x l) ^ 2
    let X : ℝ → ι → ℝ := fun c l => min 1 (c * v l)
    let H : ℝ → Finset ι := fun c => Finset.univ.filter fun l => 1 ≤ c * v l
    let d : ℝ → ℝ := fun c =>
      ∑ l ∈ Finset.univ.filter (fun l => l ∉ H c), a l
    let S : ℝ → ℝ := fun c => ∑ l ∈ H c, v l
    ∃ c : ℝ,
      (0 < c ∧
        (∑ l, min (a l) (v l / c)) = ε ∧
        (∀ l, 0 ≤ X c l ∧ X c l ≤ 1) ∧
        (∀ x, (∀ l, 0 ≤ x l ∧ x l ≤ 1) → F x ≤ F (X c)) ∧
        d c < ε ∧
        c = S c / (ε - d c) ∧
        F (X c) = ε * (S c) ^ 2 / (ε - d c) - ε * (H c).card) ∧
      (∀ c', 0 < c' → (∑ l, min (a l) (v l / c')) = ε → c' = c) := by
  classical
  haveI : Nonempty ι := by
    by_contra hι
    letI : IsEmpty ι := not_nonempty_iff.mp hι
    have hzero : (∑ l, a l) = 0 := by simp
    linarith
  let v : ι → ℝ := fun l => Real.sqrt (a l)
  let F : (ι → ℝ) → ℝ := fun x => (∑ l, v l * x l) ^ 2 - ε * ∑ l, (x l) ^ 2
  let X : ℝ → ι → ℝ := fun c l => min 1 (c * v l)
  let H : ℝ → Finset ι := fun c => Finset.univ.filter fun l => 1 ≤ c * v l
  let d : ℝ → ℝ := fun c =>
    ∑ l ∈ Finset.univ.filter (fun l => l ∉ H c), a l
  let S : ℝ → ℝ := fun c => ∑ l ∈ H c, v l
  let g : ℝ → ℝ := fun c => ∑ l, min (a l) (v l / c)
  change ∃ c : ℝ,
    (0 < c ∧ g c = ε ∧
      (∀ l, 0 ≤ X c l ∧ X c l ≤ 1) ∧
      (∀ x, (∀ l, 0 ≤ x l ∧ x l ≤ 1) → F x ≤ F (X c)) ∧
      d c < ε ∧ c = S c / (ε - d c) ∧
      F (X c) = ε * (S c) ^ 2 / (ε - d c) - ε * (H c).card) ∧
    (∀ c', 0 < c' → g c' = ε → c' = c)
  have hvpos (l : ι) : 0 < v l := by
    exact Real.sqrt_pos.2 (ha l)
  have hvsq (l : ι) : (v l) ^ 2 = a l := by
    exact Real.sq_sqrt (ha l).le
  have haleone (l : ι) : a l ≤ 1 := by
    calc
      a l ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => (ha j).le) (Finset.mem_univ l)
      _ = 1 := hsum
  have halev (l : ι) : a l ≤ v l := by
    simpa only [v] using Real.le_sqrt_self_iff.mpr (haleone l)
  have hg_one : g 1 = 1 := by
    simp only [g, div_one, min_eq_left (halev _), hsum]
  let V : ℝ := ∑ l, v l
  have hVone : 1 ≤ V := by
    rw [← hsum]
    exact Finset.sum_le_sum fun l _ => halev l
  have hVpos : 0 < V := lt_of_lt_of_le zero_lt_one hVone
  let C : ℝ := V / ε
  have hCone : 1 < C := by
    rw [show C = V / ε by rfl, lt_div_iff₀ hε0]
    simpa only [one_mul] using hε1.trans_le hVone
  have hg_C : g C ≤ ε := by
    calc
      g C ≤ ∑ l, v l / C := Finset.sum_le_sum fun l _ => min_le_right _ _
      _ = V / C := by rw [Finset.sum_div]
      _ = ε := by
        dsimp [C]
        field_simp
  have hg_continuous : ContinuousOn g (Set.Ioi (0 : ℝ)) := by
    apply continuousOn_finsetSum
    intro l _ x hx
    exact (continuousWithinAt_const).min
      (continuousWithinAt_const.div continuousWithinAt_id (ne_of_gt hx))
  have hroot_exists : ∃ c ∈ Set.Icc (1 : ℝ) C, g c = ε := by
    have hcont : ContinuousOn g (Set.Icc (1 : ℝ) C) :=
      hg_continuous.mono fun c hc => lt_of_lt_of_le zero_lt_one hc.1
    have hmem : ε ∈ Set.Icc (g C) (g 1) := by
      rw [hg_one]
      exact ⟨hg_C, hε1.le⟩
    simpa only [Set.mem_image] using intermediate_value_Icc' hCone.le hcont hmem
  obtain ⟨c, hcI, hgc⟩ := hroot_exists
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hcI.1
  have hg_strict {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hgp : g p < 1) :
      g q < g p := by
    have hex : ∃ l, min (a l) (v l / p) < a l := by
      by_contra h
      push Not at h
      have hall : ∀ l, min (a l) (v l / p) = a l := fun l =>
        le_antisymm (min_le_left _ _) (h l)
      have : g p = 1 := by simp only [g, hall, hsum]
      linarith
    obtain ⟨l, hl⟩ := hex
    apply Finset.sum_lt_sum
    · intro j _
      apply min_le_min_left
      exact div_le_div_of_nonneg_left (hvpos j).le hp hpq.le
    · refine ⟨l, Finset.mem_univ _, ?_⟩
      have hlp : v l / p < a l := (min_lt_iff.mp hl).resolve_left (lt_irrefl _)
      have hdiv : v l / q < v l / p := by
        exact (div_lt_div_iff₀ (lt_trans hp hpq) hp).2 (by nlinarith [hvpos l])
      rw [min_eq_right hlp.le]
      exact (min_le_right _ _).trans_lt hdiv
  have hroot_unique {q : ℝ} (hq : 0 < q) (hgq : g q = ε) : q = c := by
    rcases lt_trichotomy q c with hqc | hqc | hcq
    · have hlt := hg_strict hq hqc (by rw [hgq]; exact hε1)
      rw [hgc, hgq] at hlt
      exact (lt_irrefl ε hlt).elim
    · exact hqc
    · have hlt := hg_strict hc hcq (by rw [hgc]; exact hε1)
      rw [hgc, hgq] at hlt
      exact (lt_irrefl ε hlt).elim
  have hpartition (f : ι → ℝ) :
      (∑ l, f l) = (∑ l ∈ H c, f l) +
        ∑ l ∈ Finset.univ.filter (fun l => l ∉ H c), f l := by
    symm
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
      Finset.sum_filter_add_sum_filter_not Finset.univ (fun l => l ∈ H c) f
  have hthreshold (l : ι) :
      min (a l) (v l / c) = if l ∈ H c then v l / c else a l := by
    by_cases hl : l ∈ H c
    · rw [if_pos hl, min_eq_right]
      have hactive : 1 ≤ c * v l := by simpa [H] using hl
      rw [← hvsq l, div_le_iff₀ hc]
      nlinarith [hvpos l]
    · rw [if_neg hl, min_eq_left]
      have hinactive : c * v l < 1 := by simpa [H, not_le] using hl
      rw [← hvsq l, le_div_iff₀ hc]
      nlinarith [hvpos l]
  have hroot_split : S c / c + d c = ε := by
    rw [← hgc]
    symm
    calc
      g c = (∑ l ∈ H c, min (a l) (v l / c)) +
          ∑ l ∈ Finset.univ.filter (fun l => l ∉ H c),
            min (a l) (v l / c) := hpartition _
      _ = S c / c + d c := by
        congr 1
        · rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro l hl
          rw [hthreshold l, if_pos hl]
        · apply Finset.sum_congr rfl
          intro l hl
          rw [hthreshold l, if_neg (Finset.mem_filter.mp hl).2]
  have hHnonempty : (H c).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hd : d c = 1 := by simp [d, h, hsum]
    have hS : S c = 0 := by simp [S, h]
    rw [hd, hS, zero_div] at hroot_split
    linarith
  have hSpos : 0 < S c := by
    rw [Finset.sum_pos_iff_of_nonneg]
    · obtain ⟨l, hl⟩ := hHnonempty
      exact ⟨l, hl, hvpos l⟩
    · exact fun l _ => (hvpos l).le
  have hdlt : d c < ε := by
    have : 0 < S c / c := div_pos hSpos hc
    linarith
  have hden : 0 < ε - d c := sub_pos.mpr hdlt
  have hc_formula : c = S c / (ε - d c) := by
    apply (eq_div_iff hden.ne').2
    have hSc : S c = (ε - d c) * c :=
      (div_eq_iff hc.ne').1 (by linarith [hroot_split])
    nlinarith
  have hXactive (l : ι) (hl : l ∈ H c) : X c l = 1 := by
    exact min_eq_left (by simpa [H] using hl)
  have hXinactive (l : ι) (hl : l ∉ H c) : X c l = c * v l := by
    apply min_eq_right
    exact (le_of_not_ge fun h => hl (by simpa [H] using h))
  have hXbounds (l : ι) : 0 ≤ X c l ∧ X c l ≤ 1 := by
    exact ⟨le_min (by norm_num) (mul_nonneg hc.le (hvpos l).le), min_le_left _ _⟩
  have hAstar : (∑ l, v l * X c l) = ε * c := by
    calc
      (∑ l, v l * X c l) =
          (∑ l ∈ H c, v l * X c l) +
            ∑ l ∈ Finset.univ.filter (fun l => l ∉ H c),
              v l * X c l := hpartition _
      _ = S c + c * d c := by
        congr 1
        · apply Finset.sum_congr rfl
          intro l hl
          rw [hXactive l hl, mul_one]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          rw [hXinactive l (Finset.mem_filter.mp hl).2, ← hvsq l]
          ring
      _ = ε * c := by
        have hp : S c = (ε - d c) * c :=
          (div_eq_iff hc.ne').1 (by linarith [hroot_split])
        rw [hp]
        ring
  have hXsq : (∑ l, (X c l) ^ 2) = (H c).card + c ^ 2 * d c := by
    calc
      (∑ l, (X c l) ^ 2) =
          (∑ l ∈ H c, (X c l) ^ 2) +
            ∑ l ∈ Finset.univ.filter (fun l => l ∉ H c),
              (X c l) ^ 2 := hpartition _
      _ = (H c).card + c ^ 2 * d c := by
        congr 1
        · calc
            (∑ l ∈ H c, (X c l) ^ 2) = ∑ _l ∈ H c, (1 : ℝ) := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [hXactive l hl, one_pow]
            _ = (H c).card := by simp
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          rw [hXinactive l (Finset.mem_filter.mp hl).2, ← hvsq l]
          ring
  let K : ℝ → ℝ := fun q =>
    -ε * q ^ 2 + ∑ l, (2 * q * v l * X q l - (X q l) ^ 2)
  have hcoordinate {q z : ℝ} (hq : 0 ≤ q) {l : ι} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
      2 * q * v l * z - z ^ 2 ≤ 2 * q * v l * X q l - (X q l) ^ 2 := by
    by_cases hr : q * v l ≤ 1
    · rw [show X q l = q * v l by exact min_eq_right hr]
      nlinarith [sq_nonneg (z - q * v l)]
    · have hr' : 1 < q * v l := lt_of_not_ge hr
      rw [show X q l = 1 by exact min_eq_left hr'.le]
      have hp : 0 ≤ (1 - z) * (2 * (q * v l) - 1 - z) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
  let Y : ℝ → ι → ℝ := fun t l => min 1 (t * v l / ε)
  let J : ℝ → ℝ := fun t =>
    -t ^ 2 + ∑ l, (2 * t * v l * Y t l - ε * (Y t l) ^ 2)
  have hJderiv (t : ℝ) :
      HasDerivAt J (2 * (∑ l, v l * Y t l - t)) t := by
    have hpospart (x : ℝ) :
        HasDerivAt (fun y : ℝ => max y 0 ^ 2) (2 * max x 0) x := by
      simpa using
        (D5.S3.Analytic.Curvature.CardinalSplineRecurrence.hasDerivAt_max_sub_pow
          (0 : ℝ) 0 x)
    have hphi (l : ι) :
        HasDerivAt (fun s : ℝ =>
          2 * s * v l * min 1 (s * v l / ε) -
            ε * (min 1 (s * v l / ε)) ^ 2)
          (2 * v l * min 1 (t * v l / ε)) t := by
      have hz : HasDerivAt (fun s : ℝ => s * v l / ε - 1) (v l / ε) t := by
        have hz0 := (((hasDerivAt_id t).mul_const (v l)).div_const ε).sub_const 1
        convert! hz0 using 1 <;> ring
      have hmax : HasDerivAt (fun s : ℝ => max (s * v l / ε - 1) 0 ^ 2)
          (2 * max (t * v l / ε - 1) 0 * (v l / ε)) t :=
        by simpa [Function.comp_def] using
          (hpospart (t * v l / ε - 1)).comp t hz
      have hbase : HasDerivAt (fun s : ℝ => s ^ 2 * (v l) ^ 2 / ε)
          (2 * t * (v l) ^ 2 / ε) t := by
        have hbase0 := ((hasDerivAt_pow 2 t).const_mul ((v l) ^ 2)).div_const ε
        convert! hbase0 using 1
        · funext s
          ring
        · norm_num
          ring
      have hrewrite :
          (fun s : ℝ =>
            2 * s * v l * min 1 (s * v l / ε) -
              ε * (min 1 (s * v l / ε)) ^ 2) =
          (fun s : ℝ => s ^ 2 * (v l) ^ 2 / ε -
            ε * max (s * v l / ε - 1) 0 ^ 2) := by
        funext s
        by_cases hs : s * v l / ε ≤ 1
        · rw [min_eq_right hs]
          have hm : max (s * v l / ε - 1) 0 = 0 :=
            max_eq_right (sub_nonpos.mpr hs)
          rw [hm]
          field_simp
          ring
        · have hs' : 1 ≤ s * v l / ε := le_of_lt (lt_of_not_ge hs)
          rw [min_eq_left hs']
          rw [max_eq_left (sub_nonneg.mpr hs')]
          field_simp
          ring
      rw [hrewrite]
      have h := hbase.sub (hmax.const_mul ε)
      convert! h using 1
      · by_cases hs : t * v l / ε ≤ 1
        · rw [min_eq_right hs]
          rw [max_eq_right (sub_nonpos.mpr hs)]
          ring
        · have hs' : 1 ≤ t * v l / ε := le_of_lt (lt_of_not_ge hs)
          rw [min_eq_left hs']
          rw [max_eq_left (sub_nonneg.mpr hs')]
          field_simp [hε0.ne']
          ring
    have hsum : HasDerivAt
        (fun s : ℝ => ∑ l, (2 * s * v l * Y s l - ε * (Y s l) ^ 2))
        (∑ l, 2 * v l * Y t l) t := by
      have hsum0 := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => by
        simpa [Y] using hphi l)
      simpa only [Finset.sum_apply] using hsum0
    have hquad : HasDerivAt (fun s : ℝ => -s ^ 2) (-2 * t) t := by
      have hquad0 := (hasDerivAt_pow 2 t).neg
      convert! hquad0 using 1 <;> norm_num
    dsimp [J]
    have h := hquad.add hsum
    have hsum2 : (∑ l, 2 * v l * Y t l) = 2 * ∑ l, v l * Y t l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    convert! h using 1
    rw [hsum2]
    ring
  have hJcont : ContinuousOn J (Set.Ici (0 : ℝ)) := by
    intro t ht
    exact (hJderiv t).continuousAt.continuousWithinAt
  have hscale (r : ℝ) (hr : 0 < r) :
      (∑ l, v l * min 1 (r * v l)) = r * g r := by
    calc
      (∑ l, v l * min 1 (r * v l)) =
          ∑ l, r * min (a l) (v l / r) := by
        apply Finset.sum_congr rfl
        intro l hl
        by_cases hrv : r * v l ≤ 1
        · rw [min_eq_right hrv]
          have hle : a l ≤ v l / r := by
            rw [le_div_iff₀ hr, ← hvsq l]
            nlinarith [hvpos l]
          rw [min_eq_left hle, ← hvsq l]
          ring
        · have hrv' : 1 ≤ r * v l := le_of_lt (lt_of_not_ge hrv)
          rw [min_eq_left hrv']
          have hle : v l / r ≤ a l := by
            rw [div_le_iff₀ hr, ← hvsq l]
            nlinarith [hvpos l]
          rw [min_eq_right hle]
          field_simp
      _ = r * g r := by
        rw [Finset.mul_sum]
  have hYscale (t : ℝ) (ht : 0 < t) :
      (∑ l, v l * Y t l) = (t / ε) * g (t / ε) := by
    have hte : 0 < t / ε := div_pos ht hε0
    calc
      (∑ l, v l * Y t l) = ∑ l, v l * min 1 ((t / ε) * v l) := by
        apply Finset.sum_congr rfl
        intro l hl
        dsimp [Y]
        congr 2
        ring
      _ = (t / ε) * g (t / ε) := hscale (t / ε) hte
  have hderiv_pos {t : ℝ} (ht : 0 < t) (htc : t < ε * c) :
      0 < 2 * (∑ l, v l * Y t l - t) := by
    have htc' : t / ε < c := (div_lt_iff₀ hε0).2 (by nlinarith [htc])
    have hgt : ε < g (t / ε) := by
      by_cases hgr : g (t / ε) < 1
      · have hs := hg_strict (div_pos ht hε0) htc' hgr
        rw [hgc] at hs
        exact hs
      · exact hε1.trans_le (le_of_not_gt hgr)
    rw [hYscale t ht]
    have hte : ε * (t / ε) = t := by field_simp
    nlinarith
  have hderiv_neg {t : ℝ} (htc : ε * c < t) :
      2 * (∑ l, v l * Y t l - t) < 0 := by
    have htc' : c < t / ε := (lt_div_iff₀ hε0).2 (by nlinarith [htc])
    have hgt : g (t / ε) < ε := by
      have hs := hg_strict hc htc' (by rw [hgc]; exact hε1)
      rw [hgc] at hs
      exact hs
    rw [hYscale t (by nlinarith [htc, hε0, hc])]
    have hte : ε * (t / ε) = t := by field_simp
    nlinarith
  have hJmono : MonotoneOn J (Set.Icc (0 : ℝ) (ε * c)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (ε * c))
      (fun t ht => (hJcont t ht.1).mono (fun _ hx => hx.1))
    · intro t ht
      exact (hJderiv t).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) (ε * c) := by
        simpa only [interior_Icc] using ht
      exact (le_of_lt (hderiv_pos ht'.1 ht'.2))
  have hJanti : AntitoneOn J (Set.Ici (ε * c)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (ε * c))
    · intro t ht
      exact (hJderiv t).continuousAt.continuousWithinAt
    · intro t ht
      exact (hJderiv t).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Ioi (ε * c) := by simpa only [interior_Ici] using ht
      exact le_of_lt (hderiv_neg ht')
  have hJmax {t : ℝ} (ht : 0 ≤ t) : J t ≤ J (ε * c) := by
    rcases le_total t (ε * c) with hle | hle
    · apply hJmono
      · exact ⟨ht, hle⟩
      · exact ⟨le_of_lt (mul_pos hε0 hc), le_rfl⟩
      · exact hle
    · apply hJanti
      · exact (show ε * c ≤ ε * c from le_rfl)
      · exact (show ε * c ≤ t from hle)
      · exact hle
  have hJscale (q : ℝ) : J (ε * q) = ε * K q := by
    have hYq (l : ι) : Y (ε * q) l = X q l := by
      dsimp [Y, X]
      rw [show ε * q * v l / ε = q * v l by field_simp]
    dsimp [J, K]
    simp_rw [hYq]
    have hsum :
        (∑ x, (2 * (ε * q) * v x * X q x - ε * X q x ^ 2)) =
          ε * ∑ x, (2 * q * v x * X q x - X q x ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [hsum]
    ring
  have hKmax {q : ℝ} (hq : 0 ≤ q) : K q ≤ K c := by
    have hJq := hJmax (mul_nonneg hε0.le hq)
    rw [hJscale q, hJscale c] at hJq
    nlinarith [hJq]
  have hsumfactor (r : ℝ) :
      (∑ l, (2 * r * v l * X c l - (X c l) ^ 2)) =
        2 * r * (∑ l, v l * X c l) - ∑ l, (X c l) ^ 2 := by
    rw [Finset.sum_sub_distrib]
    congr 1
    calc
      (∑ l, 2 * r * v l * X c l) = ∑ l, (2 * r) * (v l * X c l) := by
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = 2 * r * (∑ l, v l * X c l) := by rw [Finset.mul_sum]
  have hmax : ∀ x, (∀ l, 0 ≤ x l ∧ x l ≤ 1) → F x ≤ F (X c) := by
    intro x hx
    let A : ℝ := ∑ l, v l * x l
    have hA : 0 ≤ A := Finset.sum_nonneg fun l _ =>
      mul_nonneg (hvpos l).le (hx l).1
    let q : ℝ := A / ε
    have hq : 0 ≤ q := div_nonneg hA hε0.le
    have hscaled : ε * q = A := by
      dsimp [q]
      exact mul_div_cancel₀ A hε0.ne'
    have hinner : F x ≤ ε * K q := by
      have hsumle : (∑ l, (2 * q * v l * x l - (x l) ^ 2)) ≤
          ∑ l, (2 * q * v l * X q l - (X q l) ^ 2) :=
        Finset.sum_le_sum fun l _ => hcoordinate hq (hx l).1 (hx l).2
      have hsumx : (∑ l, (2 * q * v l * x l - (x l) ^ 2)) =
          2 * q * A - ∑ l, (x l) ^ 2 := by
        rw [Finset.sum_sub_distrib]
        congr 1
        calc
          (∑ l, 2 * q * v l * x l) = ∑ l, (2 * q) * (v l * x l) := by
            apply Finset.sum_congr rfl
            intro l _
            ring
          _ = 2 * q * A := by
            dsimp [A]
            rw [Finset.mul_sum]
      have hid : F x = ε * (-ε * q ^ 2 +
          ∑ l, (2 * q * v l * x l - (x l) ^ 2)) := by
        change A ^ 2 - ε * ∑ l, (x l) ^ 2 = _
        rw [hsumx, ← hscaled]
        ring
      rw [hid]
      dsimp [K]
      exact mul_le_mul_of_nonneg_left (add_le_add_right hsumle _) hε0.le
    have houter : ε * K q ≤ ε * K c :=
      mul_le_mul_of_nonneg_left (hKmax hq) hε0.le
    have hlinear := RHLinalg.sq_ge_linear' (∑ l, v l * X c l) (ε * c)
    have hfinal : ε * K c ≤ F (X c) := by
      calc
        ε * K c =
            (2 * (ε * c) * (∑ l, v l * X c l) - (ε * c) ^ 2) -
              ε * ∑ l, (X c l) ^ 2 := by
                dsimp [K]
                rw [hsumfactor c]
                ring
        _ ≤ (∑ l, v l * X c l) ^ 2 - ε * ∑ l, (X c l) ^ 2 :=
          sub_le_sub_right hlinear _
        _ = F (X c) := by rfl
    exact hinner.trans (houter.trans hfinal)
  have hvalue : F (X c) = ε * (S c) ^ 2 / (ε - d c) - ε * (H c).card := by
    dsimp [F]
    rw [hAstar, hXsq]
    calc
      (ε * c) ^ 2 - ε * ((H c).card + c ^ 2 * d c) =
          ε * c * (c * (ε - d c)) - ε * (H c).card := by ring
      _ = ε * c * S c - ε * (H c).card := by
        have hp : c * (ε - d c) = S c := (eq_div_iff hden.ne').1 hc_formula
        rw [hp]
      _ = ε * (S c / (ε - d c)) * S c - ε * (H c).card := by
        have hm : ε * c * S c = ε * (S c / (ε - d c)) * S c :=
          congrArg (fun z => ε * z * S c) hc_formula
        exact congrArg (fun z => z - ε * (H c).card) hm
      _ = ε * (S c) ^ 2 / (ε - d c) - ε * (H c).card := by
        ring
  refine ⟨c, ⟨hc, hgc, hXbounds, hmax, hdlt, hc_formula, hvalue⟩, ?_⟩
  intro q hq hqroot
  exact hroot_unique hq hqroot

#print axioms probe_threshold_optimization

end D5.S3.Estimation.ErrorExponents.ProbeThresholdOptimization
