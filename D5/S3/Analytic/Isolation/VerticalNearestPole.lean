/- GID: D5/S3/Analytic/Isolation/VerticalNearestPole
   generality: G
   mirror-B: D5/B/S3/Analytic/Isolation/VerticalNearestPole
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vertical perturbation separates the nearest point of a locally discrete spectrum. -/

import D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue
import Mathlib.Analysis.Complex.RemovableSingularity

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic.Linarith

/-! # Nearest points after a small vertical displacement

A finite set strictly to the left of a vertical line has only finitely many
heights at which distances to distinct points agree. Local discreteness turns
the part of a spectrum in a compact positive-half-plane disk into such a finite
set. An arbitrarily small vertical displacement therefore isolates one nearest point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

open D5.S3.Analytic.Boundary.WeightedLogDerivativeResidue

namespace D5.S3.Analytic.Isolation.VerticalNearestPole

/-- The center with prescribed real coordinate and height. -/
def verticalCenter (σ t : ℝ) : ℂ := ⟨σ, t⟩

private theorem equal_distance_heights_subsingleton {σ : ℝ} {a b : ℂ}
    (ha : a.re < σ) (hb : b.re < σ) (hab : a ≠ b) :
    ({t : ℝ | dist (verticalCenter σ t) a =
      dist (verticalCenter σ t) b} : Set ℝ).Subsingleton := by
  intro t ht u hu
  have hsq (v : ℝ) :
      dist (verticalCenter σ v) a ^ 2 = (σ - a.re) ^ 2 + (v - a.im) ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp only [verticalCenter, Complex.sub_re, Complex.sub_im, pow_two]
  have hsqb (v : ℝ) :
      dist (verticalCenter σ v) b ^ 2 = (σ - b.re) ^ 2 + (v - b.im) ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp only [verticalCenter, Complex.sub_re, Complex.sub_im, pow_two]
  have ht' := congrArg (fun x : ℝ => x ^ 2) ht
  have hu' := congrArg (fun x : ℝ => x ^ 2) hu
  rw [hsq, hsqb] at ht' hu'
  by_contra htu
  have hprod : (t - u) * (a.im - b.im) = 0 := by nlinarith
  have him : a.im = b.im :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr htu))
  have hreal : (a.re - b.re) * (2 * σ - a.re - b.re) = 0 := by
    rw [him] at ht'
    nlinarith
  have hsecond : 2 * σ - a.re - b.re ≠ 0 := by linarith
  have hre : a.re = b.re :=
    sub_eq_zero.mp ((mul_eq_zero.mp hreal).resolve_right hsecond)
  exact hab (Complex.ext hre him)

private theorem finite_vertical_distance_separation {F : Set ℂ} (hF : F.Finite)
    {σ a b : ℝ} (hleft : ∀ z ∈ F, z.re < σ) (hab : a < b) :
    ∃ t ∈ Ioo a b, ∀ z ∈ F, ∀ w ∈ F,
      dist (verticalCenter σ t) z = dist (verticalCenter σ t) w → z = w := by
  let P : Set (ℂ × ℂ) := {p ∈ F ×ˢ F | p.1 ≠ p.2}
  let bad : Set ℝ := ⋃ p ∈ P,
    {t | dist (verticalCenter σ t) p.1 = dist (verticalCenter σ t) p.2}
  have hP : P.Finite := (hF.prod hF).subset fun _ hp => hp.1
  have hbad : bad.Finite := hP.biUnion fun p hp =>
    (equal_distance_heights_subsingleton (hleft _ hp.1.1)
      (hleft _ hp.1.2) hp.2).finite
  obtain ⟨t, ht, htbad⟩ := ((Ioo_infinite hab).sdiff hbad).nonempty
  refine ⟨t, ht, fun z hz w hw he => ?_⟩
  by_contra hzw
  exact htbad (mem_iUnion₂.mpr ⟨(z, w), ⟨⟨hz, hw⟩, hzw⟩, he⟩)

private theorem finite_in_positive_disk {Z : Set ℂ}
    (hdiscrete : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z)
    {c : ℂ} {R : ℝ} (hR : R < c.re) : (Z ∩ closedBall c R).Finite := by
  have hpos (w : ℂ) (hw : w ∈ closedBall c R) : 0 < w.re := by
    have hnorm : ‖w - c‖ ≤ R := by
      simpa only [dist_eq_norm] using mem_closedBall.mp hw
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (w - c)).trans hnorm)).1
    simp only [Complex.sub_re] at hre
    linarith
  have hcodiscrete : Zᶜ ∈ codiscreteWithin (closedBall c R) := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro w hw
    exact mem_of_superset (hdiscrete w (hpos w hw)) fun _ hz => Or.inl hz
  have hfinite := (isCompact_closedBall c R).finite_sdiff_of_mem_codiscreteWithin
    hcodiscrete
  simpa only [Set.sdiff_compl, inter_comm] using hfinite

private theorem finite_strict_minimum_gap {α : Type*} {F : Set α} (hF : F.Finite)
    {f : α → ℝ} {z : α} {D : ℝ} (hD : f z < D)
    (hstrict : ∀ w ∈ F \ {z}, f z < f w) :
    ∃ R : ℝ, f z < R ∧ R ≤ D ∧ ∀ w ∈ F \ {z}, R ≤ f w := by
  classical
  rcases (F \ {z}).eq_empty_or_nonempty with he | hne
  · refine ⟨D, hD, le_rfl, fun w hw => ?_⟩
    simp only [he, mem_empty_iff_false] at hw
  · obtain ⟨w, hw, hwmin⟩ := Set.exists_min_image (F \ {z}) f
      (hF.subset sdiff_subset) hne
    exact ⟨min D (f w), lt_min hD (hstrict w hw), min_le_left _ _,
      fun v hv => (min_le_right _ _).trans (hwmin v hv)⟩

/-- A locally discrete spectrum admits an isolated nearest point after an
arbitrarily small vertical perturbation, inside any horizontally accessible disk. -/
theorem isolated_nearest_of_vertical_perturbation {Z : Set ℂ}
    (hdiscrete : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z)
    {σ D ε : ℝ} (hleft : ∀ z ∈ Z, z.re < σ) (hD : D < σ)
    (hε : 0 < ε) {z₀ : ℂ} (hz₀ : z₀ ∈ Z) (haccessible : σ - z₀.re < D) :
    ∃ t : ℝ, |t - z₀.im| < ε ∧ ∃ z ∈ Z, ∃ R : ℝ,
      dist (verticalCenter σ t) z < R ∧ R ≤ D ∧
        ∀ w ∈ Z, w ∈ ball (verticalCenter σ t) R → w = z := by
  let η := min ε (min (D - (σ - z₀.re)) (σ - D) / 2)
  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min hε (half_pos (lt_min (by linarith) (by linarith)))
  have hηε : η ≤ ε := min_le_left _ _
  have hηhalf : η ≤ min (D - (σ - z₀.re)) (σ - D) / 2 := min_le_right _ _
  have hηaccess : 2 * η ≤ D - (σ - z₀.re) := by
    have h := min_le_left (D - (σ - z₀.re)) (σ - D)
    linarith
  have hησ : 2 * η ≤ σ - D := by
    have h := min_le_right (D - (σ - z₀.re)) (σ - D)
    linarith
  let c₀ := verticalCenter σ z₀.im
  let F := Z ∩ closedBall c₀ (D + η)
  have hF : F.Finite := finite_in_positive_disk hdiscrete (by
    change D + η < σ
    linarith)
  obtain ⟨t, ht, hseparate⟩ := finite_vertical_distance_separation hF
    (fun z hz => hleft z hz.1) (show z₀.im - η < z₀.im + η by linarith)
  let c := verticalCenter σ t
  have htη : |t - z₀.im| < η := abs_sub_lt_iff.mpr ⟨by linarith [ht.2],
    by linarith [ht.1]⟩
  have hcc : dist c c₀ < η := by
    have hdist : dist c c₀ = |t - z₀.im| := by
      rw [dist_eq_norm]
      have he : c - c₀ = ((t - z₀.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [c, c₀, verticalCenter]
      rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rwa [hdist]
  have hcz : dist c₀ z₀ = σ - z₀.re := by
    rw [dist_eq_norm]
    have he : c₀ - z₀ = ((σ - z₀.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c₀, verticalCenter]
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (sub_pos.mpr (hleft z₀ hz₀))
  have hzF : z₀ ∈ F := ⟨hz₀, mem_closedBall.mpr (by
    rw [dist_comm, hcz]
    linarith)⟩
  obtain ⟨z, hzF', hzmin⟩ := Set.exists_min_image F (dist c) hF ⟨z₀, hzF⟩
  have hnear : dist c z < D := by
    have htri := dist_triangle c c₀ z₀
    rw [hcz] at htri
    have hm := hzmin z₀ hzF
    linarith
  have hstrict : ∀ w ∈ F \ {z}, dist c z < dist c w := by
    intro w hw
    have hwne : w ≠ z := hw.2
    exact lt_of_le_of_ne (hzmin w hw.1) fun he => hwne
      (hseparate w hw.1 z hzF' he.symm)
  obtain ⟨R, hRnear, hRD, hRgap⟩ := finite_strict_minimum_gap hF hnear hstrict
  refine ⟨t, htη.trans_le hηε, z, hzF'.1, R, hRnear, hRD, fun w hw hwR => ?_⟩
  have hwF : w ∈ F := ⟨hw, mem_closedBall.mpr (by
    have htri := dist_triangle w c c₀
    have hwR' := mem_ball.mp hwR
    linarith)⟩
  by_contra hwz
  have hge := hRgap w ⟨hwF, hwz⟩
  have hlt := mem_ball.mp hwR
  rw [dist_comm] at hlt
  exact (not_lt_of_ge hge) hlt

private theorem real_of_horizontal_distance_bound {σ D : ℝ} {z : ℂ}
    (hleft : z.re < σ) (hupper : dist (σ : ℂ) z ≤ D)
    (hlower : D ≤ σ - z.re) : z = ((σ - D : ℝ) : ℂ) := by
  have hD : 0 ≤ D := dist_nonneg.trans hupper
  have hsq : dist (σ : ℂ) z ^ 2 = (σ - z.re) ^ 2 + z.im ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_sub, neg_mul_neg, pow_two]
  have hdist : 0 ≤ dist (σ : ℂ) z := dist_nonneg
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
  have hre : z.re = σ - D := by nlinarith
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using hre
  · simpa only [Complex.ofReal_im] using him

/-- A real center has either a zero-free disk with a horizontally accessible
spectral point, or an isolated real spectral point to the right of the threshold. -/
theorem real_center_spectral_dichotomy {Z : Set ℂ}
    (hdiscrete : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z)
    {σ θ : ℝ} (hleft : ∀ z ∈ Z, z.re < σ) (hθ : 0 < θ)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Z) (hthreshold : θ < z₀.re) :
    (∃ D : ℝ, 0 < D ∧ D ≤ σ - θ ∧
      (∀ w ∈ Z, D ≤ dist (σ : ℂ) w) ∧ ∃ z ∈ Z, σ - z.re < D) ∨
    (∃ β : ℝ, (β : ℂ) ∈ Z ∧ θ < β ∧ ∃ R : ℝ,
      σ - β < R ∧ R ≤ σ - θ ∧ ∀ w ∈ Z,
        w ∈ ball (σ : ℂ) R → w = (β : ℂ)) := by
  have hθσ : θ < σ := hthreshold.trans (hleft z₀ hz₀)
  let F := Z ∩ closedBall (σ : ℂ) (σ - θ)
  have hF : F.Finite := finite_in_positive_disk hdiscrete (by
    simpa only [Complex.ofReal_re] using sub_lt_self σ hθ)
  rcases F.eq_empty_or_nonempty with hempty | hnonempty
  · left
    refine ⟨σ - θ, sub_pos.mpr hθσ, le_rfl, fun w hw => ?_, z₀, hz₀,
      by linarith⟩
    by_contra h
    have hwF : w ∈ F := ⟨hw, mem_closedBall.mpr (by
      rw [dist_comm]
      exact (lt_of_not_ge h).le)⟩
    simp only [hempty, mem_empty_iff_false] at hwF
  · obtain ⟨z, hzF, hzmin⟩ := Set.exists_min_image F (dist (σ : ℂ)) hF hnonempty
    let d := dist (σ : ℂ) z
    have hdz : 0 < d := dist_pos.mpr (by
      intro h
      have hzre : z.re = σ := by rw [← h]; rfl
      exact (hleft z hzF.1).ne hzre)
    have hdle : d ≤ σ - θ := by
      simpa only [d, dist_comm] using mem_closedBall.mp hzF.2
    have hfree : ∀ w ∈ Z, d ≤ dist (σ : ℂ) w := by
      intro w hw
      by_contra h
      have hlt : dist (σ : ℂ) w < d := lt_of_not_ge h
      have hwF : w ∈ F := ⟨hw, mem_closedBall.mpr (by
        rw [dist_comm]
        exact hlt.le.trans hdle)⟩
      exact (not_lt_of_ge (hzmin w hwF)) hlt
    by_cases haccessible : ∃ w ∈ Z, σ - w.re < d
    · exact Or.inl ⟨d, hdz, hdle, hfree, haccessible⟩
    · have hhorizontal : ∀ w ∈ Z, d ≤ σ - w.re := by
        intro w hw
        by_contra h
        exact haccessible ⟨w, hw, lt_of_not_ge h⟩
      have hreal : z = ((σ - d : ℝ) : ℂ) :=
        real_of_horizontal_distance_bound (hleft z hzF.1) le_rfl (hhorizontal z hzF.1)
      have hdlt : d < σ - θ := (hhorizontal z₀ hz₀).trans_lt (by linarith)
      have hstrict : ∀ w ∈ F \ {z}, d < dist (σ : ℂ) w := by
        intro w hw
        have hge := hzmin w hw.1
        rcases lt_or_eq_of_le hge with hlt | heq
        · exact hlt
        · have hwreal : w = ((σ - d : ℝ) : ℂ) :=
            real_of_horizontal_distance_bound (hleft w hw.1.1) heq.symm.le
              (hhorizontal w hw.1.1)
          exact False.elim (hw.2 (hwreal.trans hreal.symm))
      obtain ⟨R, hRd, hRbound, hRgap⟩ :=
        finite_strict_minimum_gap (f := dist (σ : ℂ)) (z := z) hF hdlt hstrict
      refine Or.inr ⟨σ - d, hreal ▸ hzF.1, by linarith, R, ?_, hRbound,
        fun w hw hwR => ?_⟩
      · simpa only [sub_sub_cancel] using hRd
      · have hwF : w ∈ F := ⟨hw,
          mem_closedBall.mpr ((mem_ball.mp hwR).le.trans hRbound)⟩
        by_contra hwreal
        have hwz : w ≠ z := by simpa only [hreal] using hwreal
        have hge := hRgap w ⟨hwF, hwz⟩
        have hlt := mem_ball.mp hwR
        rw [dist_comm] at hlt
        exact (not_lt_of_ge hge) hlt


/-- Multiplying a local simple principal part by an analytic weight separates
its value at the pole from an analytic divided-difference remainder. -/
private theorem analytic_weight_principal_part {F H w b : ℂ → ℂ} {r c : ℂ}
    (hH : AnalyticAt ℂ H r) (hw : AnalyticAt ℂ w r) (hb : AnalyticAt ℂ b r)
    (hF : F =ᶠ[𝓝[≠] r] fun z => c / (z - r) + H z) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R r ∧
      (fun z => w z * F z + b z) =ᶠ[𝓝[≠] r]
        fun z => (w r * c) / (z - r) + R z := by
  have hw0 := hw
  obtain ⟨p, hp⟩ := hw
  have hq : AnalyticAt ℂ (dslope w r) r :=
    ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  refine ⟨fun z => c * dslope w r z + w z * H z + b z,
    ((analyticAt_const.mul hq).add (hw0.mul hH)).add hb, ?_⟩
  filter_upwards [hF, self_mem_nhdsWithin] with z hz hzr
  rw [hz, dslope_of_ne _ hzr, slope_def_field]
  field_simp [sub_ne_zero.mpr hzr]
  ring

/-- Every zero of a finite analytic family with positive real weights gives a
nonzero simple pole, including after a common nonvanishing analytic factor and
an arbitrary analytic correction. The residue uses actual analytic orders. -/
private theorem positive_log_deriv_analytic_weight_pole {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) (a : ι → ℝ) (w b : ℂ → ℂ) (r : ℂ)
    (hf : ∀ i, AnalyticAt ℂ (f i) r)
    (hn : ∀ i, ¬ ∀ᶠ z in 𝓝 r, f i z = 0)
    (ha : ∀ i, 0 < a i) (hzero : ∃ i, f i r = 0)
    (hw : AnalyticAt ℂ w r) (hwn : w r ≠ 0) (hb : AnalyticAt ℂ b r) :
    let c : ℝ := ∑ i, a i * analyticOrderNatAt (f i) r
    let F : ℂ → ℂ := fun z => w z * ∑ i, (a i : ℂ) * logDeriv (f i) z + b z
    0 < c ∧ w r * (c : ℂ) ≠ 0 ∧
      (∃ R : ℂ → ℂ, AnalyticAt ℂ R r ∧
        F =ᶠ[𝓝[≠] r] fun z => (w r * (c : ℂ)) / (z - r) + R z) ∧
      meromorphicOrderAt F r = -1 := by
  classical
  dsimp only
  let m : ι → ℕ := fun i => analyticOrderNatAt (f i) r
  have hfinite (i : ι) : analyticOrderAt (f i) r ≠ ⊤ := by
    exact fun h => hn i (analyticOrderAt_eq_top.mp h)
  have hm (i : ι) : meromorphicOrderAt (f i) r = (m i : ℤ) := by
    rw [(hf i).meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt (hfinite i)]
    simp only [ENat.map_natCast]
    rfl
  have hmzero (i : ι) : m i = 0 ↔ f i r ≠ 0 := by
    rw [← (hf i).analyticOrderAt_eq_zero,
      ← Nat.cast_analyticOrderNatAt (hfinite i)]
    exact_mod_cast Iff.rfl
  let c : ℝ := ∑ i, a i * (m i : ℝ)
  have hc : 0 < c := by
    obtain ⟨i, hi⟩ := hzero
    have hmi : 0 < m i := Nat.pos_of_ne_zero fun e => (hmzero i).mp e hi
    have hterm : 0 < a i * (m i : ℝ) := mul_pos (ha i) (by exact_mod_cast hmi)
    exact hterm.trans_le (Finset.single_le_sum (fun j _ =>
      mul_nonneg (ha j).le (Nat.cast_nonneg (m j))) (Finset.mem_univ i))
  have hcc : (∑ i, (a i : ℂ) * ((m i : ℤ) : ℂ)) = (c : ℂ) := by
    simp only [c, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast,
      Int.cast_natCast]
  let L : ℂ → ℂ := fun z => ∑ i, (a i : ℂ) * logDeriv (f i) z
  obtain ⟨⟨H, hH, hL⟩, hpole, _⟩ := weighted_log_deriv_residue Finset.univ f
    (fun i => (a i : ℂ)) (fun i => (m i : ℤ)) r
    (fun i _ => (hf i).meromorphicAt) (fun i _ => hm i)
  have hL' : L =ᶠ[𝓝[≠] r] fun z => (c : ℂ) / (z - r) + H z := by
    simpa only [L, hcc] using hL
  have hcne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have horderL : meromorphicOrderAt L r = -1 := by
    apply hpole.mpr
    rwa [hcc]
  have horderW : meromorphicOrderAt (w * L) r = -1 := by
    rw [meromorphicOrderAt_mul_of_ne_zero hw hwn, horderL]
  have horder : meromorphicOrderAt (w * L + b) r = -1 := by
    rw [meromorphicOrderAt_add_eq_left_of_lt hb.meromorphicAt, horderW]
    rw [horderW]
    have hlt : (-1 : WithTop ℤ) < 0 := by
      rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) by norm_cast,
        ← WithTop.coe_zero, WithTop.coe_lt_coe]
      norm_num
    exact lt_of_lt_of_le hlt hb.meromorphicOrderAt_nonneg
  refine ⟨hc, mul_ne_zero hwn hcne, ?_, horder⟩
  exact analytic_weight_principal_part hH hw hb hL'

/-- The divided difference removes the artificial pole at one before the
remaining factor at zero is divided out. -/
def regularizedLogFamily {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) (a : ι → ℝ) (K : ℂ) : ℂ → ℂ :=
  fun s => -(dslope (fun z => (∑ i, (a i : ℂ) * logDeriv (f i) z) -
    z * (∑ i, (a i : ℂ) * logDeriv (f i) 1) + K * (1 - z)) 1 s) / s

/-- The regularized finite family is analytic at every nonzero point where its
members are nonzero, including the normalization point one. At every nonzero zero its
residue is the positive weighted multiplicity times the common elementary
factor, so the pole cannot be removed by the normalization. -/
theorem regularized_positive_log_family {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) (a : ι → ℝ) (K : ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (h1 : ∀ i, f i 1 ≠ 0)
    (ha : ∀ i, 0 < a i) :
    (∀ s : ℂ, s ≠ 1 → regularizedLogFamily f a K s =
      -((∑ i, (a i : ℂ) * logDeriv (f i) s) -
        s * (∑ i, (a i : ℂ) * logDeriv (f i) 1) + K * (1 - s)) / (s * (s - 1))) ∧
    (∀ r : ℂ, r ≠ 0 → (∀ i, f i r ≠ 0) →
      AnalyticAt ℂ (regularizedLogFamily f a K) r) ∧
    (∀ r : ℂ, r ≠ 0 → (∃ i, f i r = 0) →
      let c : ℝ := ∑ i, a i * analyticOrderNatAt (f i) r
      0 < c ∧ (-1 / (r * (r - 1))) * (c : ℂ) ≠ 0 ∧
        (∃ R : ℂ → ℂ, AnalyticAt ℂ R r ∧
          regularizedLogFamily f a K =ᶠ[𝓝[≠] r]
            fun z => ((-1 / (r * (r - 1))) * (c : ℂ)) / (z - r) + R z) ∧
        meromorphicOrderAt (regularizedLogFamily f a K) r = -1) := by
  classical
  let L : ℂ → ℂ := fun z => ∑ i, (a i : ℂ) * logDeriv (f i) z
  let N : ℂ → ℂ := fun z => L z - z * L 1 + K * (1 - z)
  have hN1 : N 1 = 0 := by simp [N]
  have heq (s : ℂ) (hs : s ≠ 1) : regularizedLogFamily f a K s =
      -N s / (s * (s - 1)) := by
    change -(dslope N 1 s) / s = _
    rw [dslope_of_ne _ hs, slope_def_field, hN1, sub_zero]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  refine ⟨heq, ?_, ?_⟩
  · let V : Set ℂ := {z | ∀ i, f i z ≠ 0}
    have hV : IsOpen V := by
      convert isOpen_iInter_of_finite (fun i : ι =>
        isOpen_ne_fun (hf i).continuous
          (continuous_const : Continuous (fun _ : ℂ => (0 : ℂ)))) using 1
      ext z
      simp only [V, Set.mem_ofPred_eq, Set.mem_iInter]
    have hN : DifferentiableOn ℂ N V := by
      intro z hz
      have hL : AnalyticAt ℂ L z := by
        apply Finset.analyticAt_fun_sum
        intro i _
        have hi := (hf i).analyticAt z
        exact analyticAt_const.mul (hi.deriv.div hi (hz i))
      have hNa : AnalyticAt ℂ N z :=
        (hL.sub (analyticAt_id.mul analyticAt_const)).add
          (analyticAt_const.mul (analyticAt_const.sub analyticAt_id))
      exact hNa.differentiableAt.differentiableWithinAt
    have hD : DifferentiableOn ℂ (dslope N 1) V :=
      (Complex.differentiableOn_dslope (hV.mem_nhds h1)).mpr hN
    intro r hr hn
    exact (hD.analyticAt (hV.mem_nhds hn)).neg.div analyticAt_id hr
  · intro r hr hz
    dsimp only
    have hr1 : r ≠ 1 := by
      rintro rfl
      obtain ⟨i, hi⟩ := hz
      exact h1 i hi
    have hlocal (i : ι) : ¬ ∀ᶠ z in 𝓝 r, f i z = 0 := by
      intro hzero
      have hglobal : AnalyticOnNhd ℂ (f i) Set.univ := fun z _ => (hf i).analyticAt z
      exact h1 i (hglobal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ r) hzero (Set.mem_univ 1))
    let w : ℂ → ℂ := fun z => -1 / (z * (z - 1))
    let b : ℂ → ℂ := fun z => (z * L 1 - K * (1 - z)) / (z * (z - 1))
    have hden : r * (r - 1) ≠ 0 := mul_ne_zero hr (sub_ne_zero.mpr hr1)
    have hw : AnalyticAt ℂ w r := analyticAt_const.div
      (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)) hden
    have hwn : w r ≠ 0 := div_ne_zero (by norm_num) hden
    have hb : AnalyticAt ℂ b r :=
      ((analyticAt_id.mul analyticAt_const).sub
        (analyticAt_const.mul (analyticAt_const.sub analyticAt_id))).div
        (analyticAt_id.mul (analyticAt_id.sub analyticAt_const)) hden
    obtain ⟨hc, hcne, ⟨R, hR, hpart⟩, horder⟩ :=
      positive_log_deriv_analytic_weight_pole f a w b r
        (fun i => (hf i).analyticAt r) hlocal ha hz hw hwn hb
    have hsame : regularizedLogFamily f a K =ᶠ[𝓝[≠] r]
        fun z => w z * L z + b z := by
      have hne : ∀ᶠ z in 𝓝[≠] r, z ≠ 1 :=
        nhdsWithin_le_nhds (isOpen_ne.mem_nhds hr1)
      filter_upwards [hne] with z hz1
      rw [heq z hz1]
      dsimp only [N, w, b]
      ring
    refine ⟨hc, hcne, ⟨R, hR, hsame.trans hpart⟩, ?_⟩
    exact (meromorphicOrderAt_congr hsame).trans horder

end D5.S3.Analytic.Isolation.VerticalNearestPole
