/- GID: D5/S3/Analytic/OriginalSlitNome
   generality: I
   mirror-B: D5/B/S3/Analytic/OriginalSlitNome
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Subunit continuation of the native nome and rank-24 determinant on the Euler slit. -/

import D5.S3.Analytic.OriginalHalfBinomialNome
import D5.S3.Analytic.OriginalHalfBinomialPfaffNome
import Mathlib.Analysis.Complex.ReImTopology

/-! Subunit continuation of the native nome and rank-24 determinant on the Euler slit. -/

open Complex Filter Set
open scoped Topology

namespace D5.S3.Analytic.OriginalSlitNome
open OriginalHalfBinomialSlitPeriod
open OriginalHalfBinomialPfaffNome
open OriginalHalfBinomialNome
open OriginalHalfBinomialContinuation
open OriginalHalfBinomialDiskCorrection (disk)
open private tau_analyticAt from D5.S3.Analytic.OriginalHalfBinomialPfaffNome
open private ball_subset_slitDomain from D5.S3.Analytic.OriginalHalfBinomialSlitPeriod

noncomputable section

private def expNome (r : ℂ) : ℂ := Complex.exp (I * (Real.pi : ℂ) * tau r)

def puncturedSlit : Set ℂ := slitDomain \ {0}

private def nomeOffZero (r : ℂ) : ℂ := by
  classical
  exact if r ∈ doubleSlit then expNome r else negativeChartNome r

private theorem doubleSlit_open : IsOpen doubleSlit :=
  (Complex.isOpen_slitPlane.preimage (continuous_const.sub continuous_id)).inter
    Complex.isOpen_slitPlane

private theorem expNome_analytic {r : ℂ} (hr : r ∈ doubleSlit) :
    AnalyticAt ℂ expNome r :=
  (analyticAt_const.mul (tau_analyticAt hr)).cexp'

private theorem expNome_norm_lt_one {r : ℂ} (hr : r ∈ doubleSlit) :
    ‖expNome r‖ < 1 := by
  rw [expNome, Complex.norm_exp, Real.exp_lt_one_iff]
  simpa [Complex.mul_re, Complex.mul_im] using
    (neg_neg_of_pos (mul_pos Real.pi_pos (tau_im_pos hr)))

private theorem negative_of_not_doubleSlit {r : ℂ} (hr : r ∈ puncturedSlit)
    (h : r ∉ doubleSlit) : ∃ x : ℝ, r = (x : ℂ) ∧ x < 0 := by
  have hn : r ∉ Complex.slitPlane := fun hs => h ⟨hr.1, hs⟩
  have hre : r.re ≤ 0 := le_of_not_gt fun hp =>
    hn (Complex.mem_slitPlane_iff.2 (Or.inl hp))
  have him : r.im = 0 := by
    by_contra he
    exact hn (Complex.mem_slitPlane_iff.2 (Or.inr he))
  have hreal : r = (r.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  refine ⟨r.re, hreal, lt_of_le_of_ne hre ?_⟩
  intro he
  apply hr.2
  exact mem_singleton_iff.mpr (hreal.trans (by rw [he, ofReal_zero]))

private theorem offZero_analytic_norm {r : ℂ} (hr : r ∈ puncturedSlit) :
    AnalyticAt ℂ nomeOffZero r ∧ ‖nomeOffZero r‖ < 1 := by
  classical
  by_cases h : r ∈ doubleSlit
  · refine ⟨(expNome_analytic h).congr ?_, ?_⟩
    · filter_upwards [doubleSlit_open.mem_nhds h] with z hz
      simp [nomeOffZero, hz]
    · simpa [nomeOffZero, h] using expNome_norm_lt_one h
  · obtain ⟨x, hx, hxlt⟩ := negative_of_not_doubleSlit hr h
    subst r
    obtain ⟨U, hU, hxU, han, hnorm, hmatch, _⟩ := negative_real_nome_extension x hxlt
    refine ⟨(han _ hxU).congr ?_, ?_⟩
    · filter_upwards [hU.mem_nhds hxU] with z hz
      by_cases hz' : z ∈ doubleSlit
      · simpa [nomeOffZero, hz', expNome] using hmatch z ⟨hz, hz'⟩
      · simp [nomeOffZero, hz']
    · simpa [nomeOffZero, h] using hnorm _ hxU

private theorem slitDisk_sub {z : ℂ} (hz : z ∈ slitDisk) : z ∈ doubleSlit :=
  ⟨ball_subset_slitDomain hz.1, hz.2⟩

private theorem midpoint_mem_slitDisk : (1 / 2 : ℂ) ∈ slitDisk := by
  constructor
  · norm_num [disk, Metric.mem_ball, Complex.norm_div]
  · exact Complex.mem_slitPlane_iff.2 (Or.inl (by norm_num))

private theorem slitDisk_preconnected : IsPreconnected slitDisk := by
  have hm := midpoint_mem_slitDisk
  have hSlit : StarConvex ℝ (1 / 2 : ℂ) Complex.slitPlane := by
    have hmid : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by norm_num
    rw [← hmid]
    exact Complex.starConvex_ofReal_slitPlane (by norm_num : (0 : ℝ) < 1 / 2)
  have hStar := ((convex_ball (0 : ℂ) 1).starConvex hm.1).inter hSlit
  exact (hStar.isPathConnected hm).isConnected.isPreconnected

private theorem qDisk_eq_expNome : EqOn Q0 expNome slitDisk := by
  have hQ : AnalyticOnNhd ℂ Q0 slitDisk :=
    (actual_nome_disk.1.analyticOnNhd Metric.isOpen_ball).mono inter_subset_left
  have hExp : AnalyticOnNhd ℂ expNome slitDisk := fun _ hz => expNome_analytic (slitDisk_sub hz)
  have hm := midpoint_mem_slitDisk
  apply hQ.eqOn_of_preconnected_of_eventuallyEq hExp slitDisk_preconnected hm
  have hmo : (1 / 2 : ℂ) ∈ lens := by
    constructor
    · exact hm.1
    · have hdist : dist (1 / 2 : ℂ) 1 = 1 / 2 := by
        rw [dist_eq_norm, show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by ring, norm_neg]
        norm_num [Complex.norm_div]
      rw [Metric.mem_ball, hdist]
      norm_num
  have hLens : IsOpen lens := Metric.isOpen_ball.inter Metric.isOpen_ball
  filter_upwards [hLens.mem_nhds hmo] with z hz
  have hd : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz.1
  have hc : ‖1 - z‖ < 1 := by
    simpa only [Metric.mem_ball, dist_comm z, dist_eq_norm] using hz.2
  rw [actual_nome_source.1 z hz, expNome, OriginalHalfBinomialWronskian.tau, tau,
    slitPeriod_eq_period hd, slitPeriod_eq_period hc]

private theorem disk_eq_offZero : EqOn Q0 nomeOffZero (disk \ {0}) := by
  classical
  have hsub : disk \ {0} ⊆ puncturedSlit := fun _ hz =>
    ⟨ball_subset_slitDomain hz.1, hz.2⟩
  have hopen : IsOpen (disk \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hnonreal : Dense {z : ℂ | z.im ≠ 0} := by
    have he : {z : ℂ | z.im ≠ 0} = im ⁻¹' ({0}ᶜ : Set ℝ) := rfl
    rw [he]
    intro z
    rw [closure_preimage_im]
    exact (dense_compl_singleton (0 : ℝ)) z.im
  have heq : EqOn Q0 nomeOffZero ((disk \ {0}) ∩ {z : ℂ | z.im ≠ 0}) := by
    intro z hz
    have hs : z ∈ slitDisk := ⟨hz.1.1, Complex.mem_slitPlane_iff.2 (Or.inr hz.2)⟩
    simpa [nomeOffZero, slitDisk_sub hs] using qDisk_eq_expNome hs
  apply heq.of_subset_closure (actual_nome_disk.1.continuousOn.mono sdiff_subset)
    (fun _ hz => (offZero_analytic_norm (hsub hz)).1.continuousAt.continuousWithinAt)
    inter_subset_left
  exact fun z hz => hopen.inter_closure ⟨hz, hnonreal z⟩

/-- The original lattice nome glued from the two Euler period expressions
and taking its native value at the cusp. -/
def slitNome (r : ℂ) : ℂ := if r = 0 then 0 else nomeOffZero r

theorem slitNome_eq_Q0 : EqOn slitNome Q0 disk := by
  intro r hr
  by_cases h : r = 0
  · subst r
    simp [slitNome, Q0]
  · simpa [slitNome, h] using (disk_eq_offZero ⟨hr, h⟩).symm

theorem slitNome_eq_exp {r : ℂ} (hr : r ∈ doubleSlit) :
    slitNome r = Complex.exp (I * (Real.pi : ℂ) * tau r) := by
  have hn : r ≠ 0 := fun he => by simpa [he] using hr.2
  simp [slitNome, hn, nomeOffZero, hr, expNome]

theorem slitNome_analyticOnNhd : AnalyticOnNhd ℂ slitNome slitDomain := by
  intro r hr
  by_cases hn : r = 0
  · subst r
    have hzero : (0 : ℂ) ∈ disk := Metric.mem_ball_self zero_lt_one
    apply ((actual_nome_disk.1.analyticOnNhd Metric.isOpen_ball) 0 hzero).congr
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz
    exact (slitNome_eq_Q0 hz).symm
  · apply (offZero_analytic_norm ⟨hr, hn⟩).1.congr
    filter_upwards [eventually_ne_nhds hn] with z hz
    simp [slitNome, hz]

theorem slitNome_norm_lt_one {r : ℂ} (hr : r ∈ slitDomain) :
    ‖slitNome r‖ < 1 := by
  by_cases hn : r = 0
  · simp [slitNome, hn]
  · simpa [slitNome, hn] using (offZero_analytic_norm ⟨hr, hn⟩).2

/-- The rank-24 scalar determinant in the sewn Gaussian chart. -/
def rank24Determinant (r : ℂ) : ℂ :=
  ((1 - r) ^ (3 : ℕ))⁻¹ * (slitPeriod r ^ (12 : ℕ))⁻¹

theorem rank24Determinant_analyticOnNhd :
    AnalyticOnNhd ℂ rank24Determinant slitDomain := by
  intro r hr
  have h₁ : 1 - r ≠ 0 := fun h => Complex.zero_notMem_slitPlane (h ▸ hr)
  have h₂ := slitPeriod_ne_zero hr
  exact (((analyticAt_const.sub analyticAt_id).pow 3).inv (pow_ne_zero 3 h₁)).mul
    (((slitPeriod_analyticOnNhd _ hr).pow 12).inv (pow_ne_zero 12 h₂))

#print axioms rank24Determinant_analyticOnNhd
#print axioms slitNome_eq_Q0
#print axioms slitNome_eq_exp
#print axioms slitNome_analyticOnNhd
#print axioms slitNome_norm_lt_one

end
end D5.S3.Analytic.OriginalSlitNome
