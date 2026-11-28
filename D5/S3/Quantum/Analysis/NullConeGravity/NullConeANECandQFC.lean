/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullConeANECandQFC
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Global averaged null focusing rigidity and the quantum expansion. -/

import D5.S3.Geometry.Lorentz.SachsJacobsonEinstein4D
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology

namespace D5.S3.Quantum.Analysis.NullConeGravity.NullConeANECandQFC
open D5.S3.Geometry.Lorentz.SachsJacobsonEinstein4D

private theorem corrected_expansion_lower {θ σ ψ F : ℝ → ℝ} {M : ℝ}
    (he : ∀ x, ψ x = θ x + F x) (hF : ∀ x, |F x| ≤ M)
    (hd : ∀ x, HasDerivAt ψ (-(1/2) * θ x ^ 2 - σ x ^ 2) x) :
    ∀ x, -M ≤ ψ x := by
  have ha : Antitone ψ := by
    apply antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt)
    intro x
    rw [(hd x).deriv]
    nlinarith [sq_nonneg (θ x), sq_nonneg (σ x)]
  intro a
  by_contra! h
  -- The shifted corrected expansion is itself subject to a comparison NEC equation.
  let o : OpticalData :=
    { expansion := fun x => ψ (a + x) + M
      shear := fun _ => 0
      radius := fun _ => 0
      ricciTerm := fun x => θ (a + x) ^ 2 / 2 + σ (a + x) ^ 2 -
        (ψ (a + x) + M) ^ 2 / 2
      tideTerm := fun _ => 0 }
  have h₀ : o.expansion 0 < 0 := by dsimp [o]; rw [add_zero]; linarith
  let L := 2 / |o.expansion 0| + 1
  have hsol : SolvesOn o (Ico 0 L) := by
    constructor
    · intro x _
      have hc := ((hd (a + x)).comp x ((hasDerivAt_id x).const_add a)).add_const M
      convert hc using 1
      · rfl
      · simp [o]; ring
    · intro x _
      simpa [o] using (hasDerivAt_const x (0 : ℂ))
    · intro x _
      simpa [o] using (hasDerivAt_const x (0 : ℝ))
  have hnec (x : ℝ) (hx : x ∈ Ico 0 L) : 0 ≤ o.ricciTerm x := by
    have hψ := ha (show a ≤ a + x by linarith [hx.1])
    have hF' := (abs_le.mp (hF (a + x))).1
    have hle : θ (a + x) ≤ ψ (a + x) + M := by linarith [he (a+x)]
    have hneg : ψ (a + x) + M < 0 := by linarith
    dsimp [o]
    nlinarith [sq_nonneg (σ (a + x)),
      mul_nonneg (sub_nonneg.mpr hle)
        (show 0 ≤ -(θ (a+x) + (ψ (a+x) + M)) by linarith)]
  have hb := no_positive_optics_through_focal_bound hsol hnec h₀
  dsimp [L] at hb
  linarith

private theorem global_raychaudhuri_data {θ σ R : ℝ → ℝ}
    (hd : ∀ u, HasDerivAt θ (-(1/2) * θ u ^ 2 - σ u ^ 2 - R u) u)
    (hcR : Continuous R) (hiR : Integrable R) :
    Integrable (fun u => (1/2) * θ u ^ 2 + σ u ^ 2) ∧
      Tendsto θ atTop (𝓝 0) ∧ Tendsto θ atBot (𝓝 0) := by
  let F := fun u : ℝ => ∫ x in (0 : ℝ)..u, R x
  let M := ∫ x : ℝ, ‖R x‖
  let ψ := fun u => θ u + F u
  let q := fun u => (1/2) * θ u ^ 2 + σ u ^ 2
  have hF (x : ℝ) : |F x| ≤ M :=
    (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans
      (setIntegral_le_integral hiR.norm (ae_of_all _ fun _ => norm_nonneg _))
  have hFd (u : ℝ) : HasDerivAt F (R u) u :=
    intervalIntegral.integral_hasDerivAt_right hiR.intervalIntegrable
      hcR.stronglyMeasurable.stronglyMeasurableAtFilter hcR.continuousAt
  have hψ (u : ℝ) : HasDerivAt ψ (-(1/2) * θ u ^ 2 - σ u ^ 2) u := by
    convert (hd u).add (hFd u) using 1
    ring
  have hl := corrected_expansion_lower (θ := θ) (σ := σ) (ψ := ψ) (F := F)
    (fun _ => rfl) hF hψ
  have href (u : ℝ) : HasDerivAt (fun x => -ψ (-x))
      (-(1/2) * (-θ (-u)) ^ 2 - σ (-u) ^ 2) u := by
    convert ((hψ (-u)).comp u (hasDerivAt_id u).neg).neg using 1
    · rfl
    · ring
  have hu (u : ℝ) : ψ u ≤ M := by
    have h := corrected_expansion_lower (θ := fun x => -θ (-x)) (σ := fun x => σ (-x))
      (ψ := fun x => -ψ (-x)) (F := fun x => -F (-x))
      (fun x => by dsimp [ψ]; ring) (fun x => by rw [abs_neg]; exact hF (-x))
      href (-u)
    rw [neg_neg] at h
    linarith
  have hneg (u : ℝ) : HasDerivAt (fun x => -ψ x) (q u) u := by
    convert (hψ u).neg using 1
    dsimp [q]; ring
  have hq (u : ℝ) : 0 ≤ q u := by
    dsimp [q]
    positivity
  have hloc (a b : ℝ) : IntervalIntegrable q volume a b :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg
      (fun x _ => (hneg x).continuousAt.continuousWithinAt) (fun x _ => hneg x)
      (fun x _ => hq x)
  have hiq : Integrable q := by
    apply integrable_of_intervalIntegral_norm_bounded (2 * M)
      (a := fun x : ℝ => -x) (b := id) (l := atTop)
      (fun x => (hloc (-x) x).1) tendsto_neg_atTop_atBot tendsto_id
    apply Eventually.of_forall
    intro x
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hq _)]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hneg u) (hloc _ _)]
    dsimp
    linarith [hl x, hu (-x)]
  have hθ : Continuous θ := continuous_iff_continuousAt.2 fun u => (hd u).continuousAt
  have hiθsq : Integrable (fun u => θ u ^ 2) :=
    (hiq.const_mul 2).mono' (hθ.pow 2).aestronglyMeasurable
      (ae_of_all _ fun u => by
        dsimp [q]
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_nonneg (σ u)])
  have hid : Integrable (fun u => -(1/2) * θ u ^ 2 - σ u ^ 2 - R u) := by
    convert hiq.neg.sub hiR using 1
    ext u; dsimp [q]; ring
  have ht := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
    (a := 0) (fun x _ => hd x) hid.integrableOn
  have hb := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Iic
    (a := 0) (fun x _ => hd x) hid.integrableOn
  have ht0 : (limUnder atTop θ)^2 = 0 := by
    apply IntegrableAtFilter.eq_zero_of_tendsto (hiθsq.integrableAtFilter atTop) _ (ht.pow 2)
    intro s hs
    obtain ⟨b, hb'⟩ := mem_atTop_sets.1 hs
    rw [← top_le_iff, ← volume_Ici (a := b)]
    exact measure_mono hb'
  have hb0 : (limUnder atBot θ)^2 = 0 := by
    apply IntegrableAtFilter.eq_zero_of_tendsto (hiθsq.integrableAtFilter atBot) _ (hb.pow 2)
    intro s hs
    obtain ⟨b, hb'⟩ := mem_atBot_sets.1 hs
    rw [← top_le_iff, ← volume_Iic (a := b)]
    exact measure_mono hb'
  have ht' : limUnder atTop θ = 0 := by nlinarith
  have hb' : limUnder atBot θ = 0 := by nlinarith
  exact ⟨hiq, ht' ▸ ht, hb' ▸ hb⟩

/-- A globally regular expansion with an integrable Ricci term vanishes at both ends. -/
theorem raychaudhuri_global_tendsto_zero {θ σ R : ℝ → ℝ}
    (hd : ∀ u, HasDerivAt θ (-(1/2) * θ u ^ 2 - σ u ^ 2 - R u) u)
    (hcR : Continuous R) (hiR : Integrable R) :
    Tendsto θ atTop (𝓝 0) ∧ Tendsto θ atBot (𝓝 0) :=
  (global_raychaudhuri_data hd hcR hiR).2

/-- The exact whole-line integral of the nonnegative optical loss. -/
theorem raychaudhuri_global_anec_identity {θ σ R : ℝ → ℝ}
    (hd : ∀ u, HasDerivAt θ (-(1/2) * θ u ^ 2 - σ u ^ 2 - R u) u)
    (hcR : Continuous R) (hiR : Integrable R) :
    Integrable (fun u => (1/2) * θ u ^ 2 + σ u ^ 2) ∧
      (∫ u, (1/2) * θ u ^ 2 + σ u ^ 2) = -(∫ u, R u) := by
  obtain ⟨hi, ht, hb⟩ := global_raychaudhuri_data hd hcR hiR
  let q := fun u => (1/2) * θ u ^ 2 + σ u ^ 2
  have hd' (u : ℝ) : HasDerivAt θ (-q u - R u) u := by
    convert hd u using 1
    dsimp [q]; ring
  have h := integral_of_hasDerivAt_of_tendsto hd' (hi.neg.sub hiR) hb ht
  have hiq : Integrable q := hi
  have hsum : (∫ u, -q u - R u) = -(∫ u, q u) - (∫ u, R u) := by
    simpa only [Pi.neg_apply, integral_neg] using integral_sub hiq.neg hiR
  rw [hsum] at h
  refine ⟨hi, ?_⟩
  change (∫ u, q u) = _
  linarith

/-- Nonnegative averaged Ricci curvature forces both expansion and shear to vanish. -/
theorem anec_global_rigidity {θ σ R : ℝ → ℝ}
    (hd : ∀ u, HasDerivAt θ (-(1/2) * θ u ^ 2 - σ u ^ 2 - R u) u)
    (hcR : Continuous R) (hiR : Integrable R) (hanec : 0 ≤ ∫ u, R u) :
    (∀ u, θ u = 0) ∧ (∀ u, σ u = 0) ∧ (∫ u, R u) = 0 := by
  obtain ⟨hi, he⟩ := raychaudhuri_global_anec_identity hd hcR hiR
  have hn (u : ℝ) : 0 ≤ (1/2) * θ u ^ 2 + σ u ^ 2 := by positivity
  have h := integral_nonneg (μ := volume) (f := fun u => (1/2) * θ u ^ 2 + σ u ^ 2) hn
  have hz : (∫ u, (1/2) * θ u ^ 2 + σ u ^ 2) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg (f := fun u => (1/2) * θ u ^ 2 + σ u ^ 2) hn hi).1 hz
  have hθae : θ =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    change θ x = 0
    change (1/2) * θ x ^ 2 + σ x ^ 2 = 0 at hx
    nlinarith [sq_nonneg (σ x)]
  have hθ : θ = 0 := Measure.eq_of_ae_eq hθae
    (continuous_iff_continuousAt.2 fun u => (hd u).continuousAt) continuous_zero
  have hRae : R =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    have hdx := (hd x).deriv
    rw [hθ] at hdx
    simp only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_sub,
      deriv_zero] at hdx
    change (1/2) * θ x ^ 2 + σ x ^ 2 = 0 at hx
    rw [hθ] at hx
    change R x = 0
    simp at hx
    rw [hx] at hdx
    simpa using hdx.symm
  have hR : R = 0 := Measure.eq_of_ae_eq hRae hcR continuous_zero
  refine ⟨fun u => congrFun hθ u, fun u => ?_, by linarith⟩
  have hdu := (hd u).deriv
  rw [hθ, hR] at hdu
  simp at hdu
  simpa using hdu

/-- Strict ANEC excludes every globally regular solution of the optical equation. -/
theorem strict_anec_forces_caustic {σ R : ℝ → ℝ} (hcR : Continuous R)
    (hiR : Integrable R) (hanec : 0 < ∫ u, R u) :
    ¬ ∃ θ : ℝ → ℝ, ∀ u, HasDerivAt θ (-(1/2) * θ u ^ 2 - σ u ^ 2 - R u) u := by
  rintro ⟨θ, hd⟩
  exact hanec.ne' (anec_global_rigidity hd hcR hiR hanec.le).2.2

/-- Pointwise NEC and global regularity force exact optical and Ricci rigidity. -/
theorem nec_and_global_forces_zero_ricci {θ σ R : ℝ → ℝ}
    (hd : ∀ u, HasDerivAt θ (-(1/2) * θ u ^ 2 - σ u ^ 2 - R u) u)
    (hcR : Continuous R) (hiR : Integrable R) (hnec : ∀ u, 0 ≤ R u) :
    (∀ u, θ u = 0) ∧ (∀ u, σ u = 0) ∧ (∀ u, R u = 0) := by
  obtain ⟨hθ, hσ, _⟩ := anec_global_rigidity hd hcR hiR (integral_nonneg hnec)
  refine ⟨hθ, hσ, fun u => ?_⟩
  have hθ' : θ = 0 := funext hθ
  have h := (hd u).deriv
  rw [hθ', hσ u] at h
  simpa using h

/-- The generalized entropy along an affine generator. -/
def generalizedEntropy (G ħ : ℝ) (A S : ℝ → ℝ) (u : ℝ) : ℝ :=
  A u / (4 * G * ħ) + S u

/-- The area-normalized derivative of generalized entropy. -/
def quantumExpansion (G ħ : ℝ) (A S : ℝ → ℝ) (u : ℝ) : ℝ :=
  4 * G * ħ / A u * deriv (generalizedEntropy G ħ A S) u

theorem quantum_expansion_eq {G ħ : ℝ} {A S θ : ℝ → ℝ} {u : ℝ}
    (hG : 0 < G) (hħ : 0 < ħ) (hA : 0 < A u)
    (hdA : HasDerivAt A (θ u * A u) u) (hdS : DifferentiableAt ℝ S u) :
    quantumExpansion G ħ A S u = θ u + 4 * G * ħ / A u * deriv S u := by
  have hd := (hdA.div_const (4 * G * ħ)).add hdS.hasDerivAt
  unfold quantumExpansion
  have hg : HasDerivAt (generalizedEntropy G ħ A S)
      (θ u * A u / (4 * G * ħ) + deriv S u) u := hd
  rw [hg.deriv]
  field_simp [hA.ne', hG.ne', hħ.ne']

theorem quantum_expansion_deriv {G ħ : ℝ} {A S θ σ T : ℝ → ℝ} {u : ℝ}
    (hG : 0 < G) (hħ : 0 < ħ)
    (hA : ∀ v, 0 < A v) (hdA : ∀ v, HasDerivAt A (θ v * A v) v)
    (hdS : Differentiable ℝ S) (hddS : DifferentiableAt ℝ (deriv S) u)
    (hdθ : HasDerivAt θ (-(1/2) * θ u ^ 2 - σ u ^ 2 - 8 * Real.pi * G * T u) u) :
    HasDerivAt (quantumExpansion G ħ A S)
      (-(1/2) * θ u ^ 2 - σ u ^ 2 - 8 * Real.pi * G * T u +
        4 * G * ħ / A u * (deriv (deriv S) u - θ u * deriv S u)) u := by
  have he : quantumExpansion G ħ A S = fun v => θ v + 4 * G * ħ / A v * deriv S v :=
    funext fun v => quantum_expansion_eq hG hħ (hA v) (hdA v) (hdS v)
  rw [he]
  have hdInv := (hasDerivAt_const u (4 * G * ħ)).div (hdA u) (hA u).ne'
  convert hdθ.add (hdInv.mul hddS.hasDerivAt) using 1
  simp only [Pi.div_apply]
  field_simp [(hA u).ne']
  ring

/-- At a stationary cut the quantum focusing inequality cancels Newton's constant. -/
theorem qfc_iff_qnec_at_stationary_cut {G ħ : ℝ} {A S θ σ T : ℝ → ℝ} {u : ℝ}
    (hG : 0 < G) (hħ : 0 < ħ)
    (hA : ∀ v, 0 < A v) (hdA : ∀ v, HasDerivAt A (θ v * A v) v)
    (hdS : Differentiable ℝ S) (hddS : DifferentiableAt ℝ (deriv S) u)
    (hdθ : HasDerivAt θ (-(1/2) * θ u ^ 2 - σ u ^ 2 - 8 * Real.pi * G * T u) u)
    (hθ : θ u = 0) (hσ : σ u = 0) :
    deriv (quantumExpansion G ħ A S) u ≤ 0 ↔
      ħ / (2 * Real.pi * A u) * deriv (deriv S) u ≤ T u := by
  rw [(quantum_expansion_deriv hG hħ hA hdA hdS hddS hdθ).deriv, hθ, hσ]
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_mul, zero_sub, sub_zero]
  have hp : 0 < 8 * Real.pi * G := by positivity
  have he : 4 * G * ħ / A u * deriv (deriv S) u =
      (8 * Real.pi * G) * (ħ / (2 * Real.pi * A u) * deriv (deriv S) u) := by
    field_simp [Real.pi_ne_zero, (hA u).ne']
    <;> ring
  rw [he, show -(8 * Real.pi * G * T u) +
    8 * Real.pi * G * (ħ / (2 * Real.pi * A u) * deriv (deriv S) u) =
    (8 * Real.pi * G) * (ħ / (2 * Real.pi * A u) * deriv (deriv S) u - T u) by ring,
    ← mul_zero (8 * Real.pi * G)]
  rw [mul_le_mul_iff_of_pos_left hp]
  exact sub_nonpos

/-- The future boundary condition is cofinal on the horizon: every later tail contains
points at which the quantum expansion is arbitrarily close to nonnegative. -/
theorem qfc_implies_gsl {G ħ u₀ : ℝ} {A S : ℝ → ℝ}
    (hG : 0 < G) (hħ : 0 < ħ) (hA : ∀ u ∈ Ici u₀, 0 < A u)
    (hdA : ∀ u ∈ Ici u₀, DifferentiableAt ℝ A u)
    (hdS : ∀ u ∈ Ici u₀, DifferentiableAt ℝ S u)
    (hdQ : ∀ u ∈ Ici u₀, DifferentiableAt ℝ (quantumExpansion G ħ A S) u)
    (hqfc : ∀ u ∈ Ici u₀, deriv (quantumExpansion G ħ A S) u ≤ 0)
    (htail : ∀ ε > 0, ∀ v ≥ u₀, ∃ u ≥ v, -ε ≤ quantumExpansion G ħ A S u) :
    (∀ u ∈ Ici u₀, 0 ≤ quantumExpansion G ħ A S u) ∧
      MonotoneOn (generalizedEntropy G ħ A S) (Ici u₀) := by
  have ha : AntitoneOn (quantumExpansion G ħ A S) (Ici u₀) :=
    antitoneOn_of_deriv_nonpos (convex_Ici u₀)
      (fun u hu => (hdQ u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hdQ u (interior_subset hu)).differentiableWithinAt)
      (fun u hu => hqfc u (interior_subset hu))
  have hn : ∀ u ∈ Ici u₀, 0 ≤ quantumExpansion G ħ A S u := by
    intro v hv
    by_contra! hneg
    obtain ⟨u, huv, hu⟩ := htail (-(quantumExpansion G ħ A S v)/2) (by linarith) v hv
    have hle := ha hv (hv.trans huv) huv
    linarith
  refine ⟨hn, ?_⟩
  have hd : ∀ u ∈ Ici u₀, DifferentiableAt ℝ (generalizedEntropy G ħ A S) u :=
    fun u hu => ((hdA u hu).div_const _).add (hdS u hu)
  apply monotoneOn_of_deriv_nonneg (convex_Ici u₀)
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u (interior_subset hu)).differentiableWithinAt)
  intro u hu
  have hpos : 0 < 4 * G * ħ / A u := by have := hA u (interior_subset hu); positivity
  exact nonneg_of_mul_nonneg_right (hn u (interior_subset hu)) hpos

/-- Integration on expanding finite intervals proves ANEC without assuming absolute
integrability of the entropy second derivative. -/
theorem qnec_implies_anec {ħ A₀ : ℝ} {S T : ℝ → ℝ}
    (_hħ : 0 < ħ) (_hA : 0 < A₀)
    (hS : ContDiff ℝ 2 S)
    (hbot : Tendsto (deriv S) atBot (𝓝 0))
    (htop : Tendsto (deriv S) atTop (𝓝 0))
    (hT : Integrable T)
    (hqnec : ∀ u, ħ / (2 * Real.pi * A₀) * deriv (deriv S) u ≤ T u) :
    0 ≤ ∫ u, T u := by
  have hSd : ContDiff ℝ 1 (deriv S) := hS.deriv'
  have hSS : Continuous (deriv (deriv S)) := hSd.continuous_deriv_one
  let c := ħ / (2 * Real.pi * A₀)
  have hneg : Tendsto (fun u : ℝ => -u) atTop atBot := tendsto_neg_atTop_atBot
  have hlim := intervalIntegral_tendsto_integral hT hneg tendsto_id
  have hzero : Tendsto (fun u : ℝ => c * (deriv S u - deriv S (-u))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (htop.sub (hbot.comp hneg))
  apply le_of_tendsto_of_tendsto hzero hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  have hi : IntervalIntegrable (deriv (deriv S)) volume (-u) u := hSS.intervalIntegrable (-u) u
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (fun v _ => hSd.differentiable (by norm_num) v) hi
  rw [← hFTC, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by linarith) (hi.const_mul c) hT.intervalIntegrable
  intro v _
  exact hqnec v

end D5.S3.Quantum.Analysis.NullConeGravity.NullConeANECandQFC
