/- GID: D5/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay
   generality: G
   mirror-B: D5/B/S3/FluidDynamics/Fourier/PeriodicAllenCahnDecay
   mirror-E: none(waiver:analytic-evolution)
   anchors: []
   utility: none
   digest: Odd periodic Allen-Cahn profiles decay above the diffusive threshold. -/

/-
slice_continuousOn: proof_shape: bind-only;
  escape_witness: none;
  consumer: deriv_integral_compact, ScalarRegular.slice_continuous, ScalarRegular.slice_dx_continuous, ScalarRegular.slice_dxx_continuous, homogenizes_excludes_frozen, scalar_linear_zero.
energy_zero_of_gronwall: proof_shape: content;
  escape_witness: energy_gronwall;
  consumer: classical_unique, scalar_linear_zero.
ScalarRegular.slice_continuous: proof_shape: bind-only;
  escape_witness: none;
  consumer: scalar_energy_identity, pde_energy_deriv, scalar_riccati_bound, vectorEnergy_eq_integral, vector_energy_bound, vector_energy_zero_implies_zero, classical_unique, scalar_linear_zero.
ScalarRegular.energy_continuous: proof_shape: bind-only;
  escape_witness: none;
  consumer: scalar_exponential_bound, scalar_riccati_bound, vectorEnergy_continuous, scalar_linear_zero.
energy_nonnegative: proof_shape: bind-only;
  escape_witness: none;
  consumer: scalar_riccati_bound, scalar_exponential_decay, scalar_critical_decay, vectorEnergy_nonnegative, vector_energy_zero_implies_zero, scalar_linear_zero.
pde_energy_deriv: proof_shape: bind-only;
  escape_witness: none;
  consumer: vectorEnergy_deriv, scalar_linear_zero.
odd_allen_cahn_decay: proof_shape: content;
  escape_witness: scalar_critical_decay;
  consumer: vg_family.
ScalarRegular.sub: proof_shape: bind-only;
  escape_witness: none;
  consumer: classical_unique.
ScalarRegular.reflect: proof_shape: bind-only;
  escape_witness: none;
  consumer: solution_reflect_permute.
ScalarRegular.affine: proof_shape: bind-only;
  escape_witness: none;
  consumer: solution_pair, vg_family.
affine_derivatives: proof_shape: bind-only;
  escape_witness: none;
  consumer: solution_pair, vg_family.
admission_basis: escape-witness
Direct frozen dependencies: none; pinned Mathlib only.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
open scoped BigOperators Topology NNReal
open Set Filter MeasureTheory
namespace D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay

private lemma continuous_memLp_two_Ioc {a b : ℝ} (_hab : a ≤ b) {f : ℝ → ℂ}
    (hf : Continuous f) : MemLp f 2 (volume.restrict (Ioc a b)) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2
  exact (hf.norm.pow 2).intervalIntegrable a b |>.1

private lemma fourier_derivative_period (f f' : ℝ → ℂ)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f')
    (hp : f Real.pi = f (-Real.pi)) (k : ℤ) (hk : k ≠ 0) :
    fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f' k =
      Complex.I * (k : ℂ) *
        fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f k := by
  have h := fourierCoeffOn_of_hasDerivAt
    (by linarith [Real.pi_pos] : -Real.pi < Real.pi) hk
    (fun x _ => hd x) (hc.intervalIntegrable _ _)
  simp only [hp, sub_self, mul_zero, zero_sub] at h
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hden : (-2 * (Real.pi:ℂ) * Complex.I * (k:ℂ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero) hk'
  have hclean : fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f k =
      1 / (-2 * (Real.pi:ℂ) * Complex.I * (k:ℂ)) *
        (-(2*(Real.pi:ℂ)) * fourierCoeffOn (by linarith [Real.pi_pos] : -Real.pi < Real.pi) f' k) := by
    simpa only [Complex.ofReal_neg, sub_neg_eq_add, ← two_mul, neg_mul] using h
  rw [one_div] at hclean
  have hmul := (inv_mul_eq_iff_eq_mul₀ hden).mp hclean.symm
  apply mul_left_cancel₀ (show (2*(Real.pi:ℂ)) ≠ 0 by exact mul_ne_zero (by norm_num) hpi)
  linear_combination -hmul

/-- The sharp first-eigenvalue inequality on the circle of length 2π. -/

private theorem wirtinger (f : ℝ → ℝ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (hdf : Continuous (deriv f)) (hp : Function.Periodic f (2*Real.pi))
    (hmean : (∫ x in -Real.pi..Real.pi, f x) = 0) :
    (∫ x in -Real.pi..Real.pi, f x^2) ≤
      ∫ x in -Real.pi..Real.pi, (deriv f x)^2 := by
  have hfc : Continuous f := (show Differentiable ℝ f from hf) |>.continuous
  let F : ℝ → ℂ := fun x => (f x : ℂ)
  let F' : ℝ → ℂ := fun x => ((deriv f x : ℝ) : ℂ)
  have hF : Continuous F := Complex.continuous_ofReal.comp hfc
  have hF' : Continuous F' := Complex.continuous_ofReal.comp hdf
  have hder : ∀ x, HasDerivAt F (F' x) x := fun x => (hf x).hasDerivAt.ofReal_comp
  have hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hper : F Real.pi = F (-Real.pi) := by
    have h := hp (-Real.pi)
    have heq : -Real.pi + 2*Real.pi = Real.pi := by ring
    rw [heq] at h
    exact congrArg Complex.ofReal h
  have hz : fourierCoeffOn hab F 0 = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul]
    dsimp [F]
    rw [intervalIntegral.integral_ofReal, hmean]
    simp
  have hle : ∀ k : ℤ, ‖fourierCoeffOn hab F k‖^2 ≤ ‖fourierCoeffOn hab F' k‖^2 := by
    intro k
    by_cases hk : k = 0
    · simp only [hk, hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity
    · have heq := fourier_derivative_period F F' hder hF' hper k hk
      have hn := congrArg norm heq
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast] at hn
      have hone : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
      have hnn := norm_nonneg (fourierCoeffOn hab F k)
      have hl : ‖fourierCoeffOn hab F k‖ ≤ ‖fourierCoeffOn hab F' k‖ := by
        rw [hn]
        nlinarith
      exact pow_le_pow_left₀ hnn hl 2
  have H := hasSum_le hle
    (hasSum_sq_fourierCoeffOn hab (continuous_memLp_two_Ioc hab.le hF))
    (hasSum_sq_fourierCoeffOn hab (continuous_memLp_two_Ioc hab.le hF'))
  simp only [F, F', Complex.norm_real, Real.norm_eq_abs, sq_abs, smul_eq_mul] at H
  have hinv : 0 < (Real.pi - -Real.pi)⁻¹ := inv_pos.mpr (by linarith [Real.pi_pos])
  exact (mul_le_mul_iff_right₀ hinv).mp H

lemma slice_continuousOn {F : ℝ → ℝ → ℝ} {s r : Set ℝ}
    (h : ContinuousOn F.uncurry (s ×ˢ r)) {t : ℝ} (ht : t ∈ s) :
    ContinuousOn (F t) r := by
  exact h.uncurry_left t ht

private lemma integral_continuousOn_nonneg {F : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ContinuousOn F.uncurry (Ici 0 ×ˢ univ)) :
    ContinuousOn (fun t => ∫ x in a..b, F t x) (Ici 0) := by
  have hc : Continuous (fun z : ℝ × ℝ => F (max z.1 0) z.2) := by
    apply continuousOn_univ.mp
    exact h.comp ((continuous_fst.max continuous_const).prodMk continuous_snd).continuousOn
      (fun z _ => ⟨by simpa using le_max_right z.1 (0:ℝ),mem_univ _⟩)
  have hi := continuous_parametric_integral_of_continuous (μ := volume) (f := fun s x => F (max s 0) x) hc (s := Icc a b) isCompact_Icc
  apply hi.continuousOn.congr
  intro t ht
  simp only [mem_Ici] at ht
  dsimp only
  rw [max_eq_left ht, intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

private lemma deriv_integral_compact {F H : ℝ → ℝ → ℝ} {a b t δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ)
    (hF : ContinuousOn F.uncurry (Icc (t-δ) (t+δ) ×ˢ Icc a b))
    (hH : ContinuousOn H.uncurry (Icc (t-δ) (t+δ) ×ˢ Icc a b))
    (hd : ∀ s ∈ Ioo (t-δ) (t+δ), ∀ x ∈ Icc a b,
      HasDerivAt (fun r => F r x) (H s x) s) :
    HasDerivAt (fun s => ∫ x in a..b, F s x) (∫ x in a..b, H t x) t := by
  have ht : t ∈ Icc (t-δ) (t+δ) := by constructor <;> linarith
  have hnear : Ioo (t-δ) (t+δ) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  rcases (isCompact_Icc.prod isCompact_Icc).bddAbove_image hH.norm with ⟨C,hC⟩
  have hb : ∀ s ∈ Icc (t-δ) (t+δ), ∀ x ∈ Icc a b, ‖H s x‖ ≤ C := by
    intro s hs x hx
    exact hC ⟨(s,x),⟨hs,hx⟩,rfl⟩
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := H) (bound := fun _ => C) hnear ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hnear] with s hs
    simpa only [uIoc_of_le hab] using ((slice_continuousOn hF ⟨hs.1.le,hs.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
  · exact (slice_continuousOn hF ht).intervalIntegrable_of_Icc hab
  · simpa only [uIoc_of_le hab] using ((slice_continuousOn hH ht).mono Ioc_subset_Icc_self).aestronglyMeasurable (μ := volume) measurableSet_Ioc
  · apply ae_of_all
    intro x hx s hs
    rw [uIoc_of_le hab] at hx
    exact hb s ⟨hs.1.le,hs.2.le⟩ x ⟨hx.1.le,hx.2⟩
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro x hx s hs
    rw [uIoc_of_le hab] at hx
    exact hd s hs x ⟨hx.1.le,hx.2⟩

private lemma periodic_derivative {f g : ℝ → ℝ} {P : ℝ}
    (hf : Function.Periodic f P) (hd : ∀ x, HasDerivAt f (g x) x) :
    Function.Periodic g P := by
  intro x
  have heq : (fun y => f (y+P)) = f := funext hf
  have H : HasDerivAt (fun y => f (y+P)) (g (x+P)) x := by
    convert! (hd (x+P)).comp x ((hasDerivAt_id x).add_const P) using 1 <;> simp [Function.comp_def]
  rw [heq] at H
  exact H.unique (hd x)

private lemma periodic_integration_by_parts {f g h : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (h x) x)
    (hgc : Continuous g) (hhc : Continuous h) (hp : Function.Periodic f (2*Real.pi)) :
    (∫ x in -Real.pi..Real.pi, f x*h x) = -(∫ x in -Real.pi..Real.pi, g x^2) := by
  have hp' := periodic_derivative hp hf
  have heq : -Real.pi + 2*Real.pi = Real.pi := by ring
  have hp0 := hp (-Real.pi); rw [heq] at hp0
  have hp1 := hp' (-Real.pi); rw [heq] at hp1
  have H := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -Real.pi) (b := Real.pi)
    (fun x _ => hf x) (fun x _ => hg x) (hgc.intervalIntegrable _ _) (hhc.intervalIntegrable _ _)
  simpa only [hp0,hp1,sub_self,zero_sub,←sq] using H

private lemma energy_gronwall {Y Y' : ℝ → ℝ} {T K : ℝ}
    (hc : ContinuousOn Y (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hb : ∀ t ∈ Ioo 0 T, Y' t ≤ K*Y t) :
    ∀ t ∈ Icc 0 T, Y t ≤ Y 0*Real.exp (K*t) := by
  let J := fun t => Y t*Real.exp (-K*t)
  have hJc : ContinuousOn J (Icc 0 T) := hc.mul (by fun_prop)
  have hJd : ∀ t ∈ Ioo 0 T,
      HasDerivAt J ((Y' t-K*Y t)*Real.exp (-K*t)) t := by
    intro t ht
    convert! (hd t ht).mul (((hasDerivAt_id t).const_mul (-K)).exp) using 1 <;> simp only [id_eq] <;> ring
  have hm : AntitoneOn J (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hJc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hJd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hJd t ht).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hb t ht)) (Real.exp_pos _).le
  intro t ht
  have H := hm (show 0 ∈ Icc 0 T by exact ⟨le_rfl,ht.1.trans ht.2⟩) ht ht.1
  dsimp [J] at H
  simp only [mul_zero, Real.exp_zero, mul_one] at H
  calc
    Y t = (Y t*Real.exp (-K*t))*Real.exp (K*t) := by
      rw [mul_assoc,←Real.exp_add]
      simp
    _ ≤ Y 0*Real.exp (K*t) := mul_le_mul_of_nonneg_right H (Real.exp_pos _).le

lemma energy_zero_of_gronwall {Y Y' : ℝ → ℝ} {T K : ℝ}
    (hc : ContinuousOn Y (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hb : ∀ t ∈ Ioo 0 T, Y' t ≤ K*Y t)
    (h0 : Y 0 = 0) (hn : ∀ t ∈ Icc 0 T, 0 ≤ Y t) :
    ∀ t ∈ Icc 0 T, Y t = 0 := by
  intro t ht
  have H := energy_gronwall hc hd hb t ht
  rw [h0,zero_mul] at H
  exact le_antisymm H (hn t ht)

private lemma riccati_bound {Y Y' : ℝ → ℝ} {T c : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hcont : ContinuousOn Y (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt Y (Y' t) t)
    (hn : ∀ t ∈ Icc 0 T, 0 ≤ Y t)
    (hb : ∀ t ∈ Ioo 0 T, Y' t ≤ -c*(Y t)^2) :
    Y T ≤ Y 0/(1+c*Y 0*T) := by
  have hmono : AntitoneOn Y (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hd t ht).deriv]
      exact (hb t ht).trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg _))
  have hzero : 0 ≤ Y 0 := hn 0 ⟨le_rfl,hT⟩
  have hden : 0 < 1+c*Y 0*T := by positivity
  by_cases hpos : 0 < Y T
  · have hYpos : ∀ t ∈ Icc 0 T, 0 < Y t := by
      intro t ht
      exact hpos.trans_le (hmono ht ⟨hT,le_rfl⟩ ht.2)
    have hY0 : 0 < Y 0 := hYpos 0 ⟨le_rfl,hT⟩
    let J := fun t => (Y t)⁻¹-c*t
    have hJc : ContinuousOn J (Icc 0 T) :=
      (hcont.inv₀ (fun t ht => (hYpos t ht).ne')).sub (by fun_prop)
    have hJd : ∀ t ∈ Ioo 0 T,
        HasDerivAt J (-Y' t/(Y t)^2-c) t := by
      intro t ht
      convert! ((hd t ht).inv (hYpos t ⟨ht.1.le,ht.2.le⟩).ne').sub
        ((hasDerivAt_id t).const_mul c) using 1 <;> simp [J, div_eq_mul_inv]
    have hm : MonotoneOn J (Icc 0 T) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hJc
      · intro t ht
        rw [interior_Icc] at ht
        exact (hJd t ht).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        rw [(hJd t ht).deriv]
        have hy := hYpos t ⟨ht.1.le,ht.2.le⟩
        have hsq : 0 < (Y t)^2 := sq_pos_of_pos hy
        have H := (le_div_iff₀ hsq).2 (show c*(Y t)^2 ≤ -Y' t by linarith [hb t ht])
        linarith
    have H := hm (show 0 ∈ Icc 0 T from ⟨le_rfl,hT⟩) ⟨hT,le_rfl⟩ hT
    dsimp [J] at H
    simp only [mul_zero, sub_zero] at H
    rw [le_div_iff₀ hden]
    have H' := mul_le_mul_of_nonneg_left H (mul_pos hY0 hpos).le
    field_simp at H'
    nlinarith
  · have heq : Y T = 0 := le_antisymm (le_of_not_gt hpos) (hn T ⟨hT,le_rfl⟩)
    rw [heq]
    positivity

structure ScalarRegular (w : ℝ → ℝ → ℝ) : Prop where
  continuous : ContinuousOn w.uncurry (Ici 0 ×ˢ univ)
  periodic : ∀ t, 0 ≤ t → Function.Periodic (w t) (2*Real.pi)
  time_deriv : ∀ t x, 0 < t → HasDerivAt (fun s => w s x) ((deriv (fun s => w s x) t)) t
  space_deriv : ∀ t x, 0 < t → HasDerivAt (w t) ((deriv (w t) x)) x
  space_deriv2 : ∀ t x, 0 < t → HasDerivAt ((deriv (w t))) ((deriv (deriv (w t)) x)) x
  continuous_dt : ContinuousOn ((fun t x => deriv (fun s => w s x) t)).uncurry (Ioi 0 ×ˢ univ)
  continuous_dx : ContinuousOn ((fun t x => deriv (w t) x)).uncurry (Ioi 0 ×ˢ univ)
  continuous_dxx : ContinuousOn ((fun t x => deriv (deriv (w t)) x)).uncurry (Ioi 0 ×ˢ univ)

def energy (w : ℝ → ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in -Real.pi..Real.pi, (w t x)^2

private lemma ScalarRegular.continuous_pos {w} (h : ScalarRegular w) :
    ContinuousOn w.uncurry (Ioi 0 ×ˢ univ) :=
  h.continuous.mono (fun z hz => ⟨(show 0 < z.1 from hz.1).le,hz.2⟩)

lemma ScalarRegular.slice_continuous {w} (h : ScalarRegular w) {t} (ht : 0 ≤ t) :
    Continuous (w t) := continuousOn_univ.mp (slice_continuousOn h.continuous ht)

private lemma ScalarRegular.slice_dx_continuous {w} (h : ScalarRegular w) {t} (ht : 0 < t) :
    Continuous ((deriv (w t))) := continuousOn_univ.mp (slice_continuousOn h.continuous_dx ht)

private lemma ScalarRegular.slice_dxx_continuous {w} (h : ScalarRegular w) {t} (ht : 0 < t) :
    Continuous ((deriv (deriv (w t)))) := continuousOn_univ.mp (slice_continuousOn h.continuous_dxx ht)

lemma ScalarRegular.energy_continuous {w} (h : ScalarRegular w) :
    ContinuousOn (energy w) (Ici 0) :=
  integral_continuousOn_nonneg (by linarith [Real.pi_pos]) (h.continuous.pow 2)

lemma energy_nonnegative (w : ℝ → ℝ → ℝ) (t : ℝ) : 0 ≤ energy w t :=
  intervalIntegral.integral_nonneg_of_forall (by linarith [Real.pi_pos]) (fun _ => sq_nonneg _)

private lemma ScalarRegular.energy_deriv {w} (h : ScalarRegular w) {t} (ht : 0 < t) :
    HasDerivAt (energy w) (∫ x in -Real.pi..Real.pi, 2*w t x*(deriv (fun s => w s x) t)) t := by
  change HasDerivAt (fun t => ∫ x in -Real.pi..Real.pi, (w t x)^2) _ t
  apply deriv_integral_compact (F := fun s x => (w s x)^2) (H := fun s x => 2*w s x*(deriv (fun s => w s x) s)) (δ := t/2) (by linarith [Real.pi_pos]) (by positivity)
  · exact (h.continuous_pos.pow 2).mono (fun z hz => ⟨by change 0 < z.1; have hzlow : t-t/2 ≤ z.1 := hz.1.1; linarith,mem_univ _⟩)
  · exact ((continuousOn_const.mul h.continuous_pos).mul h.continuous_dt).mono
      (fun z hz => ⟨by change 0 < z.1; have hzlow : t-t/2 ≤ z.1 := hz.1.1; linarith,mem_univ _⟩)
  · intro s hs x _
    have hspos : 0 < s := by linarith [hs.1]
    convert! (h.time_deriv s x hspos).pow 2 using 1 <;> ring

private lemma odd_mean_zero {f : ℝ → ℝ} (ho : ∀ x, f (-x) = -f x) :
    (∫ x in -Real.pi..Real.pi, f x) = 0 := by
  have H := intervalIntegral.integral_comp_neg (a := -Real.pi) (b := Real.pi) f
  simp only [neg_neg] at H
  have heq : (fun x => f (-x)) = fun x => -f x := funext ho
  rw [heq,intervalIntegral.integral_neg] at H
  linarith

private lemma quartic_lower_bound (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in -Real.pi..Real.pi, f x^2)^2 ≤
      (2*Real.pi)*(∫ x in -Real.pi..Real.pi, f x^4) := by
  let Y := ∫ x in -Real.pi..Real.pi, f x^2
  let c := Y/(2*Real.pi)
  have h2 : IntervalIntegrable (fun x => f x^2) volume (-Real.pi) Real.pi := (hf.pow 2).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x => f x^4) volume (-Real.pi) Real.pi := (hf.pow 4).intervalIntegrable _ _
  have heq : (fun x => (f x^2-c)^2) = fun x => f x^4 - (2*c)*f x^2+c^2 := by
    funext x; ring
  have hnon := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi) (fun x => sq_nonneg (f x^2-c))
  rw [heq,intervalIntegral.integral_add (h4.sub (h2.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub h4 (h2.const_mul _),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hnon
  dsimp [c,Y] at hnon
  try simp only [smul_eq_mul] at hnon
  have hp := Real.pi_pos
  field_simp at hnon
  nlinarith

lemma pde_energy_deriv {w : ℝ → ℝ → ℝ} (hr : ScalarRegular w)
    {t D : ℝ} (ht : 0 < t) (Q : ℝ → ℝ) (hQ : Continuous Q)
    (he : ∀ x, (deriv (fun s => w s x) t) = D*(deriv (deriv (w t)) x)+Q x) :
    HasDerivAt (energy w) (2*(∫ x in -Real.pi..Real.pi, w t x*Q x)-
      2*D*(∫ x in -Real.pi..Real.pi, ((deriv (w t) x))^2)) t := by
  have hw := hr.slice_continuous ht.le
  have hxx := hr.slice_dxx_continuous ht
  have hparts := periodic_integration_by_parts (hr.space_deriv t · ht)
    (hr.space_deriv2 t · ht) (hr.slice_dx_continuous ht) hxx (hr.periodic t ht.le)
  have heq : (fun x => 2*w t x*(deriv (fun s => w s x) t)) =
      fun x => 2*(D*(w t x*(deriv (deriv (w t)) x))+w t x*Q x) := by
    funext x
    rw [he x]
    ring
  have hA : IntervalIntegrable (fun x => D*(w t x*(deriv (deriv (w t)) x))) volume (-Real.pi) Real.pi := by
    convert! ((hw.mul hxx).const_mul D).intervalIntegrable (μ := volume) (-Real.pi) Real.pi using 1
  have hB : IntervalIntegrable (fun x => w t x*Q x) volume (-Real.pi) Real.pi := by
    convert! (hw.mul hQ).intervalIntegrable (μ := volume) (-Real.pi) Real.pi using 1
  convert! hr.energy_deriv ht using 1
  rw [heq,intervalIntegral.integral_const_mul,intervalIntegral.integral_add hA hB,
    intervalIntegral.integral_const_mul,hparts]
  ring

private lemma scalar_energy_identity {w : ℝ → ℝ → ℝ} {D μ : ℝ}
    (hr : ScalarRegular w)
    (he : ∀ t x, 0 < t → (deriv (fun s => w s x) t) = D*(deriv (deriv (w t)) x)+μ*(w t x-(w t x)^3))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (energy w)
      (2*(-D*(∫ x in -Real.pi..Real.pi, ((deriv (w t) x))^2)+μ*energy w t-
        μ*(∫ x in -Real.pi..Real.pi, (w t x)^4))) t := by
  have hw := hr.slice_continuous ht.le
  have h := pde_energy_deriv hr ht (fun x => μ*(w t x-(w t x)^3))
    ((hw.sub (hw.pow 3)).const_mul μ) (fun x => he t x ht)
  have hi : (∫ x in -Real.pi..Real.pi, w t x*(μ*(w t x-(w t x)^3))) =
      μ*energy w t-μ*(∫ x in -Real.pi..Real.pi, (w t x)^4) := by
    have heq : (fun x => w t x*(μ*(w t x-(w t x)^3))) =
        (fun x => μ*(w t x)^2-μ*(w t x)^4) := by funext x; ring
    have hA : IntervalIntegrable (fun x => μ*(w t x)^2) volume (-Real.pi) Real.pi := by
      convert! ((hw.pow 2).const_mul μ).intervalIntegrable (μ := volume) (-Real.pi) Real.pi using 1
    have hB : IntervalIntegrable (fun x => μ*(w t x)^4) volume (-Real.pi) Real.pi := by
      convert! ((hw.pow 4).const_mul μ).intervalIntegrable (μ := volume) (-Real.pi) Real.pi using 1
    rw [heq, intervalIntegral.integral_sub hA hB,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  rw [hi] at h
  convert h using 1 <;> ring

private def scalarSlope (w : ℝ → ℝ → ℝ) (D μ t : ℝ) :=
  2*(-D*(∫ x in -Real.pi..Real.pi, ((deriv (w t) x))^2)+μ*energy w t-
    μ*(∫ x in -Real.pi..Real.pi, (w t x)^4))

private lemma scalar_slope_bound {w D μ} (hr : ScalarRegular w) (hD : 0 ≤ D) (hμ : 0 ≤ μ)
    (hmean : ∀ t, 0 < t → (∫ x in -Real.pi..Real.pi, w t x) = 0) {t} (ht : 0 < t) :
    scalarSlope w D μ t ≤ -2*(D-μ)*energy w t-2*μ*(∫ x in -Real.pi..Real.pi, (w t x)^4) := by
  have H := wirtinger (w t) (fun x => (hr.space_deriv t x ht).differentiableAt)
    (hr.slice_dx_continuous ht) (hr.periodic t ht.le) (hmean t ht)
  have H' := mul_le_mul_of_nonneg_left H hD
  unfold scalarSlope energy at *
  linarith

private lemma scalar_exponential_bound {w D μ} (hr : ScalarRegular w) (hD : 0 ≤ D) (hμ : 0 ≤ μ)
    (he : ∀ t x, 0 < t → (deriv (fun s => w s x) t) = D*(deriv (deriv (w t)) x)+μ*(w t x-(w t x)^3))
    (hmean : ∀ t, 0 < t → (∫ x in -Real.pi..Real.pi, w t x) = 0) {T} (hT : 0 ≤ T) :
    energy w T ≤ energy w 0*Real.exp ((-2*(D-μ))*T) := by
  apply energy_gronwall (Y' := scalarSlope w D μ)
    (hr.energy_continuous.mono (fun _ ht => ht.1))
    (fun t ht => scalar_energy_identity hr he ht.1) ?_ T ⟨hT,le_rfl⟩
  intro t ht
  have H := scalar_slope_bound hr hD hμ hmean ht.1
  have hQ : 0 ≤ ∫ x in -Real.pi..Real.pi, (w t x)^4 :=
    intervalIntegral.integral_nonneg_of_forall (by linarith [Real.pi_pos]) (fun _ => by positivity)
  nlinarith [mul_nonneg hμ hQ]

private lemma scalar_riccati_bound {w μ} (hr : ScalarRegular w) (hμ : 0 ≤ μ)
    (he : ∀ t x, 0 < t → (deriv (fun s => w s x) t) = μ*(deriv (deriv (w t)) x)+μ*(w t x-(w t x)^3))
    (hmean : ∀ t, 0 < t → (∫ x in -Real.pi..Real.pi, w t x) = 0) {T} (hT : 0 ≤ T) :
    energy w T ≤ energy w 0/(1+(μ/Real.pi)*energy w 0*T) := by
  apply riccati_bound (Y' := scalarSlope w μ μ) hT (div_nonneg hμ Real.pi_pos.le)
    (hr.energy_continuous.mono (fun _ ht => ht.1))
    (fun t ht => scalar_energy_identity hr he ht.1) (fun t _ => energy_nonnegative _ _) ?_
  intro t ht
  have H := scalar_slope_bound hr hμ hμ hmean ht.1
  have hQ := quartic_lower_bound (w t) (hr.slice_continuous ht.1.le)
  have hmul := mul_le_mul_of_nonneg_left hQ (div_nonneg hμ Real.pi_pos.le)
  have heq : (μ/Real.pi)*((2*Real.pi)*(∫ x in -Real.pi..Real.pi, (w t x)^4)) =
      2*μ*(∫ x in -Real.pi..Real.pi, (w t x)^4) := by field_simp
  rw [heq] at hmul
  change (energy w t)^2 ≤ _ at hQ
  change (μ/Real.pi)*(energy w t)^2 ≤ _ at hmul
  nlinarith

private lemma scalar_exponential_decay {w D μ} (hr : ScalarRegular w) (hD : 0 ≤ D) (hμ : 0 ≤ μ)
    (hstrict : μ < D)
    (he : ∀ t x, 0 < t → (deriv (fun s => w s x) t) = D*(deriv (deriv (w t)) x)+μ*(w t x-(w t x)^3))
    (hmean : ∀ t, 0 < t → (∫ x in -Real.pi..Real.pi, w t x) = 0) :
    Tendsto (energy w) atTop (𝓝 0) := by
  have hcoef : -2*(D-μ) < 0 := by linarith
  have ht : Tendsto (fun t : ℝ => Real.exp ((-2*(D-μ))*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hcoef).mpr tendsto_id)
  have hupper := ht.const_mul (energy w 0)
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall (energy_nonnegative w)) ?_ hupper
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact scalar_exponential_bound hr hD hμ he hmean ht

private lemma scalar_critical_decay {w μ} (hr : ScalarRegular w) (hμ : 0 < μ)
    (he : ∀ t x, 0 < t → (deriv (fun s => w s x) t) = μ*(deriv (deriv (w t)) x)+μ*(w t x-(w t x)^3))
    (hmean : ∀ t, 0 < t → (∫ x in -Real.pi..Real.pi, w t x) = 0) :
    Tendsto (energy w) atTop (𝓝 0) := by
  by_cases hzero : energy w 0 = 0
  · apply squeeze_zero' (Eventually.of_forall (energy_nonnegative w)) ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have H := scalar_riccati_bound hr hμ.le he hmean ht
    simpa only [hzero,zero_div] using H
  · have hpos : 0 < energy w 0 := lt_of_le_of_ne (energy_nonnegative w 0) (Ne.symm hzero)
    have hcoef : 0 < (μ/Real.pi)*energy w 0 := by positivity
    have hd : Tendsto (fun t : ℝ => 1+((μ/Real.pi)*energy w 0)*t) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 ((tendsto_const_mul_atTop_of_pos hcoef).mpr tendsto_id)
    have hupper := hd.const_div_atTop (energy w 0)
    apply squeeze_zero' (Eventually.of_forall (energy_nonnegative w)) ?_ hupper
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact scalar_riccati_bound hr hμ.le he hmean ht

theorem odd_allen_cahn_decay {w D μ} (hr : ScalarRegular w) (hD : 0 < D) (hμ : 0 ≤ μ)
    (hthreshold : μ ≤ D)
    (he : ∀ t x, 0 < t → (deriv (fun s => w s x) t) = D*(deriv (deriv (w t)) x)+μ*(w t x-(w t x)^3))
    (hodd : ∀ t, 0 < t → ∀ x, w t (-x) = -w t x) :
    Tendsto (energy w) atTop (𝓝 0) := by
  have hmean : ∀ t, 0 < t → (∫ x in -Real.pi..Real.pi, w t x) = 0 :=
    fun t ht => odd_mean_zero (hodd t ht)
  rcases lt_or_eq_of_le hthreshold with hlt | heq
  · exact scalar_exponential_decay hr hD.le hμ hlt he hmean
  · subst D
    exact scalar_critical_decay hr hD he hmean

private lemma regular_of_explicit (w Wt Wx Wxx : ℝ → ℝ → ℝ)
    (hcont : ContinuousOn w.uncurry (Ici 0 ×ˢ univ))
    (hp : ∀ t, 0 ≤ t → Function.Periodic (w t) (2*Real.pi))
    (ht : ∀ t x, 0 < t → HasDerivAt (fun s => w s x) (Wt t x) t)
    (hx : ∀ t x, 0 < t → HasDerivAt (w t) (Wx t x) x)
    (hxx : ∀ t x, 0 < t → HasDerivAt (Wx t) (Wxx t x) x)
    (hct : ContinuousOn Wt.uncurry (Ioi 0 ×ˢ univ))
    (hcx : ContinuousOn Wx.uncurry (Ioi 0 ×ˢ univ))
    (hcxx : ContinuousOn Wxx.uncurry (Ioi 0 ×ˢ univ)) : ScalarRegular w := by
  have eT : ∀ t x, 0 < t → (deriv (fun s => w s x) t) = Wt t x := fun t x h => (ht t x h).deriv
  have eX : ∀ t x, 0 < t → (deriv (w t) x) = Wx t x := fun t x h => (hx t x h).deriv
  have eXX : ∀ t x, 0 < t → (deriv (deriv (w t)) x) = Wxx t x := by
    intro t x h
    have hfun : (deriv (w t)) = Wx t := funext (fun x => eX t x h)
    rw [hfun]
    exact (hxx t x h).deriv
  refine ⟨hcont,hp,?_,?_,?_,?_,?_,?_⟩
  · intro t x h; rw [eT t x h]; exact ht t x h
  · intro t x h; rw [eX t x h]; exact hx t x h
  · intro t x h
    have hfun : (deriv (w t)) = Wx t := funext (fun x => eX t x h)
    rw [hfun]
    exact (hxx t x h).differentiableAt.hasDerivAt
  · exact hct.congr (fun z hz => eT z.1 z.2 hz.1)
  · exact hcx.congr (fun z hz => eX z.1 z.2 hz.1)
  · exact hcxx.congr (fun z hz => eXX z.1 z.2 hz.1)

private lemma ScalarRegular.linear {f g : ℝ → ℝ → ℝ} (hf : ScalarRegular f) (hg : ScalarRegular g) (a b : ℝ) :
    ScalarRegular (fun t x => a*f t x+b*g t x) := by
  apply regular_of_explicit _ (fun t x => a*(deriv (fun s => f s x) t)+b*(deriv (fun s => g s x) t))
    (fun t x => a*(deriv (f t) x)+b*(deriv (g t) x)) (fun t x => a*(deriv (deriv (f t)) x)+b*(deriv (deriv (g t)) x))
  · exact (hf.continuous.const_mul a).add (hg.continuous.const_mul b)
  · intro t ht x
    dsimp
    rw [hf.periodic t ht x,hg.periodic t ht x]
  · intro t x ht
    exact ((hf.time_deriv t x ht).const_mul a).add ((hg.time_deriv t x ht).const_mul b)
  · intro t x ht
    exact ((hf.space_deriv t x ht).const_mul a).add ((hg.space_deriv t x ht).const_mul b)
  · intro t x ht
    exact ((hf.space_deriv2 t x ht).const_mul a).add ((hg.space_deriv2 t x ht).const_mul b)
  · exact (hf.continuous_dt.const_mul a).add (hg.continuous_dt.const_mul b)
  · exact (hf.continuous_dx.const_mul a).add (hg.continuous_dx.const_mul b)
  · exact (hf.continuous_dxx.const_mul a).add (hg.continuous_dxx.const_mul b)

lemma ScalarRegular.sub {f g : ℝ → ℝ → ℝ} (hf : ScalarRegular f) (hg : ScalarRegular g) :
    ScalarRegular (fun t x => f t x-g t x) := by
  convert! hf.linear hg 1 (-1) using 1
  funext t x; ring

lemma ScalarRegular.reflect {w : ℝ → ℝ → ℝ} (h : ScalarRegular w) :
    ScalarRegular (fun t x => w t (-x)) := by
  apply regular_of_explicit _ (fun t x => (deriv (fun s => w s (-x)) t)) (fun t x => -(deriv (w t) (-x)))
    (fun t x => (deriv (deriv (w t)) (-x)))
  · exact h.continuous.comp (continuousOn_fst.prodMk continuousOn_snd.neg)
      (fun z hz => ⟨hz.1,mem_univ _⟩)
  · intro t ht x
    dsimp
    convert! (h.periodic t ht).sub_eq (-x) using 1 <;> ring
  · intro t x ht; exact h.time_deriv t (-x) ht
  · intro t x ht
    convert! (h.space_deriv t (-x) ht).comp x (hasDerivAt_neg x) using 1 <;> simp
  · intro t x ht
    convert! ((h.space_deriv2 t (-x) ht).comp x (hasDerivAt_neg x)).neg using 1 <;> simp
  · exact h.continuous_dt.comp (continuousOn_fst.prodMk continuousOn_snd.neg)
      (fun z hz => ⟨hz.1,mem_univ _⟩)
  · exact (h.continuous_dx.comp (continuousOn_fst.prodMk continuousOn_snd.neg)
      (fun z hz => ⟨hz.1,mem_univ _⟩)).neg
  · exact h.continuous_dxx.comp (continuousOn_fst.prodMk continuousOn_snd.neg)
      (fun z hz => ⟨hz.1,mem_univ _⟩)

private lemma ScalarRegular.const (c : ℝ) : ScalarRegular (fun _ _ => c) := by
  apply regular_of_explicit _ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
  · exact continuousOn_const
  · intro _ _ _; rfl
  · intro t _ _; exact hasDerivAt_const t c
  · intro _ x _; exact hasDerivAt_const x c
  · intro _ x _; exact hasDerivAt_const x 0
  · exact continuousOn_const
  · exact continuousOn_const
  · exact continuousOn_const

lemma ScalarRegular.affine {f g : ℝ → ℝ → ℝ} (hf : ScalarRegular f)
    (hg : ScalarRegular g) (a b c : ℝ) : ScalarRegular (fun t x => a*f t x+b*g t x+c) := by
  convert! (hf.linear hg a b).linear (ScalarRegular.const c) 1 1 using 1
  funext t x; ring

lemma affine_derivatives {f g : ℝ → ℝ → ℝ} (hf : ScalarRegular f)
    (hg : ScalarRegular g) (a b c : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (deriv (fun s => (fun t x => a*f t x+b*g t x+c) s x) t) = a*(deriv (fun s => f s x) t)+b*(deriv (fun s => g s x) t) ∧
    (deriv (deriv ((fun t x => a*f t x+b*g t x+c) t)) x) = a*(deriv (deriv (f t)) x)+b*(deriv (deriv (g t)) x) := by
  have hT := (((hf.time_deriv t x ht).const_mul a).add
    ((hg.time_deriv t x ht).const_mul b)).add_const c
  have hX : (deriv ((fun t x => a*f t x+b*g t x+c) t)) =
      fun x => a*(deriv (f t) x)+b*(deriv (g t) x) := by
    funext y
    exact ((((hf.space_deriv t y ht).const_mul a).add
      ((hg.space_deriv t y ht).const_mul b)).add_const c).deriv
  refine ⟨hT.deriv,?_⟩
  rw [hX]
  exact (((hf.space_deriv2 t x ht).const_mul a).add
    ((hg.space_deriv2 t x ht).const_mul b)).deriv

end D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay
