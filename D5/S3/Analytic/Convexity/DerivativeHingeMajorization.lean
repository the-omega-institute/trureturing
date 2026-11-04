/- GID: D5/S3/Analytic/Convexity/DerivativeHingeMajorization
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/DerivativeHingeMajorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derivative cancellation and convex hinge integrals on two rays. -/
/-
admission_basis: escape-witness
boundary_cancellation: proof_shape: content; escape_witness: boundary_cancellation;
  consumers: VacuumOnePhotonWignerMajorization.concrete_cancel.
radial: proof_shape: bind-only; escape_witness: none;
  consumers: VacuumOnePhotonWignerMajorization.level_reduction.
hingeIntegral: proof_shape: bind-only; escape_witness: none;
  consumers: hinge_min, hinge_convex, VacuumOnePhotonWignerMajorization.concrete_rays.
hinge_integrable: proof_shape: bind-only; escape_witness: none;
  consumers: hinge_min, hinge_convex.
hinge_subgradient: proof_shape: bind-only; escape_witness: none; consumers: hinge_min.
hinge_min: proof_shape: bind-only; escape_witness: none;
  consumers: VacuumOnePhotonWignerMajorization.concrete_rays.
hinge_convex: proof_shape: bind-only; escape_witness: none;
  consumers: VacuumOnePhotonWignerMajorization.concrete_rays.
convex_rays: proof_shape: bind-only; escape_witness: none;
  consumers: VacuumOnePhotonWignerMajorization.concrete_rays.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/20140
Direct frozen dependencies: none.
The integral identities concern real Bochner integrals with Lebesgue measure.
No declaration is a finite computation or certified instance; utility is none.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

namespace D5.S3.Analytic.Convexity.DerivativeHingeMajorization
open MeasureTheory Set Filter
open scoped Topology

lemma radial (g : ℝ → ℝ) :
    (∫ r : ℝ × ℝ, g (r.1 ^ 2 + r.2 ^ 2)) = Real.pi * ∫ s in Ioi (0 : ℝ), g s := by
  rw [← integral_comp_polarCoord_symm]
  have trig (p : ℝ × ℝ) :
      (polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2 = p.1 ^ 2 := by
    simp only [polarCoord_symm_apply]
    nlinarith [Real.sin_sq_add_cos_sq p.2]
  simp_rw [trig, smul_eq_mul]
  rw [polarCoord_target]
  have prod := setIntegral_prod_mul (μ := volume) (ν := volume) (s := Ioi (0 : ℝ)) (t := Ioo (-Real.pi) Real.pi)
    (fun r : ℝ => r * g (r ^ 2)) (fun _ : ℝ => (1 : ℝ))
  simp only [mul_one] at prod
  rw [Measure.volume_eq_prod ℝ ℝ, prod]
  have change := integral_comp_rpow_Ioi g (by norm_num : (2 : ℝ) ≠ 0)
  simp only [abs_of_pos (by norm_num : (0 : ℝ) < 2), show (2 : ℝ) - 1 = 1 by norm_num,
    Real.rpow_one, Real.rpow_two, smul_eq_mul] at change
  rw [show (∫ r in Ioi (0 : ℝ), 2 * r * g (r ^ 2)) =
      2 * ∫ r in Ioi (0 : ℝ), r * g (r ^ 2) by rw [← integral_const_mul]; congr 1; funext r; ring] at change
  simp only [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ioo, smul_eq_mul, mul_one]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  rw [← change]
  ring



lemma boundary_cancellation (h k : ℝ → ℝ) (hc : Continuous h)
    (hd : ∀ x : ℝ, HasDerivAt h (k x) x)
    (ki : IntegrableOn k (Ioi (0 : ℝ)))
    (p : ℝ) (hp : 0 ≤ p)
    (kpos : ∀ x ∈ Ioo (0 : ℝ) p, 0 ≤ k x)
    (kneg : ∀ x ∈ Ioi p, k x ≤ 0)
    (hzero : h 0 = 0) (hlim : Tendsto h atTop (𝓝 0)) (T : ℝ) :
    (∫ s in Ioi (0 : ℝ), k s * (if T < h s then 1 else 0)) = 0 := by
  let G : ℝ → ℝ := fun y => if T < y then 1 else 0
  let P : ℝ → ℝ := fun s => k s * G (h s)
  have pi : IntegrableOn P (Ioi (0 : ℝ)) := by
    have hi := ki.indicator (isOpen_lt (continuous_const (y := T)) hc).measurableSet
    convert hi using 1
    funext x
    by_cases hx : T < h x <;> simp [P, G, Set.indicator, hx]
  have intP {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable P volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact pi.mono_set (fun x hx => lt_of_le_of_lt ha hx.1)
  have intG (a b : ℝ) : IntervalIntegrable G volume a b := by
    have ci : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b := intervalIntegrable_const
    have ci2 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (uIcc a b) :=
      (intervalIntegrable_iff').mp ci
    have im := ci2.indicator (measurableSet_Ioi (a := T))
    convert im.intervalIntegrable using 1
    funext y
    by_cases hy : T < y <;> simp [G, Set.indicator, hy]
  have eqP (b : ℝ) (hb : p ≤ b) :
      (∫ s in (0 : ℝ)..b, P s) = ∫ y in (0 : ℝ)..h b, G y := by
    have e1 : (∫ s in (0 : ℝ)..p, P s) = ∫ y in (0 : ℝ)..h p, G y := by
      have e := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (f := h) (f' := k) (g := G) (a := 0) (b := p) hc.continuousOn
        (fun x _ => hd x) (by simpa [min_eq_left hp, max_eq_right hp] using kpos)
      simpa only [Function.comp_apply, mul_comm (G _) (k _), hzero] using e
    have e2 : (∫ s in p..b, P s) = ∫ y in h p..h b, G y := by
      have e := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
        (f := h) (f' := k) (g := G) (a := p) (b := b) hc.continuousOn
        (fun x _ => hd x) (by
          intro x hx
          apply kneg x
          have hx' : x ∈ Ioo p b := by simpa [min_eq_left hb, max_eq_right hb] using hx
          exact hx'.1)
      simpa only [Function.comp_apply, mul_comm (G _) (k _)] using e
    rw [← intervalIntegral.integral_add_adjacent_intervals (intP (a := 0) (b := p) le_rfl hp)
      (intP hp hb), e1, e2]
    exact intervalIntegral.integral_add_adjacent_intervals (intG _ _) (intG _ _)
  have bound (b : ℝ) : ‖∫ y in (0 : ℝ)..h b, G y‖ ≤ |h b| := by
    simpa only [one_mul, sub_zero] using
      (intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := h b) (C := 1) (f := G) (fun y _ => by
          dsimp [G]
          split_ifs <;> norm_num))
  have glimit : Tendsto (fun b : ℝ => ∫ y in (0 : ℝ)..h b, G y) atTop (𝓝 0) := by
    exact squeeze_zero_norm (fun b => bound b) (by simpa using hlim.abs)
  have plimit := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) pi tendsto_id
  have eventual : (fun b : ℝ => ∫ s in (0 : ℝ)..b, P s) =ᶠ[atTop]
      (fun b : ℝ => ∫ y in (0 : ℝ)..h b, G y) := by
    filter_upwards [eventually_ge_atTop p] with b hb
    exact eqP b hb
  exact tendsto_nhds_unique plimit (glimit.congr' eventual.symm)


noncomputable def hingeIntegral (h k : ℝ → ℝ) (T c : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), max (|h s + c * k s| - T) 0

private lemma hinge_integrable (h k : ℝ → ℝ) (hc : Continuous h) (kc : Continuous k)
    (hi : IntegrableOn h (Ioi (0 : ℝ))) (ki : IntegrableOn k (Ioi (0 : ℝ)))
    (T c : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun s => max (|h s + c * k s| - T) 0) (Ioi (0 : ℝ)) := by
  apply (hi.add (ki.const_mul c)).abs.mono'
    ((((hc.add (continuous_const.mul kc)).abs.sub continuous_const).max continuous_const).aestronglyMeasurable)
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (sub_le_self _ hT) (abs_nonneg _)

private lemma hinge_subgradient (H K T c : ℝ) :
    max (H - T) 0 + c * K * (if T < H then 1 else 0) ≤ max (|H + c * K| - T) 0 := by
  by_cases ht : T < H
  · rw [if_pos ht, mul_one, max_eq_left (sub_nonneg.mpr ht.le)]
    have a := le_abs_self (H + c * K)
    have b := le_max_left (|H + c * K| - T) 0
    linarith
  · rw [if_neg ht, mul_zero, add_zero, max_eq_right (sub_nonpos.mpr (le_of_not_gt ht))]
    exact le_max_right _ _

lemma hinge_min (h k : ℝ → ℝ) (hc : Continuous h) (kc : Continuous k)
    (hi : IntegrableOn h (Ioi (0 : ℝ))) (ki : IntegrableOn k (Ioi (0 : ℝ)))
    (hn : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ h s)
    (T c : ℝ) (hT : 0 ≤ T)
    (cancel : (∫ s in Ioi (0 : ℝ), k s * (if T < h s then 1 else 0)) = 0) :
    hingeIntegral h k T 0 ≤ hingeIntegral h k T c := by
  have ii : IntegrableOn (fun s => k s * (if T < h s then 1 else 0)) (Ioi (0 : ℝ)) := by
    convert ki.indicator (isOpen_lt (continuous_const (y := T)) hc).measurableSet using 1
    funext x
    by_cases hx : T < h x <;> simp [Set.indicator, hx]
  have base := hinge_integrable h k hc kc hi ki T 0 hT
  have full := hinge_integrable h k hc kc hi ki T c hT
  have lower : IntegrableOn (fun s => max (|h s + 0 * k s| - T) 0 +
      c * (k s * (if T < h s then 1 else 0))) (Ioi (0 : ℝ)) := base.add (ii.const_mul c)
  have ineq := integral_mono_ae lower full (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simpa [abs_of_nonneg (hn s hs), mul_assoc] using hinge_subgradient (h s) (k s) T c)
  rw [integral_add base (ii.const_mul c), integral_const_mul, cancel, mul_zero, add_zero] at ineq
  exact ineq

lemma hinge_convex (h k : ℝ → ℝ) (hc : Continuous h) (kc : Continuous k)
    (hi : IntegrableOn h (Ioi (0 : ℝ))) (ki : IntegrableOn k (Ioi (0 : ℝ)))
    (T : ℝ) (hT : 0 ≤ T) : ConvexOn ℝ univ (hingeIntegral h k T) := by
  have cv (s : ℝ) : ConvexOn ℝ univ (fun c : ℝ => max (|h s + c * k s| - T) 0) := by
    let A : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ (h s) + k s • AffineMap.id ℝ ℝ
    have cn : ConvexOn ℝ univ (fun c : ℝ => |h s + c * k s|) := by
      simpa [A, Function.comp_def, Real.norm_eq_abs, mul_comm] using
        (convexOn_norm (E := ℝ) convex_univ).comp_affineMap A
    simpa only [Pi.sup_def, Pi.add_def, sub_eq_add_neg] using
      (cn.add_const (-T)).sup (convexOn_const (0 : ℝ) convex_univ)
  exact integral_convexOn_of_integrand_ae convex_univ (Eventually.of_forall cv)
    (fun c _ => hinge_integrable h k hc kc hi ki T c hT)

lemma convex_rays (F : ℝ → ℝ) (hf : ConvexOn ℝ univ F) (hmin : ∀ c : ℝ, F 0 ≤ F c) :
    MonotoneOn F (Ici (0 : ℝ)) ∧ AntitoneOn F (Iic (0 : ℝ)) := by
  constructor
  · intro x hx y hy hxy
    change 0 ≤ x at hx
    rcases eq_or_lt_of_le hx with rfl | hx
    · exact hmin y
    rcases eq_or_lt_of_le hxy with rfl | hxy
    · exact le_rfl
    exact hf.le_right_of_left_le (mem_univ 0) (mem_univ y)
      (by rw [openSegment_eq_Ioo (by linarith : (0 : ℝ) < y)]; exact ⟨hx, hxy⟩) (hmin x)
  · intro x hx y hy hxy
    change y ≤ 0 at hy
    rcases eq_or_lt_of_le hy with rfl | hy
    · exact hmin x
    rcases eq_or_lt_of_le hxy with rfl | hxy
    · exact le_rfl
    exact hf.le_left_of_right_le (mem_univ x) (mem_univ 0)
      (by rw [openSegment_eq_Ioo (by linarith : x < (0 : ℝ))]; exact ⟨hxy, hy⟩) (hmin y)



end D5.S3.Analytic.Convexity.DerivativeHingeMajorization
