/- GID: D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/BoundaryEstimate
   generality: G
   mirror-B: D5/B/S3/Analytic/Laplace/QuantitativeFejerBoundary/BoundaryEstimate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Piecewise affine Fourier weights give quantitative oscillatory bounds for the regular part. -/

import D5.S3.Analytic.Laplace.QuantitativeFejerBoundary.DampedIdentity

/-! Piecewise affine Fourier weights give quantitative oscillatory bounds for the regular part. -/

namespace D5.S3.Analytic.Laplace.QuantitativeFejerBoundary

open D5.S3.Analytic.Fourier.AngularFejerKernel
  D5.S3.Analytic.Oscillation.OrdinateCounting
  D5.S3.Analytic.Laplace.PairedPoleRegularity
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

set_option backward.isDefEq.respectTransparency false

private lemma oscillatory_interval_bound {a c y B C : ℝ} {F F' : ℝ → ℂ}
    (hac : a ≤ c) (hy : 0 < y)
    (hF' : ContinuousOn F' (uIcc a c))
    (hder : ∀ t ∈ uIcc a c, HasDerivAt F (F' t) t)
    (hFa : ‖F a‖ ≤ B) (hFc : ‖F c‖ ≤ B)
    (hbound : ∀ t ∈ uIcc a c, ‖F' t‖ ≤ C) :
    ‖∫ t in a..c, F t * Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)‖
      ≤ (2*B+C*(c-a))/y := by
  let E : ℝ → ℂ := fun t => Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)
  have hE (t : ℝ) : HasDerivAt E (E t * ((y : ℂ)*Complex.I)) t := by
    simpa [E, mul_assoc] using
      (((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (y : ℂ)).mul_const Complex.I).cexp
  have hcE : Continuous E := by dsimp [E]; fun_prop
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hder (fun t _ => hE t) hF'.intervalIntegrable
    ((hcE.mul continuous_const).intervalIntegrable a c)
  have he : (∫ t in a..c, F t * E t) * ((y : ℂ)*Complex.I) =
      F c * E c - F a * E a - ∫ t in a..c, F' t * E t := by
    rw [← intervalIntegral.integral_mul_const]
    simpa only [mul_assoc] using hi
  have hnE (t : ℝ) : ‖E t‖ = 1 := by
    simpa [E, ← Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I (t*y)
  have hInt : ‖∫ t in a..c, F' t * E t‖ ≤ C*(c-a) := by
    simpa [abs_of_nonneg (sub_nonneg.mpr hac)] using
      intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t => F' t * E t) (a := a) (b := c)
        (fun t ht => by rw [norm_mul, hnE, mul_one]; exact hbound t (uIoc_subset_uIcc ht))
  have hb : ‖∫ t in a..c, F t * E t‖ * y ≤ 2*B+C*(c-a) := by
    have hh := norm_sub_le (F c*E c-F a*E a) (∫ t in a..c, F' t*E t)
    rw [← he, norm_mul] at hh
    have hyN : ‖(y : ℂ)*Complex.I‖ = y := by simp [abs_of_pos hy]
    rw [hyN] at hh
    have hh2 := norm_sub_le (F c*E c) (F a*E a)
    simp only [norm_mul, hnE, mul_one] at hh2
    linarith
  exact (le_div_iff₀ hy).mpr hb

private lemma affine_oscillatory_bound {a c α β b y B : ℝ} {Q Q' : ℝ → ℂ}
    (hb : 0 < b) (hy : 0 < y) (hlen : c-a=b) (hB : 0 ≤ B)
    (hQ' : ContinuousOn Q' (uIcc a c))
    (hder : ∀ t ∈ uIcc a c, HasDerivAt Q (Q' t) t)
    (hQ : ∀ t ∈ uIcc a c, ‖Q t‖+‖Q' t‖ ≤ B)
    (hα : |α| ≤ 1/b) (hA : ∀ t ∈ uIcc a c, |α*t+β| ≤ 1) :
    ‖∫ t in a..c, ((α*t+β : ℝ) : ℂ)*Q t*
      Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)‖ ≤ (3+b)*B/y := by
  have hac : a ≤ c := by linarith
  have hcQ : ContinuousOn Q (uIcc a c) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  let F : ℝ → ℂ := fun t => ((α*t+β : ℝ) : ℂ)*Q t
  let F' : ℝ → ℂ := fun t => (α : ℂ)*Q t+((α*t+β : ℝ) : ℂ)*Q' t
  have hcF' : ContinuousOn F' (uIcc a c) := by
    exact (continuous_const.continuousOn.mul hcQ).add
      ((by fun_prop : Continuous (fun t : ℝ => ((α*t+β : ℝ) : ℂ))).continuousOn.mul hQ')
  have hdF (t : ℝ) (ht : t ∈ uIcc a c) : HasDerivAt F (F' t) t := by
    have ha : HasDerivAt (fun t : ℝ => ((α*t+β : ℝ) : ℂ)) (α : ℂ) t := by
      simpa using (((hasDerivAt_id t).const_mul α).add_const β).ofReal_comp
    exact ha.mul (hder t ht)
  have hQ0 (t : ℝ) (ht : t ∈ uIcc a c) : ‖Q t‖ ≤ B := by
    linarith [hQ t ht, norm_nonneg (Q' t)]
  have hQ1 (t : ℝ) (ht : t ∈ uIcc a c) : ‖Q' t‖ ≤ B := by
    linarith [hQ t ht, norm_nonneg (Q t)]
  have hf (t : ℝ) (ht : t ∈ uIcc a c) : ‖F t‖ ≤ B := by
    calc
      _ = |α*t+β| * ‖Q t‖ := by simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1*B := mul_le_mul (hA t ht) (hQ0 t ht) (norm_nonneg _) (by norm_num)
      _ = B := one_mul _
  have hf' (t : ℝ) (ht : t ∈ uIcc a c) : ‖F' t‖ ≤ (1/b+1)*B := by
    calc
      _ ≤ ‖(α : ℂ)*Q t‖+‖((α*t+β : ℝ) : ℂ)*Q' t‖ := norm_add_le _ _
      _ = |α| * ‖Q t‖+|α*t+β| * ‖Q' t‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (1/b)*B+1*B := add_le_add
        (mul_le_mul hα (hQ0 t ht) (norm_nonneg _) (by positivity))
        (mul_le_mul (hA t ht) (hQ1 t ht) (norm_nonneg _) (by norm_num))
      _ = (1/b+1)*B := by ring
  have h := oscillatory_interval_bound hac hy hcF' hdF
    (hf a left_mem_uIcc) (hf c right_mem_uIcc) hf'
  have he : (2*B+((1/b+1)*B)*(c-a))/y=(3+b)*B/y := by
    rw [hlen]
    field_simp [hb.ne']
    <;> ring
  rw [he] at h
  exact h

private lemma shifted_phi_zero {b d t : ℝ} (hb : 0 < b)
    (ht : t ∉ Icc (d-b) (d+b)) : phi b (t-d)=0 := by
  apply phi_eq_zero hb
  by_contra h
  have hh : |t-d| < b := lt_of_not_ge h
  have := abs_lt.mp hh
  exact ht ⟨by linarith, by linarith⟩

private lemma tent_weighted_integrable {b d : ℝ} {Q : ℝ → ℂ} (hb : 0 < b)
    (hQ : ContinuousOn Q (Icc (d-b) (d+b))) :
    Integrable (fun t => (phi b (t-d) : ℂ)*Q t) := by
  have hc : ContinuousOn (fun t => (phi b (t-d) : ℂ)*Q t) (Icc (d-b) (d+b)) :=
    ((Complex.continuous_ofReal.comp ((phi_continuous b).comp
      (continuous_id.sub continuous_const))).continuousOn).mul hQ
  apply hc.integrableOn_Icc.integrable_of_forall_notMem_eq_zero
  intro t ht
  simp [shifted_phi_zero hb ht]

private lemma tent_oscillatory_bound {b d y B : ℝ} {Q Q' : ℝ → ℂ}
    (hb : 0 < b) (hy : 0 < y) (hB : 0 ≤ B)
    (hQ' : ContinuousOn Q' (Icc (d-b) (d+b)))
    (hder : ∀ t ∈ Icc (d-b) (d+b), HasDerivAt Q (Q' t) t)
    (hQ : ∀ t ∈ Icc (d-b) (d+b), ‖Q t‖+‖Q' t‖ ≤ B) :
    ‖∫ t, (phi b (t-d) : ℂ)*Q t*
      Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)‖ ≤ 6*(1+b)*B/y := by
  let E : ℝ → ℂ := fun t => Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)
  have hcQ : ContinuousOn Q (Icc (d-b) (d+b)) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun t => (phi b (t-d) : ℂ)*Q t*E t)
      (Icc (d-b) (d+b)) := by
    exact (((Complex.continuous_ofReal.comp ((phi_continuous b).comp
      (continuous_id.sub continuous_const))).continuousOn).mul hcQ).mul
      (by dsimp [E]; fun_prop : Continuous E).continuousOn
  have hleft : uIcc (d-b) d ⊆ Icc (d-b) (d+b) := by
    rw [uIcc_of_le (by linarith)]
    intro t ht; exact ⟨ht.1, by linarith [ht.2]⟩
  have hright : uIcc d (d+b) ⊆ Icc (d-b) (d+b) := by
    rw [uIcc_of_le (by linarith)]
    intro t ht; exact ⟨by linarith [ht.1], ht.2⟩
  have hL := affine_oscillatory_bound (Q := Q) (Q' := Q')
    (a := d-b) (c := d) (α := 1/b) (β := 1-d/b) hb hy (by ring) hB
    (hQ'.mono hleft) (fun t ht => hder t (hleft ht)) (fun t ht => hQ t (hleft ht))
    (by rw [abs_of_pos (by positivity : 0 < 1/b)]) (by
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      rw [abs_le]
      have h0 : 0 ≤ (t-(d-b))/b := div_nonneg (by linarith [ht.1]) hb.le
      have h1 : (t-(d-b))/b ≤ 1 := (div_le_one hb).mpr (by linarith [ht.2])
      have he : (1/b)*t+(1-d/b)=(t-(d-b))/b := by field_simp [hb.ne']; ring
      constructor <;> linarith)
  have hR := affine_oscillatory_bound (Q := Q) (Q' := Q')
    (a := d) (c := d+b) (α := -(1/b)) (β := 1+d/b) hb hy (by ring) hB
    (hQ'.mono hright) (fun t ht => hder t (hright ht)) (fun t ht => hQ t (hright ht))
    (by rw [abs_neg, abs_of_pos (by positivity : 0 < 1/b)]) (by
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      rw [abs_le]
      have h0 : 0 ≤ ((d+b)-t)/b := div_nonneg (by linarith [ht.2]) hb.le
      have h1 : ((d+b)-t)/b ≤ 1 := (div_le_one hb).mpr (by linarith [ht.1])
      have he : -(1/b)*t+(1+d/b)=((d+b)-t)/b := by field_simp [hb.ne']; ring
      constructor <;> linarith)
  have hφL (t : ℝ) (ht : t ∈ uIcc (d-b) d) :
      phi b (t-d)=(1/b)*t+(1-d/b) := by
    rw [uIcc_of_le (by linarith)] at ht
    have ha : t-d ≤ 0 := by linarith [ht.2]
    unfold phi
    rw [abs_of_nonpos ha, max_eq_right (by
      apply sub_nonneg.mpr
      exact (div_le_one hb).mpr (by linarith [ht.1]))]
    ring
  have hφR (t : ℝ) (ht : t ∈ uIcc d (d+b)) :
      phi b (t-d)=-(1/b)*t+(1+d/b) := by
    rw [uIcc_of_le (by linarith)] at ht
    have ha : 0 ≤ t-d := by linarith [ht.1]
    unfold phi
    rw [abs_of_nonneg ha, max_eq_right (by
      apply sub_nonneg.mpr
      exact (div_le_one hb).mpr (by linarith [ht.2]))]
    ring
  have he : (∫ t, (phi b (t-d) : ℂ)*Q t*E t) =
      (∫ t in (d-b)..d, (((1/b)*t+(1-d/b) : ℝ) : ℂ)*Q t*E t)+
      ∫ t in d..(d+b), ((-(1/b)*t+(1+d/b) : ℝ) : ℂ)*Q t*E t := by
    have hz (t : ℝ) (ht : t ∉ Icc (d-b) (d+b)) :
        (phi b (t-d) : ℂ)*Q t*E t=0 := by simp [shifted_phi_zero hb ht]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.mono hleft).intervalIntegrable (hc.mono hright).intervalIntegrable]
    congr 1
    · exact intervalIntegral.integral_congr (fun t ht => by rw [hφL t ht])
    · exact intervalIntegral.integral_congr (fun t ht => by rw [hφR t ht])
  change ‖∫ t, (phi b (t-d) : ℂ)*Q t*E t‖ ≤ _
  rw [he]
  have hn := norm_add_le
    (∫ t in (d-b)..d, (((1/b)*t+(1-d/b) : ℝ) : ℂ)*Q t*E t)
    (∫ t in d..(d+b), ((-(1/b)*t+(1+d/b) : ℝ) : ℂ)*Q t*E t)
  calc
    _ ≤ 2*((3+b)*B/y) := by linarith
    _ ≤ 6*(1+b)*B/y := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right hy).mpr
      nlinarith

private lemma admissible_oscillatory_bound {g w : ℝ → ℝ} {b M y B : ℝ}
    {Q Q' : ℝ → ℂ} (hb : 0 < b) (hy : 0 < y) (hB : 0 ≤ B)
    (had : Admissible g w b M)
    (hQ' : ContinuousOn Q' (Icc (-M) M))
    (hder : ∀ t ∈ Icc (-M) M, HasDerivAt Q (Q' t) t)
    (hQ : ∀ t ∈ Icc (-M) M, ‖Q t‖+‖Q' t‖ ≤ B) :
    ‖∫ t in Icc (-M) M, (w t : ℂ)*Q t*
      Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)‖ ≤ 12*(1+b)*B/y := by
  let E : ℝ → ℂ := fun t => Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)
  have hcE : Continuous E := by dsimp [E]; fun_prop
  have hcQ : ContinuousOn Q (Icc (-M) M) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hsub (d : ℝ) (hd : |d|+b ≤ M) : Icc (d-b) (d+b) ⊆ Icc (-M) M := by
    intro t ht
    exact ⟨by linarith [ht.1, neg_le_abs d], by linarith [ht.2, le_abs_self d]⟩
  have ht (d : ℝ) (hd : |d|+b ≤ M) :
      ‖∫ t, (phi b (t-d) : ℂ)*Q t*E t‖ ≤ 6*(1+b)*B/y :=
    tent_oscillatory_bound hb hy hB (hQ'.mono (hsub d hd))
      (fun t ht => hder t (hsub d hd ht)) (fun t ht => hQ t (hsub d hd ht))
  have hi (d : ℝ) (hd : |d|+b ≤ M) :
      Integrable (fun t => (phi b (t-d) : ℂ)*Q t*E t) := by
    simpa only [Pi.mul_apply, mul_assoc] using tent_weighted_integrable hb
      ((hcQ.mono (hsub d hd)).mul hcE.continuousOn)
  have hwzero (t : ℝ) (ht : t ∉ Icc (-M) M) : w t=0 := by
    have htm : M < |t| := by
      by_contra h
      exact ht (abs_le.mp (le_of_not_gt h))
    exact (admissible_laws hb had).2.2.2.2.2.2 t htm
  have heq : (∫ t in Icc (-M) M, (w t : ℂ)*Q t*E t) =
      ∫ t, (w t : ℂ)*Q t*E t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by simp [hwzero t ht])
  change ‖∫ t in Icc (-M) M, (w t : ℂ)*Q t*E t‖ ≤ _
  rw [heq]
  rcases had with ⟨_, rfl, hbM⟩ | ⟨U, hU, _, rfl, hUM⟩
  · have hh := ht 0 (by simpa using hbM)
    simp only [sub_zero] at hh
    exact hh.trans (by apply div_le_div_of_nonneg_right _ hy.le; nlinarith)
  · have hU0 : 0 < U := by linarith
    have hbM : b ≤ M := by linarith
    have h0 : |(0 : ℝ)|+b ≤ M := by simpa
    have hpos : |U|+b ≤ M := by rwa [abs_of_pos hU0]
    have hneg : |-U|+b ≤ M := by simpa only [abs_neg] using hpos
    let F₀ : ℝ → ℂ := fun t => (phi b (t-0) : ℂ)*Q t*E t
    let F₁ : ℝ → ℂ := fun t => (phi b (t-U) : ℂ)*Q t*E t
    let F₂ : ℝ → ℂ := fun t => (phi b (t-(-U)) : ℂ)*Q t*E t
    have hi0 : Integrable F₀ := hi 0 h0
    have hi1 : Integrable F₁ := hi U hpos
    have hi2 : Integrable F₂ := hi (-U) hneg
    have hfun : (fun t => (psi b U t : ℂ)*Q t*E t) =
        fun t => F₀ t-F₁ t/2-F₂ t/2 := by
      funext t
      dsimp [F₀, F₁, F₂, psi]
      simp only [sub_zero, sub_neg_eq_add]
      push_cast
      ring
    rw [hfun]
    have hs := integral_sub (hi0.sub (hi1.div_const 2)) (hi2.div_const 2)
    simp only [Pi.sub_apply] at hs
    rw [hs, integral_sub hi0 (hi1.div_const 2), integral_div, integral_div]
    have hn := norm_sub_le ((∫ t, F₀ t)-(∫ t, F₁ t)/2) ((∫ t, F₂ t)/2)
    have hn' := norm_sub_le (∫ t, F₀ t) ((∫ t, F₁ t)/2)
    simp only [norm_div, Complex.norm_ofNat] at hn hn'
    have hb0 := ht 0 h0
    have hb1 := ht U hpos
    have hb2 := ht (-U) hneg
    change ‖∫ t, F₀ t‖ ≤ _ at hb0
    change ‖∫ t, F₁ t‖ ≤ _ at hb1
    change ‖∫ t, F₂ t‖ ≤ _ at hb2
    have htwo : 12*(1+b)*B/y=2*(6*(1+b)*B/y) := by ring
    rw [htwo]
    linarith only [hn, hn', hb0, hb1, hb2]

lemma boundary_regular_integral_bound (S : Spectrum) (hN : CountAsymptotic S)
    {f : ℝ → ℝ} {k : ℕ} (D : PairedLaplaceData S f k) :
    ∃ A : ℝ, 0 < A ∧ ∀ (g w : ℝ → ℝ) (b M y : ℝ),
      0 < b → 4 ≤ M → 1 ≤ y → Admissible g w b M →
      ‖(((1/(2*Real.pi) : ℝ) : ℂ) *
        ∫ t in Icc (-M) M, (w t : ℂ)*regularPart S D.J M ((t : ℂ)*Complex.I)*
          Complex.exp (Complex.I*(t : ℂ)*(y : ℂ)))‖ ≤
        A*((1+b)*M^(max k 1)/y) := by
  obtain ⟨B, hB, hbound⟩ := regularized_boundary_bound S hN D
  refine ⟨12*B, by positivity, ?_⟩
  intro g w b M y hb hM hy had
  let R : Set ℂ := {s | |s.re| < D.eta ∧ |s.im| < M+1}
  have hR : IsOpen R := (isOpen_lt Complex.continuous_re.abs continuous_const).inter
    (isOpen_lt Complex.continuous_im.abs continuous_const)
  let G : ℂ → ℂ := regularPart S D.J M
  have hG : DifferentiableOn ℂ G R := regularPart_differentiableOn S hN D hM
  let Q : ℝ → ℂ := fun t => G ((t : ℂ)*Complex.I)
  let Q' : ℝ → ℂ := fun t => deriv G ((t : ℂ)*Complex.I)*Complex.I
  have hmap (t : ℝ) (ht : t ∈ Icc (-M) M) : (t : ℂ)*Complex.I ∈ R := by
    change |((t : ℂ)*Complex.I).re| < D.eta ∧ |((t : ℂ)*Complex.I).im| < M+1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, sub_self, abs_zero, Complex.mul_im, mul_one, add_zero]
    exact ⟨D.eta_pos, by linarith [abs_le.mpr ht]⟩
  have hcQ' : ContinuousOn Q' (Icc (-M) M) :=
    (((hG.deriv hR).continuousOn.comp (by fun_prop) hmap).mul continuous_const.continuousOn)
  have hdQ (t : ℝ) (ht : t ∈ Icc (-M) M) : HasDerivAt Q (Q' t) t := by
    have hdG := (hG.differentiableAt (hR.mem_nhds (hmap t ht))).hasDerivAt
    have hdI : HasDerivAt (fun z : ℂ => z*Complex.I) Complex.I (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const Complex.I
    exact (hdG.comp (t : ℂ) hdI).comp_ofReal
  have hQQ' (t : ℝ) (ht : t ∈ Icc (-M) M) : ‖Q t‖+‖Q' t‖ ≤ B*M^(max k 1) := by
    simpa only [Q, Q', G, norm_mul, Complex.norm_I, mul_one] using
      hbound M t hM (abs_le.mpr ht)
  have hosc := admissible_oscillatory_bound hb (by linarith : 0 < y)
    (show 0 ≤ B*M^(max k 1) by positivity) had hcQ' hdQ hQQ'
  have hc : ‖((1/(2*Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply (div_le_one (by positivity : 0 < 2*Real.pi)).mpr
    linarith [Real.two_le_pi]
  rw [norm_mul]
  calc
    _ ≤ ‖∫ t in Icc (-M) M, (w t : ℂ)*regularPart S D.J M ((t : ℂ)*Complex.I)*
        Complex.exp (Complex.I*(t : ℂ)*(y : ℂ))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hc
    _ = ‖∫ t in Icc (-M) M, (w t : ℂ)*Q t*
        Complex.exp ((t : ℂ)*(y : ℂ)*Complex.I)‖ := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by dsimp [Q,G]; congr 2 <;> ring)
    _ ≤ 12*(1+b)*(B*M^(max k 1))/y := hosc
    _ = (12*B)*((1+b)*M^(max k 1)/y) := by ring

end
end D5.S3.Analytic.Laplace.QuantitativeFejerBoundary
