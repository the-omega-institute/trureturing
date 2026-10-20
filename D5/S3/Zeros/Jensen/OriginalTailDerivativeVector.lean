/- GID: D5/S3/Zeros/Jensen/OriginalTailDerivativeVector
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/OriginalTailDerivativeVector
   mirror-E: none(waiver:universal-infinite-analytic-estimate)
   anchors: []
   utility: none
   digest: The complete derivative vector of the original primal theta tail. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.OriginalTailDerivativeVectorSources

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Jensen.OriginalTailDerivativeVector
open Real Set MeasureTheory Filter Polynomial
open scoped Topology
open OriginalPrimalTailProjection OriginalPrimalTailResponse
open NormalizedJensenDegreeLowering SourceJensenIntegralExtension
open private primalJet_zero primalJet_deriv shiftedBudget shifted_summable scale_summable
  flux_summable tailJet_summable_ray tailJet_deriv tailJet_continuous tailJet_eq_iterated
  adjoint_formula adjoint_deriv adjoint_second_deriv adjoint_square flux_eq from
  D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private mode_residual_integral residual_series later_mode_sum scale_gap full_flux_lower
  originalCoefficient originalPolynomial original_coefficient_recurrence
  original_polynomial_eval original_polynomial_origin original_polynomial_ode
  original_polynomial_energy polynomial_jet polynomial_adjoint
  polynomial_adjoint_deriv_limit polynomial_adjoint_square_integrable original_green
  original_moment_bridge original_source_split original_full_source exp_increment jet_one jet_two from
  D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

open private first_residual_64 second_residual_1100 from
  D5.S3.Zeros.Jensen.OriginalTailDerivativeVectorResiduals
open private parameterPolynomial parameter_derivative parameter_bound residual_pair_data
  five_green source_vector full_G_extraction resolvent_algebra reflected_node from
  D5.S3.Zeros.Jensen.OriginalTailDerivativeVectorSources

private theorem second_pair_integrable {N:ℕ} (hN:1≤N) (A α:ℝ) (p:ℝ[X]) :
    IntegrableOn (fun x:ℝ =>p.eval x*tailSecondResidual N A α x) (Ioi 0) := by
  have h:=residual_pair_data hN A α p
  change Integrable _ (volume.restrict (Ioi (0:ℝ)))
  convert! (h.2.2.1.const_mul (4*A^2)).sub h.2.2.2.1 using 1
  ext x; dsimp [tailSecondResidual,Pi.sub_apply]; ring

private theorem quantitative_vector {N n:ℕ} (hN:1≤N) (hn:1≤n) {a t:ℝ}
    (ht:0<t) (hαa:t/(2*(n:ℝ))≤a) (hk:0<originalFlux N)
    (hA:max 64 a≤modeScale (N+1)) :
    let A:=modeScale (N+1)
    let S:=4*A^2
    let Λ:=S+t
    let κ:=originalFlux N
    let I:=∫ x in Ioi (0:ℝ),originalB n t x*originalTail N x
    let D:=rawD n t (originalTail N)
    let M:=rawM2 n t (originalTail N)
    let G:=rawG n t (originalTail N)
    let c:=((2*(n:ℝ)+1)*S+(2*(n:ℝ)-3)*t)/((2*(n:ℝ)+1)*Λ)
    |Λ*I/κ-1|≤64/A ∧ |Λ^2*D/κ+1|≤2600/A ∧
    |Λ^3*M/(2*κ)-(S-3*t)|≤16000*Λ/A ∧
    |Λ^2*G/κ+c|≤(5200*(n:ℝ)+16000)/((2*(n:ℝ)+1)*A) ∧
    (5200*(n:ℝ)+16000)/((2*(n:ℝ)+1)*A)≤21200/(3*A) := by
  let A:=modeScale (N+1)
  let α:=t/(2*(n:ℝ))
  let S:=4*A^2
  let Λ:=S+t
  let κ:=originalFlux N
  have hκ:0<κ := hk
  let Q:=originalTail N
  let R:=tailResidual N A α
  let R₂:=tailSecondResidual N A α
  let I:=∫ x in Ioi (0:ℝ),originalB n t x*Q x
  let D:=rawD n t Q
  let M:=rawM2 n t Q
  let U:=∫ x in Ioi (0:ℝ),originalB n t x*R x
  let V:=rawD n t R
  let Y:=rawM2 n t R
  have h64:64≤A := (le_max_left 64 a).trans hA
  have hA0:0<A := by linarith
  have hα:0≤α := by dsimp [α]; positivity
  have haA:a≤A := (le_max_right 64 a).trans hA
  have hαA:α≤A := hαa.trans haA
  have r₁:=first_residual_64 hN hA hα hαa
  have r₂:=second_residual_1100 hN hA hα hαa
  have hB (x:ℝ) (hx:0≤x):|originalB n t x|≤exp (a*x^2/2) := by
    have h:=original_polynomial_energy hn ht hx
    rw [original_polynomial_eval] at h
    exact h.trans (exp_le_exp.mpr (by nlinarith [sq_nonneg x]))
  have hb (x:ℝ) (hx:0≤x):|originalb n t x|≤x^2*exp (a*x^2/2)/2 := by
    exact (parameter_bound hn ht hx).trans (by gcongr)
  have hiU:IntegrableOn (fun x:ℝ =>originalB n t x*R x) (Ioi 0) := by
    simpa only [original_polynomial_eval] using
      (residual_pair_data hN A α (originalPolynomial n t)).2.2.1
  have hiW₁:IntegrableOn (fun x:ℝ =>originalb n t x*R₂ x) (Ioi 0) :=
    second_pair_integrable hN A α (parameterPolynomial n t)
  have hiW₂:IntegrableOn (fun x:ℝ =>x^2*originalB n t x*R₂ x) (Ioi 0) := by
    have hi:Integrable (fun x:ℝ =>(X^2*originalPolynomial n t).eval x*tailSecondResidual N A α x)
        (volume.restrict (Ioi (0:ℝ))) := second_pair_integrable hN A α (X^2*originalPolynomial n t)
    change Integrable _ (volume.restrict (Ioi (0:ℝ)))
    simpa only [eval_mul,eval_pow,eval_X,original_polynomial_eval] using hi
  have hu:|U|≤64*κ/A := by
    apply abs_integral_le_integral_abs.trans
    apply (integral_mono_ae hiU.abs r₁.1 ?_).trans r₁.2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hB x hx.le) (abs_nonneg _)
  have hw₁:|rawD n t R₂|≤550*κ/A := by
    apply abs_integral_le_integral_abs.trans
    have hnorm:(∫ x in Ioi (0:ℝ),|originalb n t x*R₂ x|)≤
        (1/2)*(∫ x in Ioi (0:ℝ),x^2*exp (a*x^2/2)*|R₂ x|) := by
      rw [←integral_const_mul]
      apply integral_mono_ae hiW₁.abs (r₂.1.const_mul (1/2))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [abs_mul]
      calc
        _ ≤ (x^2*exp (a*x^2/2)/2)*|R₂ x| :=
          mul_le_mul_of_nonneg_right (hb x hx.le) (abs_nonneg _)
        _ = _ := by ring
    have hr₂:=r₂.2
    change (∫ x in Ioi (0:ℝ),x^2*exp (a*x^2/2)*|R₂ x|)≤1100*κ/A at hr₂
    exact hnorm.trans (by
      convert! mul_le_mul_of_nonneg_left hr₂ (by norm_num : (0:ℝ)≤1/2) using 1 <;> ring)
  have hw₂:|rawM2 n t R₂|≤1100*κ/A := by
    apply abs_integral_le_integral_abs.trans
    apply (integral_mono_ae hiW₂.abs r₂.1 ?_).trans r₂.2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [abs_mul,abs_pow,abs_of_nonneg (show 0≤x from hx.le)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hB x hx.le) (sq_nonneg x)) (abs_nonneg _)
  obtain ⟨g₀,g₁,g₂,g₃,g₄⟩:=five_green hN hn ht A
  have h:=resolvent_algebra h64 hα hαA ht hk (rfl:S=4*A^2) (rfl:Λ=S+t)
    g₀ g₁ g₂ g₃ g₄ hu hw₁ hw₂
  have hΛ:0<Λ := h.1
  have hi:=h.2.2.2.1
  have hd:=h.2.2.2.2.1
  have hm:=h.2.2.2.2.2
  change A*|Λ*I-κ|≤64*κ at hi
  change A*|Λ^2*D+κ|≤2600*κ at hd
  change A*|Λ^3*M-2*κ*(S-3*t)|≤31983*Λ*κ at hm
  have heI:|Λ*I/κ-1|≤64/A := by
    rw [show Λ*I/κ-1=(Λ*I-κ)/κ by field_simp [hκ.ne'] <;> ring,abs_div,abs_of_pos hk]
    apply (div_le_iff₀ hκ).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hA0).mpr
    nlinarith only [hi]
  have heD:|Λ^2*D/κ+1|≤2600/A := by
    rw [show Λ^2*D/κ+1=(Λ^2*D+κ)/κ by field_simp [hκ.ne'] <;> ring,abs_div,abs_of_pos hk]
    apply (div_le_iff₀ hκ).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hA0).mpr
    nlinarith only [hd]
  have heM:|Λ^3*M/(2*κ)-(S-3*t)|≤16000*Λ/A := by
    rw [show Λ^3*M/(2*κ)-(S-3*t)=(Λ^3*M-2*κ*(S-3*t))/(2*κ) by
      field_simp [hκ.ne'] <;> ring,abs_div,abs_of_pos (by positivity : 0<2*κ)]
    apply (div_le_iff₀ (by positivity : 0<2*κ)).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hA0).mpr
    nlinarith only [hm,mul_pos hΛ hk]
  have hn0:0<2*(n:ℝ)+1 := by positivity
  have hn1:(1:ℝ)≤n := by exact_mod_cast hn
  let c:=((2*(n:ℝ)+1)*S+(2*(n:ℝ)-3)*t)/((2*(n:ℝ)+1)*Λ)
  have heG:|Λ^2*rawG n t Q/κ+c|≤(5200*(n:ℝ)+16000)/((2*(n:ℝ)+1)*A) := by
    have hid:Λ^2*rawG n t Q/κ+c=
        (2*(n:ℝ)*(Λ^2*D/κ+1)-
          (Λ^3*M/(2*κ)-(S-3*t))/Λ)/(2*(n:ℝ)+1) := by
      dsimp only [rawG,c,D,M]
      field_simp [hκ.ne',hΛ.ne']
      change _ = _
      dsimp only [Λ]
      ring
    rw [hid,abs_div,abs_of_pos hn0]
    apply (div_le_iff₀ hn0).mpr
    have htri:|2*(n:ℝ)*(Λ^2*D/κ+1)-(Λ^3*M/(2*κ)-(S-3*t))/Λ|≤
        |2*(n:ℝ)*(Λ^2*D/κ+1)|+|(Λ^3*M/(2*κ)-(S-3*t))/Λ| := by
      have hh:=abs_add_le (2*(n:ℝ)*(Λ^2*D/κ+1)) (-((Λ^3*M/(2*κ)-(S-3*t))/Λ))
      rw [←sub_eq_add_neg,abs_neg] at hh
      exact hh
    rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*(n:ℝ)),abs_div,abs_of_pos hΛ] at htri
    have hd':=mul_le_mul_of_nonneg_left heD (show 0≤2*(n:ℝ) by positivity)
    have hm':= (div_le_div_of_nonneg_right heM hΛ.le)
    have hh:16000*Λ/A/Λ=16000/A := by field_simp <;> ring
    rw [hh] at hm'
    have hh':(5200*(n:ℝ)+16000)/((2*(n:ℝ)+1)*A)*(2*(n:ℝ)+1)=
        2*(n:ℝ)*(2600/A)+16000/A := by field_simp <;> ring
    rw [hh']
    linarith
  have hconst:(5200*(n:ℝ)+16000)/((2*(n:ℝ)+1)*A)≤21200/(3*A) := by
    apply (div_le_div_iff₀ (by positivity : 0<(2*(n:ℝ)+1)*A) (by positivity : 0<3*A)).mpr
    nlinarith
  exact ⟨heI,heD,heM,heG,hconst⟩

private theorem vector_signs {n:ℕ} (hn:1≤n) {A α t S Λ κ Z D G:ℝ}
    (hA:72000≤A) (ht:0<t) (hκ:0<κ) (hZ:0<Z)
    (hα:α=t/(2*(n:ℝ))) (hαA:α≤A) (hS:S=4*A^2) (hΛ:Λ=S+t)
    (hD:|Λ^2*D/κ+1|≤2600/A)
    (hG:|Λ^2*G/κ+((2*(n:ℝ)+1)*S+(2*(n:ℝ)-3)*t)/((2*(n:ℝ)+1)*Λ)|≤21200/(3*A)) :
    D≤-κ/(2*Λ^2) ∧ G≤-κ/(10*Λ^2) ∧
    κ^2/(20*Λ^4)≤D*G ∧ 0<κ^2/(20*Λ^4) ∧
    (2/Z)*D≤-κ/(Z*Λ^2) ∧ (2/Z)*G≤-κ/(5*Z*Λ^2) ∧
    κ^2/(5*Z^2*Λ^4)≤((2/Z)*D)*((2/Z)*G) ∧ 0<κ^2/(5*Z^2*Λ^4) := by
  have hA0:0<A := by linarith
  have hS0:0<S := by rw [hS]; positivity
  have hΛ0:0<Λ := by linarith
  have hn0:0<2*(n:ℝ)+1 := by positivity
  have hc:(1/5:ℝ)≤((2*(n:ℝ)+1)*S+(2*(n:ℝ)-3)*t)/((2*(n:ℝ)+1)*Λ) := by
    apply (le_div_iff₀ (by positivity : 0<(2*(n:ℝ)+1)*Λ)).mpr
    by_cases hn2:2≤n
    · have hn2r:(2:ℝ)≤n := by exact_mod_cast hn2
      have hnt:0≤(8*(n:ℝ)-16)*t := mul_nonneg (by linarith) ht.le
      have hns:0≤(8*(n:ℝ)+4)*S := by positivity
      nlinarith only [hΛ,hnt,hns]
    · have hn1:n=1 := by omega
      subst n
      norm_num at hα ⊢
      have htA:t≤2*A := by rw [hα] at hαA; linarith
      nlinarith only [hΛ,hS,htA,hA]
  have heD:2600/A≤1/2 := by apply (div_le_iff₀ hA0).mpr; linarith
  have heG:21200/(3*A)≤1/10 := by apply (div_le_iff₀ (by positivity : 0<3*A)).mpr; linarith
  have hd:D≤-κ/(2*Λ^2) := by
    have h:= (abs_le.mp (hD.trans heD)).2
    have hh:Λ^2*D≤-κ/2 := by have h':=(div_le_iff₀ hκ).mp (show Λ^2*D/κ≤-1/2 by linarith); nlinarith
    apply (le_div_iff₀ (by positivity : 0<2*Λ^2)).mpr
    nlinarith only [hh]
  have hg:G≤-κ/(10*Λ^2) := by
    have h:= (abs_le.mp (hG.trans heG)).2
    have hh:Λ^2*G≤-κ/10 := by have h':=(div_le_iff₀ hκ).mp (show Λ^2*G/κ≤-1/10 by linarith); nlinarith
    apply (le_div_iff₀ (by positivity : 0<10*Λ^2)).mpr
    nlinarith only [hh]
  have hgn:G≤0 := hg.trans (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ.le) (by positivity))
  have hdn:-κ/(2*Λ^2)≤0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ.le) (by positivity)
  have hprod:κ^2/(20*Λ^4)≤D*G := by
    calc
      _ = (-κ/(2*Λ^2))*(-κ/(10*Λ^2)) := by field_simp; ring
      _ ≤ (-κ/(2*Λ^2))*G := mul_le_mul_of_nonpos_left hg hdn
      _ ≤ D*G := mul_le_mul_of_nonpos_right hd hgn
  have hscale:0≤2/Z := by positivity
  have hdnorm:(2/Z)*D≤-κ/(Z*Λ^2) := by
    have h:=mul_le_mul_of_nonneg_left hd hscale
    convert! h using 1 <;> field_simp <;> ring
  have hgnorm:(2/Z)*G≤-κ/(5*Z*Λ^2) := by
    have h:=mul_le_mul_of_nonneg_left hg hscale
    convert! h using 1 <;> field_simp <;> ring
  have hpnorm:κ^2/(5*Z^2*Λ^4)≤((2/Z)*D)*((2/Z)*G) := by
    have h:=mul_le_mul_of_nonneg_left hprod (show 0≤4/Z^2 by positivity)
    convert! h using 1 <;> field_simp <;> ring
  exact ⟨hd,hg,hprod,by positivity,hdnorm,hgnorm,hpnorm,by positivity⟩

private theorem parameter_at_zero {n:ℕ} (hn:1≤n) (x:ℝ) :
    originalb n 0 x= -x^2/2 := by
  have hn0:(n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  simp only [originalb,parameterPolynomial,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  rw [Finset.sum_eq_single 1]
  · simp only [originalCoefficient,Nat.descFactorial_one,pow_one,one_pow,mul_one,
      Nat.cast_one,Nat.cast_ofNat,one_mul,Nat.sub_self,pow_zero]
    norm_num
    field_simp [hn0] <;> ring
  · intro j hj hj1
    by_cases hj0:j=0
    · subst j; simp
    · have hpow:0<j-1 := by omega
      simp [zero_pow (ne_of_gt hpow)]
  · intro h
    exact False.elim (h (by simp only [Finset.mem_range]; omega))

/-- The complete literal tail derivative vector and its exact full-source transports.
The head product and both cross terms have no sign assertion. -/
theorem original_tail_derivative_vector :
  0<fullZ ∧ (∫ x:ℝ,sourceThetaDensity x)=1 ∧
  ∀ a:ℝ,0<a → ∃ C:ℝ,0<C ∧
    ∀ N n:ℕ,1≤N → 1≤n → ∀ t:ℝ,0<t → t/(2*(n:ℝ))≤a →
      let A:=modeScale (N+1)
      let I:=∫ x in Ioi (0:ℝ),originalB n t x*originalTail N x
      let H:=∫ x in Ioi (0:ℝ),originalB n t x*originalHead N x
      0<originalFlux N ∧
      IntegrableOn (fun x:ℝ =>originalB n t x*originalTail N x) (Ioi 0) ∧
      IntegrableOn (fun x:ℝ =>originalB n t x*originalHead N x) (Ioi 0) ∧
      Integrable (fun x:ℝ =>originalB n t x*sourceThetaDensity x) ∧
      originalJ n t=(sourceP n).eval (-t) ∧ originalJ n t=(2/fullZ)*(H+I) ∧
      (sourceJensenPolynomial n).eval (((-t:ℝ):ℂ))=(originalJ n t:ℂ) ∧
      sourceJensenPolynomial n=normalizedJensen sourceThetaCoefficient n ∧
      ((sourceJensenPolynomial n).eval (((-t:ℝ):ℂ))=0 ↔ originalJ n t=0) ∧
      |t*I/originalFlux N-1|≤C*((N:ℝ)+1)^4/t ∧
      (∀ x:ℝ,HasDerivAt (fun u:ℝ =>originalB n u x) (originalb n t x) t) ∧
      (∀ x:ℝ,originalb n 0 x= -x^2/2) ∧
      (
    IntegrableOn (fun x =>originalb n t x*originalTail N x) (Ioi 0) ∧
    IntegrableOn (fun x =>x^2*originalB n t x*originalTail N x) (Ioi 0) ∧
    IntegrableOn (fun x =>originalb n t x*originalHead N x) (Ioi 0) ∧
    IntegrableOn (fun x =>x^2*originalB n t x*originalHead N x) (Ioi 0) ∧
    Integrable (fun x:ℝ =>originalb n t x*sourceThetaDensity x) ∧
    Integrable (fun x:ℝ =>x^2*originalB n t x*sourceThetaDensity x) ∧
    HasDerivAt (fun u =>∫ x in Ioi (0:ℝ),originalB n u x*originalTail N x)
      (rawD n t (originalTail N)) t ∧
    HasDerivAt (fun u =>∫ x in Ioi (0:ℝ),originalB n u x*originalHead N x)
      (rawD n t (originalHead N)) t ∧
    HasDerivAt (originalJ n) (fullD n t) t ∧
    fullD n t= -(sourceP n).derivative.eval (-t) ∧
    fullD n t=(2/fullZ)*(rawD n t (originalHead N)+rawD n t (originalTail N)) ∧
    fullM2 n t=(2/fullZ)*(rawM2 n t (originalHead N)+rawM2 n t (originalTail N)) ∧
    fullG n t=(2/fullZ)*(rawG n t (originalHead N)+rawG n t (originalTail N)) ∧
    rawG n t (originalTail N)=
      -∑ k∈Finset.range (n+1),originalCoefficient n 1 k*t^k*
        (∫ x in Ioi (0:ℝ),x^(2*(k+1))*originalTail N x)/(2*(2*(k:ℝ)+1)) ∧
    rawG n t (originalHead N)=
      -∑ k∈Finset.range (n+1),originalCoefficient n 1 k*t^k*
        (∫ x in Ioi (0:ℝ),x^(2*(k+1))*originalHead N x)/(2*(2*(k:ℝ)+1))) ∧ (
    fullG n t= -∑ k∈Finset.range (n+1),
      (-1:ℝ)^k*(n.descFactorial k:ℝ)/(n:ℝ)^k*((k:ℝ)+1)*sourceThetaCoefficient (k+1)*t^k ∧
    HasDerivAt (originalJ (n+1)) (fullG n t) (((n+1:ℕ):ℝ)/(n:ℝ)*t)) ∧ (
    let α:=t/(2*(n:ℝ))
    let S:=4*A^2
    let Λ:=S+t
    let Q:=originalTail N
    let R:=tailResidual N A α
    let R₂:=tailSecondResidual N A α
    let I:=∫ x in Ioi (0:ℝ),originalB n t x*Q x
    let U:=∫ x in Ioi (0:ℝ),originalB n t x*R x
    Λ*I=originalFlux N+U ∧
    (Λ-2*α)*rawD n t Q= -I+rawD n t R ∧
    (Λ+2*α)*rawM2 n t Q=2*I+8*t*rawD n t Q+rawM2 n t R ∧
    (Λ-2*α)*rawD n t R= -U+rawD n t R₂ ∧
    (Λ+2*α)*rawM2 n t R=2*U+8*t*rawD n t R+rawM2 n t R₂) ∧
      (max 64 a≤A → (
    IntegrableOn (fun x:ℝ => exp (a*x^2/2)*|tailResidual N (modeScale (N+1)) (t/(2*(n:ℝ))) x|) (Ioi 0) ∧
    (∫ x in Ioi (0:ℝ),exp (a*x^2/2)*|tailResidual N (modeScale (N+1)) (t/(2*(n:ℝ))) x|) ≤
      64*originalFlux N/modeScale (N+1)) ∧ (
    IntegrableOn (fun x:ℝ => x^2*exp (a*x^2/2)*
      |tailSecondResidual N (modeScale (N+1)) (t/(2*(n:ℝ))) x|) (Ioi 0) ∧
    (∫ x in Ioi (0:ℝ),x^2*exp (a*x^2/2)*
      |tailSecondResidual N (modeScale (N+1)) (t/(2*(n:ℝ))) x|) ≤1100*originalFlux N/modeScale (N+1)) ∧ (
    let A:=modeScale (N+1)
    let S:=4*A^2
    let Λ:=S+t
    let κ:=originalFlux N
    let I:=∫ x in Ioi (0:ℝ),originalB n t x*originalTail N x
    let D:=rawD n t (originalTail N)
    let M:=rawM2 n t (originalTail N)
    let G:=rawG n t (originalTail N)
    let c:=((2*(n:ℝ)+1)*S+(2*(n:ℝ)-3)*t)/((2*(n:ℝ)+1)*Λ)
    |Λ*I/κ-1|≤64/A ∧ |Λ^2*D/κ+1|≤2600/A ∧
    |Λ^3*M/(2*κ)-(S-3*t)|≤16000*Λ/A ∧
    |Λ^2*G/κ+c|≤(5200*(n:ℝ)+16000)/((2*(n:ℝ)+1)*A) ∧
    (5200*(n:ℝ)+16000)/((2*(n:ℝ)+1)*A)≤21200/(3*A))) ∧
      (max 72000 a≤A → (
    rawD n t (originalTail N)≤-originalFlux N/(2*(4*(modeScale (N+1))^2+t)^2) ∧
    rawG n t (originalTail N)≤-originalFlux N/(10*(4*(modeScale (N+1))^2+t)^2) ∧
    (originalFlux N)^2/(20*(4*(modeScale (N+1))^2+t)^4)≤rawD n t (originalTail N)*rawG n t (originalTail N) ∧
    0<(originalFlux N)^2/(20*(4*(modeScale (N+1))^2+t)^4) ∧
    (2/fullZ)*rawD n t (originalTail N)≤-originalFlux N/(fullZ*(4*(modeScale (N+1))^2+t)^2) ∧
    (2/fullZ)*rawG n t (originalTail N)≤-originalFlux N/(5*fullZ*(4*(modeScale (N+1))^2+t)^2) ∧
    (originalFlux N)^2/(5*fullZ^2*(4*(modeScale (N+1))^2+t)^4)≤
      ((2/fullZ)*rawD n t (originalTail N))*((2/fullZ)*rawG n t (originalTail N)) ∧
    0<(originalFlux N)^2/(5*fullZ^2*(4*(modeScale (N+1))^2+t)^4))) ∧
      (originalJ n t=0 → (
    let δ:ℝ:=(n:ℝ)/((n+1:ℕ):ℝ)
    let ξ:=δ/t
    let q:=sourceQ (n+1)
    0<ξ ∧ q.derivative.eval ξ=0 ∧
    ((n+1:ℕ):ℝ)*q.eval ξ=ξ^n*fullG n t ∧
    ξ^2*q.derivative.derivative.eval ξ= -(n:ℝ)*ξ^n*fullD n t ∧
    q.eval ξ*q.derivative.derivative.eval ξ=
      -((n:ℝ)/((n+1:ℕ):ℝ))*ξ^(2*n-2)*fullD n t*fullG n t ∧
    (fullD n t≠0 ↔ q.derivative.derivative.eval ξ≠0) ∧
    (fullD n t≠0 →
      SourceJensenPositiveExtension.sourceCoupling (n+1) ξ=
        (ξ^2/(n:ℝ))*(fullG n t/fullD n t) ∧
      (0≤SourceJensenPositiveExtension.sourceCoupling (n+1) ξ ↔
        0≤fullD n t*fullG n t)))) ∧
      fullD n t*fullG n t=(4/fullZ^2)*(
        rawD n t (originalHead N)*rawG n t (originalHead N)+
        rawD n t (originalHead N)*rawG n t (originalTail N)+
        rawD n t (originalTail N)*rawG n t (originalHead N)+
        rawD n t (originalTail N)*rawG n t (originalTail N)) := by
  obtain ⟨hZ,hMass,K,hK,hall⟩:=original_primal_tail_response
  refine ⟨hZ,hMass,?_⟩
  intro a ha
  obtain ⟨C,hC,hCn⟩:=hall a ha
  refine ⟨C,hC,?_⟩
  intro N n hN hn t ht hαa
  dsimp only
  obtain ⟨hk,hiQ,hiH,hiF,hP,hJ,hComplex,hPoly,hNode,hAllP,hRest⟩:=hCn N n hN hn t ht hαa
  have sv:=source_vector hN hn t
  refine ⟨hk,hiQ,hiH,hiF,hP,hJ,hComplex,hPoly,hNode,hAllP,
    fun x =>parameter_derivative n t x,parameter_at_zero hn,
    sv,full_G_extraction hn t,five_green hN hn ht (modeScale (N+1)),?_,?_,
    fun hnode =>reflected_node hn ht hnode,?_⟩
  · intro hA
    have hα:0≤t/(2*(n:ℝ)) := by positivity
    exact ⟨first_residual_64 hN hA hα hαa,second_residual_1100 hN hA hα hαa,
      quantitative_vector hN hn ht hαa hk hA⟩
  · intro hA
    have h72000:72000≤modeScale (N+1) := (le_max_left 72000 a).trans hA
    have h64:max 64 a≤modeScale (N+1) := by
      apply max_le
      · linarith
      · exact (le_max_right 72000 a).trans hA
    have q:=quantitative_vector hN hn ht hαa hk h64
    exact vector_signs hn h72000 ht hk hZ rfl
      (hαa.trans ((le_max_right 72000 a).trans hA)) rfl rfl q.2.1 (q.2.2.2.1.trans q.2.2.2.2)
  · have hD:=sv.2.2.2.2.2.2.2.2.2.2.1
    have hG:=sv.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [hD,hG]
    ring

#print axioms original_tail_derivative_vector

end D5.S3.Zeros.Jensen.OriginalTailDerivativeVector
