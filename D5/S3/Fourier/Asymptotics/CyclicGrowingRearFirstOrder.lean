/- GID: D5/S3/Fourier/Asymptotics/CyclicGrowingRearFirstOrder
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicGrowingRearFirstOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-order expansion of the scaled antipodal fit at a growing-window threshold. -/

import D5.S3.Fourier.Asymptotics.CyclicGrowingSupport

/-! The next finite contribution to the rear moment after the leading parabola. -/

open Finset Matrix Filter Asymptotics
open scoped Topology
open D5.S3.Fourier.Asymptotics.CyclicGrowingSupport
open D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
open D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
open D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation

namespace D5.S3.Fourier.Asymptotics.CyclicGrowingRearFirstOrder

noncomputable section

set_option autoImplicit false

private theorem inv_nat : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private theorem lower_mesh_powers {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5*(h n)^2) atTop (𝓝 K)) :
    Tendsto (fun n : ℕ => (n : ℝ)^3*(h n)^2) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ)*(h n)^2) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n : ℝ)^4*((n : ℝ)*h n)^4) atTop (𝓝 0) := by
  constructor
  · have ht := hK.mul (inv_nat.pow 2)
    apply (show Tendsto (fun n : ℕ => ((n : ℝ)^5*(h n)^2)*((n : ℝ)⁻¹)^2)
      atTop (𝓝 0) by simpa using ht).congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from hn).ne'
    field_simp [hn0]
  constructor
  · have ht := hK.mul (inv_nat.pow 4)
    apply (show Tendsto (fun n : ℕ => ((n : ℝ)^5*(h n)^2)*((n : ℝ)⁻¹)^4)
      atTop (𝓝 0) by simpa using ht).congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from hn).ne'
    field_simp [hn0]
  · have ht := (hK.pow 2).mul (inv_nat.pow 2)
    apply (show Tendsto (fun n : ℕ => ((n : ℝ)^5*(h n)^2)^2*((n : ℝ)⁻¹)^2)
      atTop (𝓝 0) by simpa using ht).congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from hn).ne'
    field_simp [hn0]

private theorem lattice_C_first_order :
    Tendsto (fun n : ℕ => (n : ℝ)*(latticeCoeffs n 1+3/4)) atTop (𝓝 (9/8)) := by
  let z := fun n : ℕ => (4/3 : ℝ)+2*(n:ℝ)⁻¹-(1/3)*(n:ℝ)⁻¹^2-(1/2)*(n:ℝ)⁻¹^3
  let b := fun n : ℕ => (2:ℝ)-(1/3)*(n:ℝ)⁻¹-(1/2)*(n:ℝ)⁻¹^2
  have hz : Tendsto z atTop (𝓝 (4/3)) := by
    simpa [z] using (((tendsto_const_nhds.add (inv_nat.const_mul (2:ℝ)) (a:= (4/3:ℝ))).sub
      ((inv_nat.pow 2).const_mul (1/3:ℝ))).sub ((inv_nat.pow 3).const_mul (1/2:ℝ)))
  have hb : Tendsto b atTop (𝓝 2) := by
    simpa [b] using ((tendsto_const_nhds.sub (inv_nat.const_mul (1/3:ℝ)) (a:= (2:ℝ))).sub
      ((inv_nat.pow 2).const_mul (1/2:ℝ)))
  have ht := ((hb.const_mul (3/4:ℝ)).div hz (by norm_num : (4/3:ℝ)≠0))
  have hlim : (3/4:ℝ)*2/(4/3)=9/8 := by norm_num
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ),hz.eventually_ne (by norm_num : (4/3:ℝ)≠0)]
    with n hn hzz
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from hn).ne'
  have hnorm : normalizer n (radiusSq n) = (n:ℝ)^3*z n := by
    rw [normalizer_formula]
    unfold radiusSq
    dsimp [z]
    field_simp [hn0]
    ring
  have hprod : (n:ℝ)*(z n-4/3)=b n := by
    dsimp [z,b]
    field_simp [hn0]
    ring
  change 3/4*b n/z n = (n:ℝ)*(-(n:ℝ)^3/normalizer n (radiusSq n)+3/4)
  rw [hnorm,← hprod]
  field_simp [hn0,hzz]
  ring

private theorem fitted_C_first_order {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5*(h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) :
    Tendsto (fun n : ℕ => (n : ℝ)*(coefficientFit S n (h n) 1+3/4))
      atTop (𝓝 (9/8)) := by
  have he := isBigO_pi.mp (refined_coefficients (hK.isBigO_one ℝ) S hS) (1:Fin 2)
  change (fun n : ℕ => (n:ℝ)^3*(coefficientFit S n (h n) 1-latticeCoeffs n 1))
      =O[atTop] (fun _ => (1:ℝ)) at he
  have he' : (fun n : ℕ => ((n:ℝ)^3*(coefficientFit S n (h n) 1-latticeCoeffs n 1))
      *((n:ℝ)⁻¹)^2) =O[atTop] (fun n => ((n:ℝ)⁻¹)^2) := by
    simpa only [Pi.one_apply,one_mul] using he.mul
      (isBigO_refl (fun n : ℕ => ((n:ℝ)⁻¹)^2) atTop)
  have hzero : Tendsto (fun n : ℕ => (n:ℝ)*(coefficientFit S n (h n) 1-latticeCoeffs n 1))
      atTop (𝓝 0) := by
    apply (he'.trans_tendsto (by simpa using inv_nat.pow 2)).congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from hn).ne'
    field_simp [hn0]
  apply (show Tendsto (fun n : ℕ => (n:ℝ)*(coefficientFit S n (h n) 1-latticeCoeffs n 1)
      +(n:ℝ)*(latticeCoeffs n 1+3/4)) atTop (𝓝 (9/8))
      by simpa using hzero.add lattice_C_first_order).congr
  intro n
  ring


private theorem scaled_front_last_row {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n : ℝ)^5*(h n)^2) atTop (𝓝 K)) (i : Fin 3) :
    Tendsto (fun n : ℕ => (n : ℝ)*frontMatrix n ((n:ℝ)*h n) 2 i) atTop (𝓝 0) := by
  let u := fun n : ℕ => (n:ℝ)*h n
  let w := fun n : ℕ => fun j : ℤ => (1-Real.cos ((j:ℝ)/n*u n))/2
  let f := fun n : ℕ => fun i : Fin 2 => fun j : ℤ => frontFeatures (u n) ((j:ℝ)/n) i
  have hbound := (lower_mesh_powers hK).2.2
  have hU := (critical_bound_mesh_limits (hK.isBigO_one ℝ)).2.1
  have hnonneg (n : ℕ) (j : ℤ) : 0 ≤ w n j := by
    dsimp [w]
    linarith [Real.cos_le_one ((j:ℝ)/n*u n)]
  have hfront (i : Fin 2) :
      Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)^2*(∑ j∈latticeInterval n,w n j^2*f n i j)))
        atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => 3*(n:ℝ)^4*(u n)^4/16) atTop (𝓝 0) := by
      apply (show Tendsto (fun n : ℕ => 3/16*((n:ℝ)^4*(u n)^4)) atTop (𝓝 0)
        by simpa using hbound.const_mul (3/16:ℝ)).congr
      intro n
      ring
    apply squeeze_zero' _ _ ht
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
      refine mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (sq_nonneg _) (sum_nonneg ?_))
      intro j hj
      exact mul_nonneg (sq_nonneg _) (front_site_bounds n hn (u n) hj i).2.1
    · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
      calc
        _ ≤ (n:ℝ)*(3*(n:ℝ)^3*(u n)^4/16) :=
          mul_le_mul_of_nonneg_left (front_mixed_block n hn (u n) i).2.1 (Nat.cast_nonneg n)
        _ = _ := by ring
  have hlast : Tendsto (fun n : ℕ => (n:ℝ)*(∑ j∈latticeInterval n,w n j^3)) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => 3/64*((n:ℝ)^4*(u n)^4)) atTop (𝓝 0) := by
      simpa using hbound.const_mul (3/64:ℝ)
    apply squeeze_zero' (Eventually.of_forall fun n =>
      mul_nonneg (Nat.cast_nonneg n) (sum_nonneg fun j _ => pow_nonneg (hnonneg n j) _)) _ ht
    filter_upwards [eventually_ge_atTop (1:ℕ),
      (hU.pow 2).eventually_le_const (show (0:ℝ)^2<1 by norm_num)] with n hn hu
    have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
    have hnp : (n:ℝ)^2 ≤ (n:ℝ)^4 := by
      calc
        (n:ℝ)^2 = (n:ℝ)^2 * 1 := by ring
        _ ≤ (n:ℝ)^2 * (n:ℝ)^2 := by gcongr; nlinarith
        _ = _ := by ring
    have hup : (u n)^6 ≤ (u n)^4 := by
      rw [show (6:ℕ)=4+2 by decide,pow_add]
      exact mul_le_of_le_one_right (by positivity) hu
    calc
      _ ≤ (n:ℝ)*(3*(n:ℝ)*(u n)^6/64) :=
        mul_le_mul_of_nonneg_left (front_mixed_block n hn (u n) 0).2.2 (Nat.cast_nonneg n)
      _ = 3/64*((n:ℝ)^2*(u n)^6) := by ring
      _ ≤ _ := by gcongr
  fin_cases i
  · exact hfront 0
  · exact hfront 1
  · exact hlast

private theorem scaled_rear_features {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K)) (r : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)^3*(1-rearWeight (h n) r)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n:ℝ)*(rearWeight (h n) r-1)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (n:ℝ)*(rearMoment (h n) r-r^2)) atTop (𝓝 0) := by
  obtain ⟨h3,h1,_⟩ := lower_mesh_powers hK
  have hw (t : ℝ) : 0≤1-rearWeight t r ∧ 1-rearWeight t r≤(r*t)^2/4 := by
    unfold rearWeight
    exact ⟨by linarith [Real.cos_le_one (r*t)],
      by linarith [Real.one_sub_sq_div_two_le_cos (x:=r*t)]⟩
  constructor
  · apply squeeze_zero (fun n => mul_nonneg (by positivity) (hw (h n)).1) _
      (show Tendsto (fun n : ℕ => r^2/4*((n:ℝ)^3*(h n)^2)) atTop (𝓝 0)
        by simpa using h3.const_mul (r^2/4))
    intro n
    calc
      _ ≤ (n:ℝ)^3*((r*h n)^2/4) := mul_le_mul_of_nonneg_left (hw _).2 (by positivity)
      _ = _ := by ring
  constructor
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _
      (show Tendsto (fun n : ℕ => r^2/4*((n:ℝ)*(h n)^2)) atTop (𝓝 0)
        by simpa using h1.const_mul (r^2/4))
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Nat.cast_nonneg n),
      abs_of_nonpos (by linarith [(hw (h n)).1])]
    calc
      _ ≤ (n:ℝ)*((r*h n)^2/4) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        linarith [(hw (h n)).2]
      _ = _ := by ring
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _
      (show Tendsto (fun n : ℕ => r^4/3*((n:ℝ)*(h n)^2)) atTop (𝓝 0)
        by simpa using h1.const_mul (r^4/3))
    intro n
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
    have he : |rearMoment (h n) r-r^2|≤r^4*(h n)^2/3 := by
      by_cases hh : h n=0
      · simp [hh,rearMoment]
      · rw [rear_moment_eq hh]
        exact scaled_sin_sq_error r (h n) hh
    calc
      _ ≤ (n:ℝ)*(r^4*(h n)^2/3) := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg n)
      _ = _ := by ring


private theorem scaled_rear_last_row {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K)) (r : ℝ) (i : Fin 3) :
    Tendsto (fun n : ℕ => (n:ℝ)*(rearMatrix n (h n) r 2 i - (![0,r^2,1] : Fin 3 → ℝ) i))
      atTop (𝓝 0) := by
  let w := fun n => rearWeight (h n) r
  let x := fun n => rearMoment (h n) r
  obtain ⟨hw,hx⟩ := rearFeatures_tendsto (critical_bound_mesh_limits (hK.isBigO_one ℝ)).1 r
  obtain ⟨hf,hdw,hdx⟩ := scaled_rear_features hK r
  fin_cases i
  · have ht := hf.mul (hw.pow 2)
    apply (show Tendsto (fun n : ℕ => ((n:ℝ)^3*(1-w n))*w n^2) atTop (𝓝 0)
        by simpa using ht).congr
    intro n
    simp [rearMatrix,w]
    ring
  · have ht := ((hdw.mul (hw.add (tendsto_const_nhds (x:=(1:ℝ))))).mul hx).add hdx
    apply (show Tendsto (fun n : ℕ => ((n:ℝ)*(w n-1))*(w n+1)*x n+(n:ℝ)*(x n-r^2))
      atTop (𝓝 0) by simpa using ht).congr
    intro n
    simp [rearMatrix,w,x]
    ring
  · have ht := hdw.mul (((hw.pow 2).add hw).add (tendsto_const_nhds (x:=(1:ℝ))))
    apply (show Tendsto (fun n : ℕ => ((n:ℝ)*(w n-1))*(w n^2+w n+1))
      atTop (𝓝 0) by simpa using ht).congr
    intro n
    simp [rearMatrix,w]
    ring

private def lastRow (S : Finset ℝ) : Fin 3 → ℝ := ![0,∑ r∈S,r^2,(S.card:ℝ)]

private theorem scaled_joint_last_row {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K)) (S : Finset ℝ)
    (i : Fin 3) :
    Tendsto (fun n : ℕ => (n:ℝ)*(coupledMomentMatrix S n (h n) 2 i-lastRow S i))
      atTop (𝓝 0) := by
  have hfront := scaled_front_last_row hK i
  have hrear := tendsto_finsetSum S fun r _ => scaled_rear_last_row hK r i
  have ht := hfront.add hrear
  apply (show Tendsto (fun n : ℕ => (n:ℝ)*frontMatrix n ((n:ℝ)*h n) 2 i +
      ∑ r∈S,(n:ℝ)*(rearMatrix n (h n) r 2 i - (![0,r^2,1] : Fin 3 → ℝ) i))
      atTop (𝓝 0) by simpa using ht).congr
  intro n
  have hsum : (∑ r∈S, (![0,r^2,1] : Fin 3 → ℝ) i) = lastRow S i := by
    fin_cases i <;> simp [lastRow]
  rw [← mul_sum,sum_sub_distrib,hsum]
  simp [coupledMomentMatrix,Matrix.add_apply,Matrix.sum_apply]
  ring

private theorem scaled_last_moment_error {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) :
    Tendsto (fun n : ℕ => (n:ℝ)*(target n (h n) 2 -
       ((∑ r∈S,r^2)*coefficientFit S n (h n) 1+(S.card:ℝ)*coefficientFit S n (h n) 2)))
      atTop (𝓝 0) := by
  let a := fun n => coefficientFit S n (h n)
  have ha := coefficient_tendsto hK S hS
  have hterm (i : Fin 3) :
      Tendsto (fun n : ℕ => ((n:ℝ)*(coupledMomentMatrix S n (h n) 2 i-lastRow S i))*a n i)
        atTop (𝓝 0) := by
    simpa using (scaled_joint_last_row hK S i).mul (tendsto_pi_nhds.1 ha i)
  have ht := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  apply (show Tendsto (fun n : ℕ => ∑ i : Fin 3,
      ((n:ℝ)*(coupledMomentMatrix S n (h n) 2 i-lastRow S i))*a n i)
      atTop (𝓝 0) by simpa using ht).congr'
  have hdet := coupledMatrix_eventually_det_ne_zero
      (critical_bound_mesh_limits (hK.isBigO_one ℝ)).2.2 hS
  filter_upwards [hdet] with n hn
  change (coupledMomentMatrix S n (h n)).det≠0 at hn
  have heq : coupledMomentMatrix S n (h n) *ᵥ a n = target n (h n) := by
    change coupledMomentMatrix S n (h n) *ᵥ
      ((coupledMomentMatrix S n (h n))⁻¹ *ᵥ target n (h n)) = _
    rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hn),one_mulVec]
  have hex := congrFun heq (2:Fin 3)
  simp only [mulVec,dotProduct,Fin.sum_univ_three] at hex
  simp [Fin.sum_univ_three,lastRow]
  rw [← hex]
  change _ = _
  ring

private theorem scaled_rear_point_error {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ) :
    Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)^3*rearValue S n (h n) r -
       (r^2*coefficientFit S n (h n) 1+coefficientFit S n (h n) 2)))
      atTop (𝓝 0) := by
  let a := fun n => coefficientFit S n (h n)
  let w := fun n => rearWeight (h n) r
  let x := fun n => rearMoment (h n) r
  obtain ⟨hf,hw,hx⟩ := scaled_rear_features hK r
  have ha := coefficient_tendsto hK S hS
  have ht := ((hf.mul (tendsto_pi_nhds.1 ha 0)).add
    (hx.mul (tendsto_pi_nhds.1 ha 1))).add (hw.mul (tendsto_pi_nhds.1 ha 2))
  apply (show Tendsto (fun n : ℕ => ((n:ℝ)^3*(1-w n))*a n 0 +
      ((n:ℝ)*(x n-r^2))*a n 1 + ((n:ℝ)*(w n-1))*a n 2)
      atTop (𝓝 0) by simpa using ht).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast (show 0<n from hn).ne'
  simp [rearValue,coefficientRow,dotProduct,Fin.sum_univ_three,a,w,x]
  field_simp [hn0]
  ring



/-- First-order correction to the rear parabola, including a varying critical scale. -/
theorem scaled_rear_first_order {h : ℕ → ℝ} {K L : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (hL : Tendsto (fun n : ℕ => (n:ℝ)*(3*((n:ℝ)^5*(h n)^2)/20-3*K/20))
      atTop (𝓝 L)) (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ) :
    let readout := fun state : ((Finset ℝ × ℕ) × ℝ) × ℝ =>
      rearValue state.1.1.1 state.1.1.2 state.1.2 state.2
    let D := (S.card:ℝ)*r^2-∑ s∈S,s^2
    Tendsto (fun n : ℕ => (n:ℝ)*((S.card:ℝ)*(n:ℝ)^3*readout (((S,n),h n),r)
        -(3*K/20-3*D/4))) atTop (𝓝 (L+3*K/20+9*D/8)) := by
  let D := (S.card:ℝ)*r^2-∑ s∈S,s^2
  let a := fun n => coefficientFit S n (h n)
  let Q := fun n : ℕ => 3*((n:ℝ)^5*(h n)^2)/20
  have hQ : Tendsto Q atTop (𝓝 (3*K/20)) := by
    convert (hK.const_mul (3/20:ℝ)) using 1
    · funext n
      dsimp [Q]
      ring
    · ring_nf
  have hT : Tendsto (fun n : ℕ => (n:ℝ)*(target n (h n) 2-3*K/20))
      atTop (𝓝 (L+3*K/20)) := by
    apply (show Tendsto (fun n : ℕ => (n:ℝ)*(Q n-3*K/20)+Q n)
      atTop (𝓝 (L+3*K/20)) from hL.add hQ).congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    dsimp [Q,target,budget]
    ring
  have hp := (scaled_rear_point_error hK S hS r).const_mul (S.card:ℝ)
  have hm := scaled_last_moment_error hK S hS
  have hc := (fitted_C_first_order hK S hS).const_mul D
  have ht := (((hp.sub hm).add hT).add hc)
  have hout : Tendsto (fun n : ℕ =>
      (S.card:ℝ)*((n:ℝ)*((n:ℝ)^3*rearValue S n (h n) r-(r^2*a n 1+a n 2))) -
      (n:ℝ)*(target n (h n) 2-((∑ s∈S,s^2)*a n 1+(S.card:ℝ)*a n 2))+
      (n:ℝ)*(target n (h n) 2-3*K/20)+D*((n:ℝ)*(a n 1+3/4)))
      atTop (𝓝 (L+3*K/20+9*D/8)) := by
    convert ht using 1
    simp
    ring
  apply hout.congr
  intro n
  dsimp [D,a]
  ring



private theorem rear_limit_card_mul (S : Finset ℝ) (hS : S.Nonempty) (K r : ℝ) :
    (S.card:ℝ)*(limitCoefficients S K 2-3*r^2/4) =
      3*K/20-(3*r^2/4*(S.card:ℝ)-3*(∑ s∈S,s^2)/4) := by
  have hc : (S.card:ℝ)≠0 := by exact_mod_cast hS.card_pos.ne'
  change (S.card:ℝ)*((3*K/20+3*(∑ s∈S,s^2)/4)/(S.card:ℝ)-3*r^2/4) = _
  field_simp [hc]
  ring

private theorem zero_boundary_first_order {h : ℕ → ℝ} {K L : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (hL : Tendsto (fun n : ℕ => (n:ℝ)*(3*((n:ℝ)^5*(h n)^2)/20-3*K/20))
      atTop (𝓝 L)) (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ)
    (hzero : 3*r^2/4*(S.card:ℝ)-3*(∑ s∈S,s^2)/4=3*K/20) :
    Tendsto (fun n : ℕ => (n:ℝ)*((S.card:ℝ)*(n:ℝ)^3*rearValue S n (h n) r))
      atTop (𝓝 (L+3*K/8)) := by
  have h := scaled_rear_first_order hK hL S hS r
  dsimp only at h
  have hd : (S.card:ℝ)*r^2-∑ s∈S,s^2=K/5 := by linarith only [hzero]
  rw [hd] at h
  convert h using 1
  · funext n
    ring
  · ring

private theorem leading_boundary_pos {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ)
    (hp : 3*r^2/4*(S.card:ℝ)-3*(∑ s∈S,s^2)/4 < 3*K/20) :
    ∀ᶠ n : ℕ in atTop, 0<(n:ℝ)^3*rearValue S n (h n) r := by
  have ht := scaled_rear_value hK S hS r
  have hcard : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hh := rear_limit_card_mul S hS K r
  apply ht.eventually
  apply lt_mem_nhds
  apply pos_of_mul_pos_left _ hcard.le
  linarith only [hp,hh]

private theorem leading_boundary_neg {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ)
    (hp : 3*K/20 < 3*r^2/4*(S.card:ℝ)-3*(∑ s∈S,s^2)/4) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)^3*rearValue S n (h n) r<0 := by
  have ht := scaled_rear_value hK S hS r
  have hcard : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hh := rear_limit_card_mul S hS K r
  exact ht.eventually (gt_mem_nhds (by
    apply neg_of_mul_neg_left _ hcard.le
    linarith only [hp,hh]))

/-- At a positive rear threshold the first-order scale drift selects the adjacent window. -/
theorem eventual_support_at_threshold
    (q : ℕ → ℕ) (hq : ∀ n, q n ≠ 0) (e l : ℕ)
    (hpar : ∀ᶠ n in atTop, q n % 2 = e) {K L : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(mesh (q n))^2) atTop (𝓝 K))
    (hL : Tendsto (fun n : ℕ => (n:ℝ)*(3*((n:ℝ)^5*(mesh (q n))^2)/20-3*K/20))
      atTop (𝓝 L))
    (hcrit : 3*K/20=rearThreshold e (l+1))
    (hne : L+3*K/8≠0) :
    let k := if 0<L+3*K/8 then l+1 else l
    ∀ᶠ n : ℕ in atTop,
      letI : NeZero (q n) := ⟨hq n⟩
      let v : ZMod (q n) → ℝ := windowLaw n k (coefficientFit (rearRealOffsets e k) n (mesh (q n)))
      let threshold := 1-2*budget n*(mesh (q n))^2
      cosineMoment 1 v = threshold ∧ cosineMoment 2 v = threshold ∧
      v ∈ feasible (q n) threshold ∧
        (∀ w ∈ feasible (q n) threshold, w ≠ v → energy v < energy w) ∧
        (∀ w ∈ feasible (q n) threshold, energy v + (∑ i,(w i-v i)^2) ≤ energy w) ∧
        ∀ w ∈ feasible (q n) threshold, IsMinOn energy (feasible (q n) threshold) w →
          ∀ i, 0 < max 0 (w i) ↔ i ∈ frontSites (q n) n ∪ rearSites (q n) k := by
  obtain ⟨n,hn⟩ := hpar.exists
  have he : e<2 := by rw [← hn]; omega
  let h := fun n => mesh (q n)
  have hmono := rearThreshold_strictMono e he
  have hlow : rearThreshold e l<3*K/20 := hcrit ▸ hmono (Nat.lt_succ_self l)
  have hhigh : 3*K/20<rearThreshold e (l+2) := hcrit ▸ hmono (Nat.lt_succ_self (l+1))
  by_cases hp : 0<L+3*K/8
  · dsimp only
    rw [ite_eq_left hp]
    let S := rearRealOffsets e (l+1)
    have hS := rear_offsets_nonempty e (l+1)
    obtain ⟨h0,h1⟩ := rear_threshold_endpoints e (l+1) he
    let r0 := ((l+1:ℕ):ℝ)+(e:ℝ)/2
    let r1 := ((l+1:ℕ):ℝ)+1+(e:ℝ)/2
    have hz : 3*r0^2/4*(S.card:ℝ)-3*(∑ s∈S,s^2)/4=3*K/20 := by
      exact h0.trans hcrit.symm
    have ht := zero_boundary_first_order hK hL S hS r0 hz
    have hpos := ht.eventually (lt_mem_nhds hp)
    have hrpos : ∀ᶠ n : ℕ in atTop, 0<(n:ℝ)^3*rearValue S n (h n) r0 := by
      filter_upwards [hpos] with n hn
      by_contra! hnonpos
      rw [show (n:ℝ)*((S.card:ℝ)*(n:ℝ)^3*rearValue S n (h n) r0) =
        ((n:ℝ)*(S.card:ℝ))*((n:ℝ)^3*rearValue S n (h n) r0) by ring] at hn
      exact hn.not_ge (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnonpos)
    have hrneg := leading_boundary_neg hK S hS r1 (hhigh.trans_eq h1.symm)
    exact eventual_window_support_of_signs q hq e (l+1) hpar hK hrpos hrneg
  · dsimp only
    rw [ite_eq_right hp]
    have hn : L+3*K/8<0 := lt_of_le_of_ne (le_of_not_gt hp) hne
    let S := rearRealOffsets e l
    have hS := rear_offsets_nonempty e l
    obtain ⟨h0,h1⟩ := rear_threshold_endpoints e l he
    let r0 := (l:ℝ)+(e:ℝ)/2
    let r1 := (l:ℝ)+1+(e:ℝ)/2
    have hz : 3*r1^2/4*(S.card:ℝ)-3*(∑ s∈S,s^2)/4=3*K/20 := h1.trans hcrit.symm
    have ht := zero_boundary_first_order hK hL S hS r1 hz
    have hneg := ht.eventually (gt_mem_nhds hn)
    have hrneg : ∀ᶠ n : ℕ in atTop, (n:ℝ)^3*rearValue S n (h n) r1<0 := by
      filter_upwards [hneg] with n hn
      by_contra! hnonneg
      rw [show (n:ℝ)*((S.card:ℝ)*(n:ℝ)^3*rearValue S n (h n) r1) =
        ((n:ℝ)*(S.card:ℝ))*((n:ℝ)^3*rearValue S n (h n) r1) by ring] at hn
      exact hn.not_ge (mul_nonneg (by positivity) hnonneg)
    have hrpos := leading_boundary_pos hK S hS r0 (h0.trans_lt hlow)
    exact eventual_window_support_of_signs q hq e l hpar hK hrpos hrneg


end

end D5.S3.Fourier.Asymptotics.CyclicGrowingRearFirstOrder
