/- GID: D5/S3/Fourier/Asymptotics/CyclicGrowingRearSecondOrder
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicGrowingRearSecondOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Second-order correction and support selection at a degenerate rear threshold. -/

import D5.S3.Fourier.Asymptotics.CyclicGrowingRearFirstOrder

/-! A second-order expansion settles the vanishing first-order margin. -/

open Finset Matrix Filter Asymptotics
open scoped Topology
open D5.S3.Fourier.Asymptotics.CyclicGrowingSupport
open D5.S3.Fourier.Asymptotics.CyclicGrowingRearFirstOrder
open D5.S3.Fourier.Asymptotics.CyclicGrowingEdgeLimits
open D5.S3.Fourier.Asymptotics.CyclicGrowingCoupledFit
open D5.S3.Fourier.Asymptotics.CyclicGrowingFrontFit
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open D5.S3.Fourier.Asymptotics.CyclicParityCorrection
open D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison

namespace D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder

noncomputable section

set_option autoImplicit false

private theorem lattice_C_second_order :
    Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(latticeCoeffs n 1+3/4)-9/8))
      atTop (𝓝 (-15/8)) := by
  have hi : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let z := fun n : ℕ => (4/3 : ℝ)+2*(n:ℝ)⁻¹-(1/3)*(n:ℝ)⁻¹^2-(1/2)*(n:ℝ)⁻¹^3
  let b := fun n : ℕ => (-5/2:ℝ)+(9/16)*(n:ℝ)⁻¹^2
  have hz : Tendsto z atTop (𝓝 (4/3)) := by
    simpa [z] using (((tendsto_const_nhds.add (hi.const_mul (2:ℝ)) (a:= (4/3:ℝ))).sub
      ((hi.pow 2).const_mul (1/3:ℝ))).sub ((hi.pow 3).const_mul (1/2:ℝ)))
  have hb : Tendsto b atTop (𝓝 (-5/2)) := by
    simpa [b] using ((hi.pow 2).const_mul (9/16:ℝ)).const_add (-5/2:ℝ)
  have ht := hb.div hz (by norm_num : (4/3:ℝ)≠0)
  have hlim : (-5/2:ℝ)/(4/3) = -15/8 := by norm_num
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
  change b n/z n = (n:ℝ)*((n:ℝ)*(-(n:ℝ)^3/normalizer n (radiusSq n)+3/4)-9/8)
  rw [hnorm]
  field_simp [hn0,hzz]
  dsimp [b,z]
  field_simp [hn0]
  ring

private theorem fitted_C_second_order {h : ℕ → ℝ} {K : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (S : Finset ℝ) (hS : S.Nonempty) :
    Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(coefficientFit S n (h n) 1+3/4)-9/8))
      atTop (𝓝 (-15/8)) := by
  have he := scaled_coefficient_error (hK.isBigO_one ℝ) S hS (1:Fin 2)
  change Tendsto (fun n : ℕ => (n:ℝ)^2*(coefficientFit S n (h n) 1-latticeCoeffs n 1))
    atTop (𝓝 0) at he
  apply (show Tendsto (fun n : ℕ => (n:ℝ)^2*(coefficientFit S n (h n) 1-latticeCoeffs n 1)+
    (n:ℝ)*((n:ℝ)*(latticeCoeffs n 1+3/4)-9/8)) atTop (𝓝 (-15/8))
      by simpa using he.add lattice_C_second_order).congr
  intro n
  ring

/-- The quadratic correction to the scaled rear law. -/
theorem scaled_rear_second_order {h : ℕ → ℝ} {K L H : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (hL : Tendsto (fun n : ℕ => (n:ℝ)*(3*((n:ℝ)^5*(h n)^2)/20-3*K/20))
      atTop (𝓝 L))
    (hH : Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(3*((n:ℝ)^5*(h n)^2)/20-3*K/20)-L))
      atTop (𝓝 H)) (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ) :
    let readout := fun state : ((Finset ℝ × ℕ) × ℝ) × ℝ =>
      rearValue state.1.1.1 state.1.1.2 state.1.2 state.2
    let D := (S.card:ℝ)*r^2-∑ s∈S,s^2
    Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*((S.card:ℝ)*(n:ℝ)^3*readout (((S,n),h n),r)
        -(3*K/20-3*D/4))-(L+3*K/20+9*D/8))) atTop (𝓝 (H+L-15*D/8)) := by
  let D := (S.card:ℝ)*r^2-∑ s∈S,s^2
  let a := fun n => coefficientFit S n (h n)
  let Q := fun n : ℕ => 3*((n:ℝ)^5*(h n)^2)/20
  have hT : Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(target n (h n) 2-3*K/20)-(L+3*K/20)))
      atTop (𝓝 (H+L)) := by
    apply (show Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(Q n-3*K/20)-L)+(n:ℝ)*(Q n-3*K/20))
      atTop (𝓝 (H+L)) from hH.add hL).congr
    intro n
    dsimp [Q,target,budget]
    ring
  obtain ⟨hm,hp⟩ := second_order_remainders hK S hS r
  have hp' := hp.const_mul (S.card:ℝ)
  have hc := (fitted_C_second_order hK S hS).const_mul D
  have ht := (((hp'.sub hm).add hT).add hc)
  have hout : Tendsto (fun n : ℕ =>
      (S.card:ℝ)*((n:ℝ)^2*((n:ℝ)^3*rearValue S n (h n) r-(r^2*a n 1+a n 2))) -
      (n:ℝ)^2*(target n (h n) 2-((∑ s∈S,s^2)*a n 1+(S.card:ℝ)*a n 2))+
      (n:ℝ)*((n:ℝ)*(target n (h n) 2-3*K/20)-(L+3*K/20))+
      D*((n:ℝ)*((n:ℝ)*(a n 1+3/4)-9/8)))
      atTop (𝓝 (H+L-15*D/8)) := by
    convert ht using 1
    simp
    ring
  apply hout.congr
  intro n
  dsimp [D,a]
  ring


private theorem zero_boundary_second_order {h : ℕ → ℝ} {K L H : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(h n)^2) atTop (𝓝 K))
    (hL : Tendsto (fun n : ℕ => (n:ℝ)*(3*((n:ℝ)^5*(h n)^2)/20-3*K/20))
      atTop (𝓝 L))
    (hH : Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(3*((n:ℝ)^5*(h n)^2)/20-3*K/20)-L))
      atTop (𝓝 H)) (S : Finset ℝ) (hS : S.Nonempty) (r : ℝ)
    (hzero : 3*r^2/4*(S.card:ℝ)-3*(∑ s∈S,s^2)/4=3*K/20)
    (hmargin : L+3*K/8=0) :
    Tendsto (fun n : ℕ => (n:ℝ)^2*((S.card:ℝ)*(n:ℝ)^3*rearValue S n (h n) r))
      atTop (𝓝 (H-3*K/4)) := by
  have h := scaled_rear_second_order hK hL hH S hS r
  dsimp only at h
  have hd : (S.card:ℝ)*r^2-∑ s∈S,s^2=K/5 := by linarith only [hzero]
  rw [hd] at h
  have hfirst : L+3*K/20+9*(K/5)/8=0 := by linarith only [hmargin]
  have hleading : 3*K/20-3*(K/5)/4=0 := by ring
  rw [hfirst,hleading] at h
  simp only [sub_zero] at h
  have hlim : H+L-15*(K/5)/8=H-3*K/4 := by linarith only [hmargin]
  rw [hlim] at h
  apply h.congr
  intro n
  ring

/-- At a zero first-order margin the next drift selects the adjacent support window. -/
theorem eventual_support_at_second_order_threshold
    (q : ℕ → ℕ) (hq : ∀ n, q n ≠ 0) (e l : ℕ)
    (hpar : ∀ᶠ n in atTop, q n % 2 = e) {K L H : ℝ}
    (hK : Tendsto (fun n : ℕ => (n:ℝ)^5*(mesh (q n))^2) atTop (𝓝 K))
    (hL : Tendsto (fun n : ℕ => (n:ℝ)*(3*((n:ℝ)^5*(mesh (q n))^2)/20-3*K/20))
      atTop (𝓝 L))
    (hH : Tendsto (fun n : ℕ => (n:ℝ)*((n:ℝ)*(3*((n:ℝ)^5*(mesh (q n))^2)/20-3*K/20)-L))
      atTop (𝓝 H))
    (hcrit : 3*K/20=rearThreshold e (l+1))
    (hmargin : L+3*K/8=0) (hne : H-3*K/4≠0) :
    let readout := fun state : (Finset ℝ × ℕ) × ℝ =>
      coefficientFit state.1.1 state.1.2 state.2
    let k := if 0<H-3*K/4 then l+1 else l
    ∀ᶠ n : ℕ in atTop,
      letI : NeZero (q n) := ⟨hq n⟩
      let v : ZMod (q n) → ℝ := windowLaw n k (readout ((rearRealOffsets e k,n),mesh (q n)))
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
  by_cases hp : 0<H-3*K/4
  · dsimp only
    rw [ite_eq_left hp]
    let S := rearRealOffsets e (l+1)
    have hS := rear_offsets_nonempty e (l+1)
    obtain ⟨h0,h1⟩ := rear_threshold_endpoints e (l+1) he
    let r0 := ((l+1:ℕ):ℝ)+(e:ℝ)/2
    let r1 := ((l+1:ℕ):ℝ)+1+(e:ℝ)/2
    have hz : 3*r0^2/4*(S.card:ℝ)-3*(∑ s∈S,s^2)/4=3*K/20 := h0.trans hcrit.symm
    have ht := zero_boundary_second_order hK hL hH S hS r0 hz hmargin
    have hpos := ht.eventually (lt_mem_nhds hp)
    have hrpos : ∀ᶠ n : ℕ in atTop, 0<(n:ℝ)^3*rearValue S n (h n) r0 := by
      filter_upwards [hpos] with n hn
      by_contra! hnonpos
      rw [show (n:ℝ)^2*((S.card:ℝ)*(n:ℝ)^3*rearValue S n (h n) r0) =
        ((n:ℝ)^2*(S.card:ℝ))*((n:ℝ)^3*rearValue S n (h n) r0) by ring] at hn
      exact hn.not_ge (mul_nonpos_of_nonneg_of_nonpos (by positivity) hnonpos)
    have hrneg := leading_boundary_neg hK S hS r1 (hhigh.trans_eq h1.symm)
    exact eventual_window_support_of_signs q hq e (l+1) hpar hK hrpos hrneg
  · dsimp only
    rw [ite_eq_right hp]
    have hn : H-3*K/4<0 := lt_of_le_of_ne (le_of_not_gt hp) hne
    let S := rearRealOffsets e l
    have hS := rear_offsets_nonempty e l
    obtain ⟨h0,h1⟩ := rear_threshold_endpoints e l he
    let r0 := (l:ℝ)+(e:ℝ)/2
    let r1 := (l:ℝ)+1+(e:ℝ)/2
    have hz : 3*r1^2/4*(S.card:ℝ)-3*(∑ s∈S,s^2)/4=3*K/20 := h1.trans hcrit.symm
    have ht := zero_boundary_second_order hK hL hH S hS r1 hz hmargin
    have hneg := ht.eventually (gt_mem_nhds hn)
    have hrneg : ∀ᶠ n : ℕ in atTop, (n:ℝ)^3*rearValue S n (h n) r1<0 := by
      filter_upwards [hneg] with n hn
      by_contra! hnonneg
      rw [show (n:ℝ)^2*((S.card:ℝ)*(n:ℝ)^3*rearValue S n (h n) r1) =
        ((n:ℝ)^2*(S.card:ℝ))*((n:ℝ)^3*rearValue S n (h n) r1) by ring] at hn
      exact hn.not_ge (mul_nonneg (by positivity) hnonneg)
    have hrpos := leading_boundary_pos hK S hS r0 (h0.trans_lt hlow)
    exact eventual_window_support_of_signs q hq e l hpar hK hrpos hrneg


end

end D5.S3.Fourier.Asymptotics.CyclicGrowingRearSecondOrder
