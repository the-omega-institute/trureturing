/- GID: D5/S3/Observer/CubicGain/ZeroDriftExclusion
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/ZeroDriftExclusion
   mirror-E: none(waiver:universal-continuous-world-exclusion)
   anchors: []
   utility: none
   digest: A strict original parent at zero drift has nonzero terminal gain. -/

import D5.S3.Observer.CubicGain.OriginalWorld

/-! The zero-drift layer of the literal five-reading parent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Observer.CubicGain

set_option maxHeartbeats 1000000 in
/-- Every strict original world with the literal five readings and zero actual
 drift has nonzero gain at clock seven. -/
theorem original_zero_drift_terminal_gain_ne_zero (W : OriginalWorld)
    (hW : OriginalParent W) (hd : W.2.2.1 = 0) :
    (originalPolynomial W).eval 7 ≠ 0 := by
  intro h7
  obtain ⟨r,b,d,a⟩ := W
  change d = 0 at hd
  subst d
  obtain ⟨hc,hw,_⟩ := original_coordinates (r,b,0,a) hW
  have hr : 0 < r := hW.1
  have hr1 : r < 1 := hW.2.1
  have hb : 0 < b := hW.2.2.1
  have he : parentEq (r,b,-24) = 0 := by
    simpa [worldCoordinates,decodeWorld] using hc.2.2.2
  have hw' : encodeWorld (parentWorld (r,b,-24)) = (r,b,0,a) := by
    simpa [worldCoordinates,decodeWorld] using hw
  let j := sourceJ r b
  let n := sourceN r b
  let t := 1+b
  let u := 1+2*b
  obtain ⟨hj,hn,ht,hu⟩ := source_positivity r b hr.le hr1.le hb
  change 0 < j at hj
  change 0 < n at hn
  change 0 < t at ht
  change 0 < u at hu
  have hu1 : 1 < u := by dsimp [u]; linarith
  have htu : 2*t = u+1 := by dsimp [t,u]; ring
  have e4 : 96/j - (882/5)/t + 96/n = 18/u := by
    have h := fourth_residual r b 0 (ne_of_gt hj) (ne_of_gt hn)
      (ne_of_gt ht) (ne_of_gt hu)
    norm_num only [zero_sub] at h
    rw [he] at h
    norm_num [parentGain,gain] at h
    apply (eq_div_iff (ne_of_gt hu)).mpr
    dsimp [j,n,t,u]
    linear_combination h
  have e7 : 1680/j - (12348/5)/t + 840/n = 0 := by
    rw [← hw'] at h7
    norm_num [originalPolynomial,encodeWorld,parentWorld,gainCoefficients,
      parentGain,Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four] at h7
    dsimp [j,n,t]
    linear_combination h7
  have ejinv : 1/j = (441/400)/t - (3/16)/u := by
    linear_combination (1/840)*e7 - (1/96)*e4
  have eninv : 1/n = (147/200)/t + (3/8)/u := by
    linear_combination (1/48)*e4 - (1/840)*e7
  have ej : 3*(269*u-25)*j = 400*u*(u+1) := by
    field_simp [ne_of_gt hj,ne_of_gt ht,ne_of_gt hu] at ejinv
    nlinarith only [ejinv,htu]
  have en : 3*(123*u+25)*n = 200*u*(u+1) := by
    field_simp [ne_of_gt hn,ne_of_gt ht,ne_of_gt hu] at eninv
    nlinarith only [eninv,htu]
  have nj : n = j+r := rfl
  have er : 3*(123*u+25)*(269*u-25)*r = 200*u*(u+1)*(23*u-75) := by
    linear_combination (269*u-25)*en - (123*u+25)*ej -
      (3*(123*u+25)*(269*u-25))*nj
  have hp : 0 < 123*u+25 := by linarith
  have hq : 0 < 269*u-25 := by linarith
  have hlow : 75/23 < u := by
    have hpos : 0 < 3*(123*u+25)*(269*u-25)*r := by positivity
    have : 0 < 23*u-75 := by
      by_contra h
      have hh := mul_nonpos_of_nonneg_of_nonpos
        (by positivity : 0 ≤ 200*u*(u+1)) (le_of_not_gt h)
      nlinarith only [hh,er,hpos]
    linarith
  have hupper : u < 27 := by
    by_contra h
    have hu27 : 27 ≤ u := le_of_not_gt h
    have hsmall : (123*u+25)*(269*u-25) < 35239*u^2 := by
      have hp' : 123*u+25 < 131*u := by linarith
      have hq' : 269*u-25 < 269*u := by linarith
      nlinarith only [mul_lt_mul_of_pos_right hp' hq,
        mul_lt_mul_of_pos_left hq' (by positivity : 0 < 131*u)]
    have hrbound : 3*(123*u+25)*(269*u-25)*r < 105717*u^2 := by
      nlinarith only [hsmall,mul_lt_mul_of_pos_left hr1 (by positivity : 0 < 3*(123*u+25)*(269*u-25))]
    have hlarge : 109200*u^2 ≤ 200*u*(u+1)*(23*u-75) := by
      have h1 : 546 ≤ 23*u-75 := by linarith
      have h2 : u^2 < u*(u+1) := by nlinarith only [hu]
      nlinarith only [h2,mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 200*(u*(u+1)))]
    nlinarith only [hrbound,hlarge,er,sq_pos_of_pos hu]
  let c := r*(1-r)/b
  have hbc : b*c = r*(1-r) := by dsimp [c]; field_simp
  have hjc : j = b+c := rfl
  have ec : 6*(269*u-25)*c = -7*u^2+1682*u-75 := by
    have hub : 2*b = u-1 := by dsimp [u]; ring
    linear_combination 2*ej - 6*(269*u-25)*hjc - 3*(269*u-25)*hub
  have hcLower : 245/269 < c := by
    have hnum : 1470*u < -7*u^2+1682*u-75 := by
      have hsq : u^2 < 27*u := by nlinarith only [mul_lt_mul_of_pos_right hupper hu]
      nlinarith only [hsq,hlow]
    have hden : 6*(269*u-25) < 1614*u := by linarith
    have hcpos : 0 < c := by dsimp [c]; positivity
    have hh : (245/269)*u < c*u := by
      nlinarith only [ec,hnum,mul_lt_mul_of_pos_right hden hcpos]
    exact (mul_lt_mul_iff_left₀ hu).mp (by nlinarith only [hh])
  have hbLower : 26/23 < b := by dsimp [u] at hlow; linarith
  have hprod : 6370/6187 < b*c := by
    nlinarith only [mul_lt_mul_of_pos_right hbLower (by linarith : 0 < c),
      mul_lt_mul_of_pos_left hcLower (by norm_num : (0:ℝ) < 26/23)]
  nlinarith only [hprod,hbc,sq_nonneg (r-1/2)]

#print axioms original_zero_drift_terminal_gain_ne_zero
end D5.S3.Observer.CubicGain
