/- GID: D5/S3/HardCoreHolomorphic/TubeEstimates
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/TubeEstimates
   mirror-E: none(waiver:explicit-complex-perturbation-estimates)
   anchors: []
   digest: Uniform pole and Jacobian margins from bounded positive affine messages. -/

import D5.S3.HardCoreHolomorphic.TypedJacobian

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.TubeEstimates
open scoped BigOperators
open D5.S3.HardCoreHolomorphic.AffineChart

/-- One width for every message type. It is deliberately conservative. -/
def delta : ℝ := 1 / 10^20
/-- One activity width for every finite domain and every pruning pattern. -/
def epsilon : ℝ := 1 / 10^30

/-- The exact numerical margins used below. -/
theorem width_arithmetic :
    0 < delta ∧ 0 < epsilon ∧ epsilon ≤ delta ∧
    6*delta ≤ 1/2 ∧ 100*delta ≤ 1 ∧
    60000*delta ≤ 1/200 ∧
    (999/1000:ℝ)+10^12*delta < 1999/2000 ∧
    (1999/2000:ℝ)*delta+10000*epsilon < delta := by
  norm_num [delta, epsilon]

private theorem norm_one_add_lower (u : ℂ) : 1-‖u‖ ≤ ‖1+u‖ := by
  have h := norm_sub_norm_le (1:ℂ) (-u)
  simpa using h

/-- A pole-free normalized Mobius increment controls the inverse coordinate. -/
theorem normalized_inverse_bound (x k E : ℂ) (r : ℝ)
    (hx : ‖x‖ ≤ 1) (hk : ‖k‖ ≤ 1) (hk1 : ‖1-k‖ ≤ 1)
    (hr : 0 ≤ r ∧ r ≤ 1/2) (hE : ‖E-1‖ ≤ r) :
    1+k*(E-1) ≠ 0 ∧ ‖x*E/(1+k*(E-1))-x‖ ≤ 2*r := by
  have hq : ‖k*(E-1)‖ ≤ r := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hk (norm_nonneg _)).trans (by simpa using hE)
  have hlo : (1/2:ℝ) ≤ ‖1+k*(E-1)‖ := by
    linarith [norm_one_add_lower (k*(E-1))]
  have hn : 1+k*(E-1) ≠ 0 := by
    intro h; norm_num [h] at hlo
  refine ⟨hn, ?_⟩
  have heq : x*E/(1+k*(E-1))-x = x*(1-k)*(E-1)/(1+k*(E-1)) := by
    field_simp [hn]; ring
  rw [heq, norm_div, norm_mul, norm_mul]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hlo)).mpr
  have hnum : ‖x‖*‖1-k‖*‖E-1‖ ≤ r := by
    calc
      _ ≤ 1*1*r := mul_le_mul (mul_le_mul hx hk1 (norm_nonneg _) (by norm_num))
        hE (norm_nonneg _) (by norm_num)
      _ = r := by ring
  nlinarith [mul_le_mul_of_nonneg_left hlo hr.1]

/-- Every inverse chart is pole-free and stays close to its real interval.
All three coefficient bounds are concrete numerical requirements, later checked
on the actual Lean-owned coefficient table. -/
theorem inverse_tube (a b x : ℝ)
    (ha : 0 ≤ a) (hc : (1/100:ℝ) ≤ b-a) (hb : b ≤ 3)
    (hx : 1/4 ≤ x ∧ x ≤ 1) (m : ℂ) (hm : ‖m-center a b x‖ ≤ delta) :
    1+(a:ℂ)*Complex.exp ((b:ℂ)*m) ≠ 0 ∧
    ‖inverse a b m-(x:ℂ)‖ ≤ 100*delta ∧ ‖inverse a b m‖ ≤ 2 := by
  have hbpos : 0 < b := by linarith
  have hxpos : 0 < x := by linarith [hx.1]
  have hp : 0 < b-a*x := by nlinarith [mul_le_mul_of_nonneg_left hx.2 ha]
  have hk : 0 ≤ a*x/b ∧ a*x/b ≤ 1 := by
    constructor
    · positivity
    · apply (div_le_iff₀ hbpos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hx.2 ha]
  let u := m-center a b x
  let E := Complex.exp ((b:ℂ)*u)
  let k : ℂ := ((a*x/b:ℝ):ℂ)
  have hu : ‖(b:ℂ)*u‖ ≤ 3*delta := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]
    exact mul_le_mul hb hm (norm_nonneg _) (by norm_num)
  have he : ‖E-1‖ ≤ 6*delta := by
    have hsmall : ‖(b:ℂ)*u‖ ≤ 1 := hu.trans (by norm_num [delta])
    exact (Complex.norm_exp_sub_one_le hsmall).trans (by linarith)
  have hnorm := normalized_inverse_bound (x:ℂ) k E (6*delta)
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos] using hx.2)
    (by simpa only [k, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk.1] using hk.2)
    (by
      change ‖(1:ℂ)-((a*x/b:ℝ):ℂ)‖ ≤ 1
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hk.2)]
      linarith [hk.1])
    ⟨by norm_num [delta], width_arithmetic.2.2.2.1⟩ he
  have hbne : (b:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hbpos
  have hpne : (b:ℂ)-(a:ℂ)*(x:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp
  have hexp : Complex.exp ((b:ℂ)*m) = ((x/(b-a*x):ℝ):ℂ)*E := by
    rw [show (b:ℂ)*m = (b:ℂ)*center a b x+(b:ℂ)*u by dsimp [u]; ring,
      Complex.exp_add, exp_center a b x hbpos hxpos hp]
  have hden : (1+(a:ℂ)*Complex.exp ((b:ℂ)*m))*((b:ℂ)-(a:ℂ)*x) =
      (b:ℂ)*(1+k*(E-1)) := by
    rw [hexp]; dsimp [k]; push_cast; field_simp [hbne, hpne]; ring
  have hn : 1+(a:ℂ)*Complex.exp ((b:ℂ)*m) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hden
    exact (mul_ne_zero hbne hnorm.1) hden.symm
  have hinv : inverse a b m = (x:ℂ)*E/(1+k*(E-1)) := by
    dsimp [inverse]
    apply (div_eq_div_iff hn hnorm.1).mpr
    rw [hexp]
    dsimp [k]; push_cast
    field_simp (disch := first | assumption | (convert hpne using 1; ring1))
    ring
  have hclose : ‖inverse a b m-(x:ℂ)‖ ≤ 100*delta := by
    rw [hinv]
    exact hnorm.2.trans (by norm_num [delta])
  refine ⟨hn, hclose, ?_⟩
  have ht := norm_add_le (inverse a b m-(x:ℂ)) (x:ℂ)
  rw [sub_add_cancel] at ht
  have hxn : ‖(x:ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos] using hx.2
  linarith [width_arithmetic.2.2.2.2.1]

private theorem product_norm_two {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℂ) (hx : ∀ j ∈ s, ‖x j‖ ≤ 2) :
    ‖∏ j ∈ s, x j‖ ≤ (2:ℝ)^s.card := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _j ∈ s, (2:ℝ) := Finset.prod_le_prod (fun j _ => norm_nonneg _) hx
    _ = _ := by simp

private theorem product_difference {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x r : ι → ℂ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hx : ∀ j ∈ s, ‖x j‖ ≤ 2) (hr : ∀ j ∈ s, ‖r j‖ ≤ 1)
    (he : ∀ j ∈ s, ‖x j-r j‖ ≤ rho) :
    ‖(∏ j ∈ s, x j)-(∏ j ∈ s, r j)‖ ≤ s.card*(2:ℝ)^s.card*rho := by
  revert hx hr he
  induction s using Finset.induction_on with
  | empty => intro hx hr he; simp
  | @insert j s hj ih =>
      intro hx hr he
      have hx' := fun k hk => hx k (Finset.mem_insert_of_mem hk)
      have hr' := fun k hk => hr k (Finset.mem_insert_of_mem hk)
      have he' := fun k hk => he k (Finset.mem_insert_of_mem hk)
      have htail := ih hx' hr' he'
      have hprod := product_norm_two s x hx'
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
      have hid : x j*(∏ k ∈ s, x k)-r j*(∏ k ∈ s, r k) =
          (x j-r j)*(∏ k ∈ s, x k)+r j*((∏ k ∈ s, x k)-(∏ k ∈ s, r k)) := by ring
      rw [hid]
      calc
        _ ≤ ‖x j-r j‖*‖∏ k ∈ s, x k‖+
            ‖r j‖*‖(∏ k ∈ s, x k)-(∏ k ∈ s, r k)‖ := by
          simpa only [norm_mul] using
            norm_add_le ((x j-r j)*(∏ k ∈ s, x k))
              (r j*((∏ k ∈ s, x k)-(∏ k ∈ s, r k)))
        _ ≤ rho*(2:ℝ)^s.card+1*(s.card*(2:ℝ)^s.card*rho) :=
          add_le_add (mul_le_mul (he j (Finset.mem_insert_self _ _)) hprod
            (norm_nonneg _) hrho)
            (mul_le_mul (hr j (Finset.mem_insert_self _ _)) htail
              (norm_nonneg _) (by norm_num))
        _ ≤ _ := by
          rw [pow_succ]; push_cast
          nlinarith [mul_nonneg hrho (pow_nonneg (by norm_num : (0:ℝ)≤2) s.card)]

/-- One finite-product estimate covers three-child rows and the four-child root. -/
theorem product_four_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.card ≤ 4) (x : ι → ℂ) (r : ι → ℝ)
    (hx : ∀ j ∈ s, ‖x j‖ ≤ 2)
    (hr : ∀ j ∈ s, 1/4 ≤ r j ∧ r j ≤ 1)
    (he : ∀ j ∈ s, ‖x j-(r j:ℂ)‖ ≤ 100*delta) :
    ‖∏ j ∈ s, x j‖ ≤ 16 ∧
    (0 ≤ ∏ j ∈ s, r j ∧ (∏ j ∈ s, r j) ≤ 1) ∧
    ‖(∏ j ∈ s, x j)-((∏ j ∈ s, r j):ℝ)‖ ≤ 6400*delta := by
  have hp : (2:ℝ)^s.card ≤ 16 := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hs
    norm_num at h ⊢; exact h
  have hn : (s.card:ℝ) ≤ 4 := by exact_mod_cast hs
  have hrn (j) (hj : j ∈ s) : 0 ≤ r j := by linarith [(hr j hj).1]
  refine ⟨(product_norm_two s x hx).trans hp, ?_, ?_⟩
  · refine ⟨Finset.prod_nonneg hrn, ?_⟩
    have h := Finset.prod_le_prod hrn (fun j hj => (hr j hj).2)
    simpa using h
  · have hrNorm (j) (hj : j ∈ s) : ‖(r j:ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hrn j hj)] using
        (hr j hj).2
    have h := product_difference s x (fun j => (r j:ℂ)) (100*delta)
      (by norm_num [delta]) hx hrNorm he
    have hc : (s.card:ℝ)*(2:ℝ)^s.card ≤ 64 := by
      nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) s.card]
    push_cast at h ⊢
    apply h.trans
    have hdelta : 0 ≤ 100*delta := by norm_num [delta]
    nlinarith [mul_le_mul_of_nonneg_right hc hdelta]

/-- Stable division, with the two concrete denominator floors used for the log argument. -/
theorem quotient_difference (u u0 v v0 : ℂ)
    (hv : (1/200:ℝ) ≤ ‖v‖) (hv0 : (1/100:ℝ) ≤ ‖v0‖) :
    ‖u/v-u0/v0‖ ≤ 200*‖u-u0‖+20000*‖u0‖*‖v-v0‖ := by
  have hp : 0 < ‖v‖ := lt_of_lt_of_le (by norm_num) hv
  have hp0 : 0 < ‖v0‖ := lt_of_lt_of_le (by norm_num) hv0
  have hne : v ≠ 0 := norm_pos_iff.mp hp
  have hne0 : v0 ≠ 0 := norm_pos_iff.mp hp0
  have hmul : (1/20000:ℝ) ≤ ‖v‖*‖v0‖ := by
    nlinarith [mul_le_mul hv hv0 (by norm_num : (0:ℝ)≤1/100) hp.le]
  have hid : u/v-u0/v0 = (u-u0)/v+u0*(v0-v)/(v*v0) := by
    field_simp [hne,hne0]; ring
  rw [hid]
  calc
    _ ≤ ‖u-u0‖/‖v‖+‖u0‖*‖v-v0‖/(‖v‖*‖v0‖) := by
      simpa only [norm_div, norm_mul, norm_sub_rev] using norm_add_le ((u-u0)/v) (u0*(v0-v)/(v*v0))
    _ ≤ _ := by
      apply add_le_add
      · apply (div_le_iff₀ hp).mpr
        nlinarith [mul_le_mul_of_nonneg_left hv (norm_nonneg (u-u0))]
      · apply (div_le_iff₀ (mul_pos hp hp0)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hmul
          (mul_nonneg (norm_nonneg u0) (norm_nonneg (v-v0)))]

#print axioms width_arithmetic
#print axioms normalized_inverse_bound
#print axioms inverse_tube
#print axioms product_four_bound
#print axioms quotient_difference
end D5.S3.HardCoreHolomorphic.TubeEstimates
