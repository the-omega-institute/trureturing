/- GID: D5/S3/HardCoreHolomorphic/RowTubeBounds
   generality: G
   mirror-B: D5/B/S3/HardCoreHolomorphic/RowTubeBounds
   mirror-E: none(waiver:uniform-type-and-pruning-perturbation)
   anchors: []
   digest: Pole-free complex Jacobian control from actual affine coefficients and real rows. -/

import D5.S3.HardCoreHolomorphic.TubeEstimates

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.HardCoreHolomorphic.RowTubeBounds
open scoped BigOperators
open D5.S3.HardCoreHolomorphic.AffineChart
open D5.S3.HardCoreHolomorphic.TypedJacobian
open D5.S3.HardCoreHolomorphic.TubeEstimates

/-- Fixed numerical coefficient range, satisfied by the actual 881 types. -/
def CoeffBound (a b : ℝ) : Prop := 0 ≤ a ∧ 1/100 ≤ b-a ∧ b ≤ 3

private theorem coeff_facts {a b : ℝ} (h : CoeffBound a b) :
    0 < b ∧ 0 ≤ a ∧ a ≤ 3 ∧ 0 ≤ b ∧ b ≤ 3 := by
  rcases h with ⟨ha,hc,hb⟩
  exact ⟨by linarith,ha,by linarith,by linarith,hb⟩

/-- Bounds are uniform in every child subset of cardinality at most four.
Real-row contraction is consumed later; these estimates use only coefficient ranges. -/
theorem row_tube_bounds {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.card ≤ 4) (a0 b0 : ℝ) (a b : ι → ℝ)
    (hc0 : CoeffBound a0 b0) (hc : ∀ j ∈ s, CoeffBound (a j) (b j))
    (r : ι → ℝ) (hr : ∀ j ∈ s, 1/4 ≤ r j ∧ r j ≤ 1)
    (lam : ℝ) (hlam : 0 ≤ lam ∧ lam ≤ 3)
    (z : ℂ) (hz : ‖z-(lam:ℂ)‖ ≤ epsilon)
    (m : ι → ℂ) (hm : ∀ j ∈ s, ‖m j-center (a j) (b j) (r j)‖ ≤ delta) :
    (∀ j ∈ s, 1+(a j:ℂ)*Complex.exp (b j*m j) ≠ 0) ∧
    (1/200:ℝ) ≤ (logArgument s a0 b0 (fun j => a j) (fun j => b j) z m).re ∧
    (1/2:ℝ) ≤ (1+z*messageProduct s (fun j => a j) (fun j => b j) m).re ∧
    ‖activityEntry s a0 b0 (fun j => a j) (fun j => b j) z m‖ ≤ 10000 ∧
    (∀ j ∈ s,
      ‖jacobianEntry s a0 b0 (fun j => a j) (fun j => b j) z m j -
        ((-(lam*(∏ k ∈ s, r k)*(b j-a j*r j)) /
          (b0-a0+b0*lam*(∏ k ∈ s, r k)):ℝ):ℂ)‖ ≤ 10^11*delta) := by
  let x : ι → ℂ := fun j => inverse (a j) (b j) (m j)
  let P : ℂ := ∏ j ∈ s, x j
  let P0 : ℝ := ∏ j ∈ s, r j
  let A : ℂ := z*P
  let A0 : ℝ := lam*P0
  let H : ℂ := (b0:ℂ)-a0+(b0:ℂ)*z*P
  let H0 : ℝ := b0-a0+b0*lam*P0
  have cf := coeff_facts hc0
  have xi (j) (hj : j ∈ s) :=
    inverse_tube (a j) (b j) (r j) (hc j hj).1 (hc j hj).2.1 (hc j hj).2.2
      (hr j hj) (m j) (hm j hj)
  have pp := product_four_bound s hs x r (fun j hj => (xi j hj).2.2)
    hr (fun j hj => (xi j hj).2.1)
  have hP : ‖P‖ ≤ 16 := pp.1
  have hP0 : 0 ≤ P0 ∧ P0 ≤ 1 := pp.2.1
  have hPd : ‖P-(P0:ℂ)‖ ≤ 6400*delta := pp.2.2
  have hA0 : 0 ≤ A0 ∧ A0 ≤ 3 := by
    dsimp [A0]
    exact ⟨mul_nonneg hlam.1 hP0.1,
      (mul_le_mul_of_nonneg_left hP0.2 hlam.1).trans (by simpa using hlam.2)⟩
  have hAd : ‖A-(A0:ℂ)‖ ≤ 20000*delta := by
    have heq : A-(A0:ℂ) = (z-(lam:ℂ))*P+(lam:ℂ)*(P-(P0:ℂ)) := by
      dsimp [A,A0]; push_cast; ring
    rw [heq]
    calc
      _ ≤ ‖z-(lam:ℂ)‖*‖P‖+‖(lam:ℂ)‖*‖P-(P0:ℂ)‖ := by
        simpa only [norm_mul] using norm_add_le ((z-(lam:ℂ))*P) ((lam:ℂ)*(P-(P0:ℂ)))
      _ ≤ epsilon*16+3*(6400*delta) := add_le_add
        (mul_le_mul hz hP (norm_nonneg _) width_arithmetic.2.1.le)
        (mul_le_mul (by
          simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam.1] using hlam.2)
          hPd (norm_nonneg _) (by norm_num))
      _ ≤ _ := by norm_num [delta,epsilon]
  have hH0 : (1/100:ℝ) ≤ H0 := by
    dsimp [H0, A0] at *; nlinarith [mul_nonneg cf.2.2.2.1 hA0.1, hc0.2.1]
  have hHd : ‖H-(H0:ℂ)‖ ≤ 60000*delta := by
    have heq : H-(H0:ℂ) = (b0:ℂ)*(A-(A0:ℂ)) := by
      dsimp [H,H0,A,A0]; push_cast; ring
    rw [heq,norm_mul]
    have hb : ‖(b0:ℂ)‖ ≤ 3 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos cf.1] using cf.2.2.2.2
    exact (mul_le_mul hb hAd (norm_nonneg _) (by norm_num)).trans (by ring_nf; rfl)
  have hHre : (1/200:ℝ) ≤ H.re := by
    have h := Complex.re_le_norm ((H0:ℂ)-H)
    rw [Complex.sub_re, Complex.ofReal_re, norm_sub_rev] at h
    have hsmall : 60000*delta ≤ (1/200:ℝ) := by norm_num [delta]
    linarith
  have hHnorm : (1/200:ℝ) ≤ ‖H‖ := hHre.trans (Complex.re_le_norm H)
  have hH0norm : (1/100:ℝ) ≤ ‖(H0:ℂ)‖ := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0≤H0)] using hH0
  have hDre : (1/2:ℝ) ≤ (1+A).re := by
    have h := Complex.re_le_norm ((A0:ℂ)-A)
    rw [Complex.sub_re, Complex.ofReal_re, norm_sub_rev] at h
    have hsmall : 20000*delta ≤ (1/2:ℝ) := by norm_num [delta]
    simp only [Complex.add_re, Complex.one_re]
    linarith [hA0.1]
  refine ⟨fun j hj => (xi j hj).1, hHre, hDre, ?_, ?_⟩
  · change ‖-P/H‖ ≤ 10000
    rw [norm_div,norm_neg]
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hHnorm)).mpr
    nlinarith
  · intro j hj
    have cj := coeff_facts (hc j hj)
    let Qj := psi (a j) (b j) (x j)
    let Q0 : ℝ := b j-a j*r j
    have hQ0 : 0 ≤ Q0 ∧ Q0 ≤ 3 := by
      dsimp [Q0]
      have hx0 : 0 ≤ r j := by linarith [(hr j hj).1]
      constructor <;> nlinarith [(hc j hj).2.1, mul_le_mul_of_nonneg_left (hr j hj).2 cj.2.1,
        mul_nonneg cj.2.1 hx0]
    have hQd : ‖Qj-(Q0:ℂ)‖ ≤ 300*delta := by
      have heq : Qj-(Q0:ℂ) = -(a j:ℂ)*(x j-(r j:ℂ)) := by
        dsimp [Qj,Q0,psi]; push_cast; ring
      rw [heq,norm_mul,norm_neg]
      have han : ‖(a j:ℂ)‖ ≤ 3 := by
        simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg cj.2.1] using cj.2.2.1
      exact (mul_le_mul han (xi j hj).2.1 (norm_nonneg _) (by norm_num)).trans (by ring_nf; rfl)
    have hQ : ‖Qj‖ ≤ 9 := by
      have h := norm_le_norm_sub_add Qj (Q0:ℂ)
      have hqn : ‖(Q0:ℂ)‖ ≤ 3 := by
        simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hQ0.1] using hQ0.2
      have hsmall : 300*delta ≤ (6:ℝ) := by norm_num [delta]
      linarith
    have hNum : ‖(-A*Qj)-((-(A0*Q0):ℝ):ℂ)‖ ≤ 180900*delta := by
      have heq : -A*Qj-((-(A0*Q0):ℝ):ℂ) =
          -(A-(A0:ℂ))*Qj-(A0:ℂ)*(Qj-(Q0:ℂ)) := by push_cast; ring
      rw [heq]
      calc
        _ ≤ ‖A-(A0:ℂ)‖*‖Qj‖+‖(A0:ℂ)‖*‖Qj-(Q0:ℂ)‖ := by
          simpa only [norm_mul,norm_neg] using norm_sub_le (-(A-(A0:ℂ))*Qj) ((A0:ℂ)*(Qj-(Q0:ℂ)))
        _ ≤ (20000*delta)*9+3*(300*delta) := add_le_add
          (mul_le_mul hAd hQ (norm_nonneg _) (by norm_num [delta]))
          (mul_le_mul (by simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA0.1] using hA0.2)
            hQd (norm_nonneg _) (by norm_num))
        _ = _ := by ring
    have hNum0 : ‖((-(A0*Q0):ℝ):ℂ)‖ ≤ 9 := by
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_neg,
        abs_of_nonneg (mul_nonneg hA0.1 hQ0.1)]
      nlinarith
    have hq := quotient_difference (-A*Qj) ((-(A0*Q0):ℝ):ℂ) H (H0:ℂ) hHnorm hH0norm
    have hbound : ‖(-A*Qj)/H-((-(A0*Q0):ℝ):ℂ)/(H0:ℂ)‖ ≤ (10^11:ℝ)*delta := by
      calc
        _ ≤ 200*‖-A*Qj-((-(A0*Q0):ℝ):ℂ)‖+
            20000*‖((-(A0*Q0):ℝ):ℂ)‖*‖H-(H0:ℂ)‖ := hq
        _ ≤ 200*(180900*delta)+20000*9*(60000*delta) := add_le_add
          (mul_le_mul_of_nonneg_left hNum (by norm_num))
          (mul_le_mul (mul_le_mul_of_nonneg_left hNum0 (by norm_num)) hHd
            (norm_nonneg _) (by norm_num))
        _ ≤ _ := by norm_num [delta]
    simpa [jacobianEntry, logArgument, messageProduct, A,A0,P,P0,H,H0,Qj,Q0,
      neg_mul, mul_assoc] using hbound

#print axioms row_tube_bounds
end D5.S3.HardCoreHolomorphic.RowTubeBounds
