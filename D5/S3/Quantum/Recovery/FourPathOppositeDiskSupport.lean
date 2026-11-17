/- GID: D5/S3/Quantum/Recovery/FourPathOppositeDiskSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathOppositeDiskSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complementary phase gains and deficits give opposite four-disk support. -/

import D5.S3.Quantum.Recovery.FourPathQuadraticMajorant

/-! Complementary phase estimates for the opposite coefficient pair. -/
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false

noncomputable section
namespace D5.S3.Quantum.Recovery.FourPathOppositeDiskSupport
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The gain of the real coefficient pair is quadratic in the complementary phase. -/
private lemma real_pair_gain (u v l h x y : ℝ)
    (hl : 0 < l) (ha : 0 < l^2-h^2)
    (hu : u^2=l^2+h^2+2*l*h*x) (hv : v^2=l^2+h^2-2*l*h*x)
    (hxy : x^2+y^2=1) :
    (u+v-2*l)*(l^2-h^2) ≤ l*h^2*y^2 := by
  let a := l^2-h^2
  have hp : (u*v)^2=a^2+4*l^2*h^2*y^2 := by
    calc
      _ = u^2*v^2 := by ring
      _ = (l^2+h^2+2*l*h*x)*(l^2+h^2-2*l*h*x) := by rw [hu,hv]
      _ = a^2+4*l^2*h^2-4*l^2*h^2*x^2 := by dsimp [a]; ring
      _ = _ := by nlinarith only [congrArg (fun t : ℝ => 4*l^2*h^2*t) hxy]
  have ht : (u*v)*a ≤ a^2+2*l^2*h^2*y^2 := by
    nlinarith only [hp,sq_nonneg (u*v-a)]
  have hs : ((u+v)^2-4*l^2)*a ≤ 4*l^2*h^2*y^2 := by
    have hi : (u+v)^2-4*l^2=2*(u*v-a) := by dsimp [a]; nlinarith only [hu,hv]
    rw [hi]
    nlinarith only [ht]
  have hh := mul_nonneg ha.le (sq_nonneg (u+v-2*l))
  have hc : 4*l*((u+v-2*l)*(l^2-h^2)) ≤ 4*l*(l*h^2*y^2) := by
    dsimp [a] at hs
    nlinarith only [hs,hh]
  exact (mul_le_mul_iff_right₀ (show 0 < 4*l by positivity)).mp hc

/-- A shared unit phase controls the complete sum of the four disk supports. -/
private lemma phase_support (l h c : ℝ) (u : ℂ)
    (hl : 2 ≤ l) (hh : h^2=1/2) (hc : 5/6 ≤ c^2) (hc' : c^2 ≤ 1)
    (hn : ‖u‖=1) :
    ‖(l:ℂ)+u*(h:ℂ)‖+‖(l:ℂ)-u*(h:ℂ)‖+
      ‖(l:ℂ)+u*(Complex.I*(c:ℂ))‖+‖(l:ℂ)-u*(Complex.I*(c:ℂ))‖ ≤
      2*Real.sqrt (l^2+c^2)+2*l := by
  let L := Real.sqrt (l^2+c^2)
  have lp : 0 < l := by linarith
  have l2 : 4 ≤ l^2 := by nlinarith
  have Lp : 0 < L := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg c])
  have Lsq : L^2=l^2+c^2 := Real.sq_sqrt (by positivity)
  have norm_sq (z : ℂ) : ‖z‖^2=z.re^2+z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have xy : u.re^2+u.im^2=1 := by simpa [hn] using (norm_sq u).symm
  let a := ‖(l:ℂ)+u*(h:ℂ)‖
  let b := ‖(l:ℂ)-u*(h:ℂ)‖
  have a2 : a^2=l^2+h^2+2*l*h*u.re := by
    dsimp [a]; rw [norm_sq]
    simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    nlinarith [congrArg (fun t : ℝ => h^2*t) xy]
  have b2 : b^2=l^2+h^2-2*l*h*u.re := by
    dsimp [b]; rw [norm_sq]
    simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    nlinarith [congrArg (fun t : ℝ => h^2*t) xy]
  have gain := real_pair_gain a b l h u.re u.im lp (by nlinarith) a2 b2 xy
  have gain' : a+b ≤ 2*l+(4/(7*l))*u.im^2 := by
    have den : 0 < l^2-h^2 := by nlinarith
    have coeff : l*h^2 ≤ (4/(7*l))*(l^2-h^2) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (show 0 < 7*l by positivity)).mpr
      nlinarith only [hh,l2]
    have ht := mul_le_mul_of_nonneg_right coeff (sq_nonneg u.im)
    apply (mul_le_mul_iff_left₀ den).mp
    nlinarith only [gain,ht]
  let d := ‖(l:ℂ)+u*(Complex.I*(c:ℂ))‖
  let e := ‖(l:ℂ)-u*(Complex.I*(c:ℂ))‖
  have d2 : d^2=L^2-2*l*c*u.im := by
    dsimp [d]; rw [norm_sq,Lsq]
    simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
    nlinarith [congrArg (fun t : ℝ => c^2*t) xy]
  have e2 : e^2=L^2+2*l*c*u.im := by
    dsimp [e]; rw [norm_sq,Lsq]
    simp only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
    nlinarith [congrArg (fun t : ℝ => c^2*t) xy]
  have deficit := FourPathQuadraticMajorant.scaled_pair_deficit d e L (-2*l*c*u.im)
    (norm_nonneg _) (norm_nonneg _) Lp (by linarith only [d2]) (by linarith only [e2])
  have Lu : L ≤ (9/8)*l := by
    apply (sq_le_sq₀ Lp.le (by positivity : 0 ≤ (9/8)*l)).mp
    nlinarith only [Lsq,hc',l2]
  have L2u : L^2 ≤ (5/4)*l^2 := by nlinarith only [Lsq,hc',l2]
  have L3u : L^3 ≤ (45/32)*l^3 := by
    have ht := mul_le_mul Lu L2u (sq_nonneg L) (by positivity : 0 ≤ 9/8*l)
    nlinarith only [ht]
  have coeff : (4/(7*l)) ≤ l^2*c^2/L^3 := by
    apply (div_le_div_iff₀ (show 0 < 7*l by positivity) (pow_pos Lp 3)).mpr
    have ht := mul_le_mul_of_nonneg_left hc (show 0 ≤ 7*l^3 by positivity)
    have l3pos : 0 < l^3 := pow_pos lp 3
    nlinarith only [ht,L3u,l3pos]
  have ht := mul_le_mul_of_nonneg_right coeff (sq_nonneg u.im)
  have identity : (-2*l*c*u.im)^2/(4*L^3)=(l^2*c^2/L^3)*u.im^2 := by ring
  rw [identity] at deficit
  change a+b+d+e ≤ 2*L+2*l
  linarith

/-- Uniform support for four independent complex closed unit disks. -/
theorem four_disk_support (l h c : ℝ) (z₁ z₂ z₃ z₄ : ℂ)
    (hl : 2 ≤ l) (hh : h^2=1/2) (hc : 5/6 ≤ c^2) (hc' : c^2 ≤ 1)
    (hz₁ : ‖z₁‖ ≤ 1) (hz₂ : ‖z₂‖ ≤ 1) (hz₃ : ‖z₃‖ ≤ 1) (hz₄ : ‖z₄‖ ≤ 1) :
    ‖(h:ℂ)*(z₁-z₂)-Complex.I*(c:ℂ)*(z₃-z₄)‖+
      l*(z₁+z₂+z₃+z₄).re ≤ 2*Real.sqrt (l^2+c^2)+2*l := by
  let A := (h:ℂ)*(z₁-z₂)-Complex.I*(c:ℂ)*(z₃-z₄)
  obtain ⟨u,hu,halignComplex⟩ := Complex.exists_norm_eq_mul_self A
  have halign : (u*A).re=‖A‖ := by
    have ht := congrArg Complex.re halignComplex
    simpa only [Complex.ofReal_re] using ht.symm
  have disk (q z : ℂ) (hz : ‖z‖ ≤ 1) : ((l+u*q)*z).re ≤ ‖(l:ℂ)+u*q‖ := by
    calc
      _ ≤ ‖((l:ℂ)+u*q)*z‖ := Complex.re_le_norm _
      _ = ‖(l:ℂ)+u*q‖*‖z‖ := norm_mul _ _
      _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) hz
  have H₁ := disk (h:ℂ) z₁ hz₁
  have H₂ := disk (-(h:ℂ)) z₂ hz₂
  have H₃ := disk (-Complex.I*(c:ℂ)) z₃ hz₃
  have H₄ := disk (Complex.I*(c:ℂ)) z₄ hz₄
  have total : ‖A‖+l*(z₁+z₂+z₃+z₄).re ≤
      ‖(l:ℂ)+u*(h:ℂ)‖+‖(l:ℂ)-u*(h:ℂ)‖+
      ‖(l:ℂ)+u*(Complex.I*(c:ℂ))‖+‖(l:ℂ)-u*(Complex.I*(c:ℂ))‖ := by
    rw [← halign]
    have identC : ((l+u*(h:ℂ))*z₁+(l+u*(-(h:ℂ)))*z₂+
        (l+u*(-Complex.I*(c:ℂ)))*z₃+(l+u*(Complex.I*(c:ℂ)))*z₄) =
        u*A+(l:ℂ)*(z₁+z₂+z₃+z₄) := by dsimp [A]; ring
    have hre (z : ℂ) : ((l:ℂ)*z).re=l*z.re := by simp
    have ident := congrArg Complex.re identC
    simp only [Complex.add_re,hre] at ident
    simp only [mul_neg,neg_mul,← sub_eq_add_neg] at H₂ H₃ ident
    simp only [Complex.add_re]
    linarith only [H₁,H₂,H₃,H₄,ident]
  exact total.trans (phase_support l h c u hl hh hc hc' hu)

end D5.S3.Quantum.Recovery.FourPathOppositeDiskSupport
