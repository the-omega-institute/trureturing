/- GID: D5/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryEffectOptimum
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SectorChannels/WeightedBinaryEffectOptimum
   mirror-E: none(waiver:exact-effect-optimization)
   anchors: []
   utility: none
   digest: The exact capped optimum for binary effects in a weighted two-by-two PSD order interval. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! The two determinant bounds and their explicit three-arc attainers. -/

namespace D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum

open Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev Bit := Fin 2

abbrev M₂ := Matrix Bit Bit ℂ

def tr (X : M₂) : ℝ := X.trace.re

def quad (X : M₂) : ℝ := tr (X * X)

private lemma tr_add (X Y : M₂) : tr (X+Y) = tr X + tr Y := by simp [tr,Matrix.trace_add]

private lemma tr_sub (X Y : M₂) : tr (X-Y) = tr X - tr Y := by simp [tr,Matrix.trace_sub]

private lemma tr_comm (X Y : M₂) : tr (X*Y) = tr (Y*X) := by rw [tr,tr,Matrix.trace_mul_comm]

private lemma tr_nonneg {X : M₂} (hX : X.PosSemidef) : 0 ≤ tr X := by
  exact (Complex.nonneg_iff.mp hX.trace_nonneg).1

private lemma quad_le_tr_sq (X : M₂) (hX : X.PosSemidef) : quad X ≤ (tr X)^2 := by
  have hi : X.trace.im = 0 := (Complex.nonneg_iff.mp hX.trace_nonneg).2.symm
  have hdet := (Complex.nonneg_iff.mp hX.det_nonneg).1
  have halg : X.trace ^ 2 - (X * X).trace = 2 * X.det := by
    simp [Matrix.trace, Matrix.diag, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hr := congrArg Complex.re halg
  simp [pow_two, Complex.mul_re, hi] at hr
  unfold quad tr
  nlinarith

private theorem determinant_middle_bound (a b L T q₀ : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hL : b^2 ≤ L) (hLa : L ≤ a^2)
    (hT0 : 0 ≤ T) (hTS : T ≤ a+b)
    (h₀ : q₀ ≤ T^2) (h₁ : q₀ ≤ T^2 - 2*(a+b)*T + 2*L + 2*a*b) :
    q₀ ≤ ((L+a*b)/(a+b))^2 := by
  have hS : 0 < a+b := by linarith
  let x := (L+a*b)/(a+b)
  have hx : x*(a+b) = L+a*b := div_mul_cancel₀ _ hS.ne'
  have hxb : b ≤ x := (le_div_iff₀ hS).2 (by nlinarith)
  have hxa : x ≤ a := (div_le_iff₀ hS).2 (by nlinarith)
  change q₀ ≤ x^2
  rcases le_or_gt T x with h | h
  · exact h₀.trans (pow_le_pow_left₀ hT0 h 2)
  · have hh := pow_le_pow_left₀ (show 0 ≤ a+b-T by linarith)
        (show a+b-T ≤ a+b-x by linarith) 2
    nlinarith

private theorem small_mass_bound (b L T q₀ : ℝ) (hb : 0 < b) (hT : 0 ≤ T)
    (hL : b*T ≤ L) (hQ : q₀ ≤ T^2) :
    q₀ ≤ (L/b)^2 := hQ.trans
      (pow_le_pow_left₀ hT ((le_div_iff₀ hb).2 (by linarith)) 2)

def DD (a b : ℝ) : M₂ := Matrix.diagonal ![(a:ℂ),(b:ℂ)]

private lemma diag_re_nonneg {X : M₂} (hX : X.PosSemidef) (i : Bit) : 0 ≤ (X i i).re :=
  (Complex.nonneg_iff.mp (hX.diag_nonneg (i := i))).1

private lemma DD_trace (a b : ℝ) : tr (DD a b) = a+b := by
  simp [tr,DD,Matrix.trace,Matrix.diag,Fin.sum_univ_two]

private lemma trace_det_eq (X : M₂) (hX : X.PosSemidef) :
    (tr X)^2 - quad X = 2*X.det.re := by
  have hi : X.trace.im = 0 := (Complex.nonneg_iff.mp hX.trace_nonneg).2.symm
  have he : X.trace ^ 2 - (X * X).trace = 2 * X.det := by
    simp [Matrix.trace,Matrix.diag,Matrix.det_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
    ring
  have h := congrArg Complex.re he
  simp [pow_two,Complex.mul_re,hi] at h
  unfold quad tr
  nlinarith

private lemma DD_mass (a b : ℝ) (H : M₂) :
    tr (DD a b * H) = a*(H 0 0).re + b*(H 1 1).re := by
  simp [tr,DD,Matrix.trace,Matrix.diag,Fin.sum_univ_two, Matrix.diagonal_mul,Complex.mul_re]

private lemma DD_det_sub (a b : ℝ) (H : M₂) :
    (DD a b - H).det.re = a*b - ((a+b)*tr H - tr (DD a b * H)) + H.det.re := by
  rw [DD_mass]
  simp [DD,tr,Matrix.det_fin_two,Matrix.trace,Matrix.diag,Fin.sum_univ_two,Matrix.sub_apply,
    Complex.mul_re]
  ring

private lemma tr_le_DD {a b : ℝ} {H : M₂} (hc : (DD a b-H).PosSemidef) : tr H ≤ a+b := by
  have h := tr_nonneg hc
  rw [tr_sub,DD_trace] at h
  linarith

private theorem native_middle_frontier (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (H : M₂) (hH : H.PosSemidef) (hc : (DD a b-H).PosSemidef)
    (hL : b^2 ≤ tr (DD a b*H)) (hU : tr (DD a b*H) ≤ a^2) :
    quad H ≤ ((tr (DD a b*H)+a*b)/(a+b))^2 := by
  have hm := (Complex.nonneg_iff.mp hc.det_nonneg).1
  rw [DD_det_sub] at hm
  have ht := trace_det_eq H hH
  exact determinant_middle_bound a b _ _ _ ha hb hL hU (tr_nonneg hH) (tr_le_DD hc)
    (quad_le_tr_sq H hH) (by linarith)

private theorem native_small_mass_frontier (a b : ℝ) (hab : b ≤ a) (hb : 0 < b)
    (H : M₂) (hH : H.PosSemidef) :
    quad H ≤ (tr (DD a b*H)/b)^2 := by
  have h := mul_nonneg (sub_nonneg.mpr hab) (diag_re_nonneg hH (0:Bit))
  have htr : tr H = (H 0 0).re + (H 1 1).re := by simp [tr,Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  apply small_mass_bound b _ _ _ hb (tr_nonneg hH) _ (quad_le_tr_sq H hH)
  rw [DD_mass,htr]
  nlinarith

private lemma quad_DD (a b : ℝ) : quad (DD a b) = a^2+b^2 := by
  simp [quad,tr,DD,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
    ← Complex.ofReal_mul,pow_two]

private lemma swap_mass {a b : ℝ} {H : M₂} (hn : a^2+b^2=1) :
    tr (DD a b*(DD a b-H)) = 1-tr (DD a b*H) := by
  rw [mul_sub,tr_sub,show tr (DD a b*DD a b)=1 from (quad_DD a b).trans hn]

private lemma swap_quad {a b : ℝ} (H : M₂) (hn : a^2+b^2=1) :
    quad (DD a b-H) = 1-2*tr (DD a b*H)+quad H := by
  unfold quad
  rw [sub_mul,mul_sub,mul_sub,tr_sub,tr_sub,tr_sub,tr_comm H (DD a b)]
  have h := (quad_DD a b).trans hn
  unfold quad at h
  linarith

private lemma mass_lo {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {H : M₂} (hH : H.PosSemidef) :
    0 ≤ tr (DD a b*H) := by
  rw [DD_mass]
  exact add_nonneg (mul_nonneg ha (diag_re_nonneg hH _)) (mul_nonneg hb (diag_re_nonneg hH _))

private theorem weighted_psd_hits_bound {a b : ℝ} (hb : 0 < b) (hba : b ≤ a)
    (hn : a^2+b^2=1) (H : M₂)
    (hH : H.PosSemidef) (hc : (DD a b-H).PosSemidef) :
    (∃ y : ℝ, 0 ≤ y ∧ y ≤ 1 ∧
      quad H ≤ b^2*y^2 ∧ quad (DD a b-H) ≤ 1-2*b^2*y+b^2*y^2) ∨
    (∃ x : ℝ, b ≤ x ∧ x ≤ a ∧ quad H ≤ x^2 ∧ quad (DD a b-H) ≤ (a+b-x)^2) ∨
    (∃ y : ℝ, 0 ≤ y ∧ y ≤ 1 ∧
      quad (DD a b-H) ≤ b^2*y^2 ∧ quad H ≤ 1-2*b^2*y+b^2*y^2) := by
  let D := DD a b
  let L := tr (D*H)
  have ha : 0<a := hb.trans_le hba
  have hL₀ : 0≤L := mass_lo ha.le hb.le hH
  have hL₁ : 0≤1-L := by
    have h := mass_lo ha.le hb.le hc
    rwa [swap_mass hn] at h
  have hswap : quad (D-H) = 1-2*L+quad H := swap_quad H hn
  have hlo (J : M₂) (hJ : J.PosSemidef) (hm : 0≤tr (D*J))
      (hsmall : tr (D*J) ≤ b^2) :
      ∃ y : ℝ, 0 ≤ y ∧ y ≤ 1 ∧ quad J ≤ b^2*y^2 ∧ quad (D-J) ≤ 1-2*b^2*y+b^2*y^2 := by
    let m := tr (D*J)
    let y := m/(b^2)
    have hb₂ : 0 < b^2 := sq_pos_of_pos hb
    have hy : y*(b^2) = m := div_mul_cancel₀ _ hb₂.ne'
    have h₀ : 0≤y := div_nonneg hm hb₂.le
    have h₁ : y≤1 := (div_le_iff₀ hb₂).2 (by simpa using hsmall)
    have hsq : m/b = b*y := by
      apply (div_eq_iff hb.ne').2
      nlinarith
    have hu := native_small_mass_frontier a b hba hb J hJ
    change quad J ≤ (m/b)^2 at hu
    rw [hsq] at hu
    have hquad : quad J ≤ b^2*y^2 := by simpa only [mul_pow] using hu
    refine ⟨y,h₀,h₁,hquad,?_⟩
    have hs : quad (D-J) = 1-2*m+quad J := swap_quad J hn
    rw [hs]
    nlinarith
  by_cases hsmall : L≤b^2
  · exact Or.inl (hlo H hH hL₀ hsmall)
  by_cases hlarge : a^2≤L
  · right; right
    have h0 : 0≤tr (D*(D-H)) := mass_lo ha.le hb.le hc
    have h1 : tr (D*(D-H)) ≤ b^2 := by
      change tr (DD a b*(DD a b-H)) ≤ _
      rw [swap_mass hn]
      linarith
    have hh := hlo (D-H) hc h0 h1
    have hid : D-(D-H)=H := sub_sub_cancel _ _
    rwa [hid] at hh
  right; left
  let x := (L+a*b)/(a+b)
  have hs : 0<a+b := by linarith
  have hx : x*(a+b)=L+a*b := div_mul_cancel₀ _ hs.ne'
  have hxb : b≤x := (le_div_iff₀ hs).2 (by nlinarith)
  have hxa : x≤a := (div_le_iff₀ hs).2 (by nlinarith)
  have hu := native_middle_frontier a b ha.le hb H hH hc (by linarith) (by linarith)
  change quad H≤x^2 at hu
  refine ⟨x,hxb,hxa,hu,?_⟩
  rw [hswap]
  nlinarith

private def leftCross (b y : ℝ) : M₂ := Matrix.diagonal ![0,(b*y:ℝ)]

private lemma dd_pos {a b : ℝ} (ha : 0≤a) (hb : 0≤b) : (DD a b).PosSemidef :=
  Matrix.PosSemidef.diagonal (by
    intro i
    fin_cases i
    · exact Complex.nonneg_iff.mpr ⟨ha,Complex.ofReal_im a⟩
    · exact Complex.nonneg_iff.mpr ⟨hb,Complex.ofReal_im b⟩)

private lemma leftCross_eq (b y : ℝ) : leftCross b y = DD 0 (b*y) := by rfl

private lemma leftCross_compl (a b y : ℝ) : DD a b-leftCross b y = DD a (b*(1-y)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [DD,leftCross,Matrix.sub_apply]; ring

private theorem left_cross_attains {a b y : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hn : a^2+b^2=1) (hy : 0≤y) (hy₁ : y≤1) :
    (leftCross b y).PosSemidef ∧ (DD a b-leftCross b y).PosSemidef ∧
      quad (leftCross b y) = b^2*y^2 ∧
      quad (DD a b-leftCross b y) = 1-2*b^2*y+b^2*y^2 := by
  rw [leftCross_compl,leftCross_eq,quad_DD,quad_DD]
  refine ⟨dd_pos le_rfl (mul_nonneg hb hy),dd_pos ha (mul_nonneg hb (sub_nonneg.mpr hy₁)),?_,?_⟩
  · ring
  · linear_combination hn

private def middleU (a b t : ℝ) : Bit → ℂ := ![Real.sqrt (a*t), Real.sqrt (b*(1-t))]

private def middleV (a b t : ℝ) : Bit → ℂ := ![Real.sqrt (a*(1-t)), -((Real.sqrt (b*t):ℝ):ℂ)]

private def squareVec (f : Bit → ℂ) : M₂ := Matrix.vecMulVec f (star f)

private lemma squareVec_quad (f : Bit → ℂ) : quad (squareVec f) = (tr (squareVec f))^2 := by
  have hz : (squareVec f).det = 0 := by
    simp [squareVec,Matrix.det_fin_two, Matrix.vecMulVec_apply,Pi.star_apply]
    ring
  have h := trace_det_eq (squareVec f) (Matrix.posSemidef_vecMulVec_self_star f)
  rw [hz] at h
  simp at h
  linarith

private lemma mid_squares {a b t : ℝ} (ha : 0≤a) (hb : 0≤b) (ht : 0≤t) (ht₁ : t≤1) :
    squareVec (middleU a b t)+squareVec (middleV a b t)=DD a b ∧
    tr (squareVec (middleU a b t)) = a*t+b*(1-t) := by
  have hu : 0≤1-t := sub_nonneg.mpr ht₁
  have he (x : ℝ) (hx : 0≤x) :
      ((Real.sqrt x : ℝ) : ℂ)*((Real.sqrt x : ℝ) : ℂ) = (x:ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt hx]
  have hs (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
      ((Real.sqrt x : ℝ) : ℂ)*((Real.sqrt y : ℝ) : ℂ) = (Real.sqrt (x*y):ℝ) := by
    rw [Real.sqrt_mul hx,Complex.ofReal_mul]
  constructor
  · ext i j
    simp only [Matrix.add_apply, squareVec,Matrix.vecMulVec_apply,Pi.star_apply]
    fin_cases i <;> fin_cases j
    · change ((Real.sqrt (a*t) : ℝ):ℂ)*star ((Real.sqrt (a*t) : ℝ):ℂ) +
          ((Real.sqrt (a*(1-t)) : ℝ):ℂ)*star ((Real.sqrt (a*(1-t)) : ℝ):ℂ) = (a:ℂ)
      simp only [Complex.star_def,Complex.conj_ofReal,he _ (mul_nonneg ha ht),he _ (mul_nonneg ha hu)]
      push_cast
      ring
    · change ((Real.sqrt (a*t) : ℝ):ℂ)*star ((Real.sqrt (b*(1-t)) : ℝ):ℂ) +
          ((Real.sqrt (a*(1-t)) : ℝ):ℂ)*star (-((Real.sqrt (b*t) : ℝ):ℂ)) = 0
      simp only [star_neg,Complex.star_def,Complex.conj_ofReal,mul_neg,
        hs _ _ (mul_nonneg ha ht) (mul_nonneg hb hu),
        hs _ _ (mul_nonneg ha hu) (mul_nonneg hb ht), add_neg_eq_zero]
      congr 2
      ring
    · change ((Real.sqrt (b*(1-t)) : ℝ):ℂ)*star ((Real.sqrt (a*t) : ℝ):ℂ) +
          (-((Real.sqrt (b*t) : ℝ):ℂ))*star ((Real.sqrt (a*(1-t)) : ℝ):ℂ) = 0
      simp only [Complex.star_def,Complex.conj_ofReal,neg_mul,
        hs _ _ (mul_nonneg hb hu) (mul_nonneg ha ht),
        hs _ _ (mul_nonneg hb ht) (mul_nonneg ha hu),add_neg_eq_zero]
      congr 2
      ring
    · change ((Real.sqrt (b*(1-t)) : ℝ):ℂ)*star ((Real.sqrt (b*(1-t)) : ℝ):ℂ) +
          (-((Real.sqrt (b*t) : ℝ):ℂ))*star (-((Real.sqrt (b*t) : ℝ):ℂ)) = (b:ℂ)
      simp only [star_neg,Complex.star_def,Complex.conj_ofReal,neg_mul_neg,
        he _ (mul_nonneg hb ht),he _ (mul_nonneg hb hu)]
      push_cast
      ring
  · simp [squareVec,middleU,tr,Matrix.trace,Matrix.diag,Matrix.vecMulVec_apply,Fin.sum_univ_two,
      Pi.star_apply, he _ (mul_nonneg ha ht),he _ (mul_nonneg hb hu)]

private theorem middle_cross_attains {a b x : ℝ} (ha : 0≤a) (hb : 0≤b) (hx₀ : b≤x) (hx₁ : x≤a) :
    ∃ H : M₂, H.PosSemidef ∧ (DD a b-H).PosSemidef ∧ quad H=x^2 ∧ quad (DD a b-H)=(a+b-x)^2 := by
  let t := if a=b then 0 else (x-b)/(a-b)
  have h₀ : 0≤t := by
    unfold t
    split
    · exact le_rfl
    · exact div_nonneg (sub_nonneg.mpr hx₀) (by linarith)
  have h₁ : t≤1 := by
    unfold t
    split
    · norm_num
    · have h : 0<a-b := by
        rename_i hn
        exact sub_pos.mpr (lt_of_le_of_ne (hx₀.trans hx₁) (Ne.symm hn))
      rw [div_le_iff₀ h]
      linarith
  have hxt : a*t+b*(1-t)=x := by
    unfold t
    split
    · rename_i h
      linarith
    · rename_i h
      have hne : a-b≠0 := sub_ne_zero.mpr h
      field_simp
      ring
  let H := squareVec (middleU a b t)
  let J := squareVec (middleV a b t)
  have hh : H.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have hj : J.PosSemidef := Matrix.posSemidef_vecMulVec_self_star _
  have h := mid_squares ha hb h₀ h₁
  have hsum : DD a b-H=J := sub_eq_iff_eq_add.mpr (add_comm H J ▸ h.1).symm
  have he : tr H=x := h.2.trans hxt
  have hf : tr J=a+b-x := by rw [← hsum,tr_sub,DD_trace,he]
  refine ⟨H,hh,hsum.symm ▸ hj,?_,?_⟩
  · rw [show quad H=(tr H)^2 from squareVec_quad _,he]
  · rw [hsum,show quad J=(tr J)^2 from squareVec_quad _,hf]

private theorem quadratic_interval {x l r c : ℝ} (hl : l≤x) (hr : x≤r) :
    x^2+(c-x)^2 ≤ max (l^2+(c-l)^2) (r^2+(c-r)^2) := by
  by_cases h : x+l≤c
  · apply le_trans _ (le_max_left _ _)
    nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr h)]
  · apply le_trans _ (le_max_right _ _)
    have hrc : c≤x+r := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hrc)]

private theorem middle_cap_max {c s t x : ℝ}
    (hs : 0≤s) (hst : s≤t) (hlt : 0≤c-t) (hcap : c≤s+t)
    (hx₀ : 0≤x) (hxc : x≤c) :
    min (x^2) (s^2) + min ((c-x)^2) (t^2) ≤ (c-t)^2+t^2 := by
  have ht : 0≤t := hs.trans hst
  have hcl : c-t≤s := by linarith
  have hcr : 0≤c-s := by linarith
  have hh : s^2+(c-s)^2 ≤ (c-t)^2+t^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr hcap)]
  by_cases hl : x≤c-t
  · have hsq := pow_le_pow_left₀ hx₀ hl 2
    linarith [min_le_left (x^2) (s^2), min_le_right ((c-x)^2) (t^2)]
  by_cases hr : s≤x
  · have hcx : c-x≤c-s := by linarith
    have hsq := pow_le_pow_left₀ (sub_nonneg.mpr hxc) hcx 2
    linarith [min_le_right (x^2) (s^2), min_le_left ((c-x)^2) (t^2)]
  have h := quadratic_interval (l:=c-t) (r:=s) (c:=c) (le_of_not_ge hl) (le_of_not_ge hr)
  have hleft : (c-t)^2+(c-(c-t))^2 = (c-t)^2+t^2 := by ring
  rw [hleft, max_eq_left hh] at h
  linarith [min_le_left (x^2) (s^2), min_le_left ((c-x)^2) (t^2)]

private theorem middle_cap_attained {c s t : ℝ} (hlt : 0≤c-t) (hcap : c≤s+t) :
    min ((c-t)^2) (s^2) + min ((c-(c-t))^2) (t^2) = (c-t)^2+t^2 := by
  have hsq := pow_le_pow_left₀ hlt (show c-t≤s by linarith) 2
  rw [min_eq_left hsq, show c-(c-t)=t by ring, min_self]

private theorem complementary_deficit {t : ℝ} (ht : 1/2≤t) (ht₁ : t≤1) :
    Real.sqrt t-t ≤ Real.sqrt (1-t)-(1-t) := by
  let a := Real.sqrt t
  let b := Real.sqrt (1-t)
  have ht₀ : 0≤t := by linarith
  have h1t : 0≤1-t := by linarith
  have hn₁ : 0≤a := Real.sqrt_nonneg _
  have hn₂ : 0≤b := Real.sqrt_nonneg _
  have ha : a^2=t := Real.sq_sqrt ht₀
  have hb : b^2=1-t := Real.sq_sqrt h1t
  have hab : b≤a := Real.sqrt_le_sqrt (by linarith)
  have hs : 1≤a+b := by nlinarith [mul_nonneg hn₁ hn₂]
  change a-t ≤ b-(1-t)
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hs)]

private theorem amplitude_sum_strict {q r : ℝ} (hq : 0≤q) (hqr : q<r) (hr : r≤1/2) :
    Real.sqrt q + Real.sqrt (1-q) < Real.sqrt r + Real.sqrt (1-r) := by
  have hs : 0<1-q-r := by linarith
  have hp : q*(1-q)<r*(1-r) := by
    nlinarith [mul_pos (sub_pos.mpr hqr) hs]
  have ha : 0≤q*(1-q) := mul_nonneg hq (by linarith)
  have htilt := Real.sqrt_lt_sqrt ha hp
  rw [Real.sqrt_mul hq, Real.sqrt_mul (show 0≤r by linarith)] at htilt
  have hq₁ : Real.sqrt q ^ 2=q := Real.sq_sqrt hq
  have hq₂ : Real.sqrt (1-q) ^ 2=1-q := Real.sq_sqrt (by linarith)
  have hr₁ : Real.sqrt r ^ 2=r := Real.sq_sqrt (by linarith)
  have hr₂ : Real.sqrt (1-r) ^ 2=1-r := Real.sq_sqrt (by linarith)
  by_contra! h
  have hs := pow_le_pow_left₀
    (add_nonneg (Real.sqrt_nonneg r) (Real.sqrt_nonneg (1-r))) h 2
  nlinarith

private def leftOverlap (q t y : ℝ) : ℝ :=
  min (q*y^2) (q*t) + min (1-2*q*y+q*y^2) (1-q*t)

private theorem left_cap_bound {q t y : ℝ} (hq : 0≤q) (ht : 0≤t) (ht₁ : t≤1)
    (hy : 0≤y) (hy₁ : y≤1) :
    leftOverlap q t y ≤ max (1-2*q*(Real.sqrt t-t))
      (1-2*q*(Real.sqrt (1-t)-(1-t))) := by
  let a := Real.sqrt t
  let b := Real.sqrt (1-t)
  let l := 1-b
  have ha₀ : 0≤a := Real.sqrt_nonneg _
  have hb₀ : 0≤b := Real.sqrt_nonneg _
  have ha : a^2=t := Real.sq_sqrt ht
  have hb : b^2=1-t := Real.sq_sqrt (by linarith)
  have ha₁ : a≤1 := Real.sqrt_le_one.mpr ht₁
  have hb₁ : b≤1 := Real.sqrt_le_one.mpr (by linarith)
  have hl₀ : 0≤l := by dsimp [l]; linarith
  have hab : 1≤a+b := by nlinarith [mul_nonneg ha₀ hb₀]
  have hla : l≤a := by dsimp [l]; linarith
  have hLeft : (1-q)+q*(l^2+(1-l)^2)=1-2*q*(b-(1-t)) := by
    dsimp [l]
    linear_combination 2*q*hb
  have hRight : (1-q)+q*(a^2+(1-a)^2)=1-2*q*(a-t) := by
    linear_combination 2*q*ha
  unfold leftOverlap
  by_cases hyl : y≤l
  · apply le_trans _ (le_max_right _ _)
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyl 2) hq
    have he : q*l^2+(1-q*t)=1-2*q*(b-(1-t)) := by
      dsimp [l]
      linear_combination q*hb
    linarith [min_le_left (q*y^2) (q*t),
      min_le_right (1-2*q*y+q*y^2) (1-q*t)]
  by_cases hay : a≤y
  · apply le_trans _ (le_max_left _ _)
    have hh : 1-y≤1-a := by linarith
    have hs := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sub_nonneg.mpr hy₁) hh 2) hq
    have he : q*t+(1-q)+q*(1-a)^2=1-2*q*(a-t) := by
      linear_combination q*ha
    linarith [min_le_right (q*y^2) (q*t),
      min_le_left (1-2*q*y+q*y^2) (1-q*t)]
  have h := quadratic_interval (c:=1) (l:=l) (r:=a)
    (le_of_not_ge hyl) (le_of_not_ge hay)
  rcases le_total (l^2+(1-l)^2) (a^2+(1-a)^2) with hend|hend
  · rw [max_eq_right hend] at h
    apply le_trans _ (le_max_left _ _)
    have hh := mul_le_mul_of_nonneg_left h hq
    linarith [min_le_left (q*y^2) (q*t),
      min_le_left (1-2*q*y+q*y^2) (1-q*t)]
  · rw [max_eq_left hend] at h
    apply le_trans _ (le_max_right _ _)
    have hh := mul_le_mul_of_nonneg_left h hq
    linarith [min_le_left (q*y^2) (q*t),
      min_le_left (1-2*q*y+q*y^2) (1-q*t)]

private theorem left_cap_attained {q t : ℝ} (hq : 0≤q) (ht : 0≤t) (ht₁ : t≤1) :
    leftOverlap q t (Real.sqrt t) = 1-2*q*(Real.sqrt t-t) ∧
    leftOverlap q t (1-Real.sqrt (1-t)) =
      1-2*q*(Real.sqrt (1-t)-(1-t)) := by
  let a := Real.sqrt t
  let b := Real.sqrt (1-t)
  have ha₀ : 0≤a := Real.sqrt_nonneg _
  have hb₀ : 0≤b := Real.sqrt_nonneg _
  have ha : a^2=t := Real.sq_sqrt ht
  have hb : b^2=1-t := Real.sq_sqrt (by linarith)
  have ha₁ : a≤1 := Real.sqrt_le_one.mpr ht₁
  have hb₁ : b≤1 := Real.sqrt_le_one.mpr (by linarith)
  have hab : 1≤a+b := by nlinarith [mul_nonneg ha₀ hb₀]
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (show 0≤1-a by linarith) (show 1-a≤b by linarith) 2) hq
  have hp' := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (show 0≤1-b by linarith) (show 1-b≤a by linarith) 2) hq
  have hqa : q*a^2=q*t := congrArg (fun t : ℝ => q*t) ha
  have hqb : q*b^2=q*(1-t) := congrArg (fun t : ℝ => q*t) hb
  change leftOverlap q t a = 1-2*q*(a-t) ∧
    leftOverlap q t (1-b) = 1-2*q*(b-(1-t))
  constructor
  · unfold leftOverlap
    rw [hqa,min_self,min_eq_left (show 1-2*q*a+q*t≤1-q*t by linarith)]
    linarith
  · unfold leftOverlap
    rw [min_eq_left (show q*(1-b)^2≤q*t by linarith),
      show 1-2*q*(1-b)+q*(1-b)^2=1-q*t by linarith, min_self]
    linarith

private theorem left_cap_exact_upper {q t y : ℝ}
    (hq : 0≤q) (ht : 0≤t) (ht₁ : t≤1) (hy : 0≤y) (hy₁ : y≤1) :
    leftOverlap q t y ≤
      1-2*q*(Real.sqrt (max t (1-t))-max t (1-t)) := by
  have h := left_cap_bound hq ht ht₁ hy hy₁
  rcases le_total t (1-t) with hc|hc
  · have hd := complementary_deficit (t:=1-t) (by linarith) (by linarith)
    have hsub : 1-(1-t)=t := by ring
    rw [hsub] at hd
    have hh := mul_le_mul_of_nonneg_left hd (show 0≤2*q by positivity)
    rw [max_eq_right hc]
    rw [max_eq_right (by linarith)] at h
    exact h
  · have hd := complementary_deficit (t:=t) (by linarith) ht₁
    have hh := mul_le_mul_of_nonneg_left hd (show 0≤2*q by positivity)
    rw [max_eq_left hc]
    rw [max_eq_left (by linarith)] at h
    exact h

def capped (w p₀ p₁ : ℝ) : ℝ := min w p₀ + min (1-w) p₁

private def left₀ (b y : ℝ) : ℝ := b^2*y^2

private def left₁ (b y : ℝ) : ℝ := 1-b^2+b^2*(1-y)^2

private inductive OnArc (a b : ℝ) : ℝ → ℝ → Prop
  | left (y : ℝ) (h₀ : 0≤y) (h₁ : y≤1) : OnArc a b (left₀ b y) (left₁ b y)
  | middle (x : ℝ) (hb : b≤x) (ha : x≤a) : OnArc a b (x^2) ((a+b-x)^2)
  | right (y : ℝ) (h₀ : 0≤y) (h₁ : y≤1) : OnArc a b (left₁ b y) (left₀ b y)

private def leftBest (b w : ℝ) : ℝ :=
  let v := max (w/b^2) (1-w/b^2)
  1-2*b^2*(Real.sqrt v-v)

private def middleBest (a b w : ℝ) : ℝ := (a+b-Real.sqrt (1-w))^2 + (1-w)

private def bestOverlap (a b w : ℝ) : ℝ :=
  if w≤b^2 then leftBest b w else middleBest a b w

private theorem q_small {a b : ℝ} (hb : 0<b) (hba : b≤a) (hn : a^2+b^2=1) :
    b^2≤1/2 := by
  linarith [pow_le_pow_left₀ hb.le hba 2]

private theorem left_rw (b w y : ℝ) (hb : 0<b) :
    capped w (left₀ b y) (left₁ b y) = leftOverlap (b^2) (w/b^2) y := by
  have hq : b^2 ≠ 0 := pow_ne_zero 2 hb.ne'
  have hmul : b^2*(w/b^2)=w := by field_simp
  rw [leftOverlap,hmul]
  unfold capped left₀ left₁
  rw [min_comm w, min_comm (1-w)]
  congr 2
  ring

private theorem left_range {b w : ℝ} (hb : 0<b) (hw : 0≤w) (hq : w≤b^2) :
    0≤w/b^2 ∧ w/b^2≤1 := by
  exact ⟨div_nonneg hw (sq_nonneg b), (div_le_one (sq_pos_of_pos hb)).2 hq⟩

private theorem left_upper {a b w p₀ p₁ : ℝ} (hb : 0<b) (hba : b≤a)
    (hn : a^2+b^2=1) (hw : 0≤w) (hq : w≤b^2) (hp : OnArc a b p₀ p₁) :
    capped w p₀ p₁ ≤ leftBest b w := by
  obtain ⟨ht₀,ht₁⟩ := left_range hb hw hq
  have hleft (y : ℝ) (hy : 0≤y) (hy₁ : y≤1) :
      capped w (left₀ b y) (left₁ b y) ≤ leftBest b w := by
    rw [left_rw b w y hb]
    exact left_cap_exact_upper (sq_nonneg b) ht₀ ht₁ hy hy₁
  have hbase : w+a^2≤leftBest b w := by
    have h := hleft 1 (by norm_num) le_rfl
    have hbcap : a^2≤1-w := by linarith
    simpa [capped,left₀,left₁,min_eq_left hq,
      show 1-b^2=a^2 by linarith,min_eq_right hbcap] using h
  cases hp with
  | left y hy hy₁ => exact hleft y hy hy₁
  | middle x hx _ =>
    have hp₁ : (a+b-x)^2≤a^2 := by
      apply pow_le_pow_left₀ _ (by linarith) 2
      linarith
    exact le_trans (add_le_add (min_le_left _ _) ((min_le_right _ _).trans hp₁)) hbase
  | right y hy hy₁ =>
    have hy2 := pow_le_pow_left₀ hy hy₁ 2
    have hsq : left₀ b y≤a^2 := by
      unfold left₀
      nlinarith [mul_le_mul_of_nonneg_left hy2 (sq_nonneg b),pow_le_pow_left₀ hb.le hba 2]
    exact le_trans (add_le_add (min_le_left _ _) ((min_le_right _ _).trans hsq)) hbase

private theorem cap_root_data {a b w : ℝ} (hb : 0<b) (hba : b≤a)
    (hn : a^2+b^2=1) (hq : b^2≤w) (hw : w≤1/2) :
    let s := Real.sqrt w
    let t := Real.sqrt (1-w)
    0≤s ∧ s≤t ∧ b≤a+b-t ∧ a+b-t≤a ∧ a+b≤s+t := by
  dsimp only
  have hs : 0≤Real.sqrt w := Real.sqrt_nonneg _
  have ht : Real.sqrt w≤Real.sqrt (1-w) := Real.sqrt_le_sqrt (by linarith)
  have hA : Real.sqrt (1-w)≤a := by
    rw [show a=Real.sqrt (a^2) by rw [Real.sqrt_sq (hb.le.trans hba)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hB : b≤Real.sqrt (1-w) := by
    rw [show b=Real.sqrt (b^2) by rw [Real.sqrt_sq hb.le]]
    exact Real.sqrt_le_sqrt (by linarith [q_small hb hba hn])
  have hS : a+b≤Real.sqrt w+Real.sqrt (1-w) := by
    have ha1 : a=Real.sqrt (1-b^2) := by rw [show 1-b^2=a^2 by linarith, Real.sqrt_sq (hb.le.trans hba)]
    have hb1 : b=Real.sqrt (b^2) := (Real.sqrt_sq hb.le).symm
    rcases eq_or_lt_of_le hq with h|h
    · calc
        a+b = Real.sqrt (1-b^2)+Real.sqrt (b^2) := congrArg₂ (·+·) ha1 hb1
        _ ≤ _ := by rw [h]; linarith
    · have hs' := amplitude_sum_strict (sq_nonneg b) h hw
      linarith
  exact ⟨hs,ht,by linarith,by linarith,hS⟩

private theorem middle_upper {a b w p₀ p₁ : ℝ} (hb : 0<b) (hba : b≤a)
    (hn : a^2+b^2=1) (hq : b^2≤w) (hw : w≤1/2) (hp : OnArc a b p₀ p₁) :
    capped w p₀ p₁ ≤ middleBest a b w := by
  obtain ⟨hs,hst,hL,_,hcap⟩ := cap_root_data hb hba hn hq hw
  have hmid (x : ℝ) (hx : b≤x) (hxa : x≤a) :
      capped w (x^2) ((a+b-x)^2) ≤ middleBest a b w := by
    have h := middle_cap_max hs hst (show 0≤a+b-Real.sqrt (1-w) by linarith) hcap
      (show 0≤x by linarith) (show x≤a+b by linarith)
    rw [Real.sq_sqrt (show 0≤w by nlinarith [sq_nonneg b]), Real.sq_sqrt (show 0≤1-w by linarith)] at h
    simpa only [capped,middleBest,min_comm] using h
  have hleft : b^2+(1-w)≤middleBest a b w := by
    have h := hmid b le_rfl hba
    rw [show a+b-b=a by ring] at h
    simpa [capped,min_eq_right hq,min_eq_left (show 1-w≤a^2 by linarith)] using h
  have hright : w+b^2≤middleBest a b w := by
    have h := hmid a hba le_rfl
    rw [show a+b-a=b by ring] at h
    simpa [capped,min_eq_left (show w≤a^2 by linarith [q_small hb hba hn]),
      min_eq_right (show b^2≤1-w by linarith [q_small hb hba hn])] using h
  cases hp with
  | middle x hx hxa => exact hmid x hx hxa
  | left y hy hy₁ =>
    have hsq : left₀ b y≤b^2 := by
      unfold left₀
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hy₁ 2) (sq_nonneg b)
      simpa using hh
    have h := add_le_add ((min_le_right w (left₀ b y)).trans hsq) (min_le_left (1-w) (left₁ b y))
    linarith [show capped w (left₀ b y) (left₁ b y) ≤ b^2+(1-w) from h]
  | right y hy hy₁ =>
    have hsq : left₀ b y≤b^2 := by
      unfold left₀
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hy₁ 2) (sq_nonneg b)
      simpa using hh
    exact (add_le_add (min_le_left _ _) ((min_le_right _ _).trans hsq)).trans hright

private theorem global_capped_upper {a b w p₀ p₁ P₀ P₁ : ℝ}
    (hb : 0<b) (hba : b≤a) (hn : a^2+b^2=1) (hw₀ : 0≤w) (hw₁ : w≤1/2)
    (h₀ : p₀≤P₀) (h₁ : p₁≤P₁) (hArc : OnArc a b P₀ P₁) :
    capped w p₀ p₁≤bestOverlap a b w := by
  have hcap : capped w p₀ p₁≤capped w P₀ P₁ :=
    add_le_add (min_le_min le_rfl h₀) (min_le_min le_rfl h₁)
  unfold bestOverlap
  split
  · exact hcap.trans (left_upper hb hba hn hw₀ (by assumption) hArc)
  · exact hcap.trans (middle_upper hb hba hn (le_of_not_ge (by assumption)) hw₁ hArc)

private def optimalLeft (b w : ℝ) : ℝ :=
  let t := w/b^2
  if t≤1-t then 1-Real.sqrt (1-t) else Real.sqrt t

private theorem left_tight {a b w : ℝ} (hb : 0<b) (hw : 0≤w) (hq : w≤b^2) :
    OnArc a b (left₀ b (optimalLeft b w)) (left₁ b (optimalLeft b w)) ∧
      capped w (left₀ b (optimalLeft b w)) (left₁ b (optimalLeft b w)) = leftBest b w := by
  obtain ⟨ht₀,ht₁⟩ := left_range hb hw hq
  obtain ⟨hA,hB⟩ := left_cap_attained (sq_nonneg b) ht₀ ht₁
  let t := w/b^2
  change 0≤t at ht₀
  change t≤1 at ht₁
  by_cases h : t≤1-t
  · have hy : 0≤1-Real.sqrt (1-t) :=
      sub_nonneg.mpr (Real.sqrt_le_one.mpr (by linarith))
    have hy₁ : 1-Real.sqrt (1-t)≤1 := by linarith [Real.sqrt_nonneg (1-t)]
    have he : optimalLeft b w=1-Real.sqrt (1-t) := ite_eq_left h
    rw [he]
    refine ⟨OnArc.left _ hy hy₁, ?_⟩
    rw [left_rw _ _ _ hb]
    change leftOverlap (b^2) t (1-Real.sqrt (1-t)) =
      1-2*b^2*(Real.sqrt (max t (1-t))-max t (1-t))
    rw [max_eq_right h]
    exact hB
  · have he : optimalLeft b w=Real.sqrt t := ite_eq_right h
    rw [he]
    refine ⟨OnArc.left _ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr ht₁), ?_⟩
    rw [left_rw _ _ _ hb]
    change leftOverlap (b^2) t (Real.sqrt t) =
      1-2*b^2*(Real.sqrt (max t (1-t))-max t (1-t))
    rw [max_eq_left (le_of_not_ge h)]
    exact hA

private def optimalMiddle (a b w : ℝ) : ℝ := a+b-Real.sqrt (1-w)

private theorem middle_tight {a b w : ℝ} (hb : 0<b) (hba : b≤a)
    (hn : a^2+b^2=1) (hq : b^2≤w) (hw : w≤1/2) :
    OnArc a b ((optimalMiddle a b w)^2) ((a+b-optimalMiddle a b w)^2) ∧
      capped w ((optimalMiddle a b w)^2) ((a+b-optimalMiddle a b w)^2) =
        middleBest a b w := by
  obtain ⟨_,_,hL,hR,hcap⟩ := cap_root_data hb hba hn hq hw
  refine ⟨OnArc.middle _ hL hR,?_⟩
  have h := middle_cap_attained (show 0≤a+b-Real.sqrt (1-w) by linarith) hcap
  rw [Real.sq_sqrt (show 0≤w by nlinarith [sq_nonneg b]),Real.sq_sqrt (show 0≤1-w by linarith)] at h
  simpa only [capped,middleBest,optimalMiddle,min_comm] using h

def errorFormula (a b w : ℝ) : ℝ :=
  if w≤b^2 then
    let v := max (w/b^2) (1-w/b^2)
    4*b^2*(Real.sqrt v-v)
  else 2*(w-(a+b-Real.sqrt (1-w))^2)

private theorem error_from_overlap (a b w : ℝ) : 2*(1-bestOverlap a b w)=errorFormula a b w := by
  unfold bestOverlap errorFormula
  split <;> simp [*,leftBest,middleBest] <;> ring

private theorem global_error_lower {a b w p₀ p₁ P₀ P₁ : ℝ}
    (hb : 0<b) (hba : b≤a) (hn : a^2+b^2=1) (hw₀ : 0≤w) (hw₁ : w≤1/2)
    (h₀ : p₀≤P₀) (h₁ : p₁≤P₁) (hArc : OnArc a b P₀ P₁) :
    errorFormula a b w≤2*(1-capped w p₀ p₁) := by
  rw [← error_from_overlap]
  linarith [global_capped_upper hb hba hn hw₀ hw₁ h₀ h₁ hArc]

private theorem global_error_tight {a b w : ℝ}
    (hb : 0<b) (hba : b≤a) (hn : a^2+b^2=1) (hw₀ : 0≤w) (hw₁ : w≤1/2) :
    ∃ p₀ p₁, OnArc a b p₀ p₁ ∧ 2*(1-capped w p₀ p₁)=errorFormula a b w := by
  by_cases hq : w≤b^2
  · obtain ⟨hArc,he⟩ := left_tight (a:=a) hb hw₀ hq
    refine ⟨_,_,hArc,?_⟩
    rw [he, ← error_from_overlap, bestOverlap, ite_eq_left hq]
  · obtain ⟨hArc,he⟩ := middle_tight hb hba hn (le_of_not_ge hq) hw₁
    refine ⟨_,_,hArc,?_⟩
    rw [he, ← error_from_overlap, bestOverlap, ite_eq_right hq]

structure Benchmark where
  a : ℝ
  b : ℝ
  w : ℝ
  bPos : 0 < b
  ordered : b ≤ a
  normalized : a^2+b^2 = 1
  wNonneg : 0 ≤ w
  wHalf : w ≤ 1/2

def exactError (β : Benchmark) : ℝ := errorFormula β.a β.b β.w

theorem result (β : Benchmark) :
    ∃ H : M₂, H.PosSemidef ∧ (DD β.a β.b-H).PosSemidef ∧
      2*(1-capped β.w (quad H) (quad (DD β.a β.b-H))) = exactError β ∧
      ∀ X : M₂, X.PosSemidef → (DD β.a β.b-X).PosSemidef →
        exactError β ≤ 2*(1-capped β.w (quad X) (quad (DD β.a β.b-X))) := by
  rcases β with ⟨a,b,w,hb,hba,hn,hw₀,hw₁⟩
  have ha := hb.le.trans hba
  obtain ⟨p₀,p₁,hArc,heq⟩ := global_error_tight hb hba hn hw₀ hw₁
  have he (y : ℝ) : 1-2*b^2*y+b^2*y^2 = left₁ b y := by unfold left₁; ring
  have attain : ∃ H : M₂, H.PosSemidef ∧ (DD a b-H).PosSemidef ∧
      quad H=p₀ ∧ quad (DD a b-H)=p₁ := by
    cases hArc with
    | left y hy hy₁ =>
      obtain ⟨hH,hC,h₀,h₁⟩ := left_cross_attains ha hb.le hn hy hy₁
      exact ⟨_,hH,hC,h₀,h₁.trans (he y)⟩
    | middle x hx hx₁ => exact middle_cross_attains ha hb.le hx hx₁
    | right y hy hy₁ =>
      obtain ⟨hH,hC,h₀,h₁⟩ := left_cross_attains ha hb.le hn hy hy₁
      have hd : DD a b-(DD a b-leftCross b y)=leftCross b y := sub_sub_cancel _ _
      exact ⟨_,hC,hd.symm ▸ hH,h₁.trans (he y),(congrArg quad hd).trans h₀⟩
  obtain ⟨H,hH,hC,q₀,q₁⟩ := attain
  refine ⟨H,hH,hC,?_,fun X hX hXC => ?_⟩
  · rw [q₀,q₁]
    exact heq
  rcases weighted_psd_hits_bound hb hba hn X hX hXC with
    ⟨y,hy,hyy,t₀,t₁⟩|⟨x,hx,hxx,t₀,t₁⟩|⟨y,hy,hyy,t₁,t₀⟩
  · rw [he] at t₁
    exact global_error_lower hb hba hn hw₀ hw₁ t₀ t₁ (.left y hy hyy)
  · exact global_error_lower hb hba hn hw₀ hw₁ t₀ t₁ (.middle x hx hxx)
  · rw [he] at t₀
    exact global_error_lower hb hba hn hw₀ hw₁ t₀ t₁ (.right y hy hyy)


#print axioms result
end
end D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum
