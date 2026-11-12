/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportGrowingGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportGrowingGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entire unbounded-gap endpoint exclusions and their certificate-free actual graph family. -/
import D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointGeometry

/-! Sources: complete S.ep1gap and S.ep2gap. The original written d>=5
spectral family uses both entire endpoint exclusions without a finite base.
The broader d>=1 spectral consequence has separate finite dependencies;
the excluded structural-review source remains opaque. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportGrowingGap
open SixSupportClassificationAlgebra SixSupportEndpointGeometry
open SixSupportIdealIntersectionLift (exponents)
open IdealIntersectionSupport IdealIntersectionObstructions

private def anchor (a d : ℝ) : ℝ:=2*a^2+(2*d-3)*a-d^2-3*d/2+1

private theorem one_even_signs (a d : ℝ) (hd : 2≤d) (ha : 2*d^2+20≤a) :
    h (a : ℝ) (a+d) (anchor a d) 1<0 ∧ 0<h (a : ℝ) (a+d) (anchor a d+1) 1 := by
  let r:=d-2
  let m:=a-(2*d^2+20)
  have hr : 0≤r:=by dsimp [r];linarith
  have hm : 0≤m:=by dsimp [m];linarith
  have heD : d=2+r:=by dsimp [r];ring
  have heA : a=2*(2+r)^2+20+m:=by dsimp [m,r];ring
  have hL : 0< -8*h (a : ℝ) (a+d) (anchor a d) 1:=by
    rw [heA,heD]
    simp only [anchor,h,quintic,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
    ring_nf
    positivity
  have hU : 0<8*h (a : ℝ) (a+d) (anchor a d+1) 1:=by
    rw [heA,heD]
    simp only [anchor,h,quintic,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
    ring_nf
    positivity
  constructor <;>linarith

private theorem one_odd_signs (a d : ℝ) (hd : 1≤d) (ha : 2*d^2+20≤a) :
    h (a : ℝ) (a+d) (anchor a d-1/2) 1<0 ∧ 0<h (a : ℝ) (a+d) (anchor a d+1/2) 1 := by
  let r:=d-1
  let m:=a-(2*d^2+20)
  have hr : 0≤r:=by dsimp [r];linarith
  have hm : 0≤m:=by dsimp [m];linarith
  have heD : d=1+r:=by dsimp [r];ring
  have heA : a=2*(1+r)^2+20+m:=by dsimp [m,r];ring
  have hL : 0< -8*h (a : ℝ) (a+d) (anchor a d-1/2) 1:=by
    rw [heA,heD]
    simp only [anchor,h,quintic,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
    ring_nf
    positivity
  have hU : 0<8*h (a : ℝ) (a+d) (anchor a d+1/2) 1:=by
    rw [heA,heD]
    simp only [anchor,h,quintic,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
    ring_nf
    positivity
  constructor <;>linarith

private theorem two_signs (a d : ℝ) (hd : 5≤d) (ha : 2*d^2+20≤a) :
    h (a : ℝ) (a+d) (2*a+d-11) 2<0 ∧ 0<h (a : ℝ) (a+d) (2*a+d-10) 2 := by
  let r:=d-5
  let m:=a-(2*d^2+20)
  have hr : 0≤r:=by dsimp [r];linarith
  have hm : 0≤m:=by dsimp [m];linarith
  have heD : d=5+r:=by dsimp [r];ring
  have heA : a=2*(5+r)^2+20+m:=by dsimp [m,r];ring
  have hL : 0< -h (a : ℝ) (a+d) (2*a+d-11) 2:=by
    rw [heA,heD]
    simp only [h,quintic,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
    ring_nf
    positivity
  have hU : 0<h (a : ℝ) (a+d) (2*a+d-10) 2:=by
    rw [heA,heD]
    simp only [h,quintic,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
    ring_nf
    positivity
  constructor <;>linarith

private theorem strict_root {f : ℝ→ℝ} (L : ℝ) (hc : Continuous f)
    (hL : f L<0) (hU : 0<f (L+1)) : ∃c,L<c ∧ c<L+1 ∧ f c=0 := by
  obtain ⟨c,hcI,hc0⟩:=intermediate_value_Icc (show L≤L+1 by linarith) hc.continuousOn
    (show (0 : ℝ)∈Set.Icc (f L) (f (L+1)) from ⟨hL.le,hU.le⟩)
  refine ⟨c,lt_of_le_of_ne hcI.1 ?_,lt_of_le_of_ne hcI.2 ?_,hc0⟩
  · intro he
    have : f L=0:=by simpa [he] using hc0
    linarith
  · intro he
    have : f (L+1)=0:=by simpa [he] using hc0
    linarith

/-- The exact integer source anchor, using integer division for ceil(3d/2). -/
def lowerOne (a d : ℕ) : ℤ:=
  2*(a : ℤ)^2+(2*(d : ℤ)-3)*a-(d : ℤ)^2-(3*(d : ℤ)+1)/2+1

private theorem anchor_above (a d : ℝ) (hd : 1≤d) (ha : 2*d^2+20≤a) :
    a+d<anchor a d-1/2 := by
  have hd0 : 0≤d:=by linarith
  have hdis : 0<d^2-3*d+20:=by nlinarith [sq_nonneg (d-3/2)]
  have haD : d^2+3*d<a:=by linarith
  have ha20 : 20<a:=by nlinarith
  have had : 0≤(2*d-1)*a:=mul_nonneg (by linarith) (by linarith)
  unfold anchor
  nlinarith [sq_nonneg a]

/-- Full original endpoint-one unit brackets for every integer gap d>=1
and every integer a>=2d^2+20, with unique simple exponent root above b. -/
theorem one_bracket (a d : ℕ) (hd : 1≤d) (ha : 2*d^2+20≤a) :
    ∃c,(lowerOne a d : ℝ)<c ∧ c<(lowerOne a d : ℝ)+1 ∧
      h (a : ℝ) (a+d) c 1=0 ∧
      (onePolynomial a (a+d)).derivative.eval c≠0 ∧
      ∀t,(a+d : ℝ)<t → h (a : ℝ) (a+d) t 1=0 → t=c := by
  have hdR : (1 : ℝ)≤d:=by exact_mod_cast hd
  have haR : 2*(d : ℝ)^2+20≤a:=by exact_mod_cast ha
  have ha8 : (8 : ℝ)≤a:=by nlinarith
  have hab : (a : ℝ)≤a+d:=by
    have hh : (0 : ℝ)≤d:=Nat.cast_nonneg d
    linarith
  let q : ℤ:=(3*(d : ℤ)+1)/2
  have heL : (lowerOne a d : ℝ)=2*(a : ℝ)^2+(2*(d : ℝ)-3)*a-(d : ℝ)^2-(q : ℝ)+1:=by
    dsimp [lowerOne,q]
    push_cast
    rfl
  have hsigns : h (a : ℝ) (a+d) (lowerOne a d) 1<0 ∧ 0<h (a : ℝ) (a+d) ((lowerOne a d : ℝ)+1) 1:=by
    by_cases heven : d%2=0
    · have hd2 : (2 : ℝ)≤d:=by exact_mod_cast (show 2≤d by omega)
      have hq : 2*q=3*(d : ℤ):=by dsimp [q];omega
      have hqR : (q : ℝ)=3*(d : ℝ)/2:=by
        have hh : 2*(q : ℝ)=3*(d : ℝ):=by exact_mod_cast hq
        linarith
      have hL : (lowerOne a d : ℝ)=anchor a d:=by rw [heL,hqR];rfl
      rw [hL]
      exact one_even_signs a d hd2 haR
    · have hq : 2*q=3*(d : ℤ)+1:=by dsimp [q];omega
      have hqR : (q : ℝ)=3*(d : ℝ)/2+1/2:=by
        have hh : 2*(q : ℝ)=3*(d : ℝ)+1:=by exact_mod_cast hq
        linarith
      have hL : (lowerOne a d : ℝ)=anchor a d-1/2:=by rw [heL,hqR];unfold anchor;ring
      rw [hL]
      have hh:=one_odd_signs a d hdR haR
      constructor
      · exact hh.1
      · convert hh.2 using 1 <;> congr 1 <;> ring
  obtain ⟨c,hl,hu,hc⟩:=strict_root (lowerOne a d : ℝ)
    (f:=fun c=>h (a : ℝ) (a+d) c 1) (by simp only [h,quintic,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow];fun_prop) hsigns.1 hsigns.2
  have hqbound : (q : ℝ)≤3*(d : ℝ)/2+1/2:=by
    have hh : 2*q≤3*(d : ℤ)+1:=by dsimp [q];omega
    have hhR : 2*(q : ℝ)≤3*(d : ℝ)+1:=by exact_mod_cast hh
    linarith
  have hbL : (a+d : ℝ)<lowerOne a d:=by
    have h:=anchor_above a d hdR haR
    rw [heL]
    unfold anchor at h
    linarith
  obtain ⟨hs,huniq⟩:=(geometry_one a (a+d) ha8 hab).2 c (lt_trans hbL hl) hc
  exact ⟨c,hl,hu,hc,hs,huniq⟩

/-- Full original real endpoint-two bracket, with d allowed to grow and
all boundary inequalities inclusive, without a finite base. -/
theorem two_bracket (a d : ℝ) (hd : 5≤d) (ha : 2*d^2+20≤a) :
    ∃c,2*a+d-11<c ∧ c<2*a+d-10 ∧ h (a : ℝ) (a+d) c 2=0 ∧
      (twoPolynomial a (a+d)).derivative.eval c≠0 ∧
      ∀t,a+d<t → h (a : ℝ) (a+d) t 2=0 → t=c := by
  obtain ⟨hL,hU⟩:=two_signs a d hd ha
  obtain ⟨c,hl,hu,hc⟩:=strict_root (2*a+d-11) (f:=fun c=>h (a : ℝ) (a+d) c 2)
    (by simp only [h,quintic,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow];fun_prop) hL (by convert hU using 1 <;> congr 1 <;> ring)
  have ha70 : 70≤a:=by nlinarith
  have hbc : a+d<c:=by linarith
  obtain ⟨hs,huniq⟩:=(geometry_two a (a+d) (by linarith) (by linarith)).2 c hbc hc
  exact ⟨c,hl,by linarith,hc,hs,huniq⟩

/-- No integer last exponent on the full original endpoint-one family. -/
theorem one_integer_nonzero (a d c : ℕ) (hd : 1≤d) (ha : 2*d^2+20≤a)
    (hbc : a+d<c) : h (a : ℝ) (a+d) c 1≠0 := by
  obtain ⟨r,hl,hu,hr,hs,huniq⟩:=one_bracket a d hd ha
  intro hc
  have he:=huniq c (by exact_mod_cast hbc) hc
  have hlI : lowerOne a d<(c : ℤ):=by exact_mod_cast (show (lowerOne a d : ℝ)<c by simpa [he] using hl)
  have huI : (c : ℤ)<lowerOne a d+1:=by exact_mod_cast (show (c : ℝ)<(lowerOne a d : ℝ)+1 by simpa [he] using hu)
  omega

/-- No integer last exponent on the full original endpoint-two family. -/
theorem two_integer_nonzero (a d c : ℕ) (hd : 5≤d) (ha : 2*d^2+20≤a)
    (hbc : a+d<c) : h (a : ℝ) (a+d) c 2≠0 := by
  obtain ⟨r,hl,hu,hr,hs,huniq⟩:=two_bracket a d (by exact_mod_cast hd) (by exact_mod_cast ha)
  intro hc
  have he:=huniq c (by exact_mod_cast hbc) hc
  have hlI : 2*(a : ℤ)+d-11<(c : ℤ):=by exact_mod_cast (show 2*(a : ℝ)+d-11<c by simpa [he] using hl)
  have huI : (c : ℤ)<2*(a : ℤ)+d-10:=by exact_mod_cast (show (c : ℝ)<2*(a : ℝ)+d-10 by simpa [he] using hu)
  omega

/-- The complete parity-free original written spectral family on actual
ideals, with no finite exponent base or assumed endpoint emptiness. -/
theorem result (p : Fin 3→ℕ) (hp : ∀i,Nat.Prime (p i)) (hinj : Function.Injective p)
    (a d c : ℕ) (hd : 5≤d) (ha : 2*d^2+20≤a) (hbc : a+d<c) :
    ¬ActualLaplacianIntegral (modulus p (exponents a (a+d) c)) := by
  intro hi
  have ha0 : 0<a:=by omega
  rcases endpoint_one_or_two p hp hinj a (a+d) c ha0 (by omega) hbc.le hi with h1|h2
  · exact one_integer_nonzero a d c (by omega) ha hbc (by simpa only [Nat.cast_add] using h1)
  · exact two_integer_nonzero a d c hd ha hbc (by simpa only [Nat.cast_add] using h2)

/-- The complete fixed-real-gap expansion through the inverse-square term. -/
def fixedGapApproximation (a d : ℝ) : ℝ :=
  2*a^2+(2*d-3)*a-(d+2)*(2*d-1)/2+d^2/(2*a)+d^2*(d+1)*(2*d-3)/(4*a^2)

private def realLower (a d : ℝ) : ℝ := anchor a d-1/2

private theorem real_bracket (a d : ℝ) (hd : 1≤d) (ha : 2*d^2+20≤a) :
    ∃ c, realLower a d<c ∧ c<realLower a d+1 ∧ a+d<c ∧ h a (a+d) c 1=0 := by
  obtain ⟨hL,hU⟩:=one_odd_signs a d hd ha
  obtain ⟨c,hcL,hcU,hc0⟩:=strict_root (realLower a d)
    (show Continuous (fun c : ℝ=>h a (a+d) c 1) by
      simp only [h,quintic,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,
        Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow];fun_prop)
    hL (by
      have hshift : realLower a d+1=anchor a d+1/2 := by unfold realLower;ring
      rw [hshift]
      exact hU)
  exact ⟨c,hcL,hcU,lt_trans (anchor_above a d hd ha) hcL,hc0⟩

private def slope (a d c x : ℝ) : ℝ :=
  (a^2+(a+d)^2-1)*(c^2+c*x+x^2)+
  (a^3-4*a^2*(a+d)^2+2*a^2*(a+d)-a^2+2*a*(a+d)^2+a*(a+d)-3*a+
    (a+d)^3-(a+d)^2-3*(a+d)+3)*(c+x)+
  (a-1)*(a+d-1)*(2*a*(a+d)+3*a+3*(a+d)-3)

private theorem slope_bound (a d c x : ℝ) (hd : 1≤d) (ha : 2*d^2+20≤a)
    (hc : realLower a d≤c) (hx : realLower a d≤x) : a^6≤slope a d c x := by
  let r:=d-1
  let m:=a-(2*d^2+20)
  let u:=c-realLower a d
  let v:=x-realLower a d
  have hr : 0≤r:=by dsimp [r];linarith
  have hm : 0≤m:=by dsimp [m];linarith
  have hu : 0≤u:=sub_nonneg.mpr hc
  have hv : 0≤v:=sub_nonneg.mpr hx
  have heD : d=1+r:=by dsimp [r];ring
  have heA : a=2*(1+r)^2+20+m:=by dsimp [m,r];ring
  have heC : c=realLower a d+u:=by dsimp [u];ring
  have heX : x=realLower a d+v:=by dsimp [v];ring
  apply sub_nonneg.mp
  rw [heC,heX]
  dsimp [slope,realLower,anchor]
  rw [heA,heD]
  ring_nf
  positivity

private theorem approximation_above (a d : ℝ) (hd : 1≤d) (ha : 2*d^2+20≤a) :
    realLower a d<fixedGapApproximation a d := by
  have ha0 : 0<a:=by nlinarith [sq_nonneg d]
  let r:=d-1
  let m:=a-(2*d^2+20)
  have hr : 0≤r:=by dsimp [r];linarith
  have hm : 0≤m:=by dsimp [m];linarith
  have heD : d=1+r:=by dsimp [r];ring
  have heA : a=2*(1+r)^2+20+m:=by dsimp [m,r];ring
  have hpos : 0<2*a^2+2*a*d^2+d^2*(d+1)*(2*d-3):=by
    rw [heA,heD]
    ring_nf
    positivity
  have hid : 4*a^2*(fixedGapApproximation a d-realLower a d)=
      2*a^2+2*a*d^2+d^2*(d+1)*(2*d-3):=by
    dsimp [fixedGapApproximation,realLower,anchor]
    field_simp [ne_of_gt ha0]
    <;>ring
  have hh : 0<4*a^2*(fixedGapApproximation a d-realLower a d):=by rw [hid];exact hpos
  exact sub_pos.mp ((mul_pos_iff_of_pos_left (show (0 : ℝ)<4*a^2 by positivity)).mp hh)

private def residualCoefficients (d : ℝ) : Fin 10→ℝ :=
  ![8*d^14 - 12*d^13 - 38*d^12 + 47*d^11 + 75*d^10 - 62*d^9 - 72*d^8 + 27*d^7 + 27*d^6,
    16*d^13 - 84*d^11 - 20*d^10 + 150*d^9 + 66*d^8 - 90*d^7 - 54*d^6,
    -32*d^12 + 16*d^11 + 184*d^10 - 48*d^9 - 334*d^8 - 6*d^7 + 198*d^6 + 54*d^5,
    -256*d^10 + 128*d^9 + 848*d^8 - 180*d^7 - 788*d^6 - 36*d^5 + 108*d^4,
    224*d^10 - 240*d^9 - 856*d^8 + 604*d^7 + 920*d^6 - 316*d^5 - 192*d^4,
    64*d^9 + 384*d^8 + 48*d^7 - 1072*d^6 - 232*d^5 + 440*d^4,
    -256*d^8 - 448*d^7 + 1824*d^6 + 432*d^5 - 1864*d^4 + 264*d^3,
    256*d^7 - 1664*d^6 + 320*d^5 + 2624*d^4 - 1584*d^3 + 144*d^2,
    640*d^6 - 832*d^5 - 1088*d^4 + 1824*d^3 - 624*d^2,
    256*d^5 - 384*d^3 + 448*d^2]

private theorem residual_identity (a d : ℝ) (ha : a≠0) :
    64*a^6*h a (a+d) (fixedGapApproximation a d) 1=
      ∑ i : Fin 10,residualCoefficients d i*a^(i : ℕ) := by
  rw [SixSupportEndpointSmallGaps.endpoint_identity]
  norm_num [Fin.sum_univ_succ,residualCoefficients,SixSupportEndpointSmallGaps.cubic,
    fixedGapApproximation]
  field_simp [ha]
  <;>ring

private theorem residual_bound (a d : ℝ) (ha : 1≤a) :
    |64*a^6*h a (a+d) (fixedGapApproximation a d) 1|≤
      (∑ i : Fin 10,|residualCoefficients d i|)*a^9 := by
  rw [residual_identity a d (by linarith)]
  calc
    |∑ i : Fin 10,residualCoefficients d i*a^(i : ℕ)| ≤
        ∑ i : Fin 10,|residualCoefficients d i*a^(i : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin 10,|residualCoefficients d i| *a^(i : ℕ) := by
      simp_rw [abs_mul,abs_pow,abs_of_nonneg (by linarith : 0≤a)]
    _ ≤ ∑ i : Fin 10,|residualCoefficients d i| *a^9 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact pow_le_pow_right₀ ha (by have :=i.isLt;omega)
    _ = (∑ i : Fin 10,|residualCoefficients d i|)*a^9 := by rw [Finset.sum_mul]

/-- For every fixed real gap d>=1, the actual unique endpoint-one exponent
root has the complete received expansion with an explicit O_d(a^-3) bound.
The constant may depend on d; no uniform growing-gap remainder is asserted.
Existence and uniqueness on the entire eventual domain are conclusions. -/
theorem fixed_gap_expansion (d : ℝ) (hd : 1≤d) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℝ,2*d^2+20≤a →
      (∃! c : ℝ,a+d<c ∧ h a (a+d) c 1=0) ∧
      ∀ c : ℝ,a+d<c → h a (a+d) c 1=0 →
        |c-fixedGapApproximation a d|≤C/a^3 := by
  let C0 : ℝ:=∑ i : Fin 10,|residualCoefficients d i|
  have hC0 : 0≤C0:=Finset.sum_nonneg (fun i _=>abs_nonneg _)
  refine ⟨C0+1,by linarith,?_⟩
  intro a ha
  have ha1 : 1≤a:=by nlinarith [sq_nonneg d]
  have ha0 : 0<a:=by linarith
  have ha8 : 8≤a:=by nlinarith [sq_nonneg d]
  have hab : a≤a+d:=by linarith
  obtain ⟨root,hrL,hrU,hrAbove,hr0⟩:=real_bracket a d hd ha
  have huniq:=((geometry_one a (a+d) ha8 hab).2 root hrAbove hr0).2
  refine ⟨⟨root,⟨hrAbove,hr0⟩,fun y hy=>huniq y hy.1 hy.2⟩,?_⟩
  intro c hc hc0
  have hcL : realLower a d≤c:=by rw [huniq c hc hc0];exact hrL.le
  have hs:=slope_bound a d c (fixedGapApproximation a d) hd ha hcL
    (approximation_above a d hd ha).le
  have hsplit : h a (a+d) c 1-h a (a+d) (fixedGapApproximation a d) 1=
      (c-fixedGapApproximation a d)*slope a d c (fixedGapApproximation a d):=by
    simp only [SixSupportEndpointSmallGaps.endpoint_identity]
    unfold SixSupportEndpointSmallGaps.cubic slope
    ring
  have hsa : |c-fixedGapApproximation a d| *slope a d c (fixedGapApproximation a d)=
      |h a (a+d) (fixedGapApproximation a d) 1|:=by
    have hh:=congrArg abs hsplit
    rw [hc0,zero_sub,abs_neg,abs_mul,abs_of_nonneg (le_trans (pow_nonneg ha0.le 6) hs)] at hh
    exact hh.symm
  have hbound:=residual_bound a d ha1
  rw [abs_mul,abs_of_pos (show (0 : ℝ)<64*a^6 by positivity)] at hbound
  have hsmall : |c-fixedGapApproximation a d| *(64*a^3)≤C0 := by
    apply (mul_le_mul_iff_left₀ (show (0 : ℝ)<a^9 by positivity)).mp
    calc
      (|c-fixedGapApproximation a d| *(64*a^3))*a^9=
          (64*a^6)*(|c-fixedGapApproximation a d| *a^6) := by ring
      _ ≤ (64*a^6)*(|c-fixedGapApproximation a d| *slope a d c (fixedGapApproximation a d)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) (by positivity)
      _ = (64*a^6)*|h a (a+d) (fixedGapApproximation a d) 1| := by rw [hsa]
      _ ≤ C0*a^9 := hbound
  apply (le_div_iff₀ (show (0 : ℝ)<a^3 by positivity)).mpr
  have herr : 0≤|c-fixedGapApproximation a d| *a^3:=mul_nonneg (abs_nonneg _) (by positivity)
  nlinarith

end D5.S3.Combinatorics.SpectralGraph.SixSupportGrowingGap
