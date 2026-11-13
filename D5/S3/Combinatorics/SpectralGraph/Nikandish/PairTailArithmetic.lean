/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairTailArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairTailArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact nonzero quadratic tail equations and positive coefficient domains. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants
import Mathlib.Algebra.Polynomial.Roots

/-! Sources: four-prime-tail-reduction, four-prime-harmonic-tail and
four-prime-unique-tail, supplied PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. The parameter c=0 used in
the constant coefficient is an algebraic value, never a positive ideal
exponent. These equations are necessary root tests, not an integrality
criterion; the actual-graph consumer keeps that distinction. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.PairTailArithmetic
open Matrix Polynomial PairedIdealIntersectionObstructions
open PairedIdealIntersectionDeterminants

def A {R : Type*} [CommRing R] (a b t : R) : R :=
  (a+1)^2*(b+1)*t^2+(a+1)*(b+1)*(a^2-(2*a+1)*b)*t-a^2*b^2*(2*a+1)

def B {R : Type*} [CommRing R] (a b t : R) : R :=
  t*(a^3*b^2-2*a^3*b+a^2*b^2*t-a^2*b^2+a^2*b*t-2*a^2*b+
    2*a*b^2*t-3*a*b^2-a*b*t^2+6*a*b*t-a*b-2*a*t^2+a*t+
    b^2*t-b^2-b*t^2+3*b*t-2*t^2)

def H {R : Type*} [CommRing R] (a b t : R) : R :=
  t*((a+1)*b-t)*(t*((a+1)*b-t)+a*t+a^2*b)

def tailPolynomial (a b t : ℤ) : Polynomial ℤ :=
  C (A a b t)*X^2+C (B a b t)*X+C (H a b t)

/-- The full determinant identity, before any domain restriction. -/
theorem determinant {R : Type*} [CommRing R] (a b c t : R) :
    (tensorK a b c-(a+1+t) • 1).det=A a b t*c^2+B a b t*c+H a b t := by
  rw [det_tensorK_sub_scalar]
  unfold A B H
  ring

/-- The constant is strictly positive throughout the full candidate interval. -/
theorem H_positive {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b t : R) (ha : 0<a) (hb : 0<b) (ht : 0<t) (hu : t<(a+1)*b) :
    0<H a b t := by
  unfold H
  have hd : 0<(a+1)*b-t := by linarith
  positivity

/-- In the harmonic window, every linear coefficient is positive. The
complete thirty-four-term source identity includes its boundary offsets. -/
theorem B_positive (a b t : ℤ) (ha : 1≤a) (hl : b<t) (hu : t<2*b) :
    0<B a b t := by
  let w:=a-1
  let u:=t-b-1
  let v:=2*b-t-1
  have hw : 0≤w := by dsimp [w]; omega
  have hu0 : 0≤u := by dsimp [u]; omega
  have hv : 0≤v := by dsimp [v]; omega
  have ht : 0<t := by omega
  have hid : B a b t=t*(
      (13+28*v+14*v^2+2*v^3)+u*(17+26*v+6*v^2)+u^2*(4+4*v)+
      w*(33+53*v+24*v^2+3*v^3)+w*u*(62+58*v+11*v^2)+
      w*u^2*(30+12*v)+4*w*u^3+
      w^2*(10+21*v+10*v^2+v^3)+w^2*u*(27+25*v+4*v^2)+
      w^2*u^2*(15+5*v)+2*w^2*u^3+
      w^3*(2*v+v^2)+w^3*u*(2+2*v)+w^3*u^2) := by
    dsimp [B,w,u,v]
    ring
  rw [hid]
  positivity

/-- Actual zero evaluations impose the constant-term divisibility; the
equation is never assumed as an encoding of graph integrality. -/
theorem root_divides (a b c t : ℤ)
    (hz : (tensorK a b c-(a+1+t) • 1).det=0) : c∣H a b t := by
  rw [determinant] at hz
  have hid : H a b t=c*(-(A a b t*c+B a b t)) := by nlinarith [hz]
  exact ⟨_,hid⟩

theorem eval_tailPolynomial (a b c t : ℤ) :
    (tailPolynomial a b t).eval c=(tensorK a b c-(a+1+t) • 1).det := by
  rw [determinant]
  simp [tailPolynomial]

/-- Each offset has a genuinely nonzero polynomial of degree at most two. -/
theorem polynomial_nonzero (a b t : ℤ) (ha : 0<a) (hb : 0<b)
    (ht : 0<t) (hu : t<(a+1)*b) : tailPolynomial a b t≠0 := by
  intro hz
  have hh:=H_positive a b t ha hb ht hu
  have he:=congrArg (fun p : Polynomial ℤ => p.eval 0) hz
  simp [tailPolynomial] at he
  omega

theorem degree_le_two (a b t : ℤ) : (tailPolynomial a b t).natDegree≤2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp only [tailPolynomial,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
  have h0 : n≠0 := by omega
  have h1 : n≠1 := by omega
  have h2 : 2≠n := by omega
  simp [h0,h1,h2,Ne.symm h1,Ne.symm h2]

/-- On the full integer harmonic window a nonnegative leading coefficient
excludes every positive tail, without a finite parameter base. -/
theorem no_positive_root (a b t c : ℤ) (ha : 1≤a) (hl : b<t)
    (hu : t<2*b) (hc : 0<c) (hA : 0≤A a b t) :
    (tensorK a b c-(a+1+t) • 1).det≠0 := by
  have hb : 0<b := by omega
  have hd : t<(a+1)*b := by nlinarith
  have hH:=H_positive a b t (by omega) hb (by omega) hd
  have hB:=B_positive a b t ha hl hu
  rw [determinant]
  have : 0<A a b t*c^2+B a b t*c+H a b t := by positivity
  exact ne_of_gt this

/-- Two positive integer tails at the same harmonic offset coincide.
This proves a candidate bound, not existence or integral spectrum. -/
theorem positive_root_unique (a b t c d : ℤ) (ha : 1≤a) (hl : b<t)
    (hu : t<2*b) (hc : 0<c) (hd : 0<d)
    (hcz : (tensorK a b c-(a+1+t) • 1).det=0)
    (hdz : (tensorK a b d-(a+1+t) • 1).det=0) : c=d := by
  have hB:=B_positive a b t ha hl hu
  have hA : A a b t<0 := by
    by_contra h
    exact no_positive_root a b t c ha hl hu hc (le_of_not_gt h) hcz
  rw [determinant] at hcz hdz
  by_contra hne
  have he : (c-d)*(A a b t*(c+d)+B a b t)=0 := by nlinarith [hcz,hdz]
  have hl0 : A a b t*(c+d)+B a b t=0 := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)
  have hH : 0<H a b t := H_positive a b t (by omega) (by omega)
    (by omega) (by nlinarith)
  have hprod : H a b t=A a b t*c*d := by nlinarith [hcz,hl0]
  have hneg : A a b t*c*d<0 := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hA hc) hd
  omega


/-- The unique positive real root, with every coefficient and sign retained. -/
theorem positive_real_root (a b t : ℤ) (ha : 1 ≤ a) (hl : b < t)
    (hu : t < 2*b) (hA : A a b t < 0) :
    let c := (((B a b t : ℤ) : ℝ) + Real.sqrt (((B a b t : ℤ) : ℝ)^2 -
      4*((A a b t : ℤ) : ℝ)*((H a b t : ℤ) : ℝ))) / (-2*((A a b t : ℤ) : ℝ))
    0 < c ∧ (tensorK (a:ℝ) (b:ℝ) c - ((a:ℝ)+1+(t:ℝ)) • 1).det = 0 ∧
      ∀ r : ℝ, 0 < r →
        (tensorK (a:ℝ) (b:ℝ) r - ((a:ℝ)+1+(t:ℝ)) • 1).det = 0 → r = c := by
  have hB : (0:ℝ) < ((B a b t : ℤ) : ℝ) := by exact_mod_cast B_positive a b t ha hl hu
  have hH : (0:ℝ) < ((H a b t : ℤ) : ℝ) := by
    exact_mod_cast H_positive a b t (by omega) (by omega) (by omega) (by nlinarith)
  have hAr : ((A a b t : ℤ) : ℝ) < 0 := by exact_mod_cast hA
  let d := Real.sqrt (((B a b t : ℤ) : ℝ)^2 - 4*((A a b t : ℤ) : ℝ)*((H a b t : ℤ) : ℝ))
  let c := (((B a b t : ℤ) : ℝ)+d)/(-2*((A a b t : ℤ) : ℝ))
  have hdisc : 0 ≤ ((B a b t : ℤ) : ℝ)^2 - 4*((A a b t : ℤ) : ℝ)*((H a b t : ℤ) : ℝ) := by
    have := mul_neg_of_neg_of_pos hAr hH
    nlinarith [sq_nonneg ((B a b t : ℤ) : ℝ)]
  have hd : d^2 = ((B a b t : ℤ) : ℝ)^2 - 4*((A a b t : ℤ) : ℝ)*((H a b t : ℤ) : ℝ) :=
    Real.sq_sqrt hdisc
  have hc : 0 < c := by dsimp [c]; exact div_pos (by positivity) (by linarith)
  have he : ((A a b t : ℤ) : ℝ)*c^2+((B a b t : ℤ) : ℝ)*c+((H a b t : ℤ) : ℝ)=0 := by
    dsimp [c]
    field_simp [hAr.ne]
    nlinarith [hd]
  have castA : A (a:ℝ) (b:ℝ) (t:ℝ) = ((A a b t : ℤ) : ℝ) := by simp [A]
  have castB : B (a:ℝ) (b:ℝ) (t:ℝ) = ((B a b t : ℤ) : ℝ) := by simp [B]
  have castH : H (a:ℝ) (b:ℝ) (t:ℝ) = ((H a b t : ℤ) : ℝ) := by simp [H]
  have hdet : (tensorK (a:ℝ) (b:ℝ) c-((a:ℝ)+1+(t:ℝ)) • 1).det=0 := by
    rw [determinant,castA,castB,castH]
    exact he
  refine ⟨hc,hdet,?_⟩
  intro r hr hrz
  rw [determinant,castA,castB,castH] at hrz
  by_contra hne
  have hfactor : (r-c)*(((A a b t : ℤ) : ℝ)*(r+c)+((B a b t : ℤ) : ℝ))=0 := by
    nlinarith [he,hrz]
  have hsum : ((A a b t : ℤ) : ℝ)*(r+c)+((B a b t : ℤ) : ℝ)=0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
  have hprod : ((H a b t : ℤ) : ℝ)=((A a b t : ℤ) : ℝ)*r*c := by nlinarith [hrz,hsum]
  have hneg : ((A a b t : ℤ) : ℝ)*r*c < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hAr hr) hc
  linarith

/-- The leading coefficient is strictly increasing on the whole tail ray. -/
theorem leading_strict (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hx : b ≤ x) (hxy : x < y) : A a b x < A a b y := by
  have hid : A a b y-A a b x =
      (y-x)*(a+1)*(b+1)*((a+1)*(x+y)+a^2-(2*a+1)*b) := by unfold A; ring
  have hbr : 0 < (a+1)*(x+y)+a^2-(2*a+1)*b := by nlinarith
  have hp : 0 < A a b y-A a b x := by rw [hid]; positivity
  linarith


/-- The positive integer-sized tail has one exact leading-coefficient cutoff. -/
theorem leading_cutoff (a b : ℝ) (ha : 0 < a) (hb : 1 ≤ b) :
    ∃ τ : ℝ, b < τ ∧ τ < 2*b ∧ A a b τ=0 ∧
      ∀ t : ℝ, b ≤ t → (A a b t < 0 ↔ t < τ) := by
  have hb0 : 0 < b := by linarith
  have hl : A a b b < 0 := by
    have hid : A a b b = -a*b*(a+b+1)*(a*(b-1)+b) := by unfold A; ring
    have hbm : 0 ≤ b-1 := by linarith
    have hp : 0 < a*b*(a+b+1)*(a*(b-1)+b) := by positivity
    rw [hid]
    nlinarith
  have hu : 0 < A a b (2*b) := by
    have hid : A a b (2*b) =
        b*(2*a^3+a^2*b+2*a^2+2*a*b^2+2*a*b+2*b^2+2*b) := by unfold A; ring
    rw [hid]
    positivity
  have hf : Continuous (fun t : ℝ => A a b t) := by dsimp [A]; fun_prop
  obtain ⟨τ,hτ,hz⟩ := intermediate_value_Icc (by linarith : b ≤ 2*b)
    hf.continuousOn (show (0:ℝ) ∈ Set.Icc (A a b b) (A a b (2*b)) from ⟨hl.le,hu.le⟩)
  change A a b τ=0 at hz
  have hτl : b < τ := by
    have hn : b ≠ τ := by intro he; rw [←he] at hz; exact hl.ne hz
    exact lt_of_le_of_ne hτ.1 hn
  have hτu : τ < 2*b := by
    have hn : τ ≠ 2*b := by intro he; rw [he] at hz; exact hu.ne' hz
    exact lt_of_le_of_ne hτ.2 hn
  refine ⟨τ,hτl,hτu,hz,?_⟩
  intro t ht
  constructor
  · intro hnegative
    by_contra hn
    have hτt : τ ≤ t := le_of_not_gt hn
    rcases lt_or_eq_of_le hτt with hlt | heq
    · have hp:=leading_strict a b τ t ha hb0 hτl.le hlt
      rw [hz] at hp
      linarith
    · rw [←heq,hz] at hnegative
      linarith
  · intro hlt
    have hp:=leading_strict a b t τ ha hb0 ht hlt
    rwa [hz] at hp

end D5.S3.Combinatorics.SpectralGraph.PairTailArithmetic
