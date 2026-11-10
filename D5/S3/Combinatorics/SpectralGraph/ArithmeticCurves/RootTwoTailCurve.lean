/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/RootTwoTailCurve
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/RootTwoTailCurve
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full positive-tail root-two curve, exact quartic recovery and finite fibers -/

import D5.S3.Combinatorics.SpectralGraph.PairLowArithmetic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Int.Interval

/-! Source: Ma/Nikandish/Zhang, supplied PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02,
notes/four-prime-root-two-curve.md, blob
f3751b6be960a3712fd9c7a7a532c06bfc39e80f. Original Nikandish graph
and problem attribution is retained. The positive-tail finiteness proof below
uses a direct global sign bound and complete polynomial fibers. The source's
separate squarefree projective normalization, geometric irreducibility,
genus-one/elliptic-model and Siegel arguments are not certified by this
alternative arithmetic proof. Neither this finite set nor a root two is a
sufficient criterion for integral graph spectrum. No tail ordering or
coprimality is imposed. Both quartic signs and the exceptional A=0 fibers
are retained; c=0 is only a rational base point, not a graph exponent. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
open Matrix Polynomial Finset
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.RootTwoTailCurve
open D5.S3.Combinatorics.SpectralGraph
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants
open PairedIdealIntersectionLift IdealIntersectionSupport IdealIntersectionObstructions

def A {R : Type*} [CommRing R] (a b : R) : R :=
  -(2*a+1)*b^2+2*a*(a^2-1)*b-(a^2-1)

def B {R : Type*} [CommRing R] (a b : R) : R :=
  (a-1)*(2*a*(a+1)*b^2+(4*a^3+6*a^2-3*a-2)*b+(a-1)*(2*a^2+a-2))

def C₀ {R : Type*} [CommRing R] (a b : R) : R :=
  (a-1)*((a-1)*(2*a-1)-b)*((a+1)*b+a-1)

def equation {R : Type*} [CommRing R] (a b c : R) : R :=
  A a b*c^2+B a b*c+C₀ a b

def quartic {R : Type*} [CommRing R] (a b : R) : R :=
  B a b^2-4*A a b*C₀ a b

/-- The exact characteristic equation of the full four-dimensional operator. -/
theorem determinant {R : Type*} [CommRing R] (a b c : R) :
    (tensorK a b c-(2:R) • 1).det=equation a b c := by
  rw [det_tensorK_sub_scalar]
  unfold equation A B C₀
  ring

theorem symmetric {R : Type*} [CommRing R] (a b c : R) :
    equation a b c=equation a c b := by unfold equation A B C₀;ring

theorem recovery_identity {R : Type*} [CommRing R] (a b c : R) :
    (2*A a b*c+B a b)^2-quartic a b=4*A a b*equation a b c := by
  unfold quartic equation
  ring

/-- Complete affine and quartic point objects over Q, before exceptional fibers. -/
def AffinePoint (a : ℚ) := {q : ℚ × ℚ // equation a q.1 q.2=0}
def QuarticPoint (a : ℚ) := {q : ℚ × ℚ // q.2^2=quartic a q.1}

def to_quartic {a : ℚ} (q : AffinePoint a) : QuarticPoint a :=
  ⟨(q.1.1,2*A a q.1.1*q.1.2+B a q.1.1),by
    have h:=recovery_identity a q.1.1 q.1.2
    rw [q.2,mul_zero] at h
    exact sub_eq_zero.mp h⟩

def from_quartic {a : ℚ} (q : QuarticPoint a) (hA : A a q.1.1≠0) : AffinePoint a := by
  refine ⟨(q.1.1,(q.1.2-B a q.1.1)/(2*A a q.1.1)),?_⟩
  have hd : 2*A a q.1.1≠0 := mul_ne_zero (by norm_num) hA
  have h:=recovery_identity a q.1.1 ((q.1.2-B a q.1.1)/(2*A a q.1.1))
  have he : 2*A a q.1.1*((q.1.2-B a q.1.1)/(2*A a q.1.1))+B a q.1.1=q.1.2 := by
    field_simp [hA]
    <;>ring
  rw [he,q.2,sub_self] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero (by norm_num) hA)

theorem from_to {a : ℚ} (q : AffinePoint a) (hA : A a q.1.1≠0) :
    from_quartic (to_quartic q) hA=q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (2*A a q.1.1*q.1.2+B a q.1.1-B a q.1.1)/(2*A a q.1.1)=q.1.2
    field_simp [hA]
    <;> ring

theorem to_from {a : ℚ} (q : QuarticPoint a) (hA : A a q.1.1≠0) :
    to_quartic (from_quartic q hA)=q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change 2*A a q.1.1*((q.1.2-B a q.1.1)/(2*A a q.1.1))+B a q.1.1=q.1.2
    field_simp [hA]
    <;>ring

/-- No sign selection occurs in integer recovery. -/
theorem integer_recovery (a b y : ℤ) (hA : A a b≠0)
    (hy : y^2=quartic a b) :
    (∃ c : ℤ, equation a b c=0 ∧ y=2*A a b*c+B a b) ↔
      2*A a b∣y-B a b := by
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact ⟨c,by ring⟩
  · rintro ⟨c,hc⟩
    have he : y=2*A a b*c+B a b := by linarith
    refine ⟨c,?_,he⟩
    have h:=recovery_identity a b c
    rw [←he,hy,sub_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero (by norm_num) hA)

/-- Nonzero coefficient throughout the entire positive-tail domain, including A=0. -/
theorem B_positive (a b : ℤ) (ha : 2≤a) (hb : 0<b) : 0<B a b := by
  have ha1 : 0<a-1 := by omega
  have h2 : 0<2*a^2+a-2 := by nlinarith [sq_nonneg a]
  have h3 : 0<4*a^3+6*a^2-3*a-2 := by
    have h : 0≤a^2*(a-1) := mul_nonneg (sq_nonneg a) (by omega)
    nlinarith [sq_nonneg a]
  unfold B
  positivity

/-- Every exceptional A=0 fiber is genuinely linear, not dropped. -/
theorem exceptional_fiber (a b c : ℤ) (ha : 2≤a) (hb : 0<b)
    (hA : A a b=0) :
    equation a b c=0 ↔ B a b*c= -C₀ a b := by
  simp only [equation,hA,zero_mul,zero_add]
  exact add_eq_zero_iff_eq_neg

theorem exceptional_fiber_unique (a b c d : ℤ) (ha : 2≤a) (hb : 0<b)
    (hA : A a b=0) (hc : equation a b c=0) (hd : equation a b d=0) : c=d := by
  have hc':=(exceptional_fiber a b c ha hb hA).mp hc
  have hd':=(exceptional_fiber a b d ha hb hA).mp hd
  exact mul_left_cancel₀ (B_positive a b ha hb).ne' (hc'.trans hd'.symm)

def baseB {R : Type*} [CommRing R] (a : R) : R := (a-1)*(2*a-1)

def rational_base (a : ℚ) : QuarticPoint a :=
  ⟨(baseB a,B a (baseB a)),by simp [quartic,C₀,baseB]⟩

theorem base_zero_tail {R : Type*} [CommRing R] (a : R) :
    equation a (baseB a) 0=0 := by simp [equation,C₀,baseB]

/-- All five quartic coefficients, including the nonzero constant term. -/
theorem quartic_coefficients {R : Type*} [CommRing R] (a b : R) :
    quartic a b=
      4*(a-1)*(a+1)*(a^2-a-1)*(a^2+a+1)*b^4+
      4*(a-1)^2*(a^2+a+1)*(4*a^3+6*a^2-a-2)*b^3+
      (a-1)^2*(16*a^6+40*a^5+8*a^4-20*a^3-31*a^2-8*a+4)*b^2+
      2*a*(a-1)^3*(2*a+1)*(4*a^3+2*a^2-a-2)*b+
      a^2*(a-1)^4*(2*a+1)^2 := by unfold quartic A B C₀;ring

def tailPolynomial (a b : ℤ) : Polynomial ℤ :=
  Polynomial.C (A a b)*X^2+Polynomial.C (B a b)*X+Polynomial.C (C₀ a b)

theorem eval_tail (a b c : ℤ) : (tailPolynomial a b).eval c=equation a b c := by
  simp [tailPolynomial,equation]

theorem tail_nonzero (a b : ℤ) (ha : 2≤a) (hb : 0<b) : tailPolynomial a b≠0 := by
  intro hz
  have h:=congrArg (fun q : Polynomial ℤ => q.coeff 1) hz
  have hb':=B_positive a b ha hb
  have he : (tailPolynomial a b).coeff 1=B a b := by
    simp only [tailPolynomial,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
    norm_num
  rw [he] at h
  simp only [coeff_zero] at h
  omega

theorem tail_degree (a b : ℤ) : (tailPolynomial a b).natDegree≤2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have h0 : n≠0 := by omega
  have h1 : n≠1 := by omega
  have h2 : 2≠n := by omega
  simp only [tailPolynomial,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
  simp [h0,h1,h2,Ne.symm h1,Ne.symm h2]

def positiveFiber (a b : ℤ) : Finset ℤ :=
  (tailPolynomial a b).roots.toFinset.filter (0<·)

theorem fiber_card (a b : ℤ) : (positiveFiber a b).card≤2 := by
  exact (Finset.card_filter_le _ _).trans
    (((tailPolynomial a b).roots.toFinset_card_le).trans
      ((Polynomial.card_roots' _).trans (tail_degree a b)))

theorem mem_fiber (a b c : ℤ) (ha : 2≤a) (hb : 0<b) (hc : 0<c) :
    c∈positiveFiber a b ↔ equation a b c=0 := by
  simp only [positiveFiber,Finset.mem_filter,Multiset.mem_toFinset]
  rw [Polynomial.mem_roots (tail_nonzero a b ha hb)]
  simp [Polynomial.IsRoot,eval_tail,hc]

/-- A full parameter sign certificate, with no bounded parameter enumeration. -/
theorem negative_large_tails (a b c : ℤ) (ha : 2≤a)
    (hb : 2*(a+1)^2≤b) (hc : 2*(a+1)^2≤c) : equation a b c<0 := by
  let u:=a-2
  let v:=b-2*(a+1)^2
  let w:=c-2*(a+1)^2
  have hu : 0≤u := by dsimp [u];omega
  have hv : 0≤v := by dsimp [v];omega
  have hw : 0≤w := by dsimp [w];omega
  have he : -equation a b c=
      64*u^8 +
      8*u^7*v +
      8*u^7*w +
      1528*u^7 +
      216*u^6*v +
      216*u^6*w +
      15924*u^6 +
      4*u^5*v^2 +
      16*u^5*v*w +
      2356*u^5*v +
      4*u^5*w^2 +
      2356*u^5*w +
      94600*u^5 +
      68*u^4*v^2 +
      268*u^4*v*w +
      13724*u^4*v +
      68*u^4*w^2 +
      13724*u^4*w +
      350286*u^4 +
      6*u^3*v^2*w +
      448*u^3*v^2 +
      6*u^3*v*w^2 +
      1758*u^3*v*w +
      46593*u^3*v +
      448*u^3*w^2 +
      46593*u^3*w +
      827471*u^3 +
      56*u^2*v^2*w +
      1441*u^2*v^2 +
      56*u^2*v*w^2 +
      5661*u^2*v*w +
      92738*u^2*v +
      1441*u^2*w^2 +
      92738*u^2*w +
      1217125*u^2 +
      2*u*v^2*w^2 +
      170*u*v^2*w +
      2272*u*v^2 +
      170*u*v*w^2 +
      8955*u*v*w +
      100541*u*v +
      2272*u*w^2 +
      100541*u*w +
      1018525*u +
      5*v^2*w^2 +
      168*v^2*w +
      1407*v^2 +
      168*v*w^2 +
      5568*v*w +
      45892*v +
      1407*w^2 +
      45892*w +
      371013 := by
    dsimp [u,v,w,equation,A,B,C₀]
    ring
  have hp : 0< -equation a b c := by rw [he];positivity
  omega

/-- Complete finite positive integral-point candidate set in both orientations. -/
def positivePairs (a : ℤ) : Finset (ℤ × ℤ) :=
  let forward := (Finset.Ioo 0 (2*(a+1)^2)).biUnion
    (fun b => (positiveFiber a b).image (fun c => (b,c)))
  forward ∪ forward.image Prod.swap

theorem mem_positivePairs (a b c : ℤ) (ha : 2≤a) :
    (b,c)∈positivePairs a ↔ 0<b ∧ 0<c ∧ equation a b c=0 := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨b',hb',hh⟩:=Finset.mem_biUnion.mp h
      obtain ⟨c',hc',he⟩:=Finset.mem_image.mp hh
      have hb : 0<b' := (Finset.mem_Ioo.mp hb').1
      cases he
      exact ⟨hb,(Finset.mem_filter.mp hc').2,(mem_fiber a b c ha hb (Finset.mem_filter.mp hc').2).mp hc'⟩
    · obtain ⟨q,hq,he⟩:=Finset.mem_image.mp h
      obtain ⟨b',hb',hh⟩:=Finset.mem_biUnion.mp hq
      obtain ⟨c',hc',he'⟩:=Finset.mem_image.mp hh
      cases he'
      change (c',b')=(b,c) at he
      cases he
      have hc : 0<c := (Finset.mem_Ioo.mp hb').1
      have hb : 0<b := (Finset.mem_filter.mp hc').2
      have hz : equation a b c=0 := by
        rw [symmetric]
        exact (mem_fiber a c b ha hc hb).mp hc'
      exact ⟨hb,hc,hz⟩
  · rintro ⟨hb,hc,hz⟩
    have hs : b<2*(a+1)^2 ∨ c<2*(a+1)^2 := by
      by_contra hh
      push_neg at hh
      exact (negative_large_tails a b c ha hh.1 hh.2).ne hz
    apply Finset.mem_union.mpr
    rcases hs with hs | hs
    · apply Or.inl
      exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_Ioo.mpr ⟨hb,hs⟩,
        Finset.mem_image.mpr ⟨c,(mem_fiber a b c ha hb hc).mpr hz,rfl⟩⟩
    · apply Or.inr
      exact Finset.mem_image.mpr ⟨(c,b),Finset.mem_biUnion.mpr
        ⟨c,Finset.mem_Ioo.mpr ⟨hc,hs⟩,Finset.mem_image.mpr
          ⟨b,(mem_fiber a c b ha hc hb).mpr (by rwa [symmetric]),rfl⟩⟩,rfl⟩

/-- Original full positive-tail finiteness, with a direct proof independent of Siegel. -/
theorem positive_integer_finiteness (a : ℤ) (ha : 2≤a) :
    {q : ℤ × ℤ | 0<q.1 ∧ 0<q.2 ∧ equation a q.1 q.2=0}.Finite := by
  apply (positivePairs a).finite_toSet.subset
  intro q hq
  exact (mem_positivePairs a q.1 q.2 ha).mpr hq

/-- Actual full ideal-graph consumer, on arbitrary four distinct primes. -/
theorem root_two_actual_eigenvalue (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hz : equation (a:ℤ) b c=0) :
    HasActualEigenvalue (modulus p (pairExponents a b c))
      (((((a+1)^2*(b+1)*(c+1))-2 : ℕ) : ℝ)+1-2) := by
  have hr : equation (a:ℝ) b c=0 := by
    dsimp [equation,A,B,C₀] at hz ⊢
    exact_mod_cast hz
  rw [←determinant] at hr
  obtain ⟨h,hh,hZ⟩:=Matrix.exists_mulVec_eq_zero_iff.mpr hr
  rw [sub_mulVec,smul_mulVec,one_mulVec] at hZ
  exact actual_paired_eigenvalue p hp hinj a b c ha hb hc 2 h hh (sub_eq_zero.mp hZ)


/-- The complete root-three fibers used in the original graph corollary. -/
def threeA {R : Type*} [CommRing R] (a b : R) : R :=
  -(a+2)*(2*a+1)*b^2+(a-2)*(a^2-1)*b-(a+1)*(a-2)*(a+2)

def threeB {R : Type*} [CommRing R] (a b : R) : R :=
  (a-2)*((a^2-1)*b^2+(4*a^3+3*a^2-8*a-2)*b+(a-2)*(2*a^2-a-4))

def threeC {R : Type*} [CommRing R] (a b : R) : R :=
  (a-2)*(a*b+a+b-2)*(2*a^2-a*b-6*a-2*b+4)

def equationThree {R : Type*} [CommRing R] (a b c : R) : R :=
  threeA a b*c^2+threeB a b*c+threeC a b

theorem determinant_three {R : Type*} [CommRing R] (a b c : R) :
    (tensorK a b c-(3:R) • 1).det=equationThree a b c := by
  rw [det_tensorK_sub_scalar]
  unfold equationThree threeA threeB threeC
  ring

theorem symmetric_three {R : Type*} [CommRing R] (a b c : R) :
    equationThree a b c=equationThree a c b := by
  unfold equationThree threeA threeB threeC
  ring

theorem threeB_positive (a b : ℤ) (ha : 3≤a) (hb : 0<b) : 0<threeB a b := by
  have h0 : 0<a-2 := by omega
  have h1 : 0<a^2-1 := by nlinarith [sq_nonneg a]
  have h2 : 0<4*a^3+3*a^2-8*a-2 := by
    have h : 0≤a^2*(a-2) := mul_nonneg (sq_nonneg a) (by omega)
    nlinarith [sq_nonneg a]
  have h3 : 0<2*a^2-a-4 := by nlinarith [sq_nonneg a]
  unfold threeB
  positivity

def threePolynomial (a b : ℤ) : Polynomial ℤ :=
  Polynomial.C (threeA a b)*X^2+Polynomial.C (threeB a b)*X+Polynomial.C (threeC a b)

theorem eval_three (a b c : ℤ) : (threePolynomial a b).eval c=equationThree a b c := by
  simp [threePolynomial,equationThree]

theorem three_nonzero (a b : ℤ) (ha : 3≤a) (hb : 0<b) : threePolynomial a b≠0 := by
  intro hz
  have h:=congrArg (fun q : Polynomial ℤ => q.coeff 1) hz
  have hb':=threeB_positive a b ha hb
  have he : (threePolynomial a b).coeff 1=threeB a b := by
    simp only [threePolynomial,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
    norm_num
  rw [he] at h
  simp only [coeff_zero] at h
  omega

theorem three_degree (a b : ℤ) : (threePolynomial a b).natDegree≤2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have h0 : n≠0 := by omega
  have h1 : n≠1 := by omega
  have h2 : 2≠n := by omega
  simp only [threePolynomial,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
  simp [h0,h1,h2,Ne.symm h1,Ne.symm h2]

def positiveThreeFiber (a b : ℤ) : Finset ℤ :=
  (threePolynomial a b).roots.toFinset.filter (0<·)

theorem three_fiber_card (a b : ℤ) : (positiveThreeFiber a b).card≤2 := by
  exact (Finset.card_filter_le _ _).trans
    (((threePolynomial a b).roots.toFinset_card_le).trans
      ((Polynomial.card_roots' _).trans (three_degree a b)))

theorem mem_three_fiber (a b c : ℤ) (ha : 3≤a) (hb : 0<b) (hc : 0<c) :
    c∈positiveThreeFiber a b ↔ equationThree a b c=0 := by
  simp only [positiveThreeFiber,Finset.mem_filter,Multiset.mem_toFinset]
  rw [Polynomial.mem_roots (three_nonzero a b ha hb)]
  simp [Polynomial.IsRoot,eval_three,hc]

/-- Full parameter sign certificate for the second necessary endpoint. -/
theorem three_negative_large_tails (a b c : ℤ) (ha : 5≤a)
    (hb : 2*(a+1)^2≤b) (hc : 2*(a+1)^2≤c) : equationThree a b c<0 := by
  let u:=a-5
  let v:=b-2*(a+1)^2
  let w:=c-2*(a+1)^2
  have hu : 0≤u := by dsimp [u];omega
  have hv : 0≤v := by dsimp [v];omega
  have hw : 0≤w := by dsimp [w];omega
  have he : -equationThree a b c=
      32*u^10 +
      1920*u^9 +
      32*u^8*v +
      32*u^8*w +
      51888*u^8 +
      1540*u^7*v +
      1540*u^7*w +
      831740*u^7 +
      8*u^6*v^2 +
      32*u^6*v*w +
      32460*u^6*v +
      8*u^6*w^2 +
      32460*u^6*w +
      8757212*u^6 +
      290*u^5*v^2 +
      1160*u^5*v*w +
      391366*u^5*v +
      290*u^5*w^2 +
      391366*u^5*w +
      63278784*u^5 +
      8*u^4*v^2*w +
      4386*u^4*v^2 +
      8*u^4*v*w^2 +
      17540*u^4*v*w +
      2951880*u^4*v +
      4386*u^4*w^2 +
      2951880*u^4*w +
      317785550*u^4 +
      195*u^3*v^2*w +
      35413*u^3*v^2 +
      195*u^3*v*w^2 +
      141573*u^3*v*w +
      14260735*u^3*v +
      35413*u^3*w^2 +
      14260735*u^3*w +
      1095136066*u^3 +
      2*u^2*v^2*w^2 +
      1783*u^2*v^2*w +
      160936*u^2*v^2 +
      1783*u^2*v*w^2 +
      643169*u^2*v*w +
      43087357*u^2*v +
      160936*u^2*w^2 +
      43087357*u^2*w +
      2478264030*u^2 +
      25*u*v^2*w^2 +
      7242*u*v^2*w +
      390177*u*v^2 +
      7242*u*v*w^2 +
      1558885*u*v*w +
      74427279*u*v +
      390177*u*w^2 +
      74427279*u*w +
      3325172850*u +
      77*v^2*w^2 +
      11016*v^2*w +
      394110*v^2 +
      11016*v*w^2 +
      1574337*v*w +
      56263095*v +
      394110*w^2 +
      56263095*w +
      2008503000 := by
    dsimp [u,v,w,equationThree,threeA,threeB,threeC]
    ring
  have hp : 0< -equationThree a b c := by rw [he];positivity
  omega

/-- Full, symmetric finite root-three candidates; no tail is discarded. -/
def positiveThreePairs (a : ℤ) : Finset (ℤ × ℤ) :=
  let forward := (Finset.Ioo 0 (2*(a+1)^2)).biUnion
    (fun b => (positiveThreeFiber a b).image (fun c => (b,c)))
  forward ∪ forward.image Prod.swap

theorem mem_positiveThreePairs (a b c : ℤ) (ha : 5≤a) :
    (b,c)∈positiveThreePairs a ↔ 0<b ∧ 0<c ∧ equationThree a b c=0 := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨b',hb',hh⟩:=Finset.mem_biUnion.mp h
      obtain ⟨c',hc',he⟩:=Finset.mem_image.mp hh
      have hb : 0<b' := (Finset.mem_Ioo.mp hb').1
      cases he
      exact ⟨hb,(Finset.mem_filter.mp hc').2,
        (mem_three_fiber a b c (by omega) hb (Finset.mem_filter.mp hc').2).mp hc'⟩
    · obtain ⟨q,hq,he⟩:=Finset.mem_image.mp h
      obtain ⟨b',hb',hh⟩:=Finset.mem_biUnion.mp hq
      obtain ⟨c',hc',he'⟩:=Finset.mem_image.mp hh
      cases he'
      change (c',b')=(b,c) at he
      cases he
      have hc : 0<c := (Finset.mem_Ioo.mp hb').1
      have hb : 0<b := (Finset.mem_filter.mp hc').2
      have hz : equationThree a b c=0 := by
        rw [symmetric_three]
        exact (mem_three_fiber a c b (by omega) hc hb).mp hc'
      exact ⟨hb,hc,hz⟩
  · rintro ⟨hb,hc,hz⟩
    have hs : b<2*(a+1)^2 ∨ c<2*(a+1)^2 := by
      by_contra hh
      push_neg at hh
      exact (three_negative_large_tails a b c ha hh.1 hh.2).ne hz
    apply Finset.mem_union.mpr
    rcases hs with hs | hs
    · apply Or.inl
      exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_Ioo.mpr ⟨hb,hs⟩,
        Finset.mem_image.mpr ⟨c,(mem_three_fiber a b c (by omega) hb hc).mpr hz,rfl⟩⟩
    · apply Or.inr
      exact Finset.mem_image.mpr ⟨(c,b),Finset.mem_biUnion.mpr
        ⟨c,Finset.mem_Ioo.mpr ⟨hc,hs⟩,Finset.mem_image.mpr
          ⟨b,(mem_three_fiber a c b (by omega) hc hb).mpr
            (by rwa [symmetric_three]),rfl⟩⟩,rfl⟩

def graphTailCandidates (a : ℕ) : Finset (ℕ × ℕ) :=
  ((positivePairs (a:ℤ)) ∪ positiveThreePairs (a:ℤ)).image
    (fun q => (q.1.toNat,q.2.toNat))

/-- Actual integrality imposes membership in the entire finite exponent set,
uniformly in every choice of four distinct primes. This is only necessary. -/
theorem actual_integral_mem (p : Fin 4 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 5≤a) (hb : a≤b) (hc : a≤c)
    (H : ActualLaplacianIntegral (modulus p (pairExponents a b c))) :
    (b,c)∈graphTailCandidates a := by
  apply Finset.mem_image.mpr
  refine ⟨((b:ℤ),(c:ℤ)),?_,by simp⟩
  apply Finset.mem_union.mpr
  rcases PairLowArithmetic.actual_low_root p hp hinj a b c ha hb hc H with h2 | h3
  · exact Or.inl ((mem_positivePairs (a:ℤ) b c (by exact_mod_cast (show 2≤a by omega))).mpr
      ⟨by exact_mod_cast (show 0<b by omega),by exact_mod_cast (show 0<c by omega),by rwa [determinant] at h2⟩)
  · exact Or.inr ((mem_positiveThreePairs (a:ℤ) b c (by exact_mod_cast ha)).mpr
      ⟨by exact_mod_cast (show 0<b by omega),by exact_mod_cast (show 0<c by omega),by rwa [determinant_three] at h3⟩)

/-- Original fixed-repeated-minimum graph finiteness. Both tails and all
four prime choices remain free; no bound on the repeated minimum is asserted. -/
theorem actual_integral_tail_finiteness (a : ℕ) (ha : 5≤a) :
    {q : ℕ × ℕ | a≤q.1 ∧ a≤q.2 ∧ ∃ p : Fin 4 → ℕ,
      (∀ i, Nat.Prime (p i)) ∧ Function.Injective p ∧
      ActualLaplacianIntegral (modulus p (pairExponents a q.1 q.2))}.Finite := by
  apply (graphTailCandidates a).finite_toSet.subset
  rintro ⟨b,c⟩ ⟨hb,hc,p,hp,hinj,H⟩
  exact actual_integral_mem p hp hinj a b c ha hb hc H


/-- The actual quartic polynomial defining the full rational double cover. -/
def quarticPolynomial (a : ℚ) : Polynomial ℚ := quartic (Polynomial.C a) X

private def bezoutU (a : ℚ) : Polynomial ℚ :=
    Polynomial.C (8192*a^21 + 38912*a^20 + 46080*a^19 - 71680*a^18 - 233984*a^17 - 128768*a^16 + 253568*a^15 + 415200*a^14 + 81808*a^13 - 316288*a^12 - 282848*a^11 + 6152*a^10 + 135908*a^9 + 70104*a^8 - 2010*a^7 - 9238*a^6 - 4244*a^5 - 4656*a^4 - 1920*a^3 - 224*a^2 - 64*a)+
    Polynomial.C (12288*a^20 + 65536*a^19 + 116736*a^18 - 13312*a^17 - 360704*a^16 - 511744*a^15 - 55552*a^14 + 654720*a^13 + 781360*a^12 + 154320*a^11 - 465568*a^10 - 496048*a^9 - 152636*a^8 + 88520*a^7 + 108448*a^6 + 56236*a^5 + 18072*a^4 + 1376*a^3 - 1344*a^2 - 576*a - 128)*X+
    Polynomial.C (4096*a^19 + 20480*a^18 + 29696*a^17 - 32768*a^16 - 165632*a^15 - 191104*a^14 + 49728*a^13 + 382080*a^12 + 413504*a^11 + 59680*a^10 - 307856*a^9 - 353296*a^8 - 145968*a^7 + 42096*a^6 + 91376*a^5 + 62320*a^4 + 27712*a^3 + 8960*a^2 + 2048*a + 256)*X^2

private def bezoutV (a : ℚ) : Polynomial ℚ :=
    Polynomial.C (-2048*a^21 - 5632*a^20 + 768*a^19 + 21632*a^18 + 21888*a^17 - 21664*a^16 - 51152*a^15 - 12232*a^14 + 41160*a^13 + 34696*a^12 - 6948*a^11 - 18582*a^10 - 4310*a^9 + 1179*a^8 - 584*a^7 + 389*a^6 + 1000*a^5 + 360*a^4 + 64*a^3 + 16*a^2)+
    Polynomial.C (-4096*a^21 - 20480*a^20 - 26624*a^19 + 35584*a^18 + 131968*a^17 + 86976*a^16 - 132288*a^15 - 255376*a^14 - 85072*a^13 + 173808*a^12 + 200744*a^11 + 34572*a^10 - 79772*a^9 - 65594*a^8 - 14419*a^7 + 5477*a^6 + 6912*a^5 + 5232*a^4 + 2016*a^3 + 368*a^2 + 64*a)*X+
    Polynomial.C (-4096*a^20 - 22016*a^19 - 39424*a^18 + 4736*a^17 + 123328*a^16 + 173952*a^15 + 14832*a^14 - 230096*a^13 - 268056*a^12 - 42920*a^11 + 172620*a^10 + 173616*a^9 + 44284*a^8 - 40240*a^7 - 40824*a^6 - 17700*a^5 - 3916*a^4 + 672*a^3 + 864*a^2 + 320*a + 64)*X^2+
    Polynomial.C (-1024*a^19 - 5120*a^18 - 7424*a^17 + 8192*a^16 + 41408*a^15 + 47776*a^14 - 12432*a^13 - 95520*a^12 - 103376*a^11 - 14920*a^10 + 76964*a^9 + 88324*a^8 + 36492*a^7 - 10524*a^6 - 22844*a^5 - 15580*a^4 - 6928*a^3 - 2240*a^2 - 512*a - 64)*X^3

def discriminantFactor (a : ℚ) : ℚ :=
  64*a^9+128*a^8+48*a^7-192*a^6-196*a^5-44*a^4+119*a^3+58*a^2+4*a+8

private def bezoutDenominator (a : ℚ) : ℚ :=
  64*a^5*(a-1)^7*(a+1)^2*(2*a+1)^3*(a^2+a+1)*discriminantFactor a

theorem discriminant_factor_positive (a : ℚ) (ha : 2≤a) : 0<discriminantFactor a := by
  let v:=a-2
  have hv : 0≤v := by dsimp [v];linarith
  have he : discriminantFactor a=
      64*v^9+1280*v^8+11312*v^7+57824*v^6+187900*v^5+
      401324*v^4+561527*v^3+494500*v^2+247744*v+53616 := by
    dsimp [v,discriminantFactor]
    ring
  rw [he]
  positivity

private theorem bezout_identity (a : ℚ) :
    bezoutU a*quarticPolynomial a+bezoutV a*(quarticPolynomial a).derivative=
      Polynomial.C (bezoutDenominator a) := by
  have hq : quarticPolynomial a=
      Polynomial.C (4*(a-1)*(a+1)*(a^2-a-1)*(a^2+a+1))*X^4+
      Polynomial.C (4*(a-1)^2*(a^2+a+1)*(4*a^3+6*a^2-a-2))*X^3+
      Polynomial.C ((a-1)^2*(16*a^6+40*a^5+8*a^4-20*a^3-31*a^2-8*a+4))*X^2+
      Polynomial.C (2*a*(a-1)^3*(2*a+1)*(4*a^3+2*a^2-a-2))*X+
      Polynomial.C (a^2*(a-1)^4*(2*a+1)^2) := by
    apply Polynomial.funext
    intro b
    simp [quarticPolynomial,quartic,A,B,C₀]
    ring
  rw [hq]
  simp only [derivative_add,derivative_mul,derivative_C,derivative_pow,
    derivative_X,zero_mul,zero_add,mul_one]
  apply Polynomial.funext
  intro b
  simp [bezoutU,bezoutV,bezoutDenominator,discriminantFactor]
  ring

/-- The complete quartic is separable at every original a>=2, not just
at the supplied three determinant controls. Bezout is kernel checked. -/
theorem quartic_separable (a : ℚ) (ha : 2≤a) : (quarticPolynomial a).Separable := by
  have hH:=discriminant_factor_positive a ha
  have ha0 : 0<a := by linarith
  have ha1 : 0<a-1 := by linarith
  have hD : bezoutDenominator a≠0 := by
    apply ne_of_gt
    dsimp [bezoutDenominator]
    positivity
  apply (Polynomial.separable_def _).mpr
  refine ⟨Polynomial.C ((bezoutDenominator a)⁻¹)*bezoutU a,
    Polynomial.C ((bezoutDenominator a)⁻¹)*bezoutV a,?_⟩
  calc
    _ = Polynomial.C ((bezoutDenominator a)⁻¹)*
        (bezoutU a*quarticPolynomial a+bezoutV a*(quarticPolynomial a).derivative) := by ring
    _ = 1 := by rw [bezout_identity,←Polynomial.C_mul,inv_mul_cancel₀ hD];simp

/-- Squarefreeness holds throughout the entire original repeated-minimum domain. -/
theorem quartic_squarefree (a : ℚ) (ha : 2≤a) : Squarefree (quarticPolynomial a) :=
  (quartic_separable a ha).squarefree

/-- The same complete quartic stays separable after every field extension. -/
theorem quartic_geometrically_separable {F : Type*} [Field F] [Algebra ℚ F]
    (a : ℚ) (ha : 2≤a) :
    ((quarticPolynomial a).map (algebraMap ℚ F)).Separable :=
  (quartic_separable a ha).map

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.RootTwoTailCurve
