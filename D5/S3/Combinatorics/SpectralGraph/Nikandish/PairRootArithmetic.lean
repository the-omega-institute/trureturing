/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairRootArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairRootArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact integer-root division and prime-unit arithmetic of the full repeated-pair operator. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic

/-! Source: PR9 four-prime-low-root-divisibility and
four-prime-root-valuation, revision 6d491f77b35dec808fc777b69939c56cdae5dc02.
The root hypothesis is the determinant of the actual full tensor K.
Zero tail specializations below are polynomial identities only; every
graph consumer retains positive exponents. Valuations use natAbs, also
when the integer offset a+1-s is negative. -/
set_option autoImplicit false
noncomputable section
open Matrix
namespace D5.S3.Combinatorics.SpectralGraph.PairRootArithmetic
open PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants

def rootQuotient {R : Type*} [CommRing R] (h b c s : R) : R :=
  h^3*(4*b*c+2*b+2*c+2) +
  h^2*(-b^2*c*s+4*b^2*c-b^2*s+2*b^2-b*c^2*s+4*b*c^2+
    9*b*c*s+2*b*s+b-c^2*s+2*c^2+2*c*s+c+s-1) +
  h*(-2*b^2*c^2*s+4*b^2*c^2-2*b^2*c*s^2+8*b^2*c*s-2*b^2*c-
    2*b^2*s^2+4*b^2*s-b^2-2*b*c^2*s^2+8*b*c^2*s-2*b*c^2+
    7*b*c*s^2-4*b*c*s+b*c+b*s-b-2*c^2*s^2+4*c^2*s-c^2+c*s-c) +
  (-4*b^2*c^2*s^2+9*b^2*c^2*s-4*b^2*c^2-b^2*c*s^3+
    4*b^2*c*s^2-2*b^2*c*s-b^2*s^3+2*b^2*s^2-b^2*s-
    b*c^2*s^3+4*b*c^2*s^2-2*b*c^2*s+2*b*c*s^3-
    4*b*c*s^2+3*b*c*s-b*c-c^2*s^3+2*c^2*s^2-c^2*s)

theorem root_division {R : Type*} [CommRing R] (a b c s : R) :
    (tensorK a b c-s • 1).det = -(s-1)^2*(2*s-1)*b^2*c^2+
      (a+1-s)*rootQuotient (a+1-s) b c s := by
  rw [det_tensorK_sub_scalar]
  unfold rootQuotient
  ring

theorem quotient_zero_left {R : Type*} [CommRing R] (c s : R) :
    rootQuotient 0 0 c s = -s*(s-1)^2*c^2 := by
  unfold rootQuotient
  ring

theorem quotient_zero_right {R : Type*} [CommRing R] (b s : R) :
    rootQuotient 0 b 0 s = -s*(s-1)^2*b^2 := by
  unfold rootQuotient
  ring

theorem root_divides (a b c s : ℤ)
    (hr : (tensorK a b c-s • 1).det=0) :
    a+1-s ∣ (s-1)^2*(2*s-1)*b^2*c^2 := by
  refine ⟨rootQuotient (a+1-s) b c s,?_⟩
  have hd:=root_division a b c s
  rw [hr] at hd
  linarith

theorem root_offset_ne_zero (a b c s : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hr : (tensorK a b c-s • 1).det=0) : a+1-s≠0 := by
  intro hz
  have hs : s=a+1 := by linarith
  have hd:=root_division a b c s
  rw [hr,hz,zero_mul,add_zero,hs] at hd
  have hf : 0 < 2*(a+1)-1 := by omega
  have hp : 0<a^2*(2*(a+1)-1)*b^2*c^2 := by positivity
  have he : -(a+1-1)^2*(2*(a+1)-1)*b^2*c^2 =
      -(a^2*(2*(a+1)-1)*b^2*c^2) := by ring
  rw [he] at hd
  linarith

/-- At a good prime of the root offset, coprime tails make the exact
polynomial quotient a unit. The two zero-tail evaluations are only used
after reduction in the residue field. -/
theorem quotient_prime_unit (a b c s : ℤ) (p : ℕ) [Fact p.Prime]
    (hcop : IsCoprime b c) (hh : (p:ℤ)∣a+1-s)
    (hgood : ¬(p:ℤ)∣s*(s-1)*(2*s-1))
    (hr : (tensorK a b c-s • 1).det=0) :
    ¬(p:ℤ)∣rootQuotient (a+1-s) b c s := by
  have hh0 : ((a:ZMod p)+1-s)=0 := by
    have hz:=(ZMod.intCast_zmod_eq_zero_iff_dvd (a+1-s) p).mpr hh
    exact_mod_cast hz
  have hg : (s:ZMod p)*((s:ZMod p)-1)*(2*(s:ZMod p)-1)≠0 := by
    have hz:=(ZMod.intCast_zmod_eq_zero_iff_dvd (s*(s-1)*(2*s-1)) p).not.mpr hgood
    exact_mod_cast hz
  have hs0 : (s:ZMod p)≠0 := by
    intro hz; apply hg; simp [hz]
  have hs1 : (s:ZMod p)-1≠0 := by
    intro hz; apply hg; simp [hz]
  have hs2 : 2*(s:ZMod p)-1≠0 := by
    intro hz; apply hg; simp [hz]
  have hconst : ((s:ZMod p)-1)^2*(2*(s:ZMod p)-1)≠0 :=
    mul_ne_zero (pow_ne_zero _ hs1) hs2
  have hroot := congrArg (fun z:ℤ => (z:ZMod p)) (root_division a b c s)
  rw [hr] at hroot
  push_cast at hroot
  rw [hh0] at hroot
  have hbc : (b:ZMod p)=0 ∨ (c:ZMod p)=0 := by
    have hz : (((s:ZMod p)-1)^2*(2*(s:ZMod p)-1))*
        (b:ZMod p)^2*(c:ZMod p)^2=0 := by linear_combination hroot
    rcases mul_eq_zero.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hz
      · exact (hconst hz).elim
      · exact Or.inl (eq_zero_of_pow_eq_zero hz)
    · exact Or.inr (eq_zero_of_pow_eq_zero hz)
  have hnotboth : ¬((b:ZMod p)=0 ∧ (c:ZMod p)=0) := by
    rintro ⟨hb,hc⟩
    obtain ⟨u,v,hbez⟩:=hcop
    have hz:=congrArg (fun z:ℤ => (z:ZMod p)) hbez
    push_cast at hz
    simp [hb,hc] at hz
  intro hq
  have hq0:=(ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hq
  have hQ : rootQuotient ((a:ZMod p)+1-s) b c s=0 := by
    simpa only [rootQuotient,Int.cast_add,Int.cast_sub,Int.cast_mul,
      Int.cast_pow,Int.cast_ofNat,Int.cast_neg,Int.cast_one] using hq0
  rw [hh0] at hQ
  rcases hbc with hb | hc
  · have hc : (c:ZMod p)≠0 := fun hc => hnotboth ⟨hb,hc⟩
    rw [hb,quotient_zero_left] at hQ
    exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hs0)
      (pow_ne_zero _ hs1)) (pow_ne_zero _ hc)) hQ
  · have hb : (b:ZMod p)≠0 := fun hb => hnotboth ⟨hb,hc⟩
    rw [hc,quotient_zero_right] at hQ
    exact (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hs0)
      (pow_ne_zero _ hs1)) (pow_ne_zero _ hb)) hQ

/-- Full root-valuation theorem: all positive integer parameters, every
integer root s>=2, every good prime of the possibly negative offset. -/
theorem root_valuation (a b c s : ℤ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hs : 2≤s) (hcop : IsCoprime b c) (p : ℕ) [Fact p.Prime]
    (hh : (p:ℤ)∣a+1-s) (hgood : ¬(p:ℤ)∣s*(s-1)*(2*s-1))
    (hr : (tensorK a b c-s • 1).det=0) :
    a+1-s≠0 ∧ padicValInt p (a+1-s)=2*padicValInt p (b*c) := by
  have hn:=root_offset_ne_zero a b c s ha hb hc hr
  have hqu:=quotient_prime_unit a b c s p hcop hh hgood hr
  have hqn : rootQuotient (a+1-s) b c s≠0 := by
    intro hz; apply hqu; rw [hz]; exact dvd_zero _
  have hcn : (s-1)^2*(2*s-1)≠0 :=
    mul_ne_zero (pow_ne_zero _ (by omega)) (by omega)
  have hcv : padicValInt p ((s-1)^2*(2*s-1))=0 := by
    apply padicValInt.eq_zero_of_not_dvd
    intro hd
    have hp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
    rcases hp.dvd_mul.mp hd with hd | hd
    · have hd1:=hp.dvd_of_dvd_pow hd
      exact hgood (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd1 _) _)
    · exact hgood (dvd_mul_of_dvd_right hd _)
  have he : (a+1-s)*rootQuotient (a+1-s) b c s=
      ((s-1)^2*(2*s-1))*((b*c)*(b*c)) := by
    have hd:=root_division a b c s
    rw [hr] at hd
    linear_combination -hd
  have hv:=congrArg (padicValInt p) he
  rw [padicValInt.mul hn hqn,padicValInt.eq_zero_of_not_dvd hqu,
    padicValInt.mul hcn (mul_ne_zero (mul_ne_zero hb.ne' hc.ne')
      (mul_ne_zero hb.ne' hc.ne')),hcv,
    padicValInt.mul (mul_ne_zero hb.ne' hc.ne') (mul_ne_zero hb.ne' hc.ne')] at hv
  exact ⟨hn,by omega⟩

end D5.S3.Combinatorics.SpectralGraph.PairRootArithmetic
