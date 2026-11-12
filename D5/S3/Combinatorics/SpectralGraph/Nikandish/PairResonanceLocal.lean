/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairResonanceLocal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PairResonanceLocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full rational-integral discriminant obstruction at every good resonant prime. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairResonanceAlgebra
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairSharedRoot
import Mathlib.Data.ZMod.Basic

/-! Source: complete four-prime-resonance-discriminant, supplied PR9
6d491f77b35dec808fc777b69939c56cdae5dc02. The integer normalization
handles all prime orders, including negative offsets and b+h=0. No
coprimality or tail ordering is assumed. Passing this necessary local
test does not assert existence of a root or integral graph spectrum. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace D5.S3.Combinatorics.SpectralGraph.PairResonanceLocal
open PairedIdealIntersectionObstructions PairResonanceAlgebra IntegerPrimeOrder

theorem square_power_dvd (p k : ℕ) [Fact p.Prime] (x : ℤ)
    (hx : (p : ℤ)^(2*k) ∣ x^2) : (p : ℤ)^k ∣ x := by
  by_cases hz : x=0
  · simp [hz]
  have hv := (padicValInt_dvd_iff (2*k) (x^2)).mp hx
  have hsq : x^2 ≠ 0 := pow_ne_zero _ hz
  have hv' := hv.resolve_left hsq
  rw [pow_two,padicValInt.mul hz hz] at hv'
  apply (padicValInt_dvd_iff k x).mpr
  exact Or.inr (by omega)

/-- Reduction of a genuinely normalized square over any field. -/
theorem normalized_square {K : Type*} [Field K] (s H U W : K)
    (hH : H ≠ 0) (hs : s-1 ≠ 0)
    (hw : W^2=(s-1)^2*((2*s-1)^2*H^2*U^2+
      2*s^2*(2*s-1)^2*H^4*U+s^4*H^6)) :
    ∃ v : K, v^2=localPolynomial s (U/H^2) := by
  refine ⟨W/((s-1)*H^3),?_⟩
  unfold localPolynomial
  field_simp
  linear_combination hw

/-- Every square discriminant at a normalized integer root reduces to a
square or zero. H is a unit, whereas the prime-power scale P vanishes. -/
theorem scaled_root_square (p e : ℕ) [hp : Fact p.Prime]
    (H U c s : ℤ) (he : 1 ≤ e) (hH : ¬(p : ℤ) ∣ H)
    (hs : ¬(p : ℤ) ∣ s-1)
    (hr : (tensorK (s-1+(p : ℤ)^e*H)
      (-(p : ℤ)^e*H+((p : ℤ)^e)^2*U) c-s • 1).det=0) :
    ∃ v : ZMod p, v^2=localPolynomial (s : ZMod p)
      ((U : ZMod p)/(H : ZMod p)^2) := by
  let P : ℤ := (p : ℤ)^e
  let W : ℤ := 2*tailA (s-1+P*H) (-P*H+P^2*U) s*c+
    tailB (s-1+P*H) (-P*H+P^2*U) s
  have hd : discriminant (s-1+P*H) (-P*H+P^2*U) s=W^2 :=
    root_discriminant _ _ c s hr
  have hdiv : (p : ℤ)^(2*(3*e)) ∣ W^2 := by
    rw [←hd,normalized_expansion]
    have hpow : (p : ℤ)^(2*(3*e))=P^6 := by dsimp [P]; rw [←pow_mul]; congr 1 <;> omega
    rw [hpow]
    exact dvd_mul_right _ _
  obtain ⟨w,hw⟩ := square_power_dvd p (3*e) W hdiv
  have hwp : W=P^3*w := by
    have hpow : (p : ℤ)^(3*e)=P^3 := by
      dsimp [P]
      rw [←pow_mul]
      congr 1
      omega
    exact hw.trans (congrArg (fun x : ℤ => x*w) hpow)
  have hn : P ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.out.ne_zero)
  have heq : w^2=(s-1)^2*((2*s-1)^2*H^2*U^2+
      2*s^2*(2*s-1)^2*H^4*U+s^4*H^6)+P*normalizedError P H U s := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hn)
    calc
      P^6*w^2 = (P^3*w)^2 := by ring
      _ = W^2 := by rw [hwp]
      _ = discriminant (s-1+P*H) (-P*H+P^2*U) s := hd.symm
      _ = _ := normalized_expansion P H U s
  have hP : (P : ZMod p)=0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd P p).mpr
    simpa only [pow_one] using lower_power p 1 e P he (dvd_refl _)
  have hcast := congrArg (fun x : ℤ => (x : ZMod p)) heq
  push_cast at hcast
  rw [hP] at hcast
  simp only [zero_mul,add_zero] at hcast
  have hHu : (H : ZMod p) ≠ 0 := by
    exact fun h => hH ((ZMod.intCast_zmod_eq_zero_iff_dvd H p).mp h)
  have hsu : (s : ZMod p)-1 ≠ 0 := by
    intro h
    apply hs
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (s-1) p).mp
    simpa using h
  exact normalized_square (s : ZMod p) H U w hHu hsu hcast

/-- Unit-denominator representatives certify local integrality of the
rational quotient, including the zero numerator. -/
theorem quotient_integral (p : ℕ) [Fact p.Prime] (U H : ℤ)
    (hH : ¬(p : ℤ) ∣ H) : 0 ≤ padicValRat p ((U : ℚ)/(H : ℚ)^2) := by
  have hn : H ≠ 0 := by intro h; exact hH (h ▸ dvd_zero _)
  by_cases hU : U=0
  · simp [hU]
  rw [padicValRat.div (Int.cast_ne_zero.mpr hU) (pow_ne_zero _ (Int.cast_ne_zero.mpr hn)),
    padicValRat.pow,padicValRat.of_int,padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd hH]
  simp

/-- The full original resonant root theorem. The explicit zero disjunct
implements the usual infinite valuation of zero; finite padicValInt uses
zero there. The quotient witnesses specify its actual residue. -/
theorem root_obstruction (a b c s : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (p : ℕ) [Fact p.Prime] (hh : (p : ℤ) ∣ a+1-s)
    (hgood : ¬(p : ℤ) ∣ s*(s-1)*(2*s-1))
    (horder : b+(a+1-s)=0 ∨
      2*padicValInt p (a+1-s) ≤ padicValInt p (b+(a+1-s)))
    (hr : (tensorK a b c-s • 1).det=0) :
    let h := a+1-s
    let e := padicValInt p h
    0 ≤ padicValRat p (((b+h : ℤ) : ℚ)/(h : ℚ)^2) ∧
      ∃ H U : ℤ, h=(p : ℤ)^e*H ∧ b+h=(p : ℤ)^(2*e)*U ∧
        ¬(p : ℤ) ∣ H ∧ (((b+h : ℤ) : ℚ)/(h : ℚ)^2)=(U : ℚ)/(H : ℚ)^2 ∧
        ∃ v : ZMod p, v^2=localPolynomial (s : ZMod p)
          ((U : ZMod p)/(H : ZMod p)^2) := by
  dsimp only
  let h := a+1-s
  let e := padicValInt p h
  have hn : h ≠ 0 := PairRootArithmetic.root_offset_ne_zero a b c s ha hb hc hr
  have he : 1 ≤ e := by
    have hd : (p : ℤ)^1 ∣ h := by simpa [h] using hh
    have ht := (padicValInt_dvd_iff 1 h).mp hd
    omega
  obtain ⟨H,hH,hHu⟩ := unit_decomposition p e h (exact_valuation p h hn)
  have hd : (p : ℤ)^(2*e) ∣ b+h := by
    apply (padicValInt_dvd_iff _ _).mpr
    simpa [e,h] using horder
  obtain ⟨U,hU⟩ := hd
  have hP : ((p : ℤ)^e : ℤ) ≠ 0 := by
    exact pow_ne_zero _ (Int.natCast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hHn : H ≠ 0 := by intro hz; simp [hz] at hH; exact hn hH
  have hquot : ((b+h : ℤ) : ℚ)/(h : ℚ)^2=(U : ℚ)/(H : ℚ)^2 := by
    rw [hU,hH]
    push_cast
    rw [pow_mul]
    have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    field_simp [hpq,Int.cast_ne_zero.mpr hHn]
    <;> ring
  have hb' : b=-(p : ℤ)^e*H+((p : ℤ)^e)^2*U := by
    rw [←pow_mul]
    have heq : e*2=2*e := by omega
    rw [heq]
    linarith
  have ha' : a=s-1+(p : ℤ)^e*H := by dsimp [h] at hH; linarith
  have hs : ¬(p : ℤ) ∣ s-1 := by
    intro hd
    exact hgood (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)
  have hsquare := scaled_root_square p e H U c s he hHu hs (by rwa [←ha',←hb'])
  refine ⟨?_,H,U,hH,hU,hHu,hquot,hsquare⟩
  change 0 ≤ padicValRat p (((b+h : ℤ) : ℚ)/(h : ℚ)^2)
  rw [hquot]
  exact quotient_integral p U H hHu

end D5.S3.Combinatorics.SpectralGraph.PairResonanceLocal
