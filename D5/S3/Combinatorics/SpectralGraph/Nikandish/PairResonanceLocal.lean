/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/PairResonanceLocal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/PairResonanceLocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Resonant determinant algebra and full rational-integral square obstruction. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants
import D5.S3.Combinatorics.SpectralGraph.Nikandish.PairSharedRoot
import Mathlib.Data.ZMod.Basic

/-! Source: four-prime-resonance-discriminant, supplied PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02, full symbolic certificate.
The 124-term error is retained without truncation. Every identity is
proved in the kernel over an arbitrary commutative ring, before imposing
positivity or prime conditions. Algebraic zero parameters are not graph
exponent examples. The necessary local test is not a root criterion. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace D5.S3.Combinatorics.SpectralGraph.PairResonanceAlgebra
open PairedIdealIntersectionObstructions
variable {R : Type*} [CommRing R]

def tailA (a b s : R) : R :=
  -1*a^3*b*s +
    4*a^3*b -
    1*a^3*s +
    2*a^3 -
    2*a^2*b^2*s +
    4*a^2*b^2 +
    a^2*b*s^2 -
    7*a^2*b*s +
    10*a^2*b +
    a^2*s^2 -
    5*a^2*s +
    5*a^2 -
    3*a*b^2*s +
    4*a*b^2 +
    2*a*b*s^2 -
    9*a*b*s +
    8*a*b +
    2*a*s^2 -
    6*a*s +
    4*a -
    1*b^2*s +
    b^2 +
    b*s^2 -
    3*b*s +
    2*b +
    s^2 -
    2*s +
    1

def tailB (a b s : R) : R :=
  4*a^4*b +
    2*a^4 -
    1*a^3*b^2*s +
    4*a^3*b^2 -
    7*a^3*b*s +
    16*a^3*b -
    6*a^3*s +
    9*a^3 +
    a^2*b^2*s^2 -
    7*a^2*b^2*s +
    10*a^2*b^2 +
    4*a^2*b*s^2 -
    25*a^2*b*s +
    25*a^2*b +
    6*a^2*s^2 -
    20*a^2*s +
    14*a^2 +
    2*a*b^2*s^2 -
    9*a*b^2*s +
    8*a*b^2 -
    1*a*b*s^3 +
    12*a*b*s^2 -
    28*a*b*s +
    17*a*b -
    2*a*s^3 +
    13*a*s^2 -
    20*a*s +
    9*a +
    b^2*s^2 -
    3*b^2*s +
    2*b^2 -
    1*b*s^3 +
    6*b*s^2 -
    9*b*s +
    4*b -
    2*s^3 +
    6*s^2 -
    6*s +
    2

def tailC (a b s : R) : R :=
  2*a^4*b +
    2*a^4 -
    1*a^3*b^2*s +
    2*a^3*b^2 -
    6*a^3*b*s +
    9*a^3*b -
    7*a^3*s +
    7*a^3 +
    a^2*b^2*s^2 -
    5*a^2*b^2*s +
    5*a^2*b^2 +
    6*a^2*b*s^2 -
    20*a^2*b*s +
    14*a^2*b +
    9*a^2*s^2 -
    18*a^2*s +
    9*a^2 +
    2*a*b^2*s^2 -
    6*a*b^2*s +
    4*a*b^2 -
    2*a*b*s^3 +
    13*a*b*s^2 -
    20*a*b*s +
    9*a*b -
    5*a*s^3 +
    15*a*s^2 -
    15*a*s +
    5*a +
    b^2*s^2 -
    2*b^2*s +
    b^2 -
    2*b*s^3 +
    6*b*s^2 -
    6*b*s +
    2*b +
    s^4 -
    4*s^3 +
    6*s^2 -
    4*s +
    1

def discriminant (a b s : R) : R := (tailB a b s)^2-4*tailA a b s*tailC a b s

def localPolynomial (s z : R) : R := (2*s-1)^2*z^2+2*s^2*(2*s-1)^2*z+s^4

def errorPolynomial (h z s : R) : R :=
  h^7*z^4*s^2 -
    8*h^7*z^4*s +
    16*h^7*z^4 +
    4*h^6*z^4*s^3 -
    40*h^6*z^4*s^2 +
    100*h^6*z^4*s -
    48*h^6*z^4 -
    4*h^6*z^3*s^2 +
    24*h^6*z^3*s -
    32*h^6*z^3 +
    6*h^5*z^4*s^4 -
    80*h^5*z^4*s^3 +
    240*h^5*z^4*s^2 -
    208*h^5*z^4*s +
    52*h^5*z^4 -
    16*h^5*z^3*s^3 +
    122*h^5*z^3*s^2 -
    224*h^5*z^3*s +
    112*h^5*z^3 +
    6*h^5*z^2*s^2 -
    24*h^5*z^2*s +
    16*h^5*z^2 +
    4*h^4*z^4*s^5 -
    80*h^4*z^4*s^4 +
    280*h^4*z^4*s^3 -
    336*h^4*z^4*s^2 +
    160*h^4*z^4*s -
    24*h^4*z^4 -
    24*h^4*z^3*s^4 +
    246*h^4*z^3*s^3 -
    576*h^4*z^3*s^2 +
    510*h^4*z^3*s -
    152*h^4*z^3 +
    24*h^4*z^2*s^3 -
    126*h^4*z^2*s^2 +
    148*h^4*z^2*s -
    64*h^4*z^2 -
    4*h^4*z*s^2 +
    8*h^4*z*s +
    h^3*z^4*s^6 -
    40*h^3*z^4*s^5 +
    160*h^3*z^4*s^4 -
    240*h^3*z^4*s^3 +
    164*h^3*z^4*s^2 -
    48*h^3*z^4*s +
    4*h^3*z^4 -
    16*h^3*z^3*s^5 +
    246*h^3*z^3*s^4 -
    704*h^3*z^3*s^3 +
    858*h^3*z^3*s^2 -
    482*h^3*z^3*s +
    100*h^3*z^3 +
    36*h^3*z^2*s^4 -
    258*h^3*z^2*s^3 +
    433*h^3*z^2*s^2 -
    328*h^3*z^2*s +
    104*h^3*z^2 -
    16*h^3*z*s^3 +
    46*h^3*z*s^2 -
    24*h^3*z*s +
    h^3*s^2 -
    8*h^2*z^4*s^6 +
    36*h^2*z^4*s^5 -
    64*h^2*z^4*s^4 +
    56*h^2*z^4*s^3 -
    24*h^2*z^4*s^2 +
    4*h^2*z^4*s -
    4*h^2*z^3*s^6 +
    122*h^2*z^3*s^5 -
    416*h^2*z^3*s^4 +
    634*h^2*z^3*s^3 -
    508*h^2*z^3*s^2 +
    204*h^2*z^3*s -
    32*h^2*z^3 +
    24*h^2*z^2*s^5 -
    258*h^2*z^2*s^4 +
    570*h^2*z^2*s^3 -
    600*h^2*z^2*s^2 +
    350*h^2*z^2*s -
    88*h^2*z^2 -
    24*h^2*z*s^4 +
    98*h^2*z*s^3 -
    98*h^2*z*s^2 +
    26*h^2*z*s +
    4*h^2*s^3 -
    2*h^2*s^2 +
    24*h*z^3*s^6 -
    96*h*z^3*s^5 +
    174*h*z^3*s^4 -
    178*h*z^3*s^3 +
    104*h*z^3*s^2 -
    32*h*z^3*s +
    4*h*z^3 +
    6*h*z^2*s^6 -
    126*h*z^2*s^5 +
    353*h*z^2*s^4 -
    472*h*z^2*s^3 +
    392*h*z^2*s^2 -
    194*h*z^2*s +
    41*h*z^2 -
    16*h*z*s^5 +
    98*h*z*s^4 -
    148*h*z*s^3 +
    78*h*z*s^2 -
    12*h*z*s +
    6*h*s^4 -
    6*h*s^3 +
    h*s^2 -
    24*z^2*s^6 +
    84*z^2*s^5 -
    136*z^2*s^4 +
    150*z^2*s^3 -
    118*z^2*s^2 +
    54*z^2*s -
    10*z^2 -
    4*z*s^6 +
    46*z*s^5 -
    98*z*s^4 +
    78*z*s^3 -
    24*z*s^2 +
    2*z*s +
    4*s^5 -
    6*s^4 +
    2*s^3

def normalizedError (P H U s : R) : R :=
  P^7*H^6*U^4*s^2 -
    8*P^7*H^6*U^4*s +
    16*P^7*H^6*U^4 -
    4*P^6*H^7*U^3*s^2 +
    24*P^6*H^7*U^3*s -
    32*P^6*H^7*U^3 +
    4*P^6*H^5*U^4*s^3 -
    40*P^6*H^5*U^4*s^2 +
    100*P^6*H^5*U^4*s -
    48*P^6*H^5*U^4 +
    6*P^5*H^8*U^2*s^2 -
    24*P^5*H^8*U^2*s +
    16*P^5*H^8*U^2 -
    16*P^5*H^6*U^3*s^3 +
    122*P^5*H^6*U^3*s^2 -
    224*P^5*H^6*U^3*s +
    112*P^5*H^6*U^3 +
    6*P^5*H^4*U^4*s^4 -
    80*P^5*H^4*U^4*s^3 +
    240*P^5*H^4*U^4*s^2 -
    208*P^5*H^4*U^4*s +
    52*P^5*H^4*U^4 -
    4*P^4*H^9*U*s^2 +
    8*P^4*H^9*U*s +
    24*P^4*H^7*U^2*s^3 -
    126*P^4*H^7*U^2*s^2 +
    148*P^4*H^7*U^2*s -
    64*P^4*H^7*U^2 -
    24*P^4*H^5*U^3*s^4 +
    246*P^4*H^5*U^3*s^3 -
    576*P^4*H^5*U^3*s^2 +
    510*P^4*H^5*U^3*s -
    152*P^4*H^5*U^3 +
    4*P^4*H^3*U^4*s^5 -
    80*P^4*H^3*U^4*s^4 +
    280*P^4*H^3*U^4*s^3 -
    336*P^4*H^3*U^4*s^2 +
    160*P^4*H^3*U^4*s -
    24*P^4*H^3*U^4 +
    P^3*H^10*s^2 -
    16*P^3*H^8*U*s^3 +
    46*P^3*H^8*U*s^2 -
    24*P^3*H^8*U*s +
    36*P^3*H^6*U^2*s^4 -
    258*P^3*H^6*U^2*s^3 +
    433*P^3*H^6*U^2*s^2 -
    328*P^3*H^6*U^2*s +
    104*P^3*H^6*U^2 -
    16*P^3*H^4*U^3*s^5 +
    246*P^3*H^4*U^3*s^4 -
    704*P^3*H^4*U^3*s^3 +
    858*P^3*H^4*U^3*s^2 -
    482*P^3*H^4*U^3*s +
    100*P^3*H^4*U^3 +
    P^3*H^2*U^4*s^6 -
    40*P^3*H^2*U^4*s^5 +
    160*P^3*H^2*U^4*s^4 -
    240*P^3*H^2*U^4*s^3 +
    164*P^3*H^2*U^4*s^2 -
    48*P^3*H^2*U^4*s +
    4*P^3*H^2*U^4 +
    4*P^2*H^9*s^3 -
    2*P^2*H^9*s^2 -
    24*P^2*H^7*U*s^4 +
    98*P^2*H^7*U*s^3 -
    98*P^2*H^7*U*s^2 +
    26*P^2*H^7*U*s +
    24*P^2*H^5*U^2*s^5 -
    258*P^2*H^5*U^2*s^4 +
    570*P^2*H^5*U^2*s^3 -
    600*P^2*H^5*U^2*s^2 +
    350*P^2*H^5*U^2*s -
    88*P^2*H^5*U^2 -
    4*P^2*H^3*U^3*s^6 +
    122*P^2*H^3*U^3*s^5 -
    416*P^2*H^3*U^3*s^4 +
    634*P^2*H^3*U^3*s^3 -
    508*P^2*H^3*U^3*s^2 +
    204*P^2*H^3*U^3*s -
    32*P^2*H^3*U^3 -
    8*P^2*H*U^4*s^6 +
    36*P^2*H*U^4*s^5 -
    64*P^2*H*U^4*s^4 +
    56*P^2*H*U^4*s^3 -
    24*P^2*H*U^4*s^2 +
    4*P^2*H*U^4*s +
    6*P*H^8*s^4 -
    6*P*H^8*s^3 +
    P*H^8*s^2 -
    16*P*H^6*U*s^5 +
    98*P*H^6*U*s^4 -
    148*P*H^6*U*s^3 +
    78*P*H^6*U*s^2 -
    12*P*H^6*U*s +
    6*P*H^4*U^2*s^6 -
    126*P*H^4*U^2*s^5 +
    353*P*H^4*U^2*s^4 -
    472*P*H^4*U^2*s^3 +
    392*P*H^4*U^2*s^2 -
    194*P*H^4*U^2*s +
    41*P*H^4*U^2 +
    24*P*H^2*U^3*s^6 -
    96*P*H^2*U^3*s^5 +
    174*P*H^2*U^3*s^4 -
    178*P*H^2*U^3*s^3 +
    104*P*H^2*U^3*s^2 -
    32*P*H^2*U^3*s +
    4*P*H^2*U^3 +
    4*H^7*s^5 -
    6*H^7*s^4 +
    2*H^7*s^3 -
    4*H^5*U*s^6 +
    46*H^5*U*s^5 -
    98*H^5*U*s^4 +
    78*H^5*U*s^3 -
    24*H^5*U*s^2 +
    2*H^5*U*s -
    24*H^3*U^2*s^6 +
    84*H^3*U^2*s^5 -
    136*H^3*U^2*s^4 +
    150*H^3*U^2*s^3 -
    118*H^3*U^2*s^2 +
    54*H^3*U^2*s -
    10*H^3*U^2

theorem tail_quadratic (a b c s : R) :
    (tensorK a b c-s • 1).det = tailA a b s*c^2+tailB a b s*c+tailC a b s := by
  rw [PairedIdealIntersectionDeterminants.det_tensorK_sub_scalar]
  unfold tailA tailB tailC
  ring

theorem root_discriminant (a b c s : R)
    (hr : (tensorK a b c-s • 1).det=0) :
    discriminant a b s = (2*tailA a b s*c+tailB a b s)^2 := by
  rw [tail_quadratic] at hr
  unfold discriminant
  linear_combination -4*tailA a b s*hr

theorem discriminant_expansion (h z s : R) :
    discriminant (s-1+h) (-h+h^2*z) s =
      h^6*(s-1)^2*localPolynomial s z+h^7*errorPolynomial h z s := by
  unfold discriminant tailA tailB tailC localPolynomial errorPolynomial
  ring

theorem normalized_expansion (P H U s : R) :
    discriminant (s-1+P*H) (-P*H+P^2*U) s = P^6*
      ((s-1)^2*((2*s-1)^2*H^2*U^2+2*s^2*(2*s-1)^2*H^4*U+s^4*H^6)+
        P*normalizedError P H U s) := by
  unfold discriminant tailA tailB tailC normalizedError
  ring

end D5.S3.Combinatorics.SpectralGraph.PairResonanceAlgebra

/-! Source: complete four-prime-resonance-discriminant, supplied PR9
6d491f77b35dec808fc777b69939c56cdae5dc02. The integer normalization
handles all prime orders, including negative offsets and b+h=0. No
coprimality or tail ordering is assumed. Passing this necessary local
test does not assert existence of a root or integral graph spectrum. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
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
  have hHn : H ≠ 0 := by
    intro hz
    exact hH (hz ▸ dvd_zero _)
  have hHq : (H : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hHn
  have hexp : discriminant (s-1+P*H) (-P*H+P^2*U) s = P^6*
      ((s-1)^2*((2*s-1)^2*H^2*U^2+2*s^2*(2*s-1)^2*H^4*U+s^4*H^6)+
        P*normalizedError P H U s) := by
    have hq := discriminant_expansion ((P : ℚ)*H) ((U : ℚ)/(H : ℚ)^2) s
    have hb : -((P : ℚ)*H)+((P : ℚ)*H)^2*((U : ℚ)/(H : ℚ)^2) =
        -(P : ℚ)*H+(P : ℚ)^2*U := by
      field_simp [hHq]
      <;> ring
    rw [hb] at hq
    have he : ((P : ℚ)*H)^6*((s : ℚ)-1)^2*
          localPolynomial (s : ℚ) ((U : ℚ)/(H : ℚ)^2)+
        ((P : ℚ)*H)^7*errorPolynomial ((P : ℚ)*H) ((U : ℚ)/(H : ℚ)^2) s =
        (P : ℚ)^6*(((s : ℚ)-1)^2*
          ((2*(s : ℚ)-1)^2*(H : ℚ)^2*(U : ℚ)^2+
            2*(s : ℚ)^2*(2*(s : ℚ)-1)^2*(H : ℚ)^4*U+(s : ℚ)^4*(H : ℚ)^6)+
          P*normalizedError (P : ℚ) H U s) := by
      unfold localPolynomial errorPolynomial normalizedError
      field_simp [hHq]
      <;> ring
    rw [he] at hq
    unfold discriminant tailA tailB tailC normalizedError at hq ⊢
    exact_mod_cast hq
  have heq : w^2=(s-1)^2*((2*s-1)^2*H^2*U^2+
      2*s^2*(2*s-1)^2*H^4*U+s^4*H^6)+P*normalizedError P H U s := by
    apply mul_left_cancel₀ (pow_ne_zero 6 hn)
    calc
      P^6*w^2 = (P^3*w)^2 := by ring
      _ = W^2 := by rw [hwp]
      _ = discriminant (s-1+P*H) (-P*H+P^2*U) s := hd.symm
      _ = _ := hexp
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
