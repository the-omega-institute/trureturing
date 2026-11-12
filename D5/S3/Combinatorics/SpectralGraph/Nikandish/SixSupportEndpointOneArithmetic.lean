/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneArithmetic.result; instance=D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportEndpointOneArithmetic.residue_certificate
   digest: Entire endpoint-one integer quartic constant and necessary root congruences. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportClassificationAlgebra
import Mathlib.Tactic

/-! Source: PR9 endpoint-one-constant-divisibility, root-congruences and
root-hierarchy notes, revision6d491f77b35dec808fc777b69939c56cdae5dc02;
original blob identities are retained in the complete shared scientific03.
These are necessary arithmetic tests on the actual six-support quintic,
not a sufficient splitting criterion or an exponent point enumeration. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointOneArithmetic
open Polynomial
open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra

def constant {R : Type*} [CommRing R] (a b c : R) : R :=
  a*b*c*(a+b+c)*(a+b+c+a*b+a*c+b*c)

def coefficientA {R : Type*} [CommRing R] (a b c : R) : R :=
  a*b+a*c+b*c+3*(a+b+c)-1

def coefficientB {R : Type*} [CommRing R] (a b c : R) : R :=
  let s := a+b+c
  let p := a*b+a*c+b*c
  let r := a*b*c
  s*r+2*s*p+3*s^2-3*s+1

def coefficientD {R : Type*} [CommRing R] (a b c : R) : R :=
  let s := a+b+c
  let p := a*b+a*c+b*c
  let r := a*b*c
  r^2+(s^2-s+1)*r+s^2*p+p^2+(s-1)^3

def quartic {R : Type*} [CommRing R] (a b c : R) : R[X] :=
  X^4-C (coefficientA a b c)*X^3+C (coefficientB a b c)*X^2-
    C (coefficientD a b c)*X+C (constant a b c)

/-- Literal polynomial correspondence, retaining the endpoint residual. -/
theorem factorization {R : Type*} [CommRing R] (a b c : R) :
    quintic a b c = (X-1)*quartic a b c+C (h a b c 1)*X := by
  simp [h,quintic,quartic,coefficientA,coefficientB,coefficientD,constant]
  simp only [map_ofNat]
  ring

/-- Full residue universe; kernel reduction, with no native evaluation axiom. -/
theorem residue_certificate : ∀ a b c : ZMod 12,
    value a b c 1 = 0 → constant a b c = 0 := by
  decide +kernel

/-- Every integer endpoint-one constant is divisible by twelve, without
ordering or size restrictions. The complete source domain follows. -/
theorem constant_divisibility (a b c : ℤ) (he : h a b c 1 = 0) :
    12 ∣ constant a b c := by
  have hm : value (a : ZMod 12) (b : ZMod 12) (c : ZMod 12) 1 = 0 := by
    have hz := congrArg (fun z : ℤ => (z : ZMod 12)) he
    simpa [h_eq_value,value] using hz
  have hc := residue_certificate (a : ZMod 12) (b : ZMod 12) (c : ZMod 12) hm
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (constant a b c) 12).mp
  simpa [constant] using hc

/-- All three original coefficient tests hold for every integer root,
including repeated roots and zero evaluations. -/
theorem root_coefficients (a b c d : ℤ) (hd : (quartic a b c).eval d = 0) :
    d ∣ constant a b c ∧
    d^2 ∣ constant a b c-coefficientD a b c*d ∧
    d^3 ∣ constant a b c-coefficientD a b c*d+coefficientB a b c*d^2 ∧
    d^4 ∣ constant a b c-coefficientD a b c*d+coefficientB a b c*d^2-
      coefficientA a b c*d^3 := by
  have he : d^4-coefficientA a b c*d^3+coefficientB a b c*d^2-
      coefficientD a b c*d+constant a b c = 0 := by
    simpa [quartic] using hd
  refine ⟨⟨coefficientD a b c-coefficientB a b c*d+coefficientA a b c*d^2-d^3,?_⟩,
    ⟨-(d^2-coefficientA a b c*d+coefficientB a b c),?_⟩,
    ⟨coefficientA a b c-d,?_⟩,⟨-1,?_⟩⟩ <;> nlinarith only [he]

/-- Exponent evaluation on the actual reduced characteristic polynomial. -/
theorem exponent_value {R : Type*} [CommRing R] (a b c : R) :
    h a b c a = -(a*b*c)^2*(a^2+3*a-(a+b+c)) ∧
    h a b c b = -(a*b*c)^2*(b^2+3*b-(a+b+c)) ∧
    h a b c c = -(a*b*c)^2*(c^2+3*c-(a+b+c)) := by
  simp [h,quintic]
  constructor
  · ring
  constructor <;> ring

/-- Every exponent test, with its equality case retained. -/
theorem exponent_test (a b c d e : ℤ) (he : e = a ∨ e = b ∨ e = c)
    (h1 : h a b c 1 = 0) (hd : (quartic a b c).eval d = 0) :
    (e-1)*(quartic a b c).eval e = -(a*b*c)^2*(e^2+3*e-(a+b+c)) ∧
    d-e ∣ (quartic a b c).eval e ∧
    (d=e → (quartic a b c).eval e=0) := by
  have hf := congrArg (fun p : Polynomial ℤ => p.eval e) (factorization a b c)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_C,h1,zero_mul,add_zero] at hf
  have hx : h a b c e = -(a*b*c)^2*(e^2+3*e-(a+b+c)) := by
    rcases he with he | he | he
    · simpa [he] using (exponent_value a b c).1
    · simpa [he] using (exponent_value a b c).2.1
    · simpa [he] using (exponent_value a b c).2.2
  have hv := Polynomial.sub_dvd_eval_sub d e (quartic a b c)
  rw [hd,zero_sub] at hv
  exact ⟨hf.symm.trans hx, dvd_neg.mp hv, fun heq => heq ▸ hd⟩

/-- The divisor twelve is sharp on the entire ordered integer surface.
The reverse implication uses four actual points of that same surface,
so no assertion about fully distinct points is introduced. -/
theorem common_divisors (d : ℤ) :
    (∀ a b c : ℤ, 4 ≤ a → a ≤ b → b ≤ c → h a b c 1 = 0 →
      d ∣ constant a b c) ↔ d ∣ 12 := by
  constructor
  · intro hd
    have h4 := hd 4 4 21 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [h_eq_value,value])
    have h5 := hd 5 5 36 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [h_eq_value,value])
    have h6 := hd 6 6 55 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [h_eq_value,value])
    have h8 := hd 8 8 105 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [h_eq_value,value])
    norm_num [constant] at h4 h5 h6 h8
    have hg := dvd_gcd (dvd_gcd (dvd_gcd h4 h5) h6) h8
    norm_num at hg
    exact hg
  · intro hd a b c _ _ _ he
    exact hd.trans (constant_divisibility a b c he)

/-- The complete constant/coefficient arithmetic at every endpoint-one
point and every integer residual root, with no scalar proxy premise. -/
theorem result (a b c d : ℤ) (h1 : h a b c 1 = 0)
    (hd : (quartic a b c).eval d = 0) :
    12 ∣ constant a b c ∧ d ∣ constant a b c ∧
    d^2 ∣ constant a b c-coefficientD a b c*d ∧
    d^3 ∣ constant a b c-coefficientD a b c*d+coefficientB a b c*d^2 ∧
    d^4 ∣ constant a b c-coefficientD a b c*d+coefficientB a b c*d^2-
      coefficientA a b c*d^3 :=
  ⟨constant_divisibility a b c h1,root_coefficients a b c d hd⟩

#print axioms result
end D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointOneArithmetic
