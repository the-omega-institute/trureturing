/- GID: D5/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportCandidateCounterexamples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete persistent divisor family and its failed linear coefficient test. -/
import D5.S3.Combinatorics.SpectralGraph.SixSupportEndpointOneArithmetic

/-! Source: endpoint-one-root-hierarchy and endpoint-one-root-congruences,
PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02, as received in the
original scientific03. This is the source's entire k>=1 repeated-minimum
candidate family. It excludes that candidate, not every divisor, and is
not a new graph nonintegrality family. The fully distinct Diophantine
and integer-point questions retain their original open boundaries. -/
set_option autoImplicit false
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportCandidateCounterexamples
open Polynomial
open SixSupportClassificationAlgebra SixSupportEndpointOneArithmetic

private def T (a : ℤ) : ℤ :=
  8*a^5+48*a^4-132*a^3+95*a^2-32*a+4

/-- Every candidate in the received unbounded family passes the constant
divisor test and the strict refined spectral window, yet is not a root
and fails the linear coefficient test. -/
theorem persistent_family (k : ℤ) (hk : 1 ≤ k) :
    let a := 6*k
    let c := (a-1)*(2*a-1)
    let d := 9*k
    h a a c 1 = 0 ∧ 4 ≤ a ∧ a ≤ c ∧
      d ∣ constant a a c ∧ a < d ∧ d < 2*a ∧
      (quartic a a c).eval d < 0 ∧
      ¬d^2 ∣ constant a a c-coefficientD a a c*d := by
  dsimp only
  let a := 6*k
  let c := (a-1)*(2*a-1)
  let d := 9*k
  have ha : 6 ≤ a := by dsimp [a]; omega
  have hkc : k ≠ 0 := by omega
  have h1 : h a a c 1 = 0 := by simp [h,quintic,c]; ring
  have hdiv : d ∣ constant a a c := by
    refine ⟨4*k*c*(2*a+c)*(2*a+c+a^2+2*a*c),?_⟩
    dsimp [constant,d,a]
    ring
  have hid : 4*(quartic a a c).eval d =
      -9*k^2*(4*a^2-2*a-1)*T a := by
    simp [quartic,coefficientA,coefficientB,coefficientD,constant,T,c,d,a]
    ring
  have hT : 0 < T a := by
    have he : T a = 8*a^5+a^3*(48*a-132)+a*(95*a-32)+4 := by dsimp [T]; ring
    rw [he]
    have ha0 : 0 < a := by omega
    have h48 : 0 < 48*a-132 := by omega
    have h95 : 0 < 95*a-32 := by omega
    positivity
  have hE : 0 < 4*a^2-2*a-1 := by nlinarith
  have hnegative : (quartic a a c).eval d < 0 := by
    have hp : 0 < 9*k^2*(4*a^2-2*a-1)*T a := by
      have hk0 : 0 < k := by omega
      positivity
    linarith only [hid,hp]
  have hnotF : ¬d^2 ∣ (quartic a a c).eval d := by
    rintro ⟨z,hz⟩
    have he : (9*k^2)*(36*z+(4*a^2-2*a-1)*T a) = 0 := by
      rw [hz] at hid
      dsimp [d] at hid
      nlinarith only [hid]
    have hnk : (9*k^2 : ℤ) ≠ 0 := by positivity
    have hcancel := (mul_eq_zero.mp he).resolve_left hnk
    have hthree : (3 : ℤ) ∣ 36*z+(4*a^2-2*a-1)*T a+4 := by
      refine ⟨12*z+2*k*(24-15*a-186*a^2+596*a^3-632*a^4+176*a^5+32*a^6),?_⟩
      dsimp [a,T]
      ring
    rw [hcancel,zero_add] at hthree
    norm_num at hthree
  have hnotlinear : ¬d^2 ∣ constant a a c-coefficientD a a c*d := by
    rintro ⟨z,hz⟩
    apply hnotF
    refine ⟨d^2-coefficientA a a c*d+coefficientB a a c+z,?_⟩
    simp only [quartic,eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C]
    linear_combination hz
  exact ⟨h1,by omega,by change a ≤ (a-1)*(2*a-1); nlinarith,hdiv,
    by change 6*k < 9*k; omega,by change 9*k < 2*(6*k); omega,hnegative,hnotlinear⟩

/-- Uniform negativity on the entire divisor window is false, even at
one of the already settled repeated-exponent controls. -/
theorem opposite_sign_control :
    h (20 : ℤ) 20 741 1 = 0 ∧
    21 ∣ constant (20 : ℤ) 20 741 ∧ 20 < (21 : ℤ) ∧ 21 < min (741 : ℤ) (20+20) ∧
    (quartic (20 : ℤ) 20 741).eval 21 = 1207587225600 ∧
    30 ∣ constant (20 : ℤ) 20 741 ∧ 20 < (30 : ℤ) ∧ 30 < min (741 : ℤ) (20+20) ∧
    (quartic (20 : ℤ) 20 741).eval 30 = -1257386661900 := by
  norm_num [h_eq_value,value,quartic,constant,coefficientA,coefficientB,coefficientD]

/-- The full proposed sign rule, on all ordered integer endpoint-one
triples and every positive constant divisor in the original window. -/
def uniform_negativity : Prop :=
  ∀ a b c d : ℤ, 4 ≤ a → a ≤ b → b ≤ c → h a b c 1 = 0 →
    d ∣ constant a b c → a < d → d < min c (a+b) →
    (quartic a b c).eval d < 0

/-- The original full-surface uniform-negativity proposal fails. No
claim is made about its restriction to fully distinct integer points. -/
theorem refutation : ¬uniform_negativity := by
  intro hneg
  obtain ⟨h1,hdiv,hlow,hupp,hpositive,_,_,_,_⟩ := opposite_sign_control
  have hh := hneg 20 20 741 21 (by norm_num) (by norm_num) (by norm_num)
    h1 hdiv hlow hupp
  rw [hpositive] at hh
  norm_num at hh

#print axioms persistent_family
#print axioms opposite_sign_control
#print axioms refutation
end D5.S3.Combinatorics.SpectralGraph.SixSupportCandidateCounterexamples
