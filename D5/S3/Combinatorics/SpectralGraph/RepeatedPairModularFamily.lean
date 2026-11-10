/- GID: D5/S3/Combinatorics/SpectralGraph/RepeatedPairModularFamily
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/RepeatedPairModularFamily
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unbounded odd repeated-pair family and full sufficient-region comparison margins. -/
import D5.S3.Combinatorics.SpectralGraph.RepeatedPairModularTables

/-! Source: repeated-pair-modular, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. The infinite family is
(a,a,2a,2a^2+1), for every odd a>=5, with arbitrary distinct graph
primes. All four choices in the small-exponent comparison are retained.
The comparisons concern the recorded sufficient tests only and make
no literature-priority claim. General Q3 and passing residue cases remain open. -/
set_option autoImplicit false
noncomputable section
open Finset
namespace D5.S3.Combinatorics.SpectralGraph.RepeatedPairModularFamily
open RepeatedPairSupport RepeatedPairModularResidues
open IdealIntersectionSupport IdealIntersectionObstructions

/-- Every member of the full source family is a nonintegral actual graph. -/
theorem actual_family (p : Fin 2 ⊕ Fin 2 → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (a : ℕ) (ha : 5 ≤ a) (hodd : a%2=1) :
    ¬ActualLaplacianIntegral
      (modulus p (pairExponents a ![2*a,2*a^2+1])) := by
  apply actual_odd_pair_obstruction p hp hinj a ![2*a,2*a^2+1]
    (by omega) (by intro i; fin_cases i <;> simp <;> positivity) hodd 1
  simp

/-- The full four-coordinate exponent vector for comparison with the
small-exponent sufficient condition; either repeated coordinate is allowed. -/
def exponents (a : ℝ) : Fin 4 → ℝ := ![a,a,2*a,2*a^2+1]

def smallMargin (a : ℝ) (i : Fin 4) : ℝ :=
  let A := ∏ j : Fin 4, if j=i then 1 else exponents a j
  let B := (∏ j : Fin 4, if j=i then 1 else exponents a j+1)-1-A
  ((exponents a i)^2-1)*B-(exponents a i-1)-A

/-- The five exact normalized positive-coefficient identities from the
source. The two repeated-coordinate small-exponent margins agree. -/
theorem comparison_identities (z : ℝ) :
    (((z+5)^2-1)*(2*(z+5)+1)*(2*(z+5)^2+2)+(z+4)*(z+3)-
      (z+5)^2*(2*(z+5))*(2*(z+5)^2+1) =
      2*z^4+38*z^3+271*z^2+853*z+990) ∧
    ((2*(z+5)+1)*(2*(z+5)^2-2*(z+5)+1)^2-8*(z+5)^2 =
      8*z^5+188*z^4+1768*z^3+8312*z^2+19518*z+18291) ∧
    (smallMargin (z+5) 0=6*z^5+150*z^4+1500*z^3+7495*z^2+18693*z+18590) ∧
    (smallMargin (z+5) 1=6*z^5+150*z^4+1500*z^3+7495*z^2+18693*z+18590) ∧
    (smallMargin (z+5) 2=16*z^5+410*z^4+4212*z^3+21680*z^2+55894*z+57720) ∧
    (smallMargin (z+5) 3=20*z^6+616*z^5+7920*z^4+54414*z^3+
      210708*z^2+436030*z+376700) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;>
    norm_num [smallMargin,exponents,Fin.prod_univ_succ] <;> ring

/-- Every coordinate fails the small-exponent sufficient region, and
both the product-tail and weighted odd-gap tests fail strictly. -/
theorem comparison_positive (a : ℝ) (ha : 5 ≤ a) :
    0 < (a^2-1)*(2*a+1)*(2*a^2+2)+(a-1)*(a-2)-a^2*(2*a)*(2*a^2+1) ∧
    0 < (2*a+1)*(2*a^2-2*a+1)^2-8*a^2 ∧
    ∀ i, 0 < smallMargin a i := by
  let z := a-5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have he : a=z+5 := by dsimp [z]; ring
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := comparison_identities z
  rw [he]
  constructor
  · convert (show 0 < 2*z^4+38*z^3+271*z^2+853*z+990 by positivity) using 1
    rw [←h1]
    ring
  constructor
  · rw [h2]
    positivity
  intro i
  fin_cases i
  · change 0 < smallMargin (z+5) 0
    rw [h3]
    positivity
  · change 0 < smallMargin (z+5) 1
    rw [h4]
    positivity
  · change 0 < smallMargin (z+5) 2
    rw [h5]
    positivity
  · change 0 < smallMargin (z+5) 3
    rw [h6]
    positivity

/-- The complete family's gap and large-tail comparisons; no finite
parameter scan or asymptotic qualification is used. -/
theorem remaining_comparisons (a : ℝ) (ha : 5 ≤ a) :
    (∀ i, 4 < exponents a i) ∧ a < 2*a ∧ 2*a < 2*a^2+1 ∧
    41 ≤ 2*a^2-2*a+1 ∧ 2*a-6 < 2*a^2+1 ∧
    2*a < (2*a^2-2*a+1)^2 ∧
    2*a^2+1 < 24*((a+1)*(2*a+1)+a)^3*(3*((a+1)*(2*a+1))+a) := by
  have hz : 0 ≤ a-5 := by linarith
  have ha2 : 25 ≤ a^2 := by nlinarith
  have hgap : 41 ≤ 2*a^2-2*a+1 := by nlinarith [sq_nonneg (a-5)]
  have hg : 2*a < (2*a^2-2*a+1)^2 := by
    have hs : 2*a ≤ 2*a^2-2*a+1 := by nlinarith [sq_nonneg (a-5)]
    nlinarith
  refine ⟨?_,by linarith,by nlinarith,hgap,by nlinarith,hg,?_⟩
  · intro i; fin_cases i <;> simp [exponents] <;> nlinarith
  · let M := (a+1)*(2*a+1)
    have hM : 2*a^2 < M := by dsimp [M]; nlinarith
    have hM1 : 1 < M := by nlinarith
    have hP : M^4 < (M+a)^3*(3*M+a) := by
      have h1 : M^3 < (M+a)^3 := by nlinarith [sq_nonneg a]
      have h2 : 0 < M^3 := by positivity
      nlinarith
    change 2*a^2+1 < 24*(M+a)^3*(3*M+a)
    have h4 : M ≤ M^4 := by nlinarith [sq_nonneg (M^2-1)]
    nlinarith

end D5.S3.Combinatorics.SpectralGraph.RepeatedPairModularFamily
