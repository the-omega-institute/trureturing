/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/RepeatedPairProductArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact four-prime product-tail arithmetic and failed-criterion boundary. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.RepeatedPairProductSpectrum

/-! Source: repeated-pair-product-tail, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02, blob
66664013207b88567bf74f1a9a0c6eaf65d07f24. These are unbounded polynomial
identities and exact parameter inequalities. Fixed source controls do not
replace any of the universal quantifiers. -/
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Classical
namespace D5.S3.Combinatorics.SpectralGraph.RepeatedPairProductArithmetic
open RepeatedPairSupport RepeatedPairProductTail RepeatedPairProductSpectrum
open IdealIntersectionSupport IdealIntersectionObstructions

/-- Exact four-prime specialization of the full product inequality. -/
theorem four_criterion (a b c : ℝ) :
    (a^2-1)*(b+1)*(c+1)+(a-1)*(a-2) ≤ a^2*b*c ↔
      (a^2-1)*(b+c)+(a-1)*(2*a-1) ≤ b*c := by
  constructor <;> intro h <;> nlinarith only [h]

/-- The whole uniform product tail, with both boundary parameters included. -/
theorem uniform_tail (a b c : ℝ) (ha : 2 ≤ a)
    (hb : 2*a^2-1 ≤ b) (hc : 2*a^2-1 ≤ c) :
    (a^2-1)*(b+c)+(a-1)*(2*a-1) < b*c := by
  have h1 : 0 ≤ (b-(2*a^2-1))*(c-(2*a^2-1)) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ a^2*((b-(2*a^2-1))+(c-(2*a^2-1))) :=
    mul_nonneg (sq_nonneg a) (by linarith)
  have he : b*c-((a^2-1)*(b+c)+(a-1)*(2*a-1)) =
      (b-(2*a^2-1))*(c-(2*a^2-1))+
      a^2*((b-(2*a^2-1))+(c-(2*a^2-1)))+3*a-2 := by ring
  linarith

/-- The unbounded exact equality family, not a finite boundary sample. -/
theorem equality_family (a : ℝ) (ha : 2 ≤ a) :
    0 < a^2 ∧ 0 < a^4+a^2-3*a+1 ∧
    (a^2-1)*(a^2+(a^4+a^2-3*a+1))+(a-1)*(2*a-1) =
      a^2*(a^4+a^2-3*a+1) := by
  have h2 : 4 ≤ a^2 := by nlinarith
  have h4 : 16 ≤ a^4 := by nlinarith [sq_nonneg (a^2-4)]
  refine ⟨by positivity,?_,by ring⟩
  nlinarith [sq_nonneg (a-2)]

/-- The actual earlier distinguished-coordinate sufficient inequality,
on a complete exponent vector; failure says only that this method fails. -/
def smallExponentCriterion (k : Fin 4 → ℝ) : Prop :=
  ∃ i, ((k i)^2-1)*((∏ j ∈ univ.erase i, (k j+1))-1-
    (∏ j ∈ univ.erase i, k j)) ≤ k i-1+(∏ j ∈ univ.erase i, k j)

private theorem comparison_margins (a : ℝ) (ha : 2 ≤ a) :
    0 < 4*a^6-4*a^4-a^3-a^2-a+2 ∧
    0 < 16*a^7+12*a^6-16*a^5-18*a^4+3*a^2+2 := by
  have hz : 0 ≤ a-2 := by linarith
  have h1 : 4*a^6-4*a^4-a^3-a^2-a+2 =
      4*(a-2)^6+48*(a-2)^5+236*(a-2)^4+607*(a-2)^3+
      857*(a-2)^2+623*(a-2)+180 := by ring
  have h2 : 16*a^7+12*a^6-16*a^5-18*a^4+3*a^2+2 =
      16*(a-2)^7+236*(a-2)^6+1472*(a-2)^5+5022*(a-2)^4+
      10096*(a-2)^3+11923*(a-2)^2+7628*(a-2)+2030 := by ring
  rw [h1,h2]
  constructor <;> positivity

/-- Every member of the full diagonal uniform-tail family fails all four
coordinate choices of the old small-exponent criterion. This is a precise
failed-method boundary, not a graph-integrality assertion or priority claim. -/
theorem old_criterion_fails (a : ℝ) (ha : 2 ≤ a) :
    ¬smallExponentCriterion ![a,a,2*a^2-1,2*a^2-1] := by
  obtain ⟨h1,h2⟩ := comparison_margins a ha
  have hu : (univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  rintro ⟨i,hi⟩
  fin_cases i <;> simp (disch := decide) [hu,Finset.erase_insert,Finset.erase_insert_of_ne] at hi
  all_goals nlinarith only [hi,h1,h2]

end D5.S3.Combinatorics.SpectralGraph.RepeatedPairProductArithmetic
