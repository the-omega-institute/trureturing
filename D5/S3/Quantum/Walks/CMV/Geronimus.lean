/- GID: D5/S3/Quantum/Walks/CMV/Geronimus
   generality: I
   mirror-B: D5/B/S3/Quantum/Walks/CMV/Geronimus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Riesz moment and CMV identities for scale-four self-similarity. -/

/- admission_basis: escape-witness
   Module witness: schur_equals_gram
   Direct frozen dependencies:
   D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail
     declaration statement_id: sha256:866d2544f66c1d06437a72737a30260611f3d3ad3546581a69fd50db1c634bb4
   PolynomialSeries.polynomial_expansion: proof_shape: bind-only; escape_witness: none
     Direct frozen dependencies: none; consumers: CMV.Geronimus.PolynomialSeries.asPS_expansion, CMV.Geronimus.PolynomialSeries.moment_coefficients, CMV.Geronimus.phi_zero, CMV.Representation.CMVFromGramParameters.normalizedPhi_zero.
   schur_equals_gram: proof_shape: content; escape_witness: CMV.Geronimus.GeronimusFiniteCriterion.geronimus_of_pade_data
     Direct frozen dependencies: tail; consumers: RieszWalkSelfSimilarity.cumulative_scale_four.
   Schur monomial removal and Padé coefficient tails use the frozen
   RecursiveBoundaryRowSeries.tail on the coefficient sequence.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15854
-/

import D5.S3.Quantum.Walks.CMV.SzegoRecurrence
import D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries

open LaurentPolynomial
noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.Geronimus.Functions
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis
def caratheodory : PowerSeries ℝ :=
  PowerSeries.mk (fun n => if n = 0 then 1 else 2 * (rieszMoment (n : ℤ) : ℝ))

def schur0 : PowerSeries ℝ :=
  D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail
    (fun k => PowerSeries.coeff k ((caratheodory - 1) * (caratheodory + 1)⁻¹)) 1

def schurStep (f : PowerSeries ℝ) : PowerSeries ℝ :=
  let a := PowerSeries.constantCoeff f
  D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail
    (fun k => PowerSeries.coeff k ((f - PowerSeries.C a) * (1 - PowerSeries.C a * f)⁻¹)) 1

def schurSeq : ℕ → PowerSeries ℝ
  | 0 => schur0
  | k+1 => schurStep (schurSeq k)

def alpha (k : ℕ) : ℝ := PowerSeries.constantCoeff (schurSeq k)
private theorem tail_shift_one (F : PowerSeries ℝ) :
    D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail (fun k => PowerSeries.coeff k F) 1 =
      PowerSeries.mk (fun k => PowerSeries.coeff (k+1) F) := by
  ext k
  simp only [D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail,PowerSeries.coeff_mk,Nat.add_comm]

private theorem caratheodory_constant : PowerSeries.constantCoeff caratheodory = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [caratheodory]



private theorem schur0_spec : PowerSeries.X * schur0 * (caratheodory+1) = caratheodory-1 := by
  have hq : PowerSeries.constantCoeff ((caratheodory-1)*(caratheodory+1)⁻¹) = 0 := by
    simp [map_mul, map_sub, caratheodory_constant]
  rw [schur0, tail_shift_one, ← PowerSeries.sub_const_eq_X_mul_shift, hq]
  simp only [map_zero, sub_zero]
  rw [mul_assoc, PowerSeries.inv_mul_cancel (caratheodory+1) (by simp [caratheodory_constant]), mul_one]

private theorem schurStep_spec (f : PowerSeries ℝ)
    (h : 1-(PowerSeries.constantCoeff f)^2 ≠ 0) :
    PowerSeries.X * schurStep f * (1-PowerSeries.C (PowerSeries.constantCoeff f)*f) =
      f-PowerSeries.C (PowerSeries.constantCoeff f) := by
  have hq : PowerSeries.constantCoeff ((f-PowerSeries.C (PowerSeries.constantCoeff f))*
      (1-PowerSeries.C (PowerSeries.constantCoeff f)*f)⁻¹) = 0 := by simp
  rw [schurStep, tail_shift_one, ← PowerSeries.sub_const_eq_X_mul_shift, hq]
  simp only [map_zero, sub_zero]
  rw [mul_assoc, PowerSeries.inv_mul_cancel, mul_one]
  simpa [pow_two] using h


end D5.S3.Quantum.Walks.CMV.Geronimus.Functions
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.Geronimus.PolynomialSeries
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions
open D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence LaurentPolynomial

/-- Exact finite coefficient expansion on a nonnegative Laurent window. -/
theorem polynomial_expansion (n : ℕ) {p : (LaurentPolynomial ℝ)} (hp : p ∈ polyWindow n) :
    p=∑ k ∈ Finset.range (n+1), coeffLM (k:ℤ) p • T (k:ℤ) := by
  apply LaurentPolynomial.ext
  intro e
  change coeffLM e p=coeffLM e (∑ k ∈ Finset.range (n+1), coeffLM (k:ℤ) p • T (k:ℤ))
  rw [map_sum]
  simp only [map_smul,smul_eq_mul,coeffLM_T]
  by_cases he : 0≤e ∧ e≤(n:ℤ)
  · have hen : (e.toNat:ℤ)=e := Int.toNat_of_nonneg he.1
    have hem : e.toNat∈Finset.range (n+1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single_of_mem e.toNat hem]
    · simp [hen]
    · intro k hk hke
      have hne : e≠(k:ℤ) := by
        intro h
        have heq : e.toNat=k := by omega
        exact hke heq.symm
      simp [hne]
  · rw [coeff_window_zero n hp e (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hne : e≠(k:ℤ) := by have h := Finset.mem_range.mp hk; omega
    simp [hne]

/-- Nonnegative Laurent coefficients as a formal power series. -/
private def asPS : (LaurentPolynomial ℝ) →ₗ[ℝ] (PowerSeries ℝ) where
  toFun p := (LaurentPolynomial.trunc p).toPowerSeries
  map_add' p q := by
    simp only [map_add, Polynomial.coe_add]
  map_smul' a p := by
    ext n
    simp [LaurentPolynomial.trunc, Polynomial.toPowerSeries]

@[simp] private theorem coeff_asPS (n : ℕ) (p : (LaurentPolynomial ℝ)) : PowerSeries.coeff n (asPS p)=coeffLM (n:ℤ) p := by
  rw [show asPS p = ((LaurentPolynomial.trunc p) : PowerSeries ℝ) from rfl,
    Polynomial.coeff_coe]
  rfl

@[simp] private theorem asPS_T (n : ℕ) : asPS (T (n:ℤ))=PowerSeries.X^n := by
  ext k
  simp [PowerSeries.coeff_X_pow,eq_comm]

private theorem asPS_expansion (n : ℕ) {p : (LaurentPolynomial ℝ)} (hp : p ∈ polyWindow n) :
    asPS p=∑ k ∈ Finset.range (n+1), coeffLM (k:ℤ) p • PowerSeries.X^k := by
  conv_lhs => rw [polynomial_expansion n hp]
  simp

/-- The finite moment equations in coefficient form. -/
private theorem moment_coefficients (n : ℕ) {p : (LaurentPolynomial ℝ)} (hp : p ∈ polyWindow n) (e : ℤ) :
    sigma (T e) p=∑ k ∈ Finset.range (n+1),
      coeffLM (k:ℤ) p*(D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment ((k:ℤ)-e):ℝ) := by
  conv_lhs => rw [polynomial_expansion n hp]
  simp only [map_sum,map_smul,smul_eq_mul,sigma,momentForm_T_T]

end D5.S3.Quantum.Walks.CMV.Geronimus.PolynomialSeries
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.Geronimus.PadeCoefficients
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCNormalization D5.S3.Quantum.Walks.CMV.Geronimus.PolynomialSeries LaurentPolynomial

/-- The finite convolution used throughout the Padé supplier. -/
private theorem coeff_mul_asPS (F : (PowerSeries ℝ)) (n k : ℕ) {p : (LaurentPolynomial ℝ)} (hp : p ∈ polyWindow n) :
    PowerSeries.coeff k (F*asPS p)=∑ l ∈ Finset.range (n+1),
      if l≤k then coeffLM (l:ℤ) p*PowerSeries.coeff (k-l) F else 0 := by
  rw [asPS_expansion n hp,Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [mul_smul_comm,map_smul,smul_eq_mul,PowerSeries.coeff_mul_X_pow']
  split_ifs <;> simp_all

/-- The second-kind polynomial is defined from a finite Carathéodory truncation. -/
private def secondStar (n : ℕ) : (LaurentPolynomial ℝ) :=
  (PowerSeries.trunc (n+1) (caratheodory*asPS (phiStar n))).toLaurent

private def second (n : ℕ) : (LaurentPolynomial ℝ) := T (n:ℤ)*invert (secondStar n)

private def numerator (n : ℕ) : (PowerSeries ℝ) := caratheodory*asPS (phiStar n)-asPS (secondStar n)
private def denominator (n : ℕ) : (PowerSeries ℝ) := caratheodory*asPS (phi n)+asPS (second n)

/-- Exact truncation coefficients, including all zero coefficients beyond n. -/
private theorem secondStar_coeff (n k : ℕ) :
    coeffLM (k:ℤ) (secondStar n)=
      if k≤n then PowerSeries.coeff k (caratheodory*asPS (phiStar n)) else 0 := by
  dsimp [secondStar,coeffLM]
  change ((PowerSeries.trunc (n+1) (caratheodory*asPS (phiStar n))).toLaurent).coeff (k:ℤ)=_
  rw [LaurentPolynomial.coeff_toLaurent]
  change (Finsupp.mapDomain Nat.castEmbedding
    ((PowerSeries.trunc (n+1) (caratheodory*asPS (phiStar n))).toFinsupp.coeff))
      (Nat.castEmbedding k)=_
  rw [Finsupp.mapDomain_apply_of_injective Nat.castEmbedding.injective]
  change (PowerSeries.trunc (n+1) (caratheodory*asPS (phiStar n))).coeff k=_
  rw [PowerSeries.coeff_trunc]
  simp only [Nat.lt_succ_iff]

private theorem secondStar_expansion (n : ℕ) : secondStar n=
    ∑ k ∈ Finset.range (n+1),
      PowerSeries.coeff k (caratheodory*asPS (phiStar n)) • T (k:ℤ) := by
  rw [secondStar,PowerSeries.trunc_apply,Nat.Ico_zero_eq_range,map_sum]
  simp only [Polynomial.toLaurent_C_mul_T,←smul_eq_C_mul]

private theorem secondStar_window (n : ℕ) : secondStar n ∈ polyWindow n := by
  rw [secondStar_expansion]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  apply T_mem_spanOn
  have h := Finset.mem_range.mp hk
  change 0≤(k:ℤ) ∧ (k:ℤ)≤n
  omega

private theorem phiStar_coeff_reflected (n l : ℕ) (hl : l≤n) :
    coeffLM (l:ℤ) (phiStar n)=coeffLM ((n-l:ℕ):ℤ) (phi n) := by
  rw [phiStar,coeffLM_shift,coeffLM_invert]
  rw [show -((l:ℤ)-(n:ℤ))=((n-l:ℕ):ℤ) by rw [Nat.cast_sub hl]; ring]

private theorem second_coeff (n k : ℕ) (hk : k≤n) : coeffLM (k:ℤ) (second n)=
    PowerSeries.coeff (n-k) (caratheodory*asPS (phiStar n)) := by
  rw [second,coeffLM_shift,coeffLM_invert,
    show -((k:ℤ)-(n:ℤ))=((n-k:ℕ):ℤ) by omega,secondStar_coeff,if_pos (Nat.sub_le n k)]

/-- Reversing the finite convolution yields the complementary half of the
Toeplitz moment equation. -/
private theorem second_coeff_sum (n k : ℕ) (hk : k≤n) : coeffLM (k:ℤ) (second n)=
    ∑ l ∈ Finset.range (n+1),
      if k≤l then coeffLM (l:ℤ) (phi n)*PowerSeries.coeff (l-k) caratheodory else 0 := by
  rw [second_coeff n k hk,coeff_mul_asPS caratheodory n (n-k) (phiStar_mem_window n)]
  rw [←Finset.sum_range_reflect (fun l =>
    if l≤n-k then coeffLM (l:ℤ) (phiStar n)*PowerSeries.coeff (n-k-l) caratheodory else 0) (n+1)]
  apply Finset.sum_congr rfl
  intro l hl
  have hlN : l≤n := by have h := Finset.mem_range.mp hl; omega
  have hidx : n+1-1-l=n-l := by omega
  rw [hidx]
  by_cases hkl : k≤l
  · have hle : n-l≤n-k := by omega
    rw [if_pos hle,if_pos hkl,phiStar_coeff_reflected n (n-l) (Nat.sub_le n l),
      show n-(n-l)=l by omega,show n-k-(n-l)=l-k by omega]
  · have hle : ¬n-l≤n-k := by omega
    rw [if_neg hle,if_neg hkl]

end D5.S3.Quantum.Walks.CMV.Geronimus.PadeCoefficients
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.Geronimus.SeriesShift
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions
open D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence D5.S3.Quantum.Walks.CMV.Geronimus.PolynomialSeries LaurentPolynomial

/-- As a series, a nonnegative Laurent polynomial commutes with multiplying
by z. This hypothesis rules out discarded negative coefficients. -/
private theorem asPS_shift (n : ℕ) {p : (LaurentPolynomial ℝ)} (hp : p ∈ polyWindow n) :
    asPS (T 1*p)=PowerSeries.X*asPS p := by
  ext k
  rw [coeff_asPS,coeffLM_shift]
  cases k with
  | zero =>
    rw [Nat.cast_zero,show (0:ℤ)-1=-1 by ring,
      coeff_window_zero n hp (-1) (by omega)]
    simp
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul,coeff_asPS]
    congr 1
    push_cast
    ring

end D5.S3.Quantum.Walks.CMV.Geronimus.SeriesShift
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.Geronimus.PadeLeadingTerms
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCNormalization D5.S3.Quantum.Walks.CMV.Geronimus.PolynomialSeries D5.S3.Quantum.Walks.CMV.Geronimus.PadeCoefficients LaurentPolynomial

@[simp] private theorem caratheodory_coeff (n : ℕ) : PowerSeries.coeff n caratheodory=
    if n=0 then 1 else 2*(rieszMoment (n:ℤ):ℝ) := by simp [caratheodory]

private theorem moment_zero : (D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment 0:ℝ)=1 := by
  rw [D5.S3.Quantum.Walks.Riesz.Moments.moment_at 0 0 (by norm_num)]
  simp [D5.S3.Quantum.Walks.Riesz.Moments.coeffRec]

/-- The sum of the two triangular convolution halves is the finite Gram
orthogonality equation. -/
private theorem denominator_coefficient (n k : ℕ) (hk : k≤n) :
    PowerSeries.coeff k (denominator n)=2*sigma (T (k:ℤ)) (phi n) := by
  rw [denominator,map_add,coeff_asPS,coeff_mul_asPS caratheodory n k (phi_mem_window n),
    second_coeff_sum n k hk,moment_coefficients n (phi_mem_window n) (k:ℤ),
    Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  rcases lt_trichotomy l k with hlk | heq | hkl
  · have hle : l≤k := hlk.le
    have hnot : ¬k≤l := by omega
    have hzero : k-l≠0 := by omega
    rw [if_pos hle,if_neg hnot,caratheodory_coeff,if_neg hzero,Nat.cast_sub hle]
    have hm : (rieszMoment ((k:ℤ)-l):ℝ)=(D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment ((l:ℤ)-k):ℝ) := by
      change (D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment ((k:ℤ)-l):ℝ)=_
      rw [show (k:ℤ)-l=-((l:ℤ)-k) by ring,D5.S3.Quantum.Walks.Riesz.Moments.moment_neg]
    rw [hm]
    ring
  · subst l
    simp only [le_refl,ite_true,Nat.sub_self,caratheodory_coeff,sub_self,moment_zero]
    norm_num
    ring
  · have hle : k≤l := hkl.le
    have hnot : ¬l≤k := by omega
    have hzero : l-k≠0 := by omega
    rw [if_neg hnot,if_pos hle,caratheodory_coeff,if_neg hzero,Nat.cast_sub hle]
    change 0+coeffLM (l:ℤ) (phi n)*(2*(D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment ((l:ℤ)-k):ℝ))=_
    ring

private theorem denominator_low_zero (n k : ℕ) (hk : k<n) :
    PowerSeries.coeff k (denominator n)=0 := by
  rw [denominator_coefficient n k hk.le,phi_orthogonal n (k:ℤ) (by omega),mul_zero]

/-- The first nonzero denominator coefficient is twice the positive Gram norm. -/
private theorem denominator_leading (n : ℕ) :
    PowerSeries.coeff n (denominator n)=2*normSquare n := by
  rw [denominator_coefficient n n le_rfl]
  have hlow : T (n:ℤ)-phi n ∈ polyBelow n := by
    apply (mem_spanOn_iff _ _).mpr
    intro e he
    change ¬(0≤e ∧ e<(n:ℤ)) at he
    rw [map_sub,coeffLM_T]
    by_cases hen : e=(n:ℤ)
    · subst e
      rw [if_pos rfl,phi_monic,sub_self]
    · rw [if_neg hen,coeff_window_zero n (phi_mem_window n) e (by omega),sub_self]
  have h := phi_orthogonal_span n _ hlow
  rw [map_sub,LinearMap.sub_apply] at h
  have heq := sub_eq_zero.mp h
  rw [heq]
  rfl

end D5.S3.Quantum.Walks.CMV.Geronimus.PadeLeadingTerms
end

noncomputable section
open scoped BigOperators
namespace D5.S3.Quantum.Walks.CMV.Geronimus.PadeNumerator
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.SzegoRecurrence.FormSymmetries D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCNormalization D5.S3.Quantum.Walks.CMV.Geronimus.PolynomialSeries D5.S3.Quantum.Walks.CMV.Geronimus.PadeCoefficients D5.S3.Quantum.Walks.CMV.Geronimus.PadeLeadingTerms LaurentPolynomial

private theorem numerator_low_zero (n k : ℕ) (hk : k≤n) :
    PowerSeries.coeff k (numerator n)=0 := by
  rw [numerator,map_sub,coeff_asPS,secondStar_coeff,if_pos hk,sub_self]

/-- Beyond the reflected polynomial's degree, a Carathéodory convolution is
exactly twice a moment test. -/
private theorem star_product_above (n k : ℕ) (hk : n<k) :
    PowerSeries.coeff k (caratheodory*asPS (phiStar n))=
      2*sigma (T ((n:ℤ)-k)) (phi n) := by
  rw [coeff_mul_asPS caratheodory n k (phiStar_mem_window n),
    ←Finset.sum_range_reflect (fun l => if l≤k then coeffLM (l:ℤ) (phiStar n)*
      PowerSeries.coeff (k-l) caratheodory else 0) (n+1),
    moment_coefficients n (phi_mem_window n) ((n:ℤ)-k),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hlN : l≤n := by have h := Finset.mem_range.mp hl; omega
  rw [show n+1-1-l=n-l by omega,if_pos (by omega : n-l≤k),
    phiStar_coeff_reflected n (n-l) (Nat.sub_le n l),show n-(n-l)=l by omega,
    caratheodory_coeff,if_neg (by omega : k-(n-l)≠0)]
  have he : ((k-(n-l):ℕ):ℤ)=(l:ℤ)-((n:ℤ)-k) := by omega
  rw [he]
  change coeffLM (l:ℤ) (phi n)*(2*(D5.S3.Quantum.Walks.Riesz.Moments.rieszMoment ((l:ℤ)-((n:ℤ)-k)):ℝ))=_
  ring

/-- The constant term of Phi_n* tests precisely its positive Gram norm. -/
private theorem phiStar_origin_moment (n : ℕ) : sigma (T 0) (phiStar n)=normSquare n := by
  have hlow : phiStar n-T 0 ∈ (Submodule.span ℝ (T '' {e : ℤ | 1≤e ∧ e≤(n:ℤ)})) := by
    apply (mem_spanOn_iff _ _).mpr
    intro e he
    change ¬(1≤e ∧ e≤(n:ℤ)) at he
    rw [map_sub,coeffLM_T]
    by_cases he0 : e=0
    · subst e
      rw [phiStar_constant,if_pos rfl,sub_self]
    · rw [phiStar_coeff_zero n e (by omega),if_neg he0,sub_self]
  have horth := form_zero_on_span sigma _ (phiStar n)
    (fun e he => phiStar_orthogonal n e he) _ hlow
  rw [map_sub,LinearMap.sub_apply,phiStar_norm] at horth
  exact (sub_eq_zero.mp horth).symm

/-- The first numerator coefficient reads off the Gram-defined parameter. -/
private theorem numerator_leading (n : ℕ) :
    PowerSeries.coeff (n+1) (numerator n)=2*verblunsky n*normSquare n := by
  rw [numerator,map_sub,coeff_asPS,secondStar_coeff,if_neg (by omega : ¬n+1≤n),sub_zero,
    star_product_above n (n+1) (by omega)]
  have he : (n:ℤ)-((n+1:ℕ):ℤ)=-1 := by push_cast; ring
  rw [he]
  have h := phi_orthogonal (n+1) 0 ⟨le_refl 0, by exact_mod_cast (Nat.succ_pos n)⟩
  rw [monic_szego,map_sub,map_smul,smul_eq_mul,phiStar_origin_moment] at h
  have hs := sigma_shift 1 (T (-1)) (phi n)
  rw [←T_add,show (1:ℤ)+ -1=0 by ring] at hs
  rw [←hs]
  rw [sub_eq_zero.mp h]
  ring

end D5.S3.Quantum.Walks.CMV.Geronimus.PadeNumerator
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.Geronimus.PadeRecurrence
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCNormalization D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCStarRecurrence D5.S3.Quantum.Walks.CMV.Geronimus.PolynomialSeries D5.S3.Quantum.Walks.CMV.Geronimus.PadeCoefficients D5.S3.Quantum.Walks.CMV.Geronimus.PadeLeadingTerms D5.S3.Quantum.Walks.CMV.Geronimus.PadeNumerator D5.S3.Quantum.Walks.CMV.Geronimus.SeriesShift LaurentPolynomial

/-- The leading Padé relation cancels the next coefficient as well as all
lower ones; this is the finite reason the second-kind recursion closes. -/
private theorem pade_remainder_zero (n k : ℕ) (hk : k≤n+1) :
    PowerSeries.coeff k (numerator n-
      PowerSeries.C (verblunsky n)*PowerSeries.X*denominator n)=0 := by
  rw [map_sub,mul_assoc,PowerSeries.coeff_C_mul]
  cases k with
  | zero =>
    rw [numerator_low_zero n 0 (by omega)]
    simp
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul]
    by_cases heq : k=n
    · subst k
      rw [numerator_leading,denominator_leading]
      ring
    · have hkn : k<n := by omega
      rw [numerator_low_zero n (k+1) (by omega),denominator_low_zero n k hkn]
      simp

private theorem second_window (n : ℕ) : second n ∈ polyWindow n := by
  apply (mem_spanOn_iff _ _).mpr
  intro e he
  change ¬(0≤e ∧ e≤(n:ℤ)) at he
  rw [second,coeffLM_shift,coeffLM_invert]
  apply coeff_window_zero n (secondStar_window n)
  omega

/-- Second-kind recursion, derived from finite truncation and moment equations. -/
private theorem secondStar_succ (n : ℕ) : secondStar (n+1)=secondStar n+
    verblunsky n • (T 1*second n) := by
  apply LaurentPolynomial.ext
  intro e
  change coeffLM e (secondStar (n+1))=coeffLM e
    (secondStar n+verblunsky n • (T 1*second n))
  by_cases he : 0≤e ∧ e≤((n+1:ℕ):ℤ)
  · have hen : (e.toNat:ℤ)=e := Int.toNat_of_nonneg he.1
    have hk : e.toNat≤n+1 := by omega
    rw [←hen,secondStar_coeff,if_pos hk]
    have hstar : asPS (phiStar (n+1))=asPS (phiStar n)-
        PowerSeries.C (verblunsky n)*PowerSeries.X*asPS (phi n) := by
      rw [monic_star_szego,map_sub,map_smul,asPS_shift n (phi_mem_window n),
        PowerSeries.smul_eq_C_mul]
      ring
    rw [hstar]
    have hseries : caratheodory*(asPS (phiStar n)-
        PowerSeries.C (verblunsky n)*PowerSeries.X*asPS (phi n)) =
      asPS (secondStar n)+PowerSeries.C (verblunsky n)*PowerSeries.X*asPS (second n)+
        (numerator n-PowerSeries.C (verblunsky n)*PowerSeries.X*denominator n) := by
      rw [numerator,denominator]
      ring
    rw [hseries,map_add,pade_remainder_zero n e.toNat hk,add_zero]
    rw [←coeff_asPS]
    have hR : asPS (secondStar n+verblunsky n • (T 1*second n))=
        asPS (secondStar n)+PowerSeries.C (verblunsky n)*PowerSeries.X*asPS (second n) := by
      rw [map_add,map_smul,asPS_shift n (second_window n),PowerSeries.smul_eq_C_mul]
      ring
    rw [hR,map_add]
  · rw [coeff_window_zero (n+1) (secondStar_window (n+1)) e (by omega),
      map_add,map_smul,coeffLM_shift,coeff_window_zero n (secondStar_window n) e (by omega),
      coeff_window_zero n (second_window n) (e-1) (by push_cast at he; omega)]
    simp

/-- The reflected second-kind recursion. -/
private theorem second_succ (n : ℕ) : second (n+1)=T 1*second n+
    verblunsky n • secondStar n := by
  simp only [second,secondStar_succ,map_add,map_smul,map_mul,invert_T,
    involutive_invert,mul_add,mul_smul_comm,←mul_assoc,←T_add]
  rw [involutive_invert,show ((n+1:ℕ):ℤ)+ -(1+(n:ℤ))=0 by push_cast; ring]
  simp only [T_zero,one_mul,Nat.cast_add,Nat.cast_one,add_comm]


end D5.S3.Quantum.Walks.CMV.Geronimus.PadeRecurrence
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.Geronimus.GeronimusAlgebra
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions PowerSeries

/-- The exact finite algebra behind the Geronimus proof. Here A and B stand
for F Phi* - Psi* and F Phi + Psi, without any convergence assertion. -/
private theorem schur_invariant_step (f A B : (PowerSeries ℝ)) (a : ℝ)
    (ha : constantCoeff f=a) (hunit : 1-a^2≠0)
    (hinv : A=X*f*B) :
    A-PowerSeries.C a*X*B = X*schurStep f*(X*B-PowerSeries.C a*A) := by
  have hs := schurStep_spec f (by simpa only [ha] using hunit)
  rw [ha] at hs
  rw [hinv]
  calc
    X*f*B-PowerSeries.C a*X*B = X*(f-PowerSeries.C a)*B := by ring
    _ = X*(X*schurStep f*(1-PowerSeries.C a*f))*B := by rw [hs]
    _ = X*schurStep f*(X*B-PowerSeries.C a*(X*f*B)) := by ring

/-- Taking the lowest nonzero denominator coefficient identifies the Schur
parameter. The remaining analytical statement is a finite moment identity. -/
private theorem parameter_of_leading_terms (f A B D E : (PowerSeries ℝ)) (n : ℕ) (a : ℝ)
    (hinv : A=X*f*B) (hB : B=X^n*D) (hA : A=X^(n+1)*E)
    (hD : constantCoeff D≠0) (hE : constantCoeff E=a*constantCoeff D) :
    constantCoeff f=a := by
  have heq : E=f*D := by
    apply X_pow_mul_cancel (k:=n+1)
    calc
      X^(n+1)*E = A := hA.symm
      _ = X*f*B := hinv
      _ = X^(n+1)*(f*D) := by rw [hB,pow_succ]; ring
  have hc := congrArg (constantCoeff (R:=ℝ)) heq
  rw [map_mul,hE] at hc
  exact (mul_right_cancel₀ hD hc).symm

end D5.S3.Quantum.Walks.CMV.Geronimus.GeronimusAlgebra
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.Geronimus.GeronimusFiniteCriterion
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.Geronimus.GeronimusAlgebra PowerSeries

/-- Finite Padé data sufficient for Geronimus. The leading-term clauses are
finite moment identities, not assumed Schur-parameter equalities. -/
private structure PadeData (a : ℕ → ℝ) (A B D E : ℕ → (PowerSeries ℝ)) : Prop where
  zeroA : A 0=caratheodory-1
  zeroB : B 0=caratheodory+1
  succA : ∀ n, A (n+1)=A n-PowerSeries.C (a n)*X*B n
  succB : ∀ n, B (n+1)=X*B n-PowerSeries.C (a n)*A n
  factorA : ∀ n, A n=X^(n+1)*E n
  factorB : ∀ n, B n=X^n*D n
  leadingA : ∀ n, constantCoeff (E n)=a n*constantCoeff (D n)
  leadingB : ∀ n, constantCoeff (D n)≠0
  unit : ∀ n, 1-(a n)^2≠0

/-- All Schur/Verblunsky parameters are identified by finite coefficient
algebra. The only data to construct is the polynomial Padé supplier. -/
private theorem geronimus_of_pade_data {a : ℕ → ℝ} {A B D E : ℕ → (PowerSeries ℝ)}
    (h : PadeData a A B D E) : ∀ n : ℕ, alpha n=a n := by
  have hi : ∀ n : ℕ, A n=X*schurSeq n*B n := by
    intro n
    induction n with
    | zero =>
      rw [h.zeroA,h.zeroB]
      exact schur0_spec.symm
    | succ n ih =>
      have ha : constantCoeff (schurSeq n)=a n :=
        parameter_of_leading_terms _ _ _ _ _ n (a n) ih (h.factorB n)
          (h.factorA n) (h.leadingB n) (h.leadingA n)
      rw [h.succA,h.succB]
      exact schur_invariant_step _ _ _ _ ha (h.unit n) ih
  intro n
  exact parameter_of_leading_terms _ _ _ _ _ n (a n) (hi n) (h.factorB n)
    (h.factorA n) (h.leadingB n) (h.leadingA n)

end D5.S3.Quantum.Walks.CMV.Geronimus.GeronimusFiniteCriterion
end

noncomputable section
namespace D5.S3.Quantum.Walks.CMV.Geronimus
open D5.S3.Quantum.Walks.Riesz.Moments D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.Riesz.Moments.Positivity D5.S3.Quantum.Walks.Riesz.Moments.RieszPositive D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Windows D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Existence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.GramBasis D5.S3.Quantum.Walks.CMV.Geronimus.Functions
open D5.S3.Quantum.Walks.CMV.Geronimus.Functions D5.S3.Quantum.Walks.CMV.SzegoRecurrence.Core D5.S3.Quantum.Walks.Riesz.Moments.Forms D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCFinite D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCRecurrence D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCNormalization D5.S3.Quantum.Walks.CMV.SzegoRecurrence.OPUCStarRecurrence D5.S3.Quantum.Walks.CMV.Geronimus.PolynomialSeries D5.S3.Quantum.Walks.CMV.Geronimus.PadeCoefficients D5.S3.Quantum.Walks.CMV.Geronimus.PadeLeadingTerms D5.S3.Quantum.Walks.CMV.Geronimus.PadeNumerator D5.S3.Quantum.Walks.CMV.Geronimus.PadeRecurrence D5.S3.Quantum.Walks.CMV.Geronimus.SeriesShift D5.S3.Quantum.Walks.CMV.Geronimus.GeronimusFiniteCriterion LaurentPolynomial

/-- Division by a removable monomial, stated without a field-of-fractions
interpretation of power-series inverse. -/

private theorem factor_tail (d : ℕ) (F : (PowerSeries ℝ)) (h : ∀ k<d, PowerSeries.coeff k F=0) :
    F=PowerSeries.X^d*D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail (fun k => PowerSeries.coeff k F) d := by
  ext k
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases hd : d≤k
  · rw [if_pos hd]
    simp only [D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail,PowerSeries.coeff_mk]
    rw [Nat.add_sub_of_le hd]
  · rw [if_neg hd,h k (by omega)]

@[simp] private theorem tail_constant (d : ℕ) (F : (PowerSeries ℝ)) :
    PowerSeries.constantCoeff (D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail (fun k => PowerSeries.coeff k F) d)=PowerSeries.coeff d F := by simp [D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail]

private theorem numerator_succ (n : ℕ) : numerator (n+1)=numerator n-
    PowerSeries.C (verblunsky n)*PowerSeries.X*denominator n := by
  rw [numerator,monic_star_szego,secondStar_succ,map_sub,map_add,map_smul,
    map_smul,asPS_shift n (phi_mem_window n),asPS_shift n (second_window n)]
  simp only [PowerSeries.smul_eq_C_mul]
  rw [numerator,denominator]
  ring

private theorem denominator_succ (n : ℕ) : denominator (n+1)=PowerSeries.X*denominator n-
    PowerSeries.C (verblunsky n)*numerator n := by
  rw [denominator,monic_szego,second_succ,map_sub,map_add,map_smul,map_smul,
    asPS_shift n (phi_mem_window n),asPS_shift n (second_window n)]
  simp only [PowerSeries.smul_eq_C_mul]
  rw [denominator,numerator]
  ring

private theorem phi_zero : phi 0=T 0 := by
  have h := polynomial_expansion 0 (phi_mem_window 0)
  have hc : coeffLM 0 (phi 0)=1 := phi_monic 0
  simpa [hc] using h

private theorem phiStar_zero : phiStar 0=T 0 := by simp [phiStar,phi_zero]

private theorem asPS_zero : asPS (T (0:ℤ))=(1:(PowerSeries ℝ)) := by
  simpa only [Nat.cast_zero,pow_zero] using (asPS_T 0)

private theorem secondStar_zero : secondStar 0=T 0 := by
  rw [secondStar_expansion,phiStar_zero,asPS_zero]
  simp [caratheodory_constant]

private theorem second_zero : second 0=T 0 := by simp [second,secondStar_zero]

private theorem numerator_zero : numerator 0=caratheodory-1 := by
  rw [numerator,phiStar_zero,secondStar_zero,asPS_zero]
  simp

private theorem denominator_zero : denominator 0=caratheodory+1 := by
  rw [denominator,phi_zero,second_zero,asPS_zero]
  simp

/-- Geronimus for the binding formal Riesz Schur algorithm and its finite
positive Toeplitz moment form. -/
theorem schur_equals_gram (n : ℕ) : alpha n=verblunsky n := by
  apply geronimus_of_pade_data (A:=numerator) (B:=denominator)
    (D:=fun n => D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail (fun k => PowerSeries.coeff k (denominator n)) n) (E:=fun n => D5.S1.Recurrence.Algebraic.RecursiveBoundaryRowSeries.tail (fun k => PowerSeries.coeff k (numerator n)) (n+1)) ?_ n
  constructor
  · exact numerator_zero
  · exact denominator_zero
  · exact numerator_succ
  · exact denominator_succ
  · intro n
    exact factor_tail (n+1) (numerator n) (by intro k hk; exact numerator_low_zero n k (by omega))
  · intro n
    exact factor_tail n (denominator n) (denominator_low_zero n)
  · intro n
    rw [tail_constant,tail_constant,numerator_leading,denominator_leading]
    ring
  · intro n
    rw [tail_constant,denominator_leading]
    exact ne_of_gt (mul_pos (by norm_num) (normSquare_pos n))
  · intro n
    exact ne_of_gt (by linarith [verblunsky_sq_lt_one n])

end D5.S3.Quantum.Walks.CMV.Geronimus
end
